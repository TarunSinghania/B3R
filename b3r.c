/* Bottleneck Bandwidth Buffer and RTT (B3R) congestion control
 */
#include <linux/module.h>
#include <net/tcp.h>
#include <linux/inet_diag.h>
#include <linux/inet.h>
#include <linux/random.h>
#include <linux/win_minmax.h>

/* Scale factor for rate in pkt/uSec unit to avoid truncation in bandwidth
 * estimation. The rate unit ~= (1500 bytes / 1 usec / 2^24) ~= 715 bps.
 * This handles bandwidths from 0.06pps (715bps) to 256Mpps (3Tbps) in a u32.
 * Since the minimum window is >=4 packets, the lower bound isn't
 * an issue. The upper bound isn't an issue with existing technologies.
 */
#define BW_SCALE 24
#define BW_UNIT (1 << BW_SCALE)

#define B3R_SCALE 8	/* scaling factor for fractions in B3R (e.g. gains) */
#define B3R_UNIT (1 << B3R_SCALE)

/* B3R has the following modes for deciding how fast to send: */
enum B3R_mode {
	B3R_STARTUP,	/* ramp up sending rate rapidly to fill pipe */
	B3R_DRAIN,	/* drain any queue created during startup */
	B3R_PROBE_BW,	/* discover, share bw: pace around estimated bw */
	B3R_PROBE_RTT,	/* cut inflight to min to probe min_rtt */
};
enum B3R_probe_bw_queue_state{
	B3R_PROBE_BW_UNKNOWN,
	B3R_LARGE_QUEUE,
	B3R_SMALL_QUEUE
};
//B3R->B3R_queue_state 4 at start , 3 at unknwown(queuestate = 0 ),1 queustate = 1 ,2 queuestate = 2;	
//large queue state 2 ,small queue 1

static int queue_state = 0 ;
//static int unknown_rtt_count = 0 ;
//static int loss_rtt_count = 0 ;
//static int loss_rtt_count_this_cycle = 0 ;
unsigned int max_rtt_stamp = 0 ;

//static int flag = 0 ;
//static int loss_flag = 0;	
static int B3R_max_rtt_win_sec = 30;
/* B3R congestion control block */
struct B3R {
	u32 max_rtt_us;
	u32	min_rtt_us;	        /* min RTT in min_rtt_win_sec window */
	u32	min_rtt_stamp;	        /* timestamp of min_rtt_us */
	u32	probe_rtt_done_stamp;   /* end time for B3R_PROBE_RTT mode */
	struct minmax bw;	/* Max recent delivery rate in pkts/uS << 24 */
	u32	rtt_cnt;	    /* count of packet-timed rounds elapsed */
	u32     next_rtt_delivered; /* scb->tx.delivered at end of round */
	u64	cycle_mstamp;	     /* time of this cycle phase start */
	u32     mode:3,		     /* current B3R_mode in state machine */
		prev_ca_state:3,     /* CA state on previous ACK */
		packet_conservation:1,  /* use packet conservation? */
		round_start:1,	     /* start of packet-timed tx->ack round? */
		idle_restart:1,	     /* restarting after idle? */
		probe_rtt_round_done:1,  /* a B3R_PROBE_RTT round at 4 pkts? */
		B3R_queue_state:3,	
		B3R_gain_num:6,
		unknown_rtt_count:3,
		loss_rtt_count_this_cycle:1,
		lt_is_sampling:1,    /* taking long-term ("LT") samples now? */
		lt_rtt_cnt:7,	     /* round trips in long-term interval */
		lt_use_bw:1;	     /* use lt_bw as our bw estimate? */
	u32	lt_bw;		     /* LT est delivery rate in pkts/uS << 24 */
	u32	lt_last_delivered;   /* LT intvl start: tp->delivered */
	u32	lt_last_stamp;	     /* LT intvl start: tp->delivered_mstamp */
	u32	lt_last_lost;	     /* LT intvl start: tp->lost */
	u32	pacing_gain:10,	/* current gain for setting pacing rate */
		cwnd_gain:10,	/* current gain for setting cwnd */
		full_bw_reached:1,   /* reached full bw in Startup? */
		full_bw_cnt:2,	/* number of rounds without large bw gains */
		cycle_idx:3,	/* current index in pacing_gain cycle array */
		has_seen_rtt:1, /* have we seen an RTT sample yet? */
		flag:1,
		loss_flag:1,
		loss_rtt_count:3;
	u32	prior_cwnd;	/* prior cwnd upon entering loss recovery */
	u32	full_bw;	/* recent bw, to estimate if pipe is full */
};

#define CYCLE_LEN	8	/* number of phases in a pacing gain cycle */

/* Window length of bw filter (in rounds): */
static const int B3R_bw_rtts = CYCLE_LEN + 2;
/* Window length of min_rtt filter (in sec): */
static const u32 B3R_min_rtt_win_sec = 10;
/* Minimum time (in ms) spent at B3R_cwnd_min_target in B3R_PROBE_RTT mode: */
static const u32 B3R_probe_rtt_mode_ms = 200;
/* Skip TSO below the following bandwidth (bits/sec): */
static const int B3R_min_tso_rate = 1200000;

/* We use a high_gain value of 2/ln(2) because it's the smallest pacing gain
 * that will allow a smoothly increasing pacing rate that will double each RTT
 * and send the same number of packets per RTT that an un-paced, slow-starting
 * Reno or CUBIC flow would:
 */
static const int B3R_high_gain  = B3R_UNIT * 2885 / 1000 + 1;
/* The pacing gain of 1/high_gain in B3R_DRAIN is calculated to typically drain
 * the queue created in B3R_STARTUP in a single round:
 */
static const int B3R_drain_gain = B3R_UNIT * 1000 / 2885;
/* The gain for deriving steady-state cwnd tolerates delayed/stretched ACKs: */
static const int B3R_cwnd_gain  = B3R_UNIT * 2;
/* The pacing_gain values for the PROBE_BW gain cycle, to discover/share bw: */
static  int B3R_pacing_gain[] = {
	B3R_UNIT * 5 / 4,	/* probe for more available bw */
	B3R_UNIT * 3 / 4,	/* drain queue and/or yield bw to other flows */
	B3R_UNIT, B3R_UNIT, B3R_UNIT,	/* cruise at 1.0*bw to utilize pipe, */
	B3R_UNIT, B3R_UNIT, B3R_UNIT	/* without creating excess queue... */
};
/* Randomize the starting gain cycling phase over N phases: */
static const u32 B3R_cycle_rand = 7;

/* Try to keep at least this many packets in flight, if things go smoothly. For
 * smooth functioning, a sliding window protocol ACKing every other packet
 * needs at least 4 packets in flight:
 */
static const u32 B3R_cwnd_min_target = 4;

/* To estimate if B3R_STARTUP mode (i.e. high_gain) has filled pipe... */
/* If bw has increased significantly (1.25x), there may be more bw available: */
static const u32 B3R_full_bw_thresh = B3R_UNIT * 5 / 4;
/* But after 3 rounds w/o significant bw growth, estimate pipe is full: */
static const u32 B3R_full_bw_cnt = 3;

/* "long-term" ("LT") bandwidth estimator parameters... */
/* The minimum number of rounds in an LT bw sampling interval: */
static const u32 B3R_lt_intvl_min_rtts = 4;
/* If lost/delivered ratio > 20%, interval is "lossy" and we may be policed: */
static const u32 B3R_lt_loss_thresh = 50;
/* If 2 intervals have a bw ratio <= 1/8, their bw is "consistent": */
static const u32 B3R_lt_bw_ratio = B3R_UNIT / 8;
/* If 2 intervals have a bw diff <= 4 Kbit/sec their bw is "consistent": */
static const u32 B3R_lt_bw_diff = 4000 / 8;
/* If we estimate we're policed, use lt_bw for this many round trips: */
static const u32 B3R_lt_bw_max_rtts = 48;

static void B3R_check_probe_rtt_done(struct sock *sk);

/* Do we estimate that STARTUP filled the pipe? */
static bool B3R_full_bw_reached(const struct sock *sk)
{
	const struct B3R *B3R = inet_csk_ca(sk);

	return B3R->full_bw_reached;
}

/* Return the windowed max recent bandwidth sample, in pkts/uS << BW_SCALE. */
static u32 B3R_max_bw(const struct sock *sk)
{
	struct B3R *B3R = inet_csk_ca(sk);

	return minmax_get(&B3R->bw);
}

/* Return the estimated bandwidth of the path, in pkts/uS << BW_SCALE. */
static u32 B3R_bw(const struct sock *sk)
{
	struct B3R *B3R = inet_csk_ca(sk);

	return B3R->lt_use_bw ? B3R->lt_bw : B3R_max_bw(sk);
}

/* Return rate in bytes per second, optionally with a gain.
 * The order here is chosen carefully to avoid overflow of u64. This should
 * work for input rates of up to 2.9Tbit/sec and gain of 2.89x.
 */
static u64 B3R_rate_bytes_per_sec(struct sock *sk, u64 rate, int gain)
{
	unsigned int mss = tcp_sk(sk)->mss_cache;

	if (!tcp_needs_internal_pacing(sk))
		mss = tcp_mss_to_mtu(sk, mss);
	rate *= mss;
	rate *= gain;
	rate >>= B3R_SCALE;
	rate *= USEC_PER_SEC;
	return rate >> BW_SCALE;
}

/* Convert a B3R bw and gain factor to a pacing rate in bytes per second. */
static u32 B3R_bw_to_pacing_rate(struct sock *sk, u32 bw, int gain)
{
	u64 rate = bw;

	rate = B3R_rate_bytes_per_sec(sk, rate, gain);
	rate = min_t(u64, rate, sk->sk_max_pacing_rate);
	return rate;
}

/* Initialize pacing rate to: high_gain * init_cwnd / RTT. */
static void B3R_init_pacing_rate_from_rtt(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	u64 bw;
	u32 rtt_us;

	if (tp->srtt_us) {		/* any RTT sample yet? */
		rtt_us = max(tp->srtt_us >> 3, 1U);
		B3R->has_seen_rtt = 1;
	} else {			 /* no RTT sample yet */
		rtt_us = USEC_PER_MSEC;	 /* use nominal default RTT */
	}
	bw = (u64)tp->snd_cwnd * BW_UNIT;
	do_div(bw, rtt_us);
	sk->sk_pacing_rate = B3R_bw_to_pacing_rate(sk, bw, B3R_high_gain);
}

/* Pace using current bw estimate and a gain factor. In order to help drive the
 * network toward lower queues while maintaining high utilization and low
 * latency, the average pacing rate aims to be slightly (~1%) lower than the
 * estimated bandwidth. This is an important aspect of the design. In this
 * implementation this slightly lower pacing rate is achieved implicitly by not
 * including link-layer headers in the packet size used for the pacing rate.
 */
static void B3R_set_pacing_rate(struct sock *sk, u32 bw, int gain)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	u32 rate = B3R_bw_to_pacing_rate(sk, bw, gain);

	if (unlikely(!B3R->has_seen_rtt && tp->srtt_us))
		B3R_init_pacing_rate_from_rtt(sk);
	if (B3R_full_bw_reached(sk) || rate > sk->sk_pacing_rate)
		sk->sk_pacing_rate = rate;
}

/* override sysctl_tcp_min_tso_segs */
static u32 B3R_min_tso_segs(struct sock *sk)
{
	return sk->sk_pacing_rate < (B3R_min_tso_rate >> 3) ? 1 : 2;
}

static u32 B3R_tso_segs_goal(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 segs, bytes;

	/* Sort of tcp_tso_autosize() but ignoring
	 * driver provided sk_gso_max_size.
	 */
	bytes = min_t(u32, sk->sk_pacing_rate >> sk->sk_pacing_shift,
		      GSO_MAX_SIZE - 1 - MAX_TCP_HEADER);
	segs = max_t(u32, bytes / tp->mss_cache, B3R_min_tso_segs(sk));

	return min(segs, 0x7FU);
}

/* Save "last known good" cwnd so we can restore it after losses or PROBE_RTT */
static void B3R_save_cwnd(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);

	if (B3R->prev_ca_state < TCP_CA_Recovery && B3R->mode != B3R_PROBE_RTT)
		B3R->prior_cwnd = tp->snd_cwnd;  /* this cwnd is good enough */
	else  /* loss recovery or B3R_PROBE_RTT have temporarily cut cwnd */
		B3R->prior_cwnd = max(B3R->prior_cwnd, tp->snd_cwnd);
}

static void B3R_cwnd_event(struct sock *sk, enum tcp_ca_event event)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);

	if (event == CA_EVENT_TX_START && tp->app_limited) {
		B3R->idle_restart = 1;
		/* Avoid pointless buffer overflows: pace at est. bw if we don't
		 * need more speed (we're restarting from idle and app-limited).
		 */
		if (B3R->mode == B3R_PROBE_BW)
			B3R_set_pacing_rate(sk, B3R_bw(sk), B3R_UNIT);
		else if (B3R->mode == B3R_PROBE_RTT)
			B3R_check_probe_rtt_done(sk);
	}
}

/* Find target cwnd. Right-size the cwnd based on min RTT and the
 * estimated bottleneck bandwidth:
 *
 * cwnd = bw * min_rtt * gain = BDP * gain
 *
 * The key factor, gain, controls the amount of queue. While a small gain
 * builds a smaller queue, it becomes more vulnerable to noise in RTT
 * measurements (e.g., delayed ACKs or other ACK compression effects). This
 * noise may cause B3R to under-estimate the rate.
 *
 * To achieve full performance in high-speed paths, we budget enough cwnd to
 * fit full-sized skbs in-flight on both end hosts to fully utilize the path:
 *   - one skb in sending host Qdisc,
 *   - one skb in sending host TSO/GSO engine
 *   - one skb being received by receiver host LRO/GRO/delayed-ACK engine
 * Don't worry, at low rates (B3R_min_tso_rate) this won't bloat cwnd because
 * in such cases tso_segs_goal is 1. The minimum cwnd is 4 packets,
 * which allows 2 outstanding 2-packet sequences, to try to keep pipe
 * full even with ACK-every-other-packet delayed ACKs.
 */
static u32 B3R_target_cwnd(struct sock *sk, u32 bw, int gain)
{
	struct B3R *B3R = inet_csk_ca(sk);
	u32 cwnd;
	u64 w;

	/* If we've never had a valid RTT sample, cap cwnd at the initial
	 * default. This should only happen when the connection is not using TCP
	 * timestamps and has retransmitted all of the SYN/SYNACK/data packets
	 * ACKed so far. In this case, an RTO can cut cwnd to 1, in which
	 * case we need to slow-start up toward something safe: TCP_INIT_CWND.
	 */
	if (unlikely(B3R->min_rtt_us == ~0U))	 /* no valid RTT samples yet? */
		return TCP_INIT_CWND;  /* be safe: cap at default initial cwnd*/

	w = (u64)bw * B3R->min_rtt_us;

	/* Apply a gain to the given value, then remove the BW_SCALE shift. */
	cwnd = (((w * gain) >> B3R_SCALE) + BW_UNIT - 1) / BW_UNIT;

	/* Allow enough full-sized skbs in flight to utilize end systems. */
	cwnd += 3 * B3R_tso_segs_goal(sk);

	/* Reduce delayed ACKs by rounding up cwnd to the next even number. */
	cwnd = (cwnd + 1) & ~1U;

	/* Ensure gain cycling gets inflight above BDP even for small BDPs. */
	if (B3R->mode == B3R_PROBE_BW && gain > B3R_UNIT)
		cwnd += 2;

	return cwnd;
}

/* An optimization in B3R to reduce losses: On the first round of recovery, we
 * follow the packet conservation principle: send P packets per P packets acked.
 * After that, we slow-start and send at most 2*P packets per P packets acked.
 * After recovery finishes, or upon undo, we restore the cwnd we had when
 * recovery started (capped by the target cwnd based on estimated BDP).
 *
 * TODO(ycheng/ncardwell): implement a rate-based approach.
 */
static bool B3R_set_cwnd_to_recover_or_restore(
	struct sock *sk, const struct rate_sample *rs, u32 acked, u32 *new_cwnd)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	u8 prev_state = B3R->prev_ca_state, state = inet_csk(sk)->icsk_ca_state;
	u32 cwnd = tp->snd_cwnd;

	/* An ACK for P pkts should release at most 2*P packets. We do this
	 * in two steps. First, here we deduct the number of lost packets.
	 * Then, in B3R_set_cwnd() we slow start up toward the target cwnd.
	 */
	if (rs->losses > 0)
		cwnd = max_t(s32, cwnd - rs->losses, 1);

	if (state == TCP_CA_Recovery && prev_state != TCP_CA_Recovery) {
		/* Starting 1st round of Recovery, so do packet conservation. */
		B3R->packet_conservation = 1;
		B3R->next_rtt_delivered = tp->delivered;  /* start round now */
		/* Cut unused cwnd from app behavior, TSQ, or TSO deferral: */
		cwnd = tcp_packets_in_flight(tp) + acked;
	} else if (prev_state >= TCP_CA_Recovery && state < TCP_CA_Recovery) {
		/* Exiting loss recovery; restore cwnd saved before recovery. */
		cwnd = max(cwnd, B3R->prior_cwnd);
		B3R->packet_conservation = 0;
	}
	B3R->prev_ca_state = state;

	if (B3R->packet_conservation) {
		*new_cwnd = max(cwnd, tcp_packets_in_flight(tp) + acked);
		return true;	/* yes, using packet conservation */
	}
	*new_cwnd = cwnd;
	return false;
}

/* Slow-start up toward target cwnd (if bw estimate is growing, or packet loss
 * has drawn us down below target), or snap down to target if we're above it.
 */
static void B3R_set_cwnd(struct sock *sk, const struct rate_sample *rs,
			 u32 acked, u32 bw, int gain)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	u32 cwnd = tp->snd_cwnd, target_cwnd = 0;

	if (!acked)
		goto done;  /* no packet fully ACKed; just apply caps */

	if (B3R_set_cwnd_to_recover_or_restore(sk, rs, acked, &cwnd))
		goto done;

	/* If we're below target cwnd, slow start cwnd toward target cwnd. */
	target_cwnd = B3R_target_cwnd(sk, bw, gain);
	if (B3R_full_bw_reached(sk))  /* only cut cwnd if we filled the pipe */
		cwnd = min(cwnd + acked, target_cwnd);
	else if (cwnd < target_cwnd || tp->delivered < TCP_INIT_CWND)
		cwnd = cwnd + acked;
	cwnd = max(cwnd, B3R_cwnd_min_target);

done:
	tp->snd_cwnd = min(cwnd, tp->snd_cwnd_clamp);	/* apply global cap */
	if (B3R->mode == B3R_PROBE_RTT)  /* drain queue, refresh min_rtt */
		tp->snd_cwnd = min(tp->snd_cwnd, B3R_cwnd_min_target);
}


static void B3R_advance_cycle_phase(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);

	B3R->cycle_idx = (B3R->cycle_idx + 1) & (CYCLE_LEN - 1);
	B3R->cycle_mstamp = tp->delivered_mstamp;
	B3R->pacing_gain = B3R->lt_use_bw ? B3R_UNIT :
					    B3R_pacing_gain[B3R->cycle_idx];
}



static void B3R_advance_cycle_phase_small_queue(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	B3R->flag = 0 ;
	

	if(B3R->cycle_idx == 1 && B3R->loss_flag == 0 && B3R->B3R_gain_num<50)
	{
		B3R->B3R_gain_num = B3R->B3R_gain_num + 2;
		B3R_pacing_gain[0] = B3R_UNIT*B3R->B3R_gain_num/40;

	}
	if(B3R->cycle_idx != 0){
		B3R->loss_flag = 0 ;
	}
	B3R->cycle_idx = (B3R->cycle_idx + 1) & (CYCLE_LEN - 1);
	B3R->cycle_mstamp = tp->delivered_mstamp;
	B3R->pacing_gain = B3R->lt_use_bw ? B3R_UNIT :
					    B3R_pacing_gain[B3R->cycle_idx];

}



static void B3R_reset_probe_bw_mode(struct sock *sk)
{
	struct B3R *B3R = inet_csk_ca(sk);

	B3R->mode = B3R_PROBE_BW;
	B3R->pacing_gain = B3R_UNIT;
	B3R->cwnd_gain = B3R_cwnd_gain;
	// ON GOING TO QUEUE MODE RESET GAIN TO 1.25
	B3R_pacing_gain[0] = B3R_UNIT*5/4;
	//queue state 
	queue_state = 2 ;
	B3R->B3R_queue_state = 2;
	B3R->cycle_idx = CYCLE_LEN - 1 - prandom_u32_max(B3R_cycle_rand);
	B3R_advance_cycle_phase(sk);	/* flip to next phase of gain cycle */
}


static void B3R_reset_probe_bw_mode_small_queue(struct sock *sk)
{
	struct B3R *B3R = inet_csk_ca(sk);
	B3R->mode = B3R_PROBE_BW;
	B3R->pacing_gain = B3R_UNIT;
	B3R->cwnd_gain = B3R_cwnd_gain;
	B3R->cycle_idx = CYCLE_LEN - 1 - prandom_u32_max(B3R_cycle_rand);
	queue_state = 1 ;
	B3R->B3R_queue_state =1;
	B3R_advance_cycle_phase_small_queue(sk);	/* flip to next phase of gain cycle */
}

static void B3R_advance_cycle_phase_unknown_queue(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);

	if(B3R->unknown_rtt_count == 4){
		if(B3R->max_rtt_us > (3*B3R->min_rtt_us)/2 && B3R->loss_rtt_count <= 1 )
		{
			B3R_reset_probe_bw_mode(sk);
			B3R->loss_flag = 0;
		}
		else if(B3R->max_rtt_us > (3*B3R->min_rtt_us)/2)
		{
			B3R_reset_probe_bw_mode(sk);
			B3R->loss_flag = 1;

		}
		else if(B3R->loss_rtt_count >= 3)//3 out of three cycles
		B3R_reset_probe_bw_mode_small_queue(sk);
		else
		B3R_reset_probe_bw_mode(sk);
		
	}	
	
	//starts from count 1, first cycle 
	if(B3R->unknown_rtt_count < 4 && B3R->cycle_idx == 1){
	B3R->unknown_rtt_count = B3R->unknown_rtt_count +1;
	B3R->loss_rtt_count_this_cycle = 0;
	}
	B3R->cycle_idx = (B3R->cycle_idx + 1) & (CYCLE_LEN - 1);
	B3R->cycle_mstamp = tp->delivered_mstamp;
	//do not use lt_bw_pacing_rate
	B3R->pacing_gain =  B3R_pacing_gain[B3R->cycle_idx];
}


static void B3R_reset_probe_bw_unknown_mode(struct sock *sk)
{
	struct B3R *B3R = inet_csk_ca(sk);

	B3R->mode = B3R_PROBE_BW;
	B3R->pacing_gain = B3R_UNIT;
	B3R_pacing_gain[0] = B3R_UNIT*5/4;
	B3R->cwnd_gain = B3R_cwnd_gain;
	B3R->cycle_idx = 1;
	B3R->unknown_rtt_count = 0 ;
	B3R->B3R_queue_state =3;
	queue_state = 0 ;
	B3R->loss_rtt_count = 0 ;
	B3R->loss_rtt_count_this_cycle = 0 ;
	B3R->loss_flag = 0;	
	
	B3R_advance_cycle_phase_unknown_queue(sk);	/* flip to next phase of gain cycle */
}


/* End cycle phase if it's time and/or we hit the phase's in-flight target. */
static bool B3R_is_next_cycle_phase(struct sock *sk,
				    const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);

	bool is_full_length2 =
		tcp_stamp_us_delta(tp->delivered_mstamp, B3R->cycle_mstamp) >
		B3R->min_rtt_us;
		

	bool is_full_length;

	u32 inflight, bw,max_queue_delay;
	max_queue_delay = B3R->max_rtt_us - B3R->min_rtt_us;
	if(max_queue_delay >0)
	is_full_length =tcp_stamp_us_delta(tp->delivered_mstamp, B3R->cycle_mstamp) >
		(max_queue_delay/8);
	else	
	is_full_length =tcp_stamp_us_delta(tp->delivered_mstamp, B3R->cycle_mstamp) >
		B3R->min_rtt_us;

	/* The pacing_gain of 1.0 paces at the estimated bw to try to fully
	 * use the pipe without increasing the queue.
	 */
	if (B3R->pacing_gain == B3R_UNIT)
		return is_full_length2;		/* just use wall clock time */

	inflight = rs->prior_in_flight;  /* what was in-flight before ACK? */
	bw = B3R_max_bw(sk);

	/* A pacing_gain > 1.0 probes for bw by trying to raise inflight to at
	 * least pacing_gain*BDP; this may take more than min_rtt if min_rtt is
	 * small (e.g. on a LAN). We do not persist if packets are lost, since
	 * a path with small buffers may not hold that much.
	 */
	if (B3R->pacing_gain > B3R_UNIT)
		return is_full_length &&
			(rs->losses ||  /* perhaps pacing_gain*BDP won't fit */
			 inflight >= B3R_target_cwnd(sk, bw, B3R->pacing_gain));

	/* A pacing_gain < 1.0 tries to drain extra queue we added if bw
	 * probing didn't find more bw. If inflight falls to match BDP then we
	 * estimate queue is drained; persisting would underutilize the pipe.
	 */

	if((B3R->max_rtt_us -B3R->min_rtt_us ) < (3*B3R->min_rtt_us)/2)
	{	if(B3R->loss_flag == 0)
			return(is_full_length || inflight <= B3R_target_cwnd(sk, bw, B3R_UNIT*15/16));
		else
			return(is_full_length2 && inflight <= B3R_target_cwnd(sk, bw, B3R_UNIT*15/16));
	}
	return is_full_length || inflight <= B3R_target_cwnd(sk, bw, B3R_UNIT);

}

static bool B3R_is_next_cycle_phase_small_queue(struct sock *sk,
				    const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	bool is_full_length =
		tcp_stamp_us_delta(tp->delivered_mstamp, B3R->cycle_mstamp) >
		B3R->min_rtt_us;

	u32 inflight, bw;

	
	if (B3R->pacing_gain == B3R_UNIT)
		return is_full_length;		/* just use wall clock time */

	inflight = rs->prior_in_flight;  /* what was in-flight before ACK? */
	bw = B3R_max_bw(sk);

	
	
	if(rs->losses)
		B3R->loss_flag = 1;

	if (B3R->pacing_gain > B3R_UNIT)
	{		
			if(B3R->B3R_gain_num > 42 && rs->losses && B3R->flag == 0 )
			{
			B3R->B3R_gain_num = B3R->B3R_gain_num - 4;
	 		B3R_pacing_gain[0] = B3R_UNIT*B3R->B3R_gain_num/40;
			B3R->flag = 1 ;
			}


		return is_full_length &&
			(rs->losses ||  /* perhaps pacing_gain*BDP won't fit */
			 inflight >= B3R_target_cwnd(sk, bw, B3R->pacing_gain));
	
	}


	if(B3R->B3R_gain_num > 42 && rs->losses && B3R->flag == 0 )
	{
			B3R->B3R_gain_num = B3R->B3R_gain_num - 2;
	 		B3R_pacing_gain[0] = B3R_UNIT*B3R->B3R_gain_num/40;
			B3R->flag = 1 ;
	}
	
	//if(B3R->B3R_gain_num >=46 )
	return is_full_length ||
		inflight <= B3R_target_cwnd(sk, bw, B3R_UNIT);
	//else
	//return inflight <= B3R_target_cwnd(sk, bw, B3R_UNIT*3/4);
}


static bool B3R_is_next_cycle_phase_unknown_queue(struct sock *sk,
				    const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	bool is_full_length =
		tcp_stamp_us_delta(tp->delivered_mstamp, B3R->cycle_mstamp) >
		B3R->min_rtt_us;
	u32 inflight, bw;

	/* The pacing_gain of 1.0 paces at the estimated bw to try to fully
	 * use the pipe without increasing the queue.
	 */
	if (B3R->pacing_gain == B3R_UNIT)
		return is_full_length;		/* just use wall clock time */

	inflight = rs->prior_in_flight;  /* what was in-flight before ACK? */
	bw = B3R_max_bw(sk);

	/* A pacing_gain > 1.0 probes for bw by trying to raise inflight to at
	 * least pacing_gain*BDP; this may take more than min_rtt if min_rtt is
	 * small (e.g. on a LAN). We do not persist if packets are lost, since
	 * a path with small buffers may not hold that much.
	 */
	
	if (rs->losses && B3R->loss_rtt_count_this_cycle == 0){
		B3R->loss_rtt_count = B3R->loss_rtt_count + 1;
		B3R->loss_rtt_count_this_cycle = 1;
	}

	if (B3R->pacing_gain > B3R_UNIT)
		return is_full_length &&
			(rs->losses ||  /* perhaps pacing_gain*BDP won't fit */
			 inflight >= B3R_target_cwnd(sk, bw, B3R->pacing_gain));

	/* A pacing_gain < 1.0 tries to drain extra queue we added if bw
	 * probing didn't find more bw. If inflight falls to match BDP then we
	 * estimate queue is drained; persisting would underutilize the pipe.
	 */
	return is_full_length ||
		inflight <= B3R_target_cwnd(sk, bw, B3R_UNIT);
}

/* Gain cycling: cycle pacing gain to converge to fair share of available bw. */
static void B3R_update_cycle_phase(struct sock *sk,
				   const struct rate_sample *rs)
{
	struct B3R *B3R = inet_csk_ca(sk);

	if (B3R->mode == B3R_PROBE_BW && B3R->B3R_queue_state == 2 && B3R_is_next_cycle_phase(sk, rs))
		B3R_advance_cycle_phase(sk);

	if (B3R->mode == B3R_PROBE_BW && B3R->B3R_queue_state == 3 && B3R_is_next_cycle_phase_unknown_queue(sk, rs))
		B3R_advance_cycle_phase_unknown_queue(sk);

	if(B3R->mode == B3R_PROBE_BW && B3R->B3R_queue_state == 1 && B3R_is_next_cycle_phase_small_queue(sk,rs))
		B3R_advance_cycle_phase_small_queue(sk);
}

static void B3R_reset_startup_mode(struct sock *sk)
{
	struct B3R *B3R = inet_csk_ca(sk);

	B3R->mode = B3R_STARTUP;
	B3R->pacing_gain = B3R_high_gain;
	B3R->cwnd_gain	 = B3R_high_gain;
}

static void B3R_reset_mode(struct sock *sk)
{
	if (!B3R_full_bw_reached(sk))
		B3R_reset_startup_mode(sk);
	else
		B3R_reset_probe_bw_unknown_mode(sk);
//B3R_reset_probe_bw_mode(sk);
}

/* Start a new long-term sampling interval. */
static void B3R_reset_lt_bw_sampling_interval(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);

	B3R->lt_last_stamp = div_u64(tp->delivered_mstamp, USEC_PER_MSEC);
	B3R->lt_last_delivered = tp->delivered;
	B3R->lt_last_lost = tp->lost;
	B3R->lt_rtt_cnt = 0;
}

/* Completely reset long-term bandwidth sampling. */
static void B3R_reset_lt_bw_sampling(struct sock *sk)
{
	struct B3R *B3R = inet_csk_ca(sk);

	B3R->lt_bw = 0;
	B3R->lt_use_bw = 0;
	B3R->lt_is_sampling = false;
	B3R_reset_lt_bw_sampling_interval(sk);
}

/* Long-term bw sampling interval is done. Estimate whether we're policed. */
static void B3R_lt_bw_interval_done(struct sock *sk, u32 bw)
{
	struct B3R *B3R = inet_csk_ca(sk);
	u32 diff;

	if (B3R->lt_bw) {  /* do we have bw from a previous interval? */
		/* Is new bw close to the lt_bw from the previous interval? */
		diff = abs(bw - B3R->lt_bw);
		if ((diff * B3R_UNIT <= B3R_lt_bw_ratio * B3R->lt_bw) ||
		    (B3R_rate_bytes_per_sec(sk, diff, B3R_UNIT) <=
		     B3R_lt_bw_diff)) {
			/* All criteria are met; estimate we're policed. */
			B3R->lt_bw = (bw + B3R->lt_bw) >> 1;  /* avg 2 intvls */
			B3R->lt_use_bw = 1;
			B3R->pacing_gain = B3R_UNIT;  /* try to avoid drops */
			B3R->lt_rtt_cnt = 0;
			return;
		}
	}
	B3R->lt_bw = bw;
	B3R_reset_lt_bw_sampling_interval(sk);
	
}

/* Token-bucket traffic policers are common (see "An Internet-Wide Analysis of
 * Traffic Policing", SIGCOMM 2016). B3R detects token-bucket policers and
 * explicitly models their policed rate, to reduce unnecessary losses. We
 * estimate that we're policed if we see 2 consecutive sampling intervals with
 * consistent throughput and high packet loss. If we think we're being policed,
 * set lt_bw to the "long-term" average delivery rate from those 2 intervals.
 */
static void B3R_lt_bw_sampling(struct sock *sk, const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	u32 lost, delivered;
	u64 bw;
	u32 t;

	if (B3R->lt_use_bw) {	/* already using long-term rate, lt_bw? */
		if (B3R->mode == B3R_PROBE_BW && B3R->round_start &&
		    ++B3R->lt_rtt_cnt >= B3R_lt_bw_max_rtts) {
			B3R_reset_lt_bw_sampling(sk);    /* stop using lt_bw */
			if(B3R->B3R_queue_state == 1)
			B3R_reset_probe_bw_mode_small_queue(sk);
			else
			B3R_reset_probe_bw_mode(sk);
			  /* restart gain cycling */
		}
		return;
	}

	/* Wait for the first loss before sampling, to let the policer exhaust
	 * its tokens and estimate the steady-state rate allowed by the policer.
	 * Starting samples earlier includes bursts that over-estimate the bw.
	 */
	if (!B3R->lt_is_sampling) {
		if (!rs->losses)
			return;
		B3R_reset_lt_bw_sampling_interval(sk);
		B3R->lt_is_sampling = true;
	}

	/* To avoid underestimates, reset sampling if we run out of data. */
	if (rs->is_app_limited) {
		B3R_reset_lt_bw_sampling(sk);
		return;
	}

	if (B3R->round_start)
		B3R->lt_rtt_cnt++;	/* count round trips in this interval */
	if (B3R->lt_rtt_cnt < B3R_lt_intvl_min_rtts)
		return;		/* sampling interval needs to be longer */
	if (B3R->lt_rtt_cnt > 4 * B3R_lt_intvl_min_rtts) {
		B3R_reset_lt_bw_sampling(sk);  /* interval is too long */
		return;
	}

	/* End sampling interval when a packet is lost, so we estimate the
	 * policer tokens were exhausted. Stopping the sampling before the
	 * tokens are exhausted under-estimates the policed rate.
	 */
	if (!rs->losses)
		return;

	/* Calculate packets lost and delivered in sampling interval. */
	lost = tp->lost - B3R->lt_last_lost;
	delivered = tp->delivered - B3R->lt_last_delivered;
	/* Is loss rate (lost/delivered) >= lt_loss_thresh? If not, wait. */
	if (!delivered || (lost << B3R_SCALE) < B3R_lt_loss_thresh * delivered)
		return;

	/* Find average delivery rate in this sampling interval. */
	t = div_u64(tp->delivered_mstamp, USEC_PER_MSEC) - B3R->lt_last_stamp;
	if ((s32)t < 1)
		return;		/* interval is less than one ms, so wait */
	/* Check if can multiply without overflow */
	if (t >= ~0U / USEC_PER_MSEC) {
		B3R_reset_lt_bw_sampling(sk);  /* interval too long; reset */
		return;
	}
	t *= USEC_PER_MSEC;
	bw = (u64)delivered * BW_UNIT;
	do_div(bw, t);
	B3R_lt_bw_interval_done(sk, bw);
}

/* Estimate the bandwidth based on how fast packets are delivered */
static void B3R_update_bw(struct sock *sk, const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	u64 bw;

	B3R->round_start = 0;
	if (rs->delivered < 0 || rs->interval_us <= 0)
		return; /* Not a valid observation */

	/* See if we've reached the next RTT */
	if (!before(rs->prior_delivered, B3R->next_rtt_delivered)) {
		B3R->next_rtt_delivered = tp->delivered;
		B3R->rtt_cnt++;
		B3R->round_start = 1;
		B3R->packet_conservation = 0;
	}

	B3R_lt_bw_sampling(sk, rs);

	/* Divide delivered by the interval to find a (lower bound) bottleneck
	 * bandwidth sample. Delivered is in packets and interval_us in uS and
	 * ratio will be <<1 for most connections. So delivered is first scaled.
	 */
	bw = (u64)rs->delivered * BW_UNIT;
	do_div(bw, rs->interval_us);

	/* If this sample is application-limited, it is likely to have a very
	 * low delivered count that represents application behavior rather than
	 * the available network rate. Such a sample could drag down estimated
	 * bw, causing needless slow-down. Thus, to continue to send at the
	 * last measured network rate, we filter out app-limited samples unless
	 * they describe the path bw at least as well as our bw model.
	 *
	 * So the goal during app-limited phase is to proceed with the best
	 * network rate no matter how long. We automatically leave this
	 * phase when app writes faster than the network can deliver :)
	 */
	if (!rs->is_app_limited || bw >= B3R_max_bw(sk)) {
		/* Incorporate new sample into our max bw filter. */
		minmax_running_max(&B3R->bw, B3R_bw_rtts, B3R->rtt_cnt, bw);
	}
}

/* Estimate when the pipe is full, using the change in delivery rate: B3R
 * estimates that STARTUP filled the pipe if the estimated bw hasn't changed by
 * at least B3R_full_bw_thresh (25%) after B3R_full_bw_cnt (3) non-app-limited
 * rounds. Why 3 rounds: 1: rwin autotuning grows the rwin, 2: we fill the
 * higher rwin, 3: we get higher delivery rate samples. Or transient
 * cross-traffic or radio noise can go away. CUBIC Hystart shares a similar
 * design goal, but uses delay and inter-ACK spacing instead of bandwidth.
 */
static void B3R_check_full_bw_reached(struct sock *sk,
				      const struct rate_sample *rs)
{
	struct B3R *B3R = inet_csk_ca(sk);
	u32 bw_thresh;

	if (B3R_full_bw_reached(sk) || !B3R->round_start || rs->is_app_limited)
		return;

	bw_thresh = (u64)B3R->full_bw * B3R_full_bw_thresh >> B3R_SCALE;
	if (B3R_max_bw(sk) >= bw_thresh) {
		B3R->full_bw = B3R_max_bw(sk);
		B3R->full_bw_cnt = 0;
		return;
	}
	++B3R->full_bw_cnt;
	B3R->full_bw_reached = B3R->full_bw_cnt >= B3R_full_bw_cnt;
}

/* If pipe is probably full, drain the queue and then enter steady-state. */
static void B3R_check_drain(struct sock *sk, const struct rate_sample *rs)
{
	struct B3R *B3R = inet_csk_ca(sk);

	if (B3R->mode == B3R_STARTUP && B3R_full_bw_reached(sk)) {
		B3R->mode = B3R_DRAIN;	/* drain queue we created */
		B3R->pacing_gain = B3R_drain_gain;	/* pace slow to drain */
		B3R->cwnd_gain = B3R_high_gain;	/* maintain cwnd */
		tcp_sk(sk)->snd_ssthresh =
				B3R_target_cwnd(sk, B3R_max_bw(sk), B3R_UNIT);
	}	/* fall through to check if in-flight is already small: */
	if (B3R->mode == B3R_DRAIN &&
	    tcp_packets_in_flight(tcp_sk(sk)) <=
	    B3R_target_cwnd(sk, B3R_max_bw(sk), B3R_UNIT))
		B3R_reset_probe_bw_unknown_mode(sk);  /* we estimate queue is drained */
}

static void B3R_check_probe_rtt_done(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);

	if (!(B3R->probe_rtt_done_stamp &&
	      after(tcp_jiffies32, B3R->probe_rtt_done_stamp)))
		return;

	B3R->min_rtt_stamp = tcp_jiffies32;  /* wait a while until PROBE_RTT */
	tp->snd_cwnd = max(tp->snd_cwnd, B3R->prior_cwnd);
	B3R_reset_mode(sk);
}

/* The goal of PROBE_RTT mode is to have B3R flows cooperatively and
 * periodically drain the bottleneck queue, to converge to measure the true
 * min_rtt (unloaded propagation delay). This allows the flows to keep queues
 * small (reducing queuing delay and packet loss) and achieve fairness among
 * B3R flows.
 *
 * The min_rtt filter window is 10 seconds. When the min_rtt estimate expires,
 * we enter PROBE_RTT mode and cap the cwnd at B3R_cwnd_min_target=4 packets.
 * After at least B3R_probe_rtt_mode_ms=200ms and at least one packet-timed
 * round trip elapsed with that flight size <= 4, we leave PROBE_RTT mode and
 * re-enter the previous mode. B3R uses 200ms to approximately bound the
 * performance penalty of PROBE_RTT's cwnd capping to roughly 2% (200ms/10s).
 *
 * Note that flows need only pay 2% if they are busy sending over the last 10
 * seconds. Interactive applications (e.g., Web, RPCs, video chunks) often have
 * natural silences or low-rate periods within 10 seconds where the rate is low
 * enough for long enough to drain its queue in the bottleneck. We pick up
 * these min RTT measurements opportunistically with our min_rtt filter. :-)
 */
static void B3R_update_min_rtt(struct sock *sk, const struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);
	bool filter_expired,max_filter_expired;
	/* Track min RTT seen in the min_rtt_win_sec filter window: */
	filter_expired = after(tcp_jiffies32,
			       B3R->min_rtt_stamp + B3R_min_rtt_win_sec * HZ);
	if (rs->rtt_us >= 0 &&
	    (rs->rtt_us <= B3R->min_rtt_us ||
	     (filter_expired && !rs->is_ack_delayed))) {
		B3R->min_rtt_us = rs->rtt_us;
		B3R->min_rtt_stamp = tcp_jiffies32;
	}


	max_filter_expired= after(tcp_jiffies32,
			       max_rtt_stamp + B3R_max_rtt_win_sec * HZ);

	if(rs->rtt_us >= 0 && rs->rtt_us >=  B3R->max_rtt_us )
	{
		max_rtt_stamp = tcp_jiffies32;
		B3R->max_rtt_us = rs->rtt_us;
	}

	if(max_filter_expired)
	{	
		max_rtt_stamp = tcp_jiffies32;
		//if(2*B3R->min_rtt_us>B3R->max_rtt_us)
		B3R->max_rtt_us = B3R->min_rtt_us;
	}

	if (B3R_probe_rtt_mode_ms > 0 && filter_expired &&
	    !B3R->idle_restart && B3R->mode != B3R_PROBE_RTT) {
		B3R->mode = B3R_PROBE_RTT;  /* dip, drain queue */
		B3R->pacing_gain = B3R_UNIT;
		B3R->cwnd_gain = B3R_UNIT;
		B3R_save_cwnd(sk);  /* note cwnd so we can restore it */
		B3R->probe_rtt_done_stamp = 0;
	}

	if (B3R->mode == B3R_PROBE_RTT) {
		/* Ignore low rate samples during this mode. */
		tp->app_limited =
			(tp->delivered + tcp_packets_in_flight(tp)) ? : 1;
		/* Maintain min packets in flight for max(200 ms, 1 round). */
		if (!B3R->probe_rtt_done_stamp &&
		    tcp_packets_in_flight(tp) <= B3R_cwnd_min_target) {
			B3R->probe_rtt_done_stamp = tcp_jiffies32 +
				msecs_to_jiffies(B3R_probe_rtt_mode_ms);
			B3R->probe_rtt_round_done = 0;
			B3R->next_rtt_delivered = tp->delivered;
		} else if (B3R->probe_rtt_done_stamp) {
			if (B3R->round_start)
				B3R->probe_rtt_round_done = 1;
			if (B3R->probe_rtt_round_done)
				B3R_check_probe_rtt_done(sk);
		}
	}
	/* Restart after idle ends only once we process a new S/ACK for data */
	if (rs->delivered > 0)
		B3R->idle_restart = 0;
}

static void B3R_update_model(struct sock *sk, const struct rate_sample *rs)
{
	B3R_update_bw(sk, rs);
	B3R_update_cycle_phase(sk, rs);
	B3R_check_full_bw_reached(sk, rs);
	B3R_check_drain(sk, rs);
	B3R_update_min_rtt(sk, rs);
}

static void B3R_main(struct sock *sk, const struct rate_sample *rs)
{
	struct B3R *B3R = inet_csk_ca(sk);
	u32 bw;

	B3R_update_model(sk, rs);

	bw = B3R_bw(sk);
	B3R_set_pacing_rate(sk, bw, B3R->pacing_gain);
	B3R_set_cwnd(sk, rs, rs->acked_sacked, bw, B3R->cwnd_gain);
}

static void B3R_init(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct B3R *B3R = inet_csk_ca(sk);

	B3R->prior_cwnd = 0;
	tp->snd_ssthresh = TCP_INFINITE_SSTHRESH;
	B3R->rtt_cnt = 0;
	B3R->next_rtt_delivered = 0;
	B3R->prev_ca_state = TCP_CA_Open;
	B3R->packet_conservation = 0;
	B3R->B3R_queue_state = 4  ;

	B3R->probe_rtt_done_stamp = 0;
	B3R->probe_rtt_round_done = 0;
	B3R->min_rtt_us = tcp_min_rtt(tp);
	B3R->min_rtt_stamp = tcp_jiffies32;

	minmax_reset(&B3R->bw, B3R->rtt_cnt, 0);  /* init max bw to 0 */

	B3R->has_seen_rtt = 0;
	B3R_init_pacing_rate_from_rtt(sk);
	B3R->B3R_gain_num= 50;
	B3R->unknown_rtt_count = 0 ;
	B3R->loss_rtt_count = 0 ;
 	B3R->loss_rtt_count_this_cycle = 0 ;
	B3R->flag = 0 ;
	B3R->loss_flag = 0;
	B3R->round_start = 0;
	B3R->idle_restart = 0;
	B3R->full_bw_reached = 0;
	B3R->full_bw = 0;
	B3R->full_bw_cnt = 0;
	B3R->cycle_mstamp = 0;
	B3R->cycle_idx = 0;
	B3R_reset_lt_bw_sampling(sk);
	B3R_reset_startup_mode(sk);

	cmpxchg(&sk->sk_pacing_status, SK_PACING_NONE, SK_PACING_NEEDED);
}

static u32 B3R_sndbuf_expand(struct sock *sk)
{
	/* Provision 3 * cwnd since B3R may slow-start even during recovery. */
	return 3;
}

/* In theory B3R does not need to undo the cwnd since it does not
 * always reduce cwnd on losses (see B3R_main()). Keep it for now.
 */
static u32 B3R_undo_cwnd(struct sock *sk)
{
	struct B3R *B3R = inet_csk_ca(sk);

	B3R->full_bw = 0;   /* spurious slow-down; reset full pipe detection */
	B3R->full_bw_cnt = 0;
	B3R_reset_lt_bw_sampling(sk);
	return tcp_sk(sk)->snd_cwnd;
}

/* Entering loss recovery, so save cwnd for when we exit or undo recovery. */
static u32 B3R_ssthresh(struct sock *sk)
{
	B3R_save_cwnd(sk);
	return tcp_sk(sk)->snd_ssthresh;
}

static size_t B3R_get_info(struct sock *sk, u32 ext, int *attr,
			   union tcp_cc_info *info)
{
	if (ext & (1 << (INET_DIAG_B3RINFO - 1)) ||
	    ext & (1 << (INET_DIAG_VEGASINFO - 1))) {
		struct tcp_sock *tp = tcp_sk(sk);
		struct B3R *B3R = inet_csk_ca(sk);
		u64 bw = B3R_bw(sk);

		bw = bw * tp->mss_cache * USEC_PER_SEC >> BW_SCALE;
		memset(&info->B3R, 0, sizeof(info->B3R));
		info->B3R.B3R_bw_lo		= (u32)bw;
		info->B3R.B3R_bw_hi		= (u32)(bw >> 32);
		//info->B3R.B3R_min_rtt		= B3R->B3R_gain_num*1000;
		info->B3R.B3R_min_rtt		= B3R->loss_flag*1000;
		//info->B3R.B3R_pacing_gain	= 
		info->B3R.B3R_pacing_gain	= B3R->pacing_gain ;
		info->B3R.B3R_cwnd_gain		= (B3R->B3R_queue_state)*256;
		//info->B3R.B3R_cwnd_gain		= B3R->pacing_gain;
		*attr = INET_DIAG_B3RINFO;
		return sizeof(info->B3R);
	}
	return 0;
}

static void B3R_set_state(struct sock *sk, u8 new_state)
{
	struct B3R *B3R = inet_csk_ca(sk);

	if (new_state == TCP_CA_Loss) {
		struct rate_sample rs = { .losses = 1 };

		B3R->prev_ca_state = TCP_CA_Loss;
		B3R->full_bw = 0;
		B3R->round_start = 1;	/* treat RTO like end of a round */
		B3R_lt_bw_sampling(sk, &rs);
	}
}

static struct tcp_congestion_ops tcp_B3R_cong_ops __read_mostly = {
	.flags		= TCP_CONG_NON_RESTRICTED,
	.name		= "B3R",
	.owner		= THIS_MODULE,
	.init		= B3R_init,
	.cong_control	= B3R_main,
	.sndbuf_expand	= B3R_sndbuf_expand,
	.undo_cwnd	= B3R_undo_cwnd,
	.cwnd_event	= B3R_cwnd_event,
	.ssthresh	= B3R_ssthresh,
	.min_tso_segs	= B3R_min_tso_segs,
	.get_info	= B3R_get_info,
	.set_state	= B3R_set_state,
};

static int __init B3R_register(void)
{
	BUILD_BUG_ON(sizeof(struct B3R) > ICSK_CA_PRIV_SIZE);
	return tcp_register_congestion_control(&tcp_B3R_cong_ops);
}

static void __exit B3R_unregister(void)
{
	tcp_unregister_congestion_control(&tcp_B3R_cong_ops);
}

module_init(B3R_register);
module_exit(B3R_unregister);

MODULE_AUTHOR("Tarun Singhania <tarunsinghania1997@gmail.com>");
MODULE_LICENSE("Dual BSD/GPL");
MODULE_DESCRIPTION("TCP B3R(Bottleneck Bandwidth and RTT)");
MODULE_DESCRIPTION("TCP B3R(Bottleneck Bandwidth and RTT)");