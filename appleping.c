#include <sys/cdefs.h>

#include <sys/param.h>		
#include <sys/socket.h>
#include <sys/sysctl.h>
#include <sys/time.h>
#include <sys/uio.h>

#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/ip_icmp.h>
#include <netinet/ip_var.h>
#include <arpa/inet.h>
#include <net/if.h>

#ifdef IPSEC
#include <netinet6/ipsec.h>
#endif /*IPSEC*/

#include <ctype.h>
#include <err.h>
#include <errno.h>
#include <math.h>
#include <netdb.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include <unistd.h>
#include <ifaddrs.h>

#define	INADDR_LEN	((int)sizeof(in_addr_t))
#define	TIMEVAL_LEN	((int)sizeof(struct tv32))
#define	MASK_LEN	(ICMP_MASKLEN - ICMP_MINLEN)
#define	TS_LEN		(ICMP_TSLEN - ICMP_MINLEN)
#define	DEFDATALEN	56		/* default data length */
#define	FLOOD_BACKOFF	20000		/* usecs to back off if F_FLOOD mode */
					/* runs out of buffer space */
#define	MAXIPLEN	(sizeof(struct ip) + MAX_IPOPTLEN)
#define	MAXICMPLEN	(ICMP_ADVLENMIN + MAX_IPOPTLEN)
#define	MAXWAIT		10000		/* max ms to wait for response */
#define	MAXALARM	(60 * 60)	/* max seconds for alarm timeout */
#define	MAXTOS		255

#define IP_NO_IFT_CELLULAR  6969 /* for internal use only */
#define IP_NO_IFT_PDP       IP_NO_IFT_CELLULAR /* deprecated */
#define SO_TRAFFIC_CLASS        0x1086      /* Traffic class (int)*/
#define SO_RECV_TRAFFIC_CLASS   0x1087      /* Receive traffic class (bool)*/
#define SO_TC_CTL 0x1088      /* Receive traffic class (bool)*/
#define SO_RECV_ANYIF 0x1089      /* Receive traffic class (bool)*/


#define	A(bit)		rcvd_tbl[(bit)>>3]	/* identify byte in array */
#define	B(bit)		(1 << ((bit) & 0x07))	/* identify bit in byte */
#define	SET(bit)	(A(bit) |= B(bit))
#define	CLR(bit)	(A(bit) &= (~B(bit)))
#define	TST(bit)	(A(bit) & B(bit))

struct tv32 {
	u_int32_t tv32_sec;
	u_int32_t tv32_usec;
};

/* various options */
int options;
#define	F_FLOOD		0x0001
#define	F_INTERVAL	0x0002
#define	F_NUMERIC	0x0004
#define	F_PINGFILLED	0x0008
#define	F_QUIET		0x0010
#define	F_RROUTE	0x0020
#define	F_SO_DEBUG	0x0040
#define	F_SO_DONTROUTE	0x0080
#define	F_VERBOSE	0x0100
#define	F_QUIET2	0x0200
#define	F_NOLOOP	0x0400
#define	F_MTTL		0x0800
#define	F_MIF		0x1000
#define	F_AUDIBLE	0x2000
#ifdef IPSEC
#ifdef IPSEC_POLICY_IPSEC
#define F_POLICY	0x4000
#endif /*IPSEC_POLICY_IPSEC*/
#endif /*IPSEC*/
#define	F_TTL		0x8000
#define	F_MISSED	0x10000
#define	F_ONCE		0x20000
#define	F_HDRINCL	0x40000
#define	F_MASK		0x80000
#define	F_TIME		0x100000
#define	F_SWEEP		0x200000
#define	F_WAITTIME	0x400000

/*
 * MAX_DUP_CHK is the number of bits in received table, i.e. the maximum
 * number of received sequence numbers we can keep track of.  Change 128
 * to 8192 for complete accuracy...
 */
#define	MAX_DUP_CHK	(8 * 128)
int mx_dup_ck = MAX_DUP_CHK;
char rcvd_tbl[MAX_DUP_CHK / 8];

struct sockaddr_in whereto;	/* who to ping */
int datalen = DEFDATALEN;
int maxpayload;
int s;				/* socket file descriptor */
u_char outpackhdr[IP_MAXPACKET], *outpack;
char BBELL = '\a';		/* characters written for MISSED and AUDIBLE */
char BSPACE = '\b';		/* characters written for flood */
char DOT = '.';
char *hostname;
char *shostname;
int ident;			/* process id to identify our packets */
int uid;			/* cached uid for micro-optimization */
u_char icmp_type = ICMP_ECHO;
u_char icmp_type_rsp = ICMP_ECHOREPLY;
int phdr_len = 0;
int send_len;
char *boundif;
unsigned int ifscope;
#if defined(IP_FORCE_OUT_IFP) && TARGET_OS_EMBEDDED
char boundifname[IFNAMSIZ];
#endif /* IP_FORCE_OUT_IFP */
int nocell;
int how_traffic_class = 0;
int traffic_class = SO_TC_CTL;	/* use control class, by default */
int no_dup = 0;

/* counters */
long nmissedmax;		/* max value of ntransmitted - nreceived - 1 */
long npackets;			/* max packets to transmit */
long nreceived;			/* # of packets we got back */
long nrepeats;			/* number of duplicates */
long ntransmitted;		/* sequence # for outbound packets = #sent */
long snpackets;			/* max packets to transmit in one sweep */
long snreceived;		/* # of packets we got back in this sweep */
long sntransmitted;		/* # of packets we sent in this sweep */
int sweepmax;			/* max value of payload in sweep */
int sweepmin = 0;		/* start value of payload in sweep */
int sweepincr = 1;		/* payload increment in sweep */
int interval = 1000;		/* interval between packets, ms */
int waittime = MAXWAIT;		/* timeout for each packet */
long nrcvtimeout = 0;		/* # of packets we got back after waittime */

/* timing */
int timing;			/* flag to do timing */
double tmin = 999999999.0;	/* minimum round trip time */
double tmax = 0.0;		/* maximum round trip time */
double tsum = 0.0;		/* sum of all times, for doing average */
double tsumsq = 0.0;		/* sum of all times squared, for std. dev. */

volatile sig_atomic_t finish_up;  /* nonzero if we've been told to finish up */
volatile sig_atomic_t siginfo_p;

static void fill(char *, char *);
static u_short in_cksum(u_short *, int);
static void check_status(void);
static void finish(void) __dead2;
static void pinger(void);
static void pr_pack(char *, int, struct sockaddr_in *, struct timeval *, int);
static void pr_retip(struct ip *);
static void status(int);
static void stopit(int);
static void tvsub(struct timeval *, const struct timeval *);

int main(int argc, char *const *argv)
{
	struct sockaddr_in from, sock_in;
	struct in_addr ifaddr;
	struct timeval last, intvl;
	struct iovec iov;
	struct ip *ip;
	struct msghdr msg;
	struct sigaction si_sa;
	size_t sz;
	u_char *datap, packet[IP_MAXPACKET] __attribute__((aligned(4)));
	char *ep, *source, *target, *payload;
	struct hostent *hp;
	struct sockaddr_in *to;
	double t;
	u_long alarmtimeout, ultmp;
	int almost_done, ch, df, hold, i, icmp_len, mib[4], preload, sockerrno,
	    tos, ttl;
	char ctrl[CMSG_SPACE(sizeof(struct timeval)) + CMSG_SPACE(sizeof(int))];
	char hnamebuf[MAXHOSTNAMELEN], snamebuf[MAXHOSTNAMELEN];
	unsigned char loop, mttl;

	payload = source = NULL;

	/*in
	 * Do the stuff that we need root priv's for *first*, and
	 * then drop our setuid bit.  Save error reporting for
	 * after arg parsing.
	 */
	if (getuid())
		s = socket(AF_INET, SOCK_DGRAM, IPPROTO_ICMP);
	else
		s = socket(AF_INET, SOCK_RAW, IPPROTO_ICMP);
	sockerrno = errno;

	if (setuid(getuid()) != 0)
		err(EX_NOPERM, "setuid() failed");
	uid = getuid();

	alarmtimeout = df = preload = tos = 0;

	outpack = outpackhdr + sizeof(struct ip);

	if (boundif != NULL && (ifscope = if_nametoindex(boundif)) == 0)
		errx(1, "bad interface name");

	target = argv[optind];

	icmp_len = sizeof(struct ip) + ICMP_MINLEN + phdr_len;
	if (options & F_RROUTE)
		icmp_len += MAX_IPOPTLEN;
	maxpayload = IP_MAXPACKET - icmp_len;
	if (datalen > maxpayload)
		errx(EX_USAGE, "packet size too large: %d > %d", datalen,
		    maxpayload);
	send_len = icmp_len + datalen;
	datap = &outpack[ICMP_MINLEN + phdr_len + TIMEVAL_LEN];
	if (source) {
		bzero((char *)&sock_in, sizeof(sock_in));
		sock_in.sin_family = AF_INET;
		if (inet_aton(source, &sock_in.sin_addr) != 0) {
			shostname = source;
		} else {
			hp = gethostbyname2(source, AF_INET);
			if (!hp)
				errx(EX_NOHOST, "cannot resolve %s: %s",
				    source, hstrerror(h_errno));

			sock_in.sin_len = sizeof sock_in;
			if ((unsigned)hp->h_length > sizeof(sock_in.sin_addr) ||
			    hp->h_length < 0)
				errx(1, "gethostbyname2: illegal address");
			memcpy(&sock_in.sin_addr, hp->h_addr_list[0],
			    sizeof(sock_in.sin_addr));
			(void)strncpy(snamebuf, hp->h_name,
			    sizeof(snamebuf) - 1);
			snamebuf[sizeof(snamebuf) - 1] = '\0';
			shostname = snamebuf;
		}
		if (bind(s, (struct sockaddr *)&sock_in, sizeof sock_in) == -1)
			err(1, "bind");
	}

	bzero(&whereto, sizeof(whereto));
	to = &whereto;
	to->sin_family = AF_INET;
	to->sin_len = sizeof *to;
	if (inet_aton(target, &to->sin_addr) != 0) {
		hostname = target;
	} else {
		hp = gethostbyname2(target, AF_INET);
		if (!hp)
			errx(EX_NOHOST, "cannot resolve %s: %s",
			    target, hstrerror(h_errno));

		if ((unsigned)hp->h_length > sizeof(to->sin_addr))
			errx(1, "gethostbyname2 returned an illegal address");
		memcpy(&to->sin_addr, hp->h_addr_list[0], sizeof to->sin_addr);
		(void)strncpy(hnamebuf, hp->h_name, sizeof(hnamebuf) - 1);
		hnamebuf[sizeof(hnamebuf) - 1] = '\0';
		hostname = hnamebuf;
	}

	do {
		struct ifaddrs *ifa_list, *ifa;
		
		if (IN_MULTICAST(ntohl(whereto.sin_addr.s_addr)) || whereto.sin_addr.s_addr == INADDR_BROADCAST) {
			no_dup = 1;
			break;
		}
		
		if (getifaddrs(&ifa_list) == -1)
			break;
		for (ifa = ifa_list; ifa; ifa = ifa->ifa_next) {
			if (ifa->ifa_addr->sa_family != AF_INET)
				continue;
			if ((ifa->ifa_flags & IFF_BROADCAST) == 0 || ifa->ifa_broadaddr == NULL)
				continue;
			if (whereto.sin_addr.s_addr != ((struct sockaddr_in*)ifa->ifa_broadaddr)->sin_addr.s_addr)
				continue;
			no_dup = 1;
			break;
		}
		
		freeifaddrs(ifa_list);
	} while (0);
	
if (datalen >= TIMEVAL_LEN)	/* can we time transfer */
		timing = 1;

	if (!(options & F_PINGFILLED))
		for (i = TIMEVAL_LEN; i < datalen; ++i)
			*datap++ = i;

	ident = getpid() & 0xFFFF;

	if (s < 0) {
		errno = sockerrno;
		err(EX_OSERR, "socket");
	}
	hold = 1;
	(void) setsockopt(s, SOL_SOCKET, SO_RECV_ANYIF, (char *)&hold,
	    sizeof(hold));
	if (ifscope != 0) {
		if (setsockopt(s, IPPROTO_IP, IP_BOUND_IF,
		    (char *)&ifscope, sizeof (ifscope)) != 0)
			err(EX_OSERR, "setsockopt(IP_BOUND_IF)");
	}
	if (nocell) {
		if (setsockopt(s, IPPROTO_IP, IP_NO_IFT_CELLULAR,
		    (char *)&nocell, sizeof (nocell)) != 0)
			err(EX_OSERR, "setsockopt(IP_NO_IFT_CELLULAR)");
	}
	if (sweepmax) {
		if (sweepmin >= sweepmax)
			errx(EX_USAGE, "Maximum packet size must be greater than the minimum packet size");

		if (datalen != DEFDATALEN)
			errx(EX_USAGE, "Packet size and ping sweep are mutually exclusive");

		if (npackets > 0) {
			snpackets = npackets;
			npackets = 0;
		} else
			snpackets = 1;
		datalen = sweepmin;
		send_len = icmp_len + sweepmin;
	}
	if (options & F_SWEEP && !sweepmax) 
		errx(EX_USAGE, "Maximum sweep size must be specified");

	/*
	 * When pinging the broadcast address, you can get a lot of answers.
	 * Doing something so evil is useful if you are trying to stress the
	 * ethernet, or just want to fill the arp cache to get some stuff for
	 * /etc/ethers.  But beware: RFC 1122 allows hosts to ignore broadcast
	 * or multicast pings if they wish.
	 */

	/*
	 * XXX receive buffer needs undetermined space for mbuf overhead
	 * as well.
	 */
	hold = IP_MAXPACKET + 128;
	(void)setsockopt(s, SOL_SOCKET, SO_RCVBUF, (char *)&hold,
	    sizeof(hold));
	if (uid == 0)
		(void)setsockopt(s, SOL_SOCKET, SO_SNDBUF, (char *)&hold,
		    sizeof(hold));

	if (to->sin_family == AF_INET) {
		(void)printf("PING %s (%s)", hostname,
		    inet_ntoa(to->sin_addr));
		if (source)
			(void)printf(" from %s", shostname);
		if (sweepmax)
			(void)printf(": (%d ... %d) data bytes\n",
			    sweepmin, sweepmax);
		else 
			(void)printf(": %d data bytes\n", datalen);
		
	} else {
		if (sweepmax)
			(void)printf("PING %s: (%d ... %d) data bytes\n",
			    hostname, sweepmin, sweepmax);
		else
			(void)printf("PING %s: %d data bytes\n", hostname, datalen);
	}

	bzero(&msg, sizeof(msg));
	msg.msg_name = (caddr_t)&from;
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;
	iov.iov_base = packet;
	iov.iov_len = IP_MAXPACKET;

	if (preload == 0)
		pinger();		/* send the first ping */
	else {
		if (npackets != 0 && preload > npackets)
			preload = npackets;
		while (preload--)	/* fire off them quickies */
			pinger();
	}
	(void)gettimeofday(&last, NULL);

	if (options & F_FLOOD) {
		intvl.tv_sec = 0;
		intvl.tv_usec = 10000;
	} else {
		intvl.tv_sec = interval / 1000;
		intvl.tv_usec = interval % 1000 * 1000;
	}

	almost_done = 0;
	while (!finish_up) {
		struct timeval now, timeout;
		fd_set rfds;
		int cc, n;
		int tc = -1;

		if ((unsigned)s >= FD_SETSIZE)
			errx(EX_OSERR, "descriptor too large");
		FD_ZERO(&rfds);
		FD_SET(s, &rfds);
		(void)gettimeofday(&now, NULL);
		timeout.tv_sec = last.tv_sec + intvl.tv_sec - now.tv_sec;
		timeout.tv_usec = last.tv_usec + intvl.tv_usec - now.tv_usec;
		while (timeout.tv_usec < 0) {
			timeout.tv_usec += 1000000;
			timeout.tv_sec--;
		}
		while (timeout.tv_usec >= 1000000) {
			timeout.tv_usec -= 1000000;
			timeout.tv_sec++;
		}
		if (timeout.tv_sec < 0)
			timeout.tv_sec = timeout.tv_usec = 0;
		n = select(s + 1, &rfds, NULL, NULL, &timeout);
		if (n < 0)
			continue;	/* Must be EINTR. */
		if (n == 1) {
			struct timeval *tv = NULL;
#ifdef SO_TIMESTAMP
			struct cmsghdr *cmsg = (struct cmsghdr *)&ctrl;

			msg.msg_controllen = sizeof(ctrl);
#endif
			msg.msg_namelen = sizeof(from);
			if ((cc = recvmsg(s, &msg, 0)) < 0) {
				if (errno == EINTR)
					continue;
				warn("recvmsg");
				continue;
			}
			for (cmsg = CMSG_FIRSTHDR(&msg); cmsg != NULL; cmsg = CMSG_NXTHDR(&msg, cmsg)) {
				if (cmsg->cmsg_level == SOL_SOCKET &&
					cmsg->cmsg_type == SO_TRAFFIC_CLASS &&
					cmsg->cmsg_len == CMSG_LEN(sizeof(int))) {
					/* Copy to avoid alignment problems: */
					memcpy(&tc, CMSG_DATA(cmsg), sizeof(tc));
				}
			}
			if (tv == NULL) {
				(void)gettimeofday(&now, NULL);
				tv = &now;
			}
			pr_pack((char *)packet, cc, &from, tv, tc);
			if ((options & F_ONCE && nreceived) ||
			    (npackets && nreceived >= npackets))
				break;
		}
		if (n == 0 || options & F_FLOOD) {
			if (sweepmax && sntransmitted == snpackets) {
				for (i = 0; i < sweepincr ; ++i)
					*datap++ = i;
				datalen += sweepincr;
				if (datalen > sweepmax)
					break;
				send_len = icmp_len + datalen;
				sntransmitted = 0;
			}
			if (!npackets || ntransmitted < npackets)
				pinger();
			else {
				if (almost_done)
					break;
				almost_done = 1;
				intvl.tv_usec = 0;
				if (nreceived) {
					intvl.tv_sec = 2 * tmax / 1000;
					if (!intvl.tv_sec)
						intvl.tv_sec = 1;
				} else {
					intvl.tv_sec = waittime / 1000;
					intvl.tv_usec = waittime % 1000 * 1000;
				}
			}
			(void)gettimeofday(&last, NULL);
			if (ntransmitted - nreceived - 1 > nmissedmax) {
				nmissedmax = ntransmitted - nreceived - 1;
				if (options & F_MISSED)
					(void)write(STDOUT_FILENO, &BBELL, 1);
				if (!(options & F_QUIET))
					printf("Request timeout for icmp_seq %ld\n", ntransmitted - 2);
			}
		}
	}
	finish();
	exit(0);	/* Make the compiler happy */
}


/*
 * pinger --
 *	Compose and transmit an ICMP ECHO REQUEST packet.  The IP packet
 * will be added on by the kernel.  The ID field is our UNIX process ID,
 * and the sequence number is an ascending integer.  The first TIMEVAL_LEN
 * bytes of the data portion are used to hold a UNIX "timeval" struct in
 * host byte-order, to compute the round-trip time.
 */
static void
pinger(void)
{
	struct timeval now;
	struct tv32 tv32;
	struct ip *ip;
	struct icmp *icp;
	int cc, i;
	u_char *packet;

	packet = outpack;
	icp = (struct icmp *)outpack;
	icp->icmp_type = icmp_type;
	icp->icmp_code = 0;
	icp->icmp_cksum = 0;
	icp->icmp_seq = htons(ntransmitted);
	icp->icmp_id = ident;			/* ID */

	CLR(ntransmitted % mx_dup_ck);

	if ((options & F_TIME) || timing) {
		(void)gettimeofday(&now, NULL);

		tv32.tv32_sec = htonl(now.tv_sec);
		tv32.tv32_usec = htonl(now.tv_usec);
		if (options & F_TIME)
			icp->icmp_otime = htonl((now.tv_sec % (24*60*60))
				* 1000 + now.tv_usec / 1000);
		if (timing)
			bcopy((void *)&tv32,
			    (void *)&outpack[ICMP_MINLEN + phdr_len],
			    sizeof(tv32));
	}

	cc = ICMP_MINLEN + phdr_len + datalen;

	/* compute ICMP checksum here */
	icp->icmp_cksum = in_cksum((u_short *)icp, cc);

	if (options & F_HDRINCL) {
		cc += sizeof(struct ip);
		ip = (struct ip *)outpackhdr;
		ip->ip_len = cc;
		ip->ip_sum = in_cksum((u_short *)outpackhdr, cc);
		packet = outpackhdr;
	}
	if (how_traffic_class > 1 && traffic_class >= 0) {
		struct msghdr msg;
		struct iovec iov;
		char *cmbuf[CMSG_SPACE(sizeof(int))];
		struct cmsghdr *cm = (struct cmsghdr *)cmbuf;

		msg.msg_name = &whereto;
		msg.msg_namelen = sizeof(whereto);

		iov.iov_base = packet;
		iov.iov_len = cc;
		msg.msg_iov = &iov;
		msg.msg_iovlen = 1;

		cm->cmsg_len = CMSG_LEN(sizeof(int));
		cm->cmsg_level = SOL_SOCKET;
		cm->cmsg_type = SO_TRAFFIC_CLASS;
		*(int *)CMSG_DATA(cm) = traffic_class;
		msg.msg_control = cm;
		msg.msg_controllen = CMSG_SPACE(sizeof(int));

		msg.msg_flags = 0;

		i = sendmsg(s, &msg, 0);
	} else {
		i = sendto(s, (char *)packet, cc, 0, (struct sockaddr *)&whereto,
			sizeof(whereto));
	}
	if (i < 0 || i != cc)  {
		if (i < 0) {
			if (options & F_FLOOD && errno == ENOBUFS) {
				usleep(FLOOD_BACKOFF);
				return;
			}
			warn("sendto");
		} else {
			warn("%s: partial write: %d of %d bytes",
			     hostname, i, cc);
		}
	}
	ntransmitted++;
	sntransmitted++;
	if (!(options & F_QUIET) && options & F_FLOOD)
		(void)write(STDOUT_FILENO, &DOT, 1);
}

/*
 * pr_pack --
 *	Print out the packet, if it came from us.  This logic is necessary
 * because ALL readers of the ICMP socket get a copy of ALL ICMP packets
 * which arrive ('tis only fair).  This permits multiple copies of this
 * program to be run without having intermingled output (or statistics!).
 */
static void
pr_pack(char *buf, int cc, struct sockaddr_in *from, struct timeval *tv,
    int tc)
{
	struct in_addr ina;
	u_char *cp, *dp;
	struct icmp *icp;
	struct ip *ip;
	const void *tp;
	double triptime;
	int dupflag, hlen, i, j, recv_len, seq;
	static int old_rrlen;
	static char old_rr[MAX_IPOPTLEN];

	/* Check the IP header */
	ip = (struct ip *)buf;
	hlen = ip->ip_hl << 2;
	recv_len = cc;
	if (cc < hlen + ICMP_MINLEN) {
		if (options & F_VERBOSE)
			warn("packet too short (%d bytes) from %s", cc,
			     inet_ntoa(from->sin_addr));
		return;
	}

	/* Now the ICMP part */
	cc -= hlen;
	icp = (struct icmp *)(buf + hlen);
	if (icp->icmp_type == icmp_type_rsp) {
		if (icp->icmp_id != ident)
			return;			/* 'Twas not our ECHO */
		++nreceived;
		triptime = 0.0;
		if (timing) {
			struct timeval tv1;
			struct tv32 tv32;
#ifndef icmp_data
			tp = &icp->icmp_ip;
#else
			tp = icp->icmp_data;
#endif
			tp = (const char *)tp + phdr_len;

			if (cc - ICMP_MINLEN - phdr_len >= sizeof(tv1)) {
				/* Copy to avoid alignment problems: */
				memcpy(&tv32, tp, sizeof(tv32));
				tv1.tv_sec = ntohl(tv32.tv32_sec);
				tv1.tv_usec = ntohl(tv32.tv32_usec);
				tvsub(tv, &tv1);
 				triptime = ((double)tv->tv_sec) * 1000.0 +
 				    ((double)tv->tv_usec) / 1000.0;
				tsum += triptime;
				tsumsq += triptime * triptime;
				if (triptime < tmin)
					tmin = triptime;
				if (triptime > tmax)
					tmax = triptime;
			} else
				timing = 0;
		}

		seq = ntohs(icp->icmp_seq);

		if (TST(seq % mx_dup_ck)) {
			++nrepeats;
			--nreceived;
			dupflag = 1;
		} else {
			SET(seq % mx_dup_ck);
			dupflag = 0;
		}

		if (options & F_QUIET)
			return;
	
		if (options & F_WAITTIME && triptime > waittime) {
			++nrcvtimeout;
			return;
		}

		if (options & F_FLOOD)
			(void)write(STDOUT_FILENO, &BSPACE, 1);
		else {
			(void)printf("%d bytes from %s: icmp_seq=%u", cc,
			   inet_ntoa(*(struct in_addr *)&from->sin_addr.s_addr),
			   seq);
			(void)printf(" ttl=%d", ip->ip_ttl);
			if (timing)
				(void)printf(" time=%.3f ms", triptime);
			if (tc != -1) {
				(void)printf(" tc=%d", tc);
			}
			if (dupflag && no_dup == 0) {
				(void)printf(" (DUP!)");
			}
			if (options & F_AUDIBLE)
				(void)write(STDOUT_FILENO, &BBELL, 1);
			if (recv_len != send_len) {
                        	(void)printf(
				     "\nwrong total length %d instead of %d",
				     recv_len, send_len);
			}
			/* check the data */
			cp = (u_char*)&icp->icmp_data[phdr_len];
			dp = &outpack[ICMP_MINLEN + phdr_len];
			cc -= ICMP_MINLEN + phdr_len;
			i = 0;
			if (timing) {   /* don't check variable timestamp */
				cp += TIMEVAL_LEN;
				dp += TIMEVAL_LEN;
				cc -= TIMEVAL_LEN;
				i += TIMEVAL_LEN;
			}
			for (; i < datalen && cc > 0; ++i, ++cp, ++dp, --cc) {
				if (*cp != *dp) {
	(void)printf("\nwrong data byte #%d should be 0x%x but was 0x%x",
	    i, *dp, *cp);
					(void)printf("\ncp:");
					cp = (u_char*)&icp->icmp_data[0];
					for (i = 0; i < datalen; ++i, ++cp) {
						if ((i % 16) == 8)
							(void)printf("\n\t");
						(void)printf("%2x ", *cp);
					}
					(void)printf("\ndp:");
					cp = &outpack[ICMP_MINLEN];
					for (i = 0; i < datalen; ++i, ++cp) {
						if ((i % 16) == 8)
							(void)printf("\n\t");
						(void)printf("%2x ", *cp);
					}
					break;
				}
			}
		}
	}

	/* Display any IP options */
	if (!(options & F_FLOOD)) {
		(void)putchar('\n');
		(void)fflush(stdout);
	}
}

/*
 * in_cksum --
 *	Checksum routine for Internet Protocol family headers (C Version)
 */
u_short
in_cksum(u_short *addr, int len)
{
	int nleft, sum;
	u_short *w;
	union {
		u_short	us;
		u_char	uc[2];
	} last;
	u_short answer;

	nleft = len;
	sum = 0;
	w = addr;

	/*
	 * Our algorithm is simple, using a 32 bit accumulator (sum), we add
	 * sequential 16 bit words to it, and at the end, fold back all the
	 * carry bits from the top 16 bits into the lower 16 bits.
	 */
	while (nleft > 1)  {
		sum += *w++;
		nleft -= 2;
	}

	/* mop up an odd byte, if necessary */
	if (nleft == 1) {
		last.uc[0] = *(u_char *)w;
		last.uc[1] = 0;
		sum += last.us;
	}

	/* add back carry outs from top 16 bits to low 16 bits */
	sum = (sum >> 16) + (sum & 0xffff);	/* add hi 16 to low 16 */
	sum += (sum >> 16);			/* add carry */
	answer = ~sum;				/* truncate to 16 bits */
	return(answer);
}

/*
 * tvsub --
 *	Subtract 2 timeval structs:  out = out - in.  Out is assumed to
 * be >= in.
 */
static void
tvsub(struct timeval *out, const struct timeval *in)
{

	if ((out->tv_usec -= in->tv_usec) < 0) {
		--out->tv_sec;
		out->tv_usec += 1000000;
	}
	out->tv_sec -= in->tv_sec;
}


/*
 * finish --
 *	Print out statistics, and give up.
 */
static void
finish(void)
{

}

