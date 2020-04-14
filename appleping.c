#include <sys/param.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/uio.h>

#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/ip_icmp.h>
#include <arpa/inet.h>


#include <err.h>
#include <errno.h>
#include <netdb.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include <unistd.h>

#define	TIMEVAL_LEN	((int)sizeof(struct tv32))
#define	DEFDATALEN	56		/* default data length */
#define	MAXWAIT		10000		/* max ms to wait for response */

#define IP_NO_IFT_CELLULAR  6969 /* for internal use only */


#define	A(bit)		rcvd_tbl[(bit)>>3]	/* identify byte in array */
#define	B(bit)		(1 << ((bit) & 0x07))	/* identify bit in byte */
#define	SET(bit)	(A(bit) |= B(bit))
#define	TST(bit)	(A(bit) & B(bit))

struct tv32 {
	u_int32_t tv32_sec;
	u_int32_t tv32_usec;
};

/* various options */
int options;
#define	F_FLOOD		0x0001
#define	F_QUIET		0x0010
#define	F_VERBOSE	0x0100
#define	F_AUDIBLE	0x2000
#ifdef IPSEC
#endif /*IPSEC*/
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
int s;				/* socket file descriptor */
u_char outpackhdr[IP_MAXPACKET], *outpack;

char BBELL = '\a';		/* characters written for MISSED and AUDIBLE */
char BSPACE = '\b';		/* characters written for flood */
char *hostname;
int ident;			/* process id to identify our packets */
u_char icmp_type = ICMP_ECHO;
u_char icmp_type_rsp = ICMP_ECHOREPLY;
int phdr_len = 0;
int send_len;
int no_dup = 0;

/* counters */
long nmissedmax;		/* max value of ntransmitted - nreceived - 1 */
long npackets;			/* max packets to transmit */
long nreceived;			/* # of packets we got back */
long nrepeats;			/* number of duplicates */
long ntransmitted;		/* sequence # for outbound packets = #sent */
long sntransmitted;		/* # of packets we sent in this sweep */
int interval = 1000;		/* interval between packets, ms */
int waittime = MAXWAIT;		/* timeout for each packet */
long nrcvtimeout = 0;		/* # of packets we got back after waittime */

/* timing */
int timing;			/* flag to do timing */
double tmin = 999999999.0;	/* minimum round trip time */
double tmax = 0.0;		/* maximum round trip time */
double tsum = 0.0;		/* sum of all times, for doing average */
double tsumsq = 0.0;		/* sum of all times squared, for std. dev. */


static u_short in_cksum(u_short *, int);
static void pinger(void);
static void pr_pack(char *, int, struct sockaddr_in *, struct timeval *, int);
static void tvsub(struct timeval *, const struct timeval *);

int main(int argc, char *const *argv)
{
	struct sockaddr_in from;
	struct timeval last, intvl;
	struct iovec iov;
	struct msghdr msg;

	// IP packet buffer
	u_char packet[IP_MAXPACKET];

	char *target;

	struct hostent *hp;
	struct sockaddr_in *to;

	int i, icmp_len;

	char hnamebuf[MAXHOSTNAMELEN];

	// create socket
	if (getuid()) {
        s = socket(AF_INET, SOCK_DGRAM, IPPROTO_ICMP);
        printf("DGRAM");
    } else {
        s = socket(AF_INET, SOCK_RAW, IPPROTO_ICMP);
        printf("RAW");
    }

	outpack = outpackhdr + sizeof(struct ip);

	target = argv[optind];

	icmp_len = sizeof(struct ip) + ICMP_MINLEN + phdr_len;
	send_len = icmp_len + datalen;
	bzero(&whereto, sizeof(whereto));
	to = &whereto;
	to->sin_family = AF_INET;
	to->sin_len = sizeof *to;

	// hostname
	if (inet_aton(target, &to->sin_addr) != 0) {
		hostname = target;
	} else {
		hp = gethostbyname2(target, AF_INET);
		if (!hp)
			errx(EX_NOHOST, "cannot resolve %s: %s",target, hstrerror(h_errno));
		memcpy(&to->sin_addr, hp->h_addr_list[0], sizeof to->sin_addr);
		strncpy(hnamebuf, hp->h_name, sizeof(hnamebuf) - 1);
		hnamebuf[sizeof(hnamebuf) - 1] = '\0';
		hostname = hnamebuf;
        printf("hostname is %s\n", hostname);
    }

	memset(&msg, 0, sizeof(msg));
	msg.msg_name = (caddr_t)&from;
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;
	iov.iov_base = packet;
	iov.iov_len = IP_MAXPACKET;

	gettimeofday(&last, NULL);

	if (options & F_FLOOD) {
		intvl.tv_sec = 0;
		intvl.tv_usec = 10000;
	} else {
		intvl.tv_sec = interval / 1000;
		intvl.tv_usec = interval % 1000 * 1000;
	}

	// PING LOOP starts here
	while (1) {
	    // printf("looping\n");
		struct timeval now, timeout;
		fd_set rfds;
		int cc, n;
		int tc = -1;

		FD_ZERO(&rfds);
		FD_SET(s, &rfds);
		gettimeofday(&now, NULL);
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
		//wait until file descriptor is ready
		n = select(s + 1, &rfds, NULL, NULL, &timeout);
		if (n < 0)
			continue;	/* Must be EINTR. */

		if (n == 1) {
			struct timeval *tv = NULL;
			msg.msg_namelen = sizeof(from);
			if ((cc = recvmsg(s, &msg, 0)) < 0) {
				if (errno == EINTR)
					continue;
				warn("recvmsg");
				continue;
			}
			if (tv == NULL) {
				gettimeofday(&now, NULL);
				tv = &now;
			}
			  pr_pack((char *)packet, cc, &from, tv, tc);
		}

		if (n == 0 || options & F_FLOOD) {
			if (!npackets || ntransmitted < npackets) {
                pinger();
            }

			gettimeofday(&last, NULL);
			if (ntransmitted - nreceived - 1 > nmissedmax) {
				nmissedmax = ntransmitted - nreceived - 1;
				if (!(options & F_QUIET))
					printf("Request timeout for icmp_seq %ld\n", ntransmitted - 2);
			}
		}
	}
	exit(0);	/* Make the compiler happy */
}

static void pinger(){
	struct icmp *icp;
	int cc;
	u_char *packet;

	packet = outpack;
	icp = (struct icmp *)outpack;
	icp->icmp_type = icmp_type;
	icp->icmp_code = 0;
	icp->icmp_cksum = 0;
	// convert to network byte order
	icp->icmp_seq = htons(ntransmitted);
	icp->icmp_id = ident;			/* ID */


	cc = ICMP_MINLEN + phdr_len + datalen;

	/* compute ICMP checksum here */
	icp->icmp_cksum = in_cksum((u_short *)icp, cc);
    // send echo request
    sendto(s, (char *)packet, cc, 0, (struct sockaddr *)&whereto,
               sizeof(whereto));
	ntransmitted++;
	sntransmitted++;
}
static void
pr_pack(char *buf, int cc, struct sockaddr_in *from, struct timeval *tv,
    int tc)
{
	u_char *cp, *dp;
	struct icmp *icp;
	struct ip *ip;
	const void *tp;
	double triptime;
	int dupflag, hlen, i, recv_len, seq;

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
			(void)printf("%d bytes from %s: icmp_seq=%u", cc,inet_ntoa(*(struct in_addr *)&from->sin_addr.s_addr),
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
u_short in_cksum(u_short *addr, int len){
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


