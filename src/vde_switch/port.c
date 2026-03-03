/* VDE4Network-Inc is forked from VDE2 and adapted for Network-In! Simulator project
 * Copyright V. Verdon - Version 20260301
 * Initial Copyright 2005 Renzo Davoli VDE-2
 * 2008 Luca Saiu (Marionnet project): a better hub implementation
 * Some minor remain from uml_switch Copyright 2002 Yon Uriarte and Jeff Dike
 * Licensed under the GPLv2 
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <syslog.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <netinet/in.h> /*ntoh conversion*/
#include <sys/types.h>
#include <grp.h>
#include <pwd.h>
#include <ctype.h>

#include <config.h>
#include <vde.h>
#include <vdecommon.h>

#include "switch.h"
#include "hash.h"
#include "qtimer.h"
#include "port.h"
#include "fcntl.h"
#include "consmgmt.h"
#include "bitarray.h"
#include "fstp.h"

#include "packetq.h"

static int pflag=0;
static int numports;
#ifdef VDE_PQ2
static int stdqlen=128;
#endif

static struct port **portv;

#ifdef DEBUGOPT
#define DBGPORTNEW (dl) 
#define DBGPORTDEL (dl+1) 
#define DBGPORTDESCR (dl+2) 
#define DBGEPNEW (dl+3) 
#define DBGEPDEL (dl+4) 
#define PKTFILTIN (dl+5)
#define PKTFILTOUT (dl+6)
static struct dbgcl dl[]= {
	  {"port/+","new port",D_PORT|D_PLUS},
		{"port/-","closed port",D_PORT|D_MINUS},
		{"port/descr","set port description",D_PORT|D_DESCR},
	  {"port/ep/+","new endpoint",D_EP|D_PLUS},
		{"port/ep/-","closed endpoint",D_EP|D_MINUS},
		{"packet/in",NULL,D_PACKET|D_IN},
		{"packet/out",NULL,D_PACKET|D_OUT},
};
#endif

// for dedugging if needed

/*
	 void packet_dump (struct packet *p)
	 {
	 int i;
	 printf ("packet dump dst");
	 for (i=0;i<ETH_ALEN;i++)
	 printf(":%02x",p->header.dest[i]);
	 printf(" src");
	 for (i=0;i<ETH_ALEN;i++)
	 printf(":%02x",p->header.src[i]);
	 printf(" proto");
	 for (i=0;i<2;i++)
	 printf(":%02x",p->header.proto[i]);
	 printf("\n");
	 }*/

struct endpoint {
	int port;
	int fd_ctl;
	int fd_data;
	char *descr;
#ifdef VDE_PQ2
	struct vdepq *vdepq;
	int vdepq_count;
	int vdepq_max;
#endif
	struct endpoint *next;
};

#define NOTINPOOL 0x8000

struct port {
	struct endpoint *ep;
	int flag;
	/* sender is already inside ms, but it needs one more memaccess */
	int (*sender)(int fd_ctl, int fd_data, void *packet, int len, int port);
	struct mod_support *ms;
	int vlanuntag;
	uid_t user;
	gid_t group;
	uid_t curuser;
#ifdef FSTP
	int cost;
#endif
#ifdef PORTCOUNTERS
	long long pktsin,pktsout,bytesin,bytesout;
#endif
};

/* VLAN MANAGEMENT:
 * table the vlan table (also for inactive ports)
 * vlan bctag is the vlan table -- only tagged forwarding ports mapping
 * vlan bcuntag is the vlan table -- only untagged forwarding ports mapping
 * validvlan is the table of valid vlans
 */

struct {
	bitarray table;
	bitarray bctag;
	bitarray bcuntag;
	bitarray notlearning;
} vlant[NUMOFVLAN+1];
bitarray validvlan;

#define IS_BROADCAST(addr) ((addr[0] & 1) == 1)


static int alloc_port(unsigned int portno)
{
	int i=portno;
	if (i==0) {
		/* take one */
		for (i=0;i<numports && portv[i] != NULL &&
				(portv[i]->ep != NULL || portv[i]->flag & NOTINPOOL) ;i++)
			;
	} else if (i<0) /* special case MGMT client port */
		i=0;
	if (i >= numports)
		return -1;
	else {
		if (portv[i] == NULL) {
			struct port *port;
			if ((port = malloc(sizeof(struct port))) == NULL){
				printlog(LOG_WARNING,"malloc port %s",strerror(errno));
				return -1;
			} else
			{
				DBGOUT(DBGPORTNEW,"%02d", i);
				EVENTOUT(DBGPORTNEW,i);

				portv[i]=port;
				port->ep=NULL;
				port->user=port->group=port->curuser=-1;
#ifdef FSTP
				port->cost=DEFAULT_COST;
#endif
#ifdef PORTCOUNTERS
				port->pktsin=0;
				port->pktsout=0;
				port->bytesin=0;
				port->bytesout=0;
#endif
				port->flag=0;
				port->sender=NULL;
				port->vlanuntag=0;
				ba_set(vlant[0].table,i);
			}
		}
		return i;
	}
}


#ifdef VDE_BIONIC
  static inline int user_belongs_to_group(uid_t uid, gid_t gid) { return 0; }
#else
/* 1 if user belongs to the group, 0 otherwise) */
static int user_belongs_to_group(uid_t uid, gid_t gid)
{
	struct passwd *pw=getpwuid(uid);
	if (pw == NULL) 
		return 0;
	else {
		if (gid==pw->pw_gid)
			return 1;
		else {
			struct group *grp;
			setgrent();
			while ((grp = getgrent())) {
				if (grp->gr_gid == gid) {
					int i;
					for (i = 0; grp->gr_mem[i]; i++) {
						if (strcmp(grp->gr_mem[i], pw->pw_name)==0) {
							endgrent();
							return 1;
						}
					}
				}
			}
			endgrent();
			return 0;
		}
	}
}
#endif


/* Access Control check:
	 returns 0->OK -1->Permission Denied */
static int checkport_ac(struct port *port, uid_t user)
{
	/*unrestricted*/
	if (port->user == -1 && port->group == -1)
		return 0;
	/*root or restricted to a specific user*/
	else if (user==0 || (port->user != -1 && port->user==user))
		return 0;
	/*restricted to a group*/
	else if (port->group != -1 && user_belongs_to_group(user,port->group))
		return 0;
	else {
		errno=EPERM;
		return -1;
	}
}

/* initialize a new endpoint */
struct endpoint *setup_ep(int portno, int fd_ctl, int fd_data, uid_t user,
		struct mod_support *modfun)
{
	struct port *port;
	struct endpoint *ep;

	if ((portno = alloc_port(portno)) >= 0) {
		port=portv[portno];	
		if (port->ep == NULL && checkport_ac(port,user)==0)
			port->curuser=user;
		if (port->curuser == user &&
				(ep=malloc(sizeof(struct endpoint))) != NULL) {
			DBGOUT(DBGEPNEW,"Port %02d FD %2d", portno,fd_ctl);
			EVENTOUT(DBGEPNEW,portno,fd_ctl);
			port->ms=modfun;
			port->sender=modfun->sender;
			ep->port=portno;
			ep->fd_ctl=fd_ctl;
			ep->fd_data=fd_data;
			ep->descr=NULL;
#ifdef VDE_PQ2
			ep->vdepq=NULL;
			ep->vdepq_count=0;
			ep->vdepq_max=stdqlen;
#endif
			if(port->ep == NULL) {/* WAS INACTIVE */
				int i;
				/* copy all the vlan defs to the active vlan defs */
				ep->next=port->ep;
				port->ep=ep;
				bac_FORALL(validvlan,NUMOFVLAN,
						({if (ba_check(vlant[i].table,portno)) {
						 ba_set(vlant[i].bctag,portno);
#ifdef FSTP
						 fstaddport(i,portno,(i!=port->vlanuntag));
#endif
						 }
						 }),i);
				if (port->vlanuntag != NOVLAN) {
					ba_set(vlant[port->vlanuntag].bcuntag,portno);
					ba_clr(vlant[port->vlanuntag].bctag,portno);
					ba_clr(vlant[port->vlanuntag].notlearning,portno);
				}
			} else {
				ep->next=port->ep;
				port->ep=ep;
			}
			return ep;
		}
		else {
			if (port->curuser != user)
				errno=EADDRINUSE;
			else 
				errno=ENOMEM;
			return NULL;
		}
	}
	else {
		errno=ENOMEM;
		return NULL;
	}
}

int ep_get_port(struct endpoint *ep)
{
	return ep->port;
}

void setup_description(struct endpoint *ep, char *descr)
{
	DBGOUT(DBGPORTDESCR,"Port %02d FD %2d -> \"%s\"",ep->port,ep->fd_ctl,descr);
	EVENTOUT(DBGPORTDESCR,ep->port,ep->fd_ctl,descr);
	ep->descr=descr;
}

static int rec_close_ep(struct endpoint **pep, int fd_ctl)
{
	struct endpoint *this=*pep;
	if (this != NULL) {
		if (this->fd_ctl==fd_ctl) {
			DBGOUT(DBGEPDEL,"Port %02d FD %2d",this->port,fd_ctl);
			EVENTOUT(DBGEPDEL,this->port,fd_ctl);
			*pep=this->next;
#ifdef VDE_PQ2
			vdepq_del(&(this->vdepq));
#endif
			if (portv[this->port]->ms->delep)
				portv[this->port]->ms->delep(this->fd_ctl,this->fd_data,this->descr);
			free(this);
			return 0;
		} else
			return rec_close_ep(&(this->next),fd_ctl);
	} else
		return ENXIO;
}

static int close_ep_port_fd(int portno, int fd_ctl)
{
	if (portno >=0 && portno < numports) {
		struct port *port=portv[portno];
		if (port != NULL) {
			int rv=rec_close_ep(&(port->ep),fd_ctl);
			if (port->ep == NULL) {
				DBGOUT(DBGPORTDEL,"%02d",portno);
				EVENTOUT(DBGPORTDEL,portno);
				hash_delete_port(portno);
				port->ms=NULL;
				port->sender=NULL;
				port->curuser=-1;
				int i;
				/* inactivate port: all active vlan defs cleared */
				bac_FORALL(validvlan,NUMOFVLAN,({
							ba_clr(vlant[i].bctag,portno);
#ifdef FSTP
							fstdelport(i,portno);
#endif
							}),i);
				if (port->vlanuntag < NOVLAN) ba_clr(vlant[port->vlanuntag].bcuntag,portno);
			}
			return rv;	
		} else
			return ENXIO;
	} else
		return EINVAL;
}

int close_ep(struct endpoint *ep)
{
	return close_ep_port_fd(ep->port, ep->fd_ctl);
}

#ifdef VDE_PQ2
static int rec_setqlen_ep(struct endpoint *ep, int fd_ctl, int len)
{
	struct endpoint *this=ep;
	if (this != NULL) {
		if (this->fd_ctl==fd_ctl) {
			ep->vdepq_max = len;
			return 0;
		} else
			return rec_setqlen_ep(this->next, fd_ctl, len);
	} else
		return ENXIO;
}

static int setqlen_ep_port_fd(int portno, int fd_ctl, int len)
{
	if (portno >=0 && portno < numports) {
		struct port *port=portv[portno];
		if (port != NULL) {
			return rec_setqlen_ep(port->ep, fd_ctl, len);
		}
		else
			return ENXIO;
	} else
		return EINVAL;
}
#endif

int portflag(int op,int f)
{
	int oldflag=pflag;
	switch(op)  {
		case P_GETFLAG: oldflag = pflag & f; break;
		case P_SETFLAG: pflag=f; break;
		case P_ADDFLAG: pflag |= f; break;
		case P_CLRFLAG: pflag &= ~f; break;
	}
	return oldflag;
}


/*********************** sending macro used by Core ******************/

/* VDBG counter: count[port].spacket++; count[port].sbytes+=len */
#ifdef PORTCOUNTERS
#define SEND_COUNTER_UPD(Port,LEN) ({Port->pktsout++; Port->bytesout +=len;})
#else
#define SEND_COUNTER_UPD(Port,LEN)
#endif

#ifndef VDE_PQ2
#define SEND_PACKET_PORT(PORT,PORTNO,PACKET,LEN) \
	({\
	 struct port *Port=(PORT); \
	 if (PACKETFILTER(PKTFILTOUT,(PORTNO),(PACKET), (LEN))) {\
	 struct endpoint *ep; \
	 SEND_COUNTER_UPD(Port,LEN); \
	 for (ep=Port->ep; ep != NULL; ep=ep->next) \
	 Port->ms->sender(ep->fd_ctl, ep->fd_data, (PACKET), (LEN), ep->port); \
	 } \
	 })
#else
#define SEND_PACKET_PORT(PORT,PORTNO,PACKET,LEN,TMPBUF) \
	({\
	 struct port *Port=(PORT); \
	 if (PACKETFILTER(PKTFILTOUT,(PORTNO),(PACKET), (LEN))) {\
	 struct endpoint *ep; \
	 SEND_COUNTER_UPD(Port,LEN); \
	 for (ep=Port->ep; ep != NULL; ep=ep->next) \
	 if (ep->vdepq_count || \
		 Port->ms->sender(ep->fd_ctl, ep->fd_data, (PACKET), (LEN), ep->port) == -EWOULDBLOCK) {\
	 if (ep->vdepq_count < ep->vdepq_max) \
	 ep->vdepq_count += vdepq_add(&(ep->vdepq), (PACKET), (LEN), TMPBUF); \
	 if (ep->vdepq_count == 1) mainloop_pollmask_add(ep->fd_data, POLLOUT);\
	 } \
	 } \
	 })
#endif

#ifdef FSTP

/* functions for FSTP */
void port_send_packet(int portno, void *packet, int len)
{
#ifndef VDE_PQ2
	SEND_PACKET_PORT(portv[portno],portno,packet,len);
#else
	void *tmpbuf=NULL;
	SEND_PACKET_PORT(portv[portno],portno,packet,len,&tmpbuf);
#endif
}

void portset_send_packet(bitarray portset, void *packet, int len)
{
	int i;
#ifndef VDE_PQ2
	ba_FORALL(portset,numports,
			SEND_PACKET_PORT(portv[i],i,packet,len), i);
#else
	void *tmpbuf=NULL;
	ba_FORALL(portset,numports,
			SEND_PACKET_PORT(portv[i],i,packet,len,&tmpbuf), i);
#endif
}


void port_set_status(int portno, int vlan, int status)
{
	if (ba_check(vlant[vlan].table,portno)) {
		if (status==DISCARDING) {
			ba_set(vlant[vlan].notlearning,portno);
			ba_clr(vlant[vlan].bctag,portno);
			ba_clr(vlant[vlan].bcuntag,portno);
		} else if (status==LEARNING) {
			ba_clr(vlant[vlan].notlearning,portno);
			ba_clr(vlant[vlan].bctag,portno);
			ba_clr(vlant[vlan].bcuntag,portno);
		} else { /*forwarding*/
			ba_clr(vlant[vlan].notlearning,portno);
			if (portv[portno]->vlanuntag == vlan) 
				ba_set(vlant[vlan].bcuntag,portno);
			else 
				ba_set(vlant[vlan].bctag,portno);
		}
	}
}

int port_get_status(int portno, int vlan)
{
	if (ba_check(vlant[vlan].notlearning,portno)) 
		return DISCARDING;
	else {
		if (ba_check(vlant[vlan].bctag,portno) ||
				ba_check(vlant[vlan].bcuntag,portno))
			return FORWARDING;
		else
			return LEARNING;
	}
}

int port_getcost(int port)
{
	return portv[port]->cost;
}
#endif

/************************************ CORE PACKET MGMT *****************************/

/* TAG2UNTAG packet:
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 *             | Destination     |    Source       |81 00|pvlan| L/T | data
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 *
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 *                         | Destination     |    Source       | L/T | data
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 *
 * Destination/Source: 4 byte right shift
 * Length -4 bytes
 * Pointer to the packet: +4 bytes
 * */

#define TAG2UNTAG(P,LEN) \
	({ memmove((char *)(P)+4,(P),2*ETH_ALEN); LEN -= 4 ; \
	 (struct packet *)((char *)(P)+4); })

/* TAG2UNTAG packet:
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 *             | Destination     |    Source       | L/T | data
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 * 
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 * | Destination     |    Source       |81 00|pvlan| L/T | data
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 * Destination/Source: 4 byte left shift
 * Length -4 bytes
 * Pointer to the packet: +4 bytes
 * The space has been allocated in advance (just in case); all the modules
 * read data into a bipacket.
 */

#define UNTAG2TAG(P,VLAN,LEN) \
	({ memmove((char *)(P)-4,(P),2*ETH_ALEN); LEN += 4 ; \
	 (P)->header.src[2]=0x81; (P)->header.src[3]=0x00;\
	 (P)->header.src[4]=(VLAN >> 8); (P)->header.src[5]=(VLAN);\
	 (struct packet *)((char *)(P)-4); })


#ifdef VDE_PQ2
static int trysendfun(struct endpoint *ep, void *packet, int len)
{
	int port=ep->port;
	return portv[port]->ms->sender(ep->fd_ctl, ep->fd_data, packet, len, port);
}

void handle_out_packet(struct endpoint *ep)
{
	//printf("handle_out_packet %d\n",ep->vdepq_count);
	ep->vdepq_count -= vdepq_try(&(ep->vdepq),ep,trysendfun);
	if (ep->vdepq_count == 0)
		mainloop_pollmask_del(ep->fd_data, POLLOUT);
}
#endif

void handle_in_packet(struct endpoint *ep,  struct packet *packet, int len)
{
	int tarport;
	int vlan,tagged;
	int port=ep->port;

	//DG minimum length of a packet is 60 bytes plus trailing CRC
	if (__builtin_expect(len < 60, 0)) {
		memset(packet->data+len,0,60-len);
		len=60;
	}

	if(PACKETFILTER(PKTFILTIN,port,packet,len)) {

#ifdef PORTCOUNTERS
		portv[port]->pktsin++;
		portv[port]->bytesin+=len;
#endif
		if (pflag & HUB_TAG) { /* this is a HUB */
			int i;
#ifndef VDE_PQ2
			for(i = 1; i < numports; i++)
				if((i != port) && (portv[i] != NULL))
					SEND_PACKET_PORT(portv[i],i,packet,len);
#else
			void *tmpbuf=NULL;
			for(i = 1; i < numports; i++)
				if((i != port) && (portv[i] != NULL))
					SEND_PACKET_PORT(portv[i],i,packet,len,&tmpbuf);
#endif
		} else { /* This is a switch, not a HUB! */
			if (packet->header.proto[0] == 0x81 && packet->header.proto[1] == 0x00) {
				tagged=1;
				vlan=((packet->data[0] << 8) + packet->data[1]) & 0xfff;
				if (! ba_check(vlant[vlan].table,port))
					return; /*discard unwanted packets*/
			} else {
				tagged=0;
				if ((vlan=portv[port]->vlanuntag) == NOVLAN)
					return; /*discard unwanted packets*/
			}

#ifdef FSTP
			/* when it works as a HUB or FSTP is off, MST packet must be forwarded */
			if (ISBPDU(packet) && fstflag(P_GETFLAG, FSTP_TAG)) {
				fst_in_bpdu(port,packet,len,vlan,tagged);
				return; /* BPDU packets are not forwarded */
			}
#endif
			/* The port is in blocked status, no packet received */
			if (ba_check(vlant[vlan].notlearning,port)) return; 

			/* We don't like broadcast source addresses */
			if(! (IS_BROADCAST(packet->header.src))) {

				int last = find_in_hash_update(packet->header.src,vlan,port);
				/* old value differs from actual input port */
				if(last >=0 && (port != last)){
					printlog(LOG_INFO,"MAC %02x:%02x:%02x:%02x:%02x:%02x moved from port %d to port %d",packet->header.src[0],packet->header.src[1],packet->header.src[2],packet->header.src[3],packet->header.src[4],packet->header.src[5],last,port);
				}
			}
			/* static void send_dst(int port,struct packet *packet, int len) */
			if(IS_BROADCAST(packet->header.dest) || 
					(tarport = find_in_hash(packet->header.dest,vlan)) < 0 ){
				/* FST HERE! broadcast only on active ports*/
				/* no cache or broadcast/multicast == all ports *except* the source port! */
				/* BROADCAST: tag/untag. Broadcast the packet untouched on the ports
				 * of the same tag-ness, then transform it to the other tag-ness for the others*/
				if (tagged) {
					int i;
#ifndef VDE_PQ2
					ba_FORALL(vlant[vlan].bctag,numports,
							({if (i != port) SEND_PACKET_PORT(portv[i],i,packet,len);}),i);
					packet=TAG2UNTAG(packet,len);
					ba_FORALL(vlant[vlan].bcuntag,numports,
							({if (i != port) SEND_PACKET_PORT(portv[i],i,packet,len);}),i);
#else
					void *tmpbuft=NULL;
					void *tmpbufu=NULL;
					ba_FORALL(vlant[vlan].bctag,numports,
							({if (i != port) SEND_PACKET_PORT(portv[i],i,packet,len,&tmpbuft);}),i);
					packet=TAG2UNTAG(packet,len);
					ba_FORALL(vlant[vlan].bcuntag,numports,
							({if (i != port) SEND_PACKET_PORT(portv[i],i,packet,len,&tmpbufu);}),i);
#endif
				} else { /* untagged */
					int i;
#ifndef VDE_PQ2
					ba_FORALL(vlant[vlan].bcuntag,numports,
							({if (i != port) SEND_PACKET_PORT(portv[i],i,packet,len);}),i);
					packet=UNTAG2TAG(packet,vlan,len);
					ba_FORALL(vlant[vlan].bctag,numports,
							({if (i != port) SEND_PACKET_PORT(portv[i],i,packet,len);}),i);
#else
					void *tmpbufu=NULL;
					void *tmpbuft=NULL;
					ba_FORALL(vlant[vlan].bcuntag,numports,
							({if (i != port) SEND_PACKET_PORT(portv[i],i,packet,len,&tmpbufu);}),i);
					packet=UNTAG2TAG(packet,vlan,len);
					ba_FORALL(vlant[vlan].bctag,numports,
							({if (i != port) SEND_PACKET_PORT(portv[i],i,packet,len,&tmpbuft);}),i);
#endif
				}
			}
			else {
				/* the hash table should not generate tarport not in vlan 
				 * any time a port is removed from a vlan, the port is flushed from the hash */
				if (tarport==port)
					return; /*do not loop!*/
#ifndef VDE_PQ2
				if (tagged) {
					if (portv[tarport]->vlanuntag==vlan) { /* TAG->UNTAG */
						packet = TAG2UNTAG(packet,len);
						SEND_PACKET_PORT(portv[tarport],tarport,packet,len);
					} else {                               /* TAG->TAG */
						SEND_PACKET_PORT(portv[tarport],tarport,packet,len);
					}
				} else {
					if (portv[tarport]->vlanuntag==vlan) { /* UNTAG->UNTAG */
						SEND_PACKET_PORT(portv[tarport],tarport,packet,len);
					} else {                              /* UNTAG->TAG */
						packet = UNTAG2TAG(packet,vlan,len);
						SEND_PACKET_PORT(portv[tarport],tarport,packet,len);
					}
				}
#else
				if (tagged) {
					void *tmpbuf=NULL;
					if (portv[tarport]->vlanuntag==vlan) { /* TAG->UNTAG */
						packet = TAG2UNTAG(packet,len);
						SEND_PACKET_PORT(portv[tarport],tarport,packet,len,&tmpbuf);
					} else {                               /* TAG->TAG */
						SEND_PACKET_PORT(portv[tarport],tarport,packet,len,&tmpbuf);
					}
				} else {
					void *tmpbuf=NULL;
					if (portv[tarport]->vlanuntag==vlan) { /* UNTAG->UNTAG */
						SEND_PACKET_PORT(portv[tarport],tarport,packet,len,&tmpbuf);
					} else {                              /* UNTAG->TAG */
						packet = UNTAG2TAG(packet,vlan,len);
						SEND_PACKET_PORT(portv[tarport],tarport,packet,len,&tmpbuf);
					}
				}
#endif
			} /* if(BROADCAST) */
		} /* if(HUB) */
	} /* if(PACKETFILTER) */
}

/**************************************** COMMAND MANAGEMENT ****************************************/

static int showinfo(FILE *fd)
{
	printoutc(fd,"Numports=%d",numports);
	printoutc(fd,"HUB=%s",(pflag & HUB_TAG)?"true":"false");
#ifdef PORTCOUNTERS
	printoutc(fd,"counters=true");
#else
	printoutc(fd,"counters=false");
#endif
#ifdef VDE_PQ2
	printoutc(fd,"default length of port packet queues: %d",stdqlen);
#endif
	return 0;
}


static int portallocatable(char *arg)
{
	int port,value;
	if (sscanf(arg,"%i %i",&port,&value) != 2)
		return EINVAL;
	if (port < 0 || port >= numports)
		return EINVAL;
	if (portv[port] == NULL)
		return ENXIO;
	if (value)
		portv[port]->flag &= ~NOTINPOOL;
	else
		portv[port]->flag |= NOTINPOOL;
	return 0;
}


static int portcreate(int val)
{
	int port;
	if (val <0 || val>=numports)
		return EINVAL;
	if (portv[val] != NULL)
		return EEXIST;
	port=alloc_port(val);
	if (port < 0)
		return ENOSPC;
	portv[port]->flag |= NOTINPOOL;
	return 0;
}

static int epclose(char *arg)
{
	int port,id;
	if (sscanf(arg,"%i %i",&port,&id) != 2)
		return EINVAL;
	else
		return close_ep_port_fd(port,id);
}

#ifdef VDE_PQ2
static int defqlen(int len)
{
	if (len < 0)
		return EINVAL;
	else {
		stdqlen=len;
		return 0;
	}
}

static int epqlen(char *arg)
{
	int port,id,len;
	if (sscanf(arg,"%i %i %i",&port,&id,&len) != 3 || len < 0)
		return EINVAL;
	else
		return setqlen_ep_port_fd(port,id,len);
}
#endif


/*Prints port configuration in console
 * return : 0 OR ERR code
 */
static int print_port(FILE *fd,int i,int inclinactive)
{
	struct endpoint *ep;
	if (portv[i] != NULL && (inclinactive || portv[i]->ep!=NULL)) {
		printoutc(fd,"Port %04d untagged_vlan=%04d %sACTIVE - %sUnnamed Allocatable",
				i,portv[i]->vlanuntag,
				portv[i]->ep?"":"IN",
				(portv[i]->flag & NOTINPOOL)?"NOT ":"");

#ifdef PORTCOUNTERS
		printoutc(fd," IN:  pkts %10lld          bytes %20lld",portv[i]->pktsin,portv[i]->bytesin);
		printoutc(fd," OUT: pkts %10lld          bytes %20lld",portv[i]->pktsout,portv[i]->bytesout);
#endif
		for (ep=portv[i]->ep; ep != NULL; ep=ep->next) {
			printoutc(fd,"  -- endpoint ID %04d module %-12s: %s",ep->fd_ctl,
					portv[i]->ms->modname,(ep->descr)?ep->descr:"no endpoint description");
#ifdef VDE_PQ2
			printoutc(fd,"              unsent packets: %d max %d",ep->vdepq_count,ep->vdepq_max);
#endif
		}
		return 0;
	} else
		return ENXIO;
}

/*Prints all ports configuration in console
 * return : 0 or ERR code
 */
static int print_ptable(FILE *fd,char *arg)
{
	int i;
	if (*arg != 0) {
		i=atoi(arg);
		if (i <0 || i>=numports)
			return EINVAL;
		else {
			return print_port(fd,i,0);
		}
	} else {
		for (i=0;i<numports;i++) 
			print_port(fd,i,0);
		return 0;
	}
}

static int print_ptableall(FILE *fd,char *arg)
{
	int i;
	if (*arg != 0) {
		i=atoi(arg);
		if (i <0 || i>=numports)
			return EINVAL;
		else {
			return print_port(fd,i,1);
		}
	} else {
		for (i=0;i<numports;i++) 
			print_port(fd,i,1);
		return 0;
	}
}


#ifdef PORTCOUNTERS
static void portzerocounter(int i)
{
	if (portv[i] != NULL) {
		portv[i]->pktsin=0;
		portv[i]->pktsout=0;
		portv[i]->bytesin=0;
		portv[i]->bytesout=0;
	}
}

static int portresetcounters(char *arg)
{
	int i;
	if (*arg != 0) {
		i=atoi(arg);
		if (i <0 || i>=numports)
			return EINVAL;
		else {
			portzerocounter(i);
			return 0;
		}
	} else {
		for (i=0;i<numports;i++)
			portzerocounter(i);
		return 0;
	}
}
#endif

/*Transform switch in hub
 * val = 1 >> hub
 * val = 0 >> switch (default value)
 */
static int portsethub(int val)
{
	if (val) {
#ifdef FSTP
		fstpshutdown();
#endif
		portflag(P_SETFLAG,HUB_TAG);
	} else
		portflag(P_CLRFLAG,HUB_TAG);
	return 0;
}

static int portsetvlan(char *arg)
{
	int port,vlan;
	if (sscanf(arg,"%i %i",&port,&vlan) != 2)
		return EINVAL;
	/* port NOVLAN is okay here, it means NO untagged traffic */
	if (vlan <0 || vlan > NUMOFVLAN || port < 0 || port >= numports) 
		return EINVAL;
	if ((vlan != NOVLAN && !bac_check(validvlan,vlan)) || portv[port] == NULL)
		return ENXIO;
	int oldvlan=portv[port]->vlanuntag;
	portv[port]->vlanuntag=NOVLAN;
	hash_delete_port(port);
	if (portv[port]->ep != NULL) {
		/*changing active port*/
		if (oldvlan != NOVLAN) 
			ba_clr(vlant[oldvlan].bcuntag,port);
		if (vlan != NOVLAN) {
			ba_set(vlant[vlan].bcuntag,port);
			ba_clr(vlant[vlan].bctag,port);
		}
#ifdef FSTP
		if (oldvlan != NOVLAN) fstdelport(oldvlan,port);
		if (vlan != NOVLAN) fstaddport(vlan,port,0);
#endif
	}
	if (oldvlan != NOVLAN) ba_clr(vlant[oldvlan].table,port);
	if (vlan != NOVLAN) ba_set(vlant[vlan].table,port);
	portv[port]->vlanuntag=vlan;
	return 0;
}

static int vlancreate_nocheck(int vlan)
{
	int rv=0;
	vlant[vlan].table=ba_alloc(numports);
	vlant[vlan].bctag=ba_alloc(numports);
	vlant[vlan].bcuntag=ba_alloc(numports);
	vlant[vlan].notlearning=ba_alloc(numports);
	if (vlant[vlan].table == NULL || vlant[vlan].bctag == NULL || 
			vlant[vlan].bcuntag == NULL) 
		return ENOMEM;
	else {
#ifdef FSTP
		rv=fstnewvlan(vlan);
#endif
		if (rv == 0) {
			bac_set(validvlan,NUMOFVLAN,vlan);
		}
		return rv;
	}
}

static int vlancreate(int vlan)
{
	if (vlan > 0 && vlan < NUMOFVLAN-1) { /*vlan NOVLAN (0xfff a.k.a. 4095) is reserved */
		if (bac_check(validvlan,vlan))
			return EEXIST;
		else 
			return vlancreate_nocheck(vlan);
	} else
		return EINVAL;
}

static int vlanremove(int vlan)
{
	if (vlan >= 0 && vlan < NUMOFVLAN) {
		if (bac_check(validvlan,vlan)) {
			int i,used=0;
			ba_FORALL(vlant[vlan].table,numports,used++,i);
			if (used)
				return EADDRINUSE;
			else {
				bac_clr(validvlan,NUMOFVLAN,vlan);
				free(vlant[vlan].table);
				free(vlant[vlan].bctag);
				free(vlant[vlan].bcuntag);
				free(vlant[vlan].notlearning);
				vlant[vlan].table=NULL;
				vlant[vlan].bctag=NULL;
				vlant[vlan].bcuntag=NULL;
				vlant[vlan].notlearning=NULL;
#ifdef FSTP
				fstremovevlan(vlan);
#endif
				return 0;
			}
		} else
			return ENXIO;
	} else
		return EINVAL;
}

/* Add a trunk port for a vlan
 * Renamed from initial function vlanaddport() - VV
 */
static int vlanaddtrunkport(char *arg)
{
	int port,vlan;
	if (sscanf(arg,"%i %i",&vlan,&port) != 2)
		return EINVAL;
	if (vlan <0 || vlan >= NUMOFVLAN-1 || port < 0 || port >= numports)
		return EINVAL;
	if (!bac_check(validvlan,vlan) || portv[port] == NULL)
		return ENXIO;
	if (portv[port]->ep != NULL && portv[port]->vlanuntag != vlan) {
		/* changing active port*/
		ba_set(vlant[vlan].bctag,port);
#ifdef FSTP
		fstaddport(vlan,port,1);
#endif
	}
	ba_set(vlant[vlan].table,port);
	return 0;
}

/* Delete a trunk port from a vlan
 * Renamed from initial function vlandelport() - VV
 */
static int vlandeltrunkport(char *arg)
{
	int port,vlan;
	if (sscanf(arg,"%i %i",&vlan,&port) != 2)
		return EINVAL;
	if (vlan <0 || vlan >= NUMOFVLAN-1 || port < 0 || port >= numports)
		return EINVAL;
	if (!bac_check(validvlan,vlan) || portv[port] == NULL)
		return ENXIO;
	if (portv[port]->vlanuntag == vlan)
		return EADDRINUSE;
	if (portv[port]->ep != NULL) {
		/*changing active port*/
		ba_clr(vlant[vlan].bctag,port);
#ifdef FSTP
		fstdelport(vlan,port);
#endif
	}
	ba_clr(vlant[vlan].table,port);
	hash_delete_port(port);
	return 0;
}

#define STRSTATUS(PN,V) \
	((ba_check(vlant[(V)].notlearning,(PN))) ? "Discarding" : \
	 (ba_check(vlant[(V)].bctag,(PN)) || ba_check(vlant[(V)].bcuntag,(PN))) ? \
	 "Forwarding" : "Learning")


static void vlanprintactive(int vlan,FILE *fd)
{
	int i;
	printoutc(fd,"VLAN %04d",vlan);
#ifdef FSTP
	if (pflag & FSTP_TAG) {
#if 0
		printoutc(fd," ++ FST root %02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x \n"
				"        designated %02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x port %d cost %d age %d",
				fsttab[vlan]->root[0], fsttab[vlan]->root[1], fsttab[vlan]->root[2], fsttab[vlan]->root[3],
				fsttab[vlan]->root[4], fsttab[vlan]->root[5], fsttab[vlan]->root[6], fsttab[vlan]->root[7],
				fsttab[vlan]->desbr[0], fsttab[vlan]->desbr[1], fsttab[vlan]->desbr[2], fsttab[vlan]->desbr[3],
				fsttab[vlan]->desbr[4], fsttab[vlan]->desbr[5], fsttab[vlan]->desbr[6], fsttab[vlan]->desbr[7],
				fsttab[vlan]->rootport, 
				ntohl(*(u_int32_t *)(&(fsttab[vlan]->rootcost))),
				qtime()-fsttab[vlan]->roottimestamp);
		ba_FORALL(vlant[vlan].table,numports,
				({ int tagged=portv[i]->vlanuntag != vlan;
				 if (portv[i]->ep)
				 printoutc(fd," -- Port %04d tagged=%d act=%d learn=%d forw=%d cost=%d role=%s",
					 i, tagged, 1, !(NOTLEARNING(i,vlan)),
					 (tagged)?(ba_check(vlant[vlan].bctag,i) != 0):(ba_check(vlant[vlan].bcuntag,i) != 0),
					 portv[i]->cost,
					 (fsttab[vlan]->rootport==i?"Root":
						((ba_check(fsttab[vlan]->backup,i)?"Alternate/Backup":"Designated")))
					 ); 0;
				 }) ,i);
#endif
	} else {
#endif
		ba_FORALL(vlant[vlan].table,numports,
				({ int tagged=portv[i]->vlanuntag != vlan;
				 if (portv[i]->ep)
				 printoutc(fd," -- Port %04d tagged=%d active=1 status=%s", i, tagged, 
					 STRSTATUS(i,vlan));
				 }), i);
#ifdef FSTP
	}
#endif
}

static int vlanprint(FILE *fd,char *arg)
{
	if (*arg != 0) {
		int vlan;
		vlan=atoi(arg);
		if (vlan >= 0 && vlan < NUMOFVLAN-1) {
			if (bac_check(validvlan,vlan))
				vlanprintactive(vlan,fd);
			else
				return ENXIO;
		} else
			return EINVAL;
	} else 
		bac_FORALLFUN(validvlan,NUMOFVLAN,vlanprintactive,fd);
	return 0;
}


// VV 20260227 Display modification
static void vlanprintelem(int vlan,FILE *fd)
{
	int i;
	printoutc(fd,"VLAN %04d",vlan);
	ba_FORALL(vlant[vlan].table,numports,
		printoutc(fd," -- Port %04d - %s - active=%d - status=%s",
			i,
			(portv[i]->vlanuntag != vlan)?"tagged (TRUNK)":"untagged      ", //VV
			portv[i]->ep != NULL,
			STRSTATUS(i,vlan)
	),i);
}

static int vlanprintall(FILE *fd,char *arg)
{
	if (*arg != 0) {
		int vlan;
		vlan=atoi(arg);
		if (vlan > 0 && vlan < NUMOFVLAN-1) {
			if (bac_check(validvlan,vlan)) {
				vlanprintelem(vlan,fd);
			} else {
				return ENXIO;
			}
		} else {
			return EINVAL;
		}
	} else {
		bac_FORALLFUN(validvlan,NUMOFVLAN,vlanprintelem,fd);
	}
	return 0;
}


/* NOT sure about the effects of changing address on FSTP */

#if 0
static int setmacaddr(char *strmac)
{
	int maci[ETH_ALEN],rv;

	if (index(strmac,':') != NULL)
		rv=sscanf(strmac,"%x:%x:%x:%x:%x:%x", maci+0, maci+1, maci+2, maci+3, maci+4, maci+5);
	else
		rv=sscanf(strmac,"%x.%x.%x.%x.%x.%x", maci+0, maci+1, maci+2, maci+3, maci+4, maci+5);
	if (rv < 6)
		return EINVAL;
	else  {
		int i;
		for (i=0;i<ETH_ALEN;i++)
			switchmac[i]=maci[i];
		return 0;
	}
}
#endif

uid_t port_user(int port)
{
	if (port<0 || port>=numports || portv[port]==NULL)
		return -1;
	else
		return portv[port]->curuser;
}

char *port_descr(int portno, int epn) {
	if (portno<0 || portno>=numports)
		return NULL;
	else {
		struct port *port=portv[portno];
		if (port == NULL)
			return NULL;
		else {
			struct endpoint *ep;
			for (ep=port->ep;ep!=NULL && epn>0;ep=ep->next,epn--)
				;
			if (ep)
				return ep->descr;
			else
				return NULL;
		}
	}
}

//VV 20260228 remove entries - rename vlan/addport to vlan/addtrunkport
static struct comlist cl[]={
	{"port","============","PORT STATUS MENU",NULL,NOARG},
	{"port/showinfo","","show port info",showinfo,NOARG|WITHFILE},
	{"port/sethub","0/1","1=HUB 0=switch",portsethub,INTARG},
	{"port/setvlan","N VLAN","set port VLAN (untagged)",portsetvlan,STRARG},
	{"port/allocatable","N 0/1","Is the port allocatable as unnamed? 1=Y 0=N",portallocatable,STRARG},
	{"port/epclose","N ID","remove the endpoint port N/id ID",epclose,STRARG},
#ifdef VDE_PQ2
	{"port/defqlen","LEN","set the default queue length for new ports",defqlen,INTARG},
	{"port/epqlen","N ID LEN","set the lenth of the queue for port N/id IP",epqlen,STRARG},
#endif
#ifdef PORTCOUNTERS
	{"port/resetcounter","[N]","reset the port (N) counters",portresetcounters,STRARG},
#endif
	{"port/print","[N]","print the port/endpoint table",print_ptable,STRARG|WITHFILE},
	{"port/allprint","[N]","print the port/endpoint table (including inactive port)",print_ptableall,STRARG|WITHFILE},
	{"vlan","============","VLAN MANAGEMENT MENU",NULL,NOARG},
	{"vlan/create","N","create the VLAN with tag N",vlancreate,INTARG},
	{"vlan/remove","N","remove the VLAN with tag N",vlanremove,INTARG},
	{"vlan/addtrunkport","N PORT","add trunk port to the vlan N",vlanaddtrunkport,STRARG},
	{"vlan/deltrunkport","N PORT","del trunk port to the vlan N",vlandeltrunkport,STRARG},
	{"vlan/print","[N]","print the list of defined vlan",vlanprint,STRARG|WITHFILE},
	{"vlan/allprint","[N]","print the list of defined vlan (including inactive port)",vlanprintall,STRARG|WITHFILE},
};

void port_init(int initnumports)
{
	if((numports=initnumports) <= 0) {
		printlog(LOG_ERR,"The switch must have at least 1 port\n");
		exit(1);
	}
	portv=calloc(numports,sizeof(struct port *));
	/* vlan_init */
	validvlan=bac_alloc(NUMOFVLAN);

	if (portv==NULL || validvlan == NULL) {
		printlog(LOG_ERR,"ALLOC port data structures");
		exit(1);
	}
	ADDCL(cl);
#ifdef DEBUGOPT
	ADDDBGCL(dl);
#endif
	if (vlancreate_nocheck(0) != 0) {
		printlog(LOG_ERR,"ALLOC vlan port data structures");
		exit(1);
	}

	//VV 20260221 - automatic port initialization at start
	for(int i = 0; i<numports; i++) {
		char *mess=NULL;
		asprintf(&mess,"init port %d", i);
		printlog(LOG_INFO, mess);
		free(mess);
		portcreate(i);
	}

}


//VV 20260221
static int vlanwritevlancreate(int vlan,FILE *fd)
{
	printoutc(fd,"vlan/create %d",vlan);
	return 0;
}

//VV 20260227
static int vlanwriteonetrunk(int vlan, int port, int tagged, FILE *fd)
{
	if (tagged) {
		printoutc(fd,"vlan/addtrunkport %d %d",vlan, port);
	}
	return 0;
}

// VV 20260227 Display modification
static void vlanwritetrunkcreate(int vlan,FILE *fd)
{
	int i;
		ba_FORALL(vlant[vlan].table,numports,
			vlanwriteonetrunk(vlan, i, portv[i]->vlanuntag != vlan, fd),i);

}

//VV 20260221
int writevlanconfig(FILE *fd)
{
	bac_FORALLFUN(validvlan,NUMOFVLAN,vlanwritevlancreate,fd);

	return 0;
}

//VV 20260222
int writeportconfig(FILE *fd)
{
	int i;
	for (i=0;i<numports;i++) {
		printoutc(fd,"port/setvlan %d %d", i, portv[i]->vlanuntag);
	}
	bac_FORALLFUN(validvlan,NUMOFVLAN,vlanwritetrunkcreate,fd);

	return 0;
}

//VV 20260303
int writesethub(FILE *fd)
{
	printoutc(fd,"port/sethub %s",(pflag & HUB_TAG)?"1":"0");
	return 0;
}

