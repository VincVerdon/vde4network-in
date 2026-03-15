/* VDE4Network-Inc is forked from VDE2 and adapted for Network-In! Simulator project
 * Copyright V. Verdon - Version 20260308
 * Initial Copyright 2002 Jeff Dike
 * Licensed under the GPL
 */

// VV 20260308 bug HAVE_TUN_TAP
#ifdef HAVE_TUNTAP

#ifndef __TUNTAP_H__
#define __TUNTAP_H__

extern int send_tap(int fd, int ctl_fd, void *packet, int len, void *unused, int port);
extern int recv_tap(int fd, void *packet, int maxlen, int port);
extern int open_tap(char *dev);

#endif

// VV 20260308 add
void start_tuntap(void);
#endif
