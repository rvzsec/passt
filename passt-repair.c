// SPDX-License-Identifier: GPL-2.0-or-later

/* PASST - Plug A Simple Socket Transport
 *  for qemu/UNIX domain socket mode
 *
 * PASTA - Pack A Subtle Tap Abstraction
 *  for network namespace/tap device mode
 *
 * passt-repair.c - Privileged helper to set/clear TCP_REPAIR on sockets
 *
 * Copyright (c) 2025 Red Hat GmbH
 * Author: Stefano Brivio <sbrivio@redhat.com>
 *
 * Connect to passt via UNIX domain socket, receive sockets via SCM_RIGHTS along
 * with byte commands mapping to TCP_REPAIR values, and switch repair mode on or
 * off. Reply by echoing the command. Exit on EOF.
 */

#include <sys/inotify.h>
#include <sys/prctl.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <errno.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <unistd.h>
#include <netdb.h>

#include <netinet/tcp.h>

#include <linux/audit.h>
#include <linux/capability.h>
#include <linux/filter.h>
#include <linux/seccomp.h>

#include "seccomp_repair.h"

#define SCM_MAX_FD 253 /* From Linux kernel (include/net/scm.h), not in UAPI */
#define REPAIR_EXT		".repair"
#define REPAIR_EXT_LEN		strlen(REPAIR_EXT)

/**
 * main() - Entry point and whole program with loop
 * @argc:	Argument count, must be 2
 * @argv:	Argument: path of UNIX domain socket to connect to
 *
 * Return: 0 on success (EOF), 1 on error, 2 on usage error
 *
 * #syscalls:repair connect setsockopt write close exit_group
 * #syscalls:repair socket s390x:socketcall i686:socketcall
 * #syscalls:repair recvfrom recvmsg arm:recv ppc64le:recv
 * #syscalls:repair sendto sendmsg arm:send ppc64le:send
 * #syscalls:repair stat|statx stat64|statx statx
 * #syscalls:repair fstat|fstat64 newfstatat|fstatat64
 * #syscalls:repair inotify_init1 inotify_add_watch
 */
int main(int argc, char **argv)
{
	char buf[CMSG_SPACE(sizeof(int) * SCM_MAX_FD)]
	     __attribute__ ((aligned(__alignof__(struct cmsghdr))));
	struct sockaddr_un a = { AF_UNIX, "" };
	int fds[SCM_MAX_FD], s, ret, i, n = 0;
	bool inotify_dir = false;
	struct sock_fprog prog;
	int8_t cmd = INT8_MAX;
	struct cmsghdr *cmsg;
	struct msghdr msg;
	struct iovec iov;
	size_t cmsg_len;
	struct stat sb;
	int op;

	prctl(PR_SET_DUMPABLE, 0);

	prog.len = (unsigned short)sizeof(filter_repair) /
				   sizeof(filter_repair[0]);
	prog.filter = filter_repair;
	if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) ||
	    prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog)) {
		fprintf(stderr, "Failed to apply seccomp filter");
		_exit(1);
	}

	iov = (struct iovec){ &cmd, sizeof(cmd) };
	msg = (struct msghdr){ .msg_name = NULL, .msg_namelen = 0,
			       .msg_iov = &iov, .msg_iovlen = 1,
			       .msg_control = buf,
			       .msg_controllen = sizeof(buf),
			       .msg_flags = 0 };
	cmsg = CMSG_FIRSTHDR(&msg);

	if (argc != 2) {
		fprintf(stderr, "Usage: %s PATH\n", argv[0]);
		_exit(2);
	}

	if ((s = socket(AF_UNIX, SOCK_STREAM, 0)) < 0) {
		fprintf(stderr, "Failed to create AF_UNIX socket: %i\n", errno);
		_exit(1);
	}

	if ((stat(argv[1], &sb))) {
		fprintf(stderr, "Can't stat() %s: %i\n", argv[1], errno);
		_exit(1);
	}

	if ((sb.st_mode & S_IFMT) == S_IFDIR) {
		char buf[sizeof(struct inotify_event) + NAME_MAX + 1]
		   __attribute__ ((aligned(__alignof__(struct inotify_event))));
		const struct inotify_event *ev;
		char path[PATH_MAX + 1];
		bool found = false;
		ssize_t n;
		int fd;

		if ((fd = inotify_init1(IN_CLOEXEC)) < 0) {
			fprintf(stderr, "inotify_init1: %i\n", errno);
			_exit(1);
		}

		if (inotify_add_watch(fd, argv[1], IN_CREATE) < 0) {
			fprintf(stderr, "inotify_add_watch: %i\n", errno);
			_exit(1);
		}

		do {
			char *p;

			n = read(fd, buf, sizeof(buf));
			if (n < 0) {
				fprintf(stderr, "inotify read: %i", errno);
				_exit(1);
			}

			if (n < (ssize_t)sizeof(*ev)) {
				fprintf(stderr, "Short inotify read: %zi", n);
				continue;
			}

			for (p = buf; p < buf + n; p += sizeof(*ev) + ev->len) {
				ev = (const struct inotify_event *)p;

				if (ev->len >= REPAIR_EXT_LEN &&
				    !memcmp(ev->name +
					    strnlen(ev->name, ev->len) -
					    REPAIR_EXT_LEN,
					    REPAIR_EXT, REPAIR_EXT_LEN)) {
					found = true;
					break;
				}
			}
		} while (!found);

		if (ev->len > NAME_MAX + 1 || ev->name[ev->len - 1] != '\0') {
			fprintf(stderr, "Invalid filename from inotify\n");
			_exit(1);
		}

		snprintf(path, sizeof(path), "%s/%s", argv[1], ev->name);
		if ((stat(path, &sb))) {
			fprintf(stderr, "Can't stat() %s: %i\n", path, errno);
			_exit(1);
		}

		ret = snprintf(a.sun_path, sizeof(a.sun_path), "%s", path);
		inotify_dir = true;
	} else {
		ret = snprintf(a.sun_path, sizeof(a.sun_path), "%s", argv[1]);
	}

	if (ret <= 0 || ret >= (int)sizeof(a.sun_path)) {
		fprintf(stderr, "Invalid socket path");
		_exit(2);
	}

	if ((sb.st_mode & S_IFMT) != S_IFSOCK) {
		fprintf(stderr, "%s is not a socket\n", a.sun_path);
		_exit(2);
	}

	while (connect(s, (struct sockaddr *)&a, sizeof(a))) {
		if (inotify_dir && errno == ECONNREFUSED)
			continue;

		fprintf(stderr, "Failed to connect to %s: %s\n", a.sun_path,
			strerror(errno));
		_exit(1);
	}

loop:
	ret = recvmsg(s, &msg, 0);
	if (ret < 0) {
		if (errno == ECONNRESET) {
			ret = 0;
		} else {
			fprintf(stderr, "Failed to read message: %i\n", errno);
			_exit(1);
		}
	}

	if (!ret)	/* Done */
		_exit(0);

	if (!cmsg ||
	    cmsg->cmsg_len < CMSG_LEN(sizeof(int)) ||
	    cmsg->cmsg_len > CMSG_LEN(sizeof(int) * SCM_MAX_FD) ||
	    cmsg->cmsg_type != SCM_RIGHTS) {
		fprintf(stderr, "No/bad ancillary data from peer\n");
		_exit(1);
	}

	/* No inverse formula for CMSG_LEN(x), and building one with CMSG_LEN(0)
	 * works but there's no guarantee it does. Search the whole domain.
	 */
	for (i = 1; i <= SCM_MAX_FD; i++) {
		if (CMSG_LEN(sizeof(int) * i) == cmsg->cmsg_len) {
			n = i;
			break;
		}
	}
	if (!n) {
		cmsg_len = cmsg->cmsg_len; /* socklen_t is 'unsigned' on musl */
		fprintf(stderr, "Invalid ancillary data length %zu from peer\n",
			cmsg_len);
		_exit(1);
	}

	memcpy(fds, CMSG_DATA(cmsg), sizeof(int) * n);

	if (cmd != TCP_REPAIR_ON && cmd != TCP_REPAIR_OFF &&
	    cmd != TCP_REPAIR_OFF_NO_WP) {
		fprintf(stderr, "Unsupported command 0x%04x\n", cmd);
		_exit(1);
	}

	op = cmd;

	for (i = 0; i < n; i++) {
		if (setsockopt(fds[i], SOL_TCP, TCP_REPAIR, &op, sizeof(op))) {
			fprintf(stderr,
				"Setting TCP_REPAIR to %i on socket %i: %s", op,
				fds[i], strerror(errno));
			_exit(1);
		}

		/* Close _our_ copy */
		close(fds[i]);
	}

	/* Confirm setting by echoing the command back */
	if (send(s, &cmd, sizeof(cmd), 0) < 0) {
		fprintf(stderr, "Reply to %i: %s\n", op, strerror(errno));
		_exit(1);
	}

	goto loop;

	return 0;
}
