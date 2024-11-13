// SPDX-License-Identifier: GPL-2.0-or-later
/* tcp_vu.c - TCP L2 vhost-user management functions
 *
 * Copyright Red Hat
 * Author: Laurent Vivier <lvivier@redhat.com>
 */

#include <errno.h>
#include <stddef.h>
#include <stdint.h>

#include <netinet/ip.h>
#include <netinet/tcp.h>

#include <sys/socket.h>

#include <linux/virtio_net.h>

#include "util.h"
#include "ip.h"
#include "passt.h"
#include "siphash.h"
#include "inany.h"
#include "vhost_user.h"
#include "tcp.h"
#include "pcap.h"
#include "flow.h"
#include "tcp_conn.h"
#include "flow_table.h"
#include "tcp_vu.h"
#include "tap.h"
#include "tcp_internal.h"
#include "checksum.h"
#include "vu_common.h"

static struct iovec iov_vu[VIRTQUEUE_MAX_SIZE + 1];
static struct vu_virtq_element elem[VIRTQUEUE_MAX_SIZE];

/**
 * tcp_vu_hdrlen() - return the size of the header in level 2 frame (TCP)
 * @v6:		Set for IPv6 packet
 *
 * Return: Return the size of the header
 */
static size_t tcp_vu_hdrlen(bool v6)
{
	size_t hdrlen;

	hdrlen = sizeof(struct virtio_net_hdr_mrg_rxbuf) +
		 sizeof(struct ethhdr) + sizeof(struct tcphdr);

	if (v6)
		hdrlen += sizeof(struct ipv6hdr);
	else
		hdrlen += sizeof(struct iphdr);

	return hdrlen;
}

/**
 * tcp_vu_update_check() - Calculate TCP checksum
 * @tapside:	Address information for one side of the flow
 * @iov:	Pointer to the array of IO vectors
 * @iov_used:	Length of the array
 */
static void tcp_vu_update_check(const struct flowside *tapside,
			        struct iovec *iov, int iov_used)
{
	char *base = iov[0].iov_base;

	if (inany_v4(&tapside->oaddr)) {
		const struct iphdr *iph = vu_ip(base);

		tcp_update_check_tcp4(iph, iov, iov_used,
				      (char *)vu_payloadv4(base) - base);
	} else {
		const struct ipv6hdr *ip6h = vu_ip(base);

		tcp_update_check_tcp6(ip6h, iov, iov_used,
				      (char *)vu_payloadv6(base) - base);
	}
}

/**
 * tcp_vu_send_flag() - Send segment with flags to vhost-user (no payload)
 * @c:		Execution context
 * @conn:	Connection pointer
 * @flags:	TCP flags: if not set, send segment only if ACK is due
 *
 * Return: negative error code on connection reset, 0 otherwise
 */
int tcp_vu_send_flag(const struct ctx *c, struct tcp_tap_conn *conn, int flags)
{
	struct vu_dev *vdev = c->vdev;
	struct vu_virtq *vq = &vdev->vq[VHOST_USER_RX_QUEUE];
	const struct flowside *tapside = TAPFLOW(conn);
	size_t l2len, l4len, optlen, hdrlen;
	struct vu_virtq_element flags_elem[2];
	struct iovec flags_iov[2];
	struct ethhdr *eh;
	int elem_cnt;
	int nb_ack;
	int ret;

	hdrlen = tcp_vu_hdrlen(CONN_V6(conn));

	vu_set_element(&flags_elem[0], NULL, &flags_iov[0]);

	elem_cnt = vu_collect(vdev, vq, &flags_elem[0], 1,
			      hdrlen + sizeof(struct tcp_syn_opts), NULL);
	if (elem_cnt != 1)
		return -1;

	vu_set_vnethdr(vdev, flags_elem[0].in_sg[0].iov_base, 1);

	eh = vu_eth(flags_elem[0].in_sg[0].iov_base);

	memcpy(eh->h_dest, c->guest_mac, sizeof(eh->h_dest));
	memcpy(eh->h_source, c->our_tap_mac, sizeof(eh->h_source));

	if (CONN_V4(conn)) {
		struct tcp_payload_t *payload;
		struct iphdr *iph;
		uint32_t seq;

		eh->h_proto = htons(ETH_P_IP);

		iph = vu_ip(flags_elem[0].in_sg[0].iov_base);
		*iph = (struct iphdr)L2_BUF_IP4_INIT(IPPROTO_TCP);

		payload = vu_payloadv4(flags_elem[0].in_sg[0].iov_base);
		memset(&payload->th, 0, sizeof(payload->th));
		payload->th.doff = offsetof(struct tcp_payload_t, data) / 4;
		payload->th.ack = 1;

		seq = conn->seq_to_tap;
		ret = tcp_prepare_flags(c, conn, flags, &payload->th,
					(struct tcp_syn_opts *)payload->data,
					&optlen);
		if (ret <= 0) {
			vu_queue_rewind(vq, 1);
			return ret;
		}

		l4len = tcp_fill_headers4(conn, NULL, iph, payload, optlen,
					  NULL, seq, true);
		l2len = sizeof(*iph);
	} else {
		struct tcp_payload_t *payload;
		struct ipv6hdr *ip6h;
		uint32_t seq;

		eh->h_proto = htons(ETH_P_IPV6);

		ip6h = vu_ip(flags_elem[0].in_sg[0].iov_base);
		*ip6h = (struct ipv6hdr)L2_BUF_IP6_INIT(IPPROTO_TCP);

		payload = vu_payloadv6(flags_elem[0].in_sg[0].iov_base);
		memset(&payload->th, 0, sizeof(payload->th));
		payload->th.doff = offsetof(struct tcp_payload_t, data) / 4;
		payload->th.ack = 1;

		seq = conn->seq_to_tap;
		ret = tcp_prepare_flags(c, conn, flags, &payload->th,
					(struct tcp_syn_opts *)payload->data,
					&optlen);
		if (ret <= 0) {
			vu_queue_rewind(vq, 1);
			return ret;
		}

		l4len = tcp_fill_headers6(conn, NULL, ip6h, payload, optlen,
					  seq, true);
		l2len = sizeof(*ip6h);
	}
	l2len += l4len + sizeof(struct ethhdr);

	flags_elem[0].in_sg[0].iov_len = l2len +
				   sizeof(struct virtio_net_hdr_mrg_rxbuf);
	if (*c->pcap) {
		tcp_vu_update_check(tapside, &flags_elem[0].in_sg[0], 1);
		pcap_iov(&flags_elem[0].in_sg[0], 1,
			 sizeof(struct virtio_net_hdr_mrg_rxbuf));
	}
	nb_ack = 1;

	if (flags & DUP_ACK) {
		vu_set_element(&flags_elem[1], NULL, &flags_iov[1]);

		elem_cnt = vu_collect(vdev, vq, &flags_elem[1], 1,
				      flags_elem[0].in_sg[0].iov_len, NULL);
		if (elem_cnt == 1) {
			memcpy(flags_elem[1].in_sg[0].iov_base,
			       flags_elem[0].in_sg[0].iov_base,
			       flags_elem[0].in_sg[0].iov_len);
			nb_ack++;

			if (*c->pcap)
				pcap_iov(&flags_elem[1].in_sg[0], 1, 0);
		}
	}

	vu_flush(vdev, vq, flags_elem, nb_ack);

	return 0;
}

/** tcp_vu_sock_recv() - Receive datastream from socket into vhost-user buffers
 * @c:			Execution context
 * @conn:		Connection pointer
 * @v6:			Set for IPv6 connections
 * @already_sent:	Number of bytes already sent
 * @fillsize:		Number of bytes we can receive
 * @iov_cnt:		number of iov (output)
 *
 * Return: Number of iov entries used to store the data
 */
static ssize_t tcp_vu_sock_recv(const struct ctx *c,
				const struct tcp_tap_conn *conn, bool v6,
				uint32_t already_sent, size_t fillsize,
				int *iov_cnt)
{
	struct vu_dev *vdev = c->vdev;
	struct vu_virtq *vq = &vdev->vq[VHOST_USER_RX_QUEUE];
	struct msghdr mh_sock = { 0 };
	uint16_t mss = MSS_GET(conn);
	int s = conn->sock;
	size_t hdrlen;
	int elem_cnt;
	ssize_t ret;

	*iov_cnt = 0;

	hdrlen = tcp_vu_hdrlen(v6);

	vu_init_elem(elem, &iov_vu[1], VIRTQUEUE_MAX_SIZE);

	elem_cnt = 0;

	while (fillsize > 0 && elem_cnt < VIRTQUEUE_MAX_SIZE) {
		struct iovec *iov;
		size_t frame_size;
		int cnt;

		if (mss > fillsize)
			mss = fillsize;

		cnt = vu_collect(vdev, vq, &elem[elem_cnt],
				 VIRTQUEUE_MAX_SIZE - elem_cnt,
				 mss + hdrlen, &frame_size);
		if (cnt == 0)
			break;

		frame_size -= hdrlen;
		iov = &elem[elem_cnt].in_sg[0];
		iov->iov_base = (char *)iov->iov_base + hdrlen;
		iov->iov_len -= hdrlen;

		fillsize -= frame_size;
		elem_cnt += cnt;

		/* All the frames must have the same size (except the last one),
		 * otherwise we will no able to scan the iov array
		 * to find iov entries with headers
		 * (headers are spread every frame_size in the the array
		 */
		if (frame_size < mss)
			break;
	}

	if (peek_offset_cap) {
		mh_sock.msg_iov = iov_vu + 1;
		mh_sock.msg_iovlen = elem_cnt;
	} else {
		iov_vu[0].iov_base = tcp_buf_discard;
		iov_vu[0].iov_len = already_sent;

		mh_sock.msg_iov = iov_vu;
		mh_sock.msg_iovlen = elem_cnt + 1;
	}

	do
		ret = recvmsg(s, &mh_sock, MSG_PEEK);
	while (ret < 0 && errno == EINTR);

	*iov_cnt = elem_cnt;

	return ret;
}

/**
 * tcp_vu_prepare() - Prepare the frame header
 * @c:		Execution context
 * @conn:	Connection pointer
 * @first:	Pointer to the array of IO vectors
 * @dlen:	Packet data length
 * @check:	Checksum, if already known
 */
static void tcp_vu_prepare(const struct ctx *c,
			   struct tcp_tap_conn *conn, struct iovec *first,
			   size_t dlen, const uint16_t **check)
{
	const struct flowside *toside = TAPFLOW(conn);
	char *base = first->iov_base;
	struct ethhdr *eh;

	/* we guess the first iovec provided by the guest can embed
	 * all the headers needed by L2 frame
	 */

	eh = vu_eth(base);

	memcpy(eh->h_dest, c->guest_mac, sizeof(eh->h_dest));
	memcpy(eh->h_source, c->our_tap_mac, sizeof(eh->h_source));

	/* initialize header */
	if (inany_v4(&toside->eaddr) && inany_v4(&toside->oaddr)) {
		struct tcp_payload_t *payload;
		struct iphdr *iph;

		ASSERT(first[0].iov_len >= tcp_vu_hdrlen(false));

		eh->h_proto = htons(ETH_P_IP);

		iph = vu_ip(base);
		*iph = (struct iphdr)L2_BUF_IP4_INIT(IPPROTO_TCP);
		payload = vu_payloadv4(base);
		memset(&payload->th, 0, sizeof(payload->th));
		payload->th.doff = offsetof(struct tcp_payload_t, data) / 4;
		payload->th.ack = 1;

		tcp_fill_headers4(conn, NULL, iph, payload, dlen,
				  *check, conn->seq_to_tap, true);
		*check = &iph->check;
	} else {
		struct tcp_payload_t *payload;
		struct ipv6hdr *ip6h;

		ASSERT(first[0].iov_len >= tcp_vu_hdrlen(true));

		eh->h_proto = htons(ETH_P_IPV6);

		ip6h = vu_ip(base);
		*ip6h = (struct ipv6hdr)L2_BUF_IP6_INIT(IPPROTO_TCP);

		payload = vu_payloadv6(base);
		memset(&payload->th, 0, sizeof(payload->th));
		payload->th.doff = offsetof(struct tcp_payload_t, data) / 4;
		payload->th.ack = 1;

		tcp_fill_headers6(conn, NULL, ip6h, payload, dlen,
				  conn->seq_to_tap, true);
	}
}

/**
 * tcp_vu_data_from_sock() - Handle new data from socket, queue to vhost-user,
 *			     in window
 * @c:		Execution context
 * @conn:	Connection pointer
 *
 * Return: Negative on connection reset, 0 otherwise
 */
int tcp_vu_data_from_sock(const struct ctx *c, struct tcp_tap_conn *conn)
{
	uint32_t wnd_scaled = conn->wnd_from_tap << conn->ws_from_tap;
	struct vu_dev *vdev = c->vdev;
	struct vu_virtq *vq = &vdev->vq[VHOST_USER_RX_QUEUE];
	const struct flowside *tapside = TAPFLOW(conn);
	uint16_t mss = MSS_GET(conn);
	size_t hdrlen, fillsize;
	int i, iov_cnt, iov_used;
	int v6 = CONN_V6(conn);
	uint32_t already_sent = 0;
	const uint16_t *check;
	struct iovec *first;
	int frame_size;
	int num_buffers;
	ssize_t len;

	if (!vu_queue_enabled(vq) || !vu_queue_started(vq)) {
		flow_err(conn,
			 "Got packet, but RX virtqueue not usable yet");
		return 0;
	}

	already_sent = conn->seq_to_tap - conn->seq_ack_from_tap;

	if (SEQ_LT(already_sent, 0)) {
		/* RFC 761, section 2.1. */
		flow_trace(conn, "ACK sequence gap: ACK for %u, sent: %u",
			   conn->seq_ack_from_tap, conn->seq_to_tap);
		conn->seq_to_tap = conn->seq_ack_from_tap;
		already_sent = 0;
		if (tcp_set_peek_offset(conn->sock, 0)) {
			tcp_rst(c, conn);
			return -1;
		}
	}

	if (!wnd_scaled || already_sent >= wnd_scaled) {
		conn_flag(c, conn, STALLED);
		conn_flag(c, conn, ACK_FROM_TAP_DUE);
		return 0;
	}

	/* Set up buffer descriptors we'll fill completely and partially. */

	fillsize = wnd_scaled - already_sent;

	/* collect the buffers from vhost-user and fill them with the
	 * data from the socket
	 */
	len = tcp_vu_sock_recv(c, conn, v6, already_sent, fillsize, &iov_cnt);
	if (len < 0) {
		vu_queue_rewind(vq, iov_cnt);
		if (errno != EAGAIN && errno != EWOULDBLOCK) {
			tcp_rst(c, conn);
			return -errno;
		}
		return 0;
	}

	if (!len) {
		vu_queue_rewind(vq, iov_cnt);
		if ((conn->events & (SOCK_FIN_RCVD | TAP_FIN_SENT)) == SOCK_FIN_RCVD) {
			int ret = tcp_vu_send_flag(c, conn, FIN | ACK);
			if (ret) {
				tcp_rst(c, conn);
				return ret;
			}

			conn_event(c, conn, TAP_FIN_SENT);
		}

		return 0;
	}

	if (!peek_offset_cap)
		len -= already_sent;

	if (len <= 0) {
		vu_queue_rewind(vq, iov_cnt);
		conn_flag(c, conn, STALLED);
		return 0;
	}

	conn_flag(c, conn, ~STALLED);

	/* Likely, some new data was acked too. */
	tcp_update_seqack_wnd(c, conn, false, NULL);

	/* initialize headers */
	hdrlen = tcp_vu_hdrlen(v6);
	iov_used = 0;
	num_buffers = 0;
	check = NULL;
	frame_size = 0;

	/* iov_vu is an array of buffers and the buffer size can be
	 * smaller than the frame size we want to use but with
	 * num_buffer we can merge several virtio iov buffers in one packet
	 * we need only to set the packet headers in the first iov and
	 * num_buffer to the number of iov entries
	 */
	for (i = 0; i < iov_cnt && len; i++) {

		if (frame_size == 0)
			first = &iov_vu[i + 1];

		if (iov_vu[i + 1].iov_len > (size_t)len)
			iov_vu[i + 1].iov_len = len;

		len -= iov_vu[i + 1].iov_len;
		iov_used++;

		frame_size += iov_vu[i + 1].iov_len;
		num_buffers++;

		if (frame_size >= mss || len == 0 ||
		    i + 1 == iov_cnt || !vu_has_feature(vdev, VIRTIO_NET_F_MRG_RXBUF)) {
			if (i + 1 == iov_cnt)
				check = NULL;

			/* restore first iovec base: point to vnet header */
			first->iov_base = (char *)first->iov_base - hdrlen;
			first->iov_len += hdrlen;
			vu_set_vnethdr(vdev, first->iov_base, num_buffers);

			tcp_vu_prepare(c, conn, first, frame_size, &check);
			if (*c->pcap)  {
				tcp_vu_update_check(tapside, first, num_buffers);
				pcap_iov(first, num_buffers,
					 sizeof(struct virtio_net_hdr_mrg_rxbuf));
			}

			conn->seq_to_tap += frame_size;

			frame_size = 0;
			num_buffers = 0;
		}
	}

	/* release unused buffers */
	vu_queue_rewind(vq, iov_cnt - iov_used);

	/* send packets */
	vu_flush(vdev, vq, elem, iov_used);

	conn_flag(c, conn, ACK_FROM_TAP_DUE);

	return 0;
}
