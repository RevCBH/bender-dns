#!/usr/bin/env python3
"""Local DNS-over-TCP servers for tests/resolver_live.sh.

  dns_server.py BASE_PORT

Serves one mode per port on 127.0.0.1, BASE_PORT + its index in MODES, and
the "ok" mode on 127.0.0.2 at every one of those ports (so a client given
the servers 127.0.0.1 and 127.0.0.2 with one port fails over from a bad
mode to a good one). Each connection carries one query (RFC 1035 4.2.2
framing). Prints "ready" once every port listens; runs until killed.
"""
import socket
import socketserver
import struct
import sys
import threading
import time

MODES = [
    "ok",        # 0: A 192.0.2.1, AAAA 2001:db8::1, MX 10 mail.<name>, TXT "hello"; else NODATA
    "nxdomain",  # 1: rcode 3
    "servfail",  # 2: rcode 2
    "refused",   # 3: rcode 5
    "cname",     # 4: alias.test -> CNAME target.test (only); target.test -> A 192.0.2.7;
                 #    chain.test -> CNAME mid.test, mid.test -> CNAME alias.test (in one answer)
    "mismatch",  # 5: an ok answer with another id
    "garbage",   # 6: a frame of 20 bytes that are no DNS message
    "silent",    # 7: reads the query, says nothing for 5 s, closes
    "cut",       # 8: a prefix announcing 100 bytes, 5 of them, then a close
    "flaky",     # 9: SERVFAIL the first time a name is asked, ok after that
    "loop",      # 10: loop.test -> CNAME loop2.test, loop2.test -> CNAME loop.test
]
# BASE_PORT + len(MODES) is closed on 127.0.0.1 (nothing listens there) and
# "ok" on 127.0.0.2.

T_A, T_CNAME, T_MX, T_TXT, T_AAAA = 1, 5, 15, 16, 28
seen_lock = threading.Lock()
seen = set()


def read_exact(sock, n):
    data = b""
    while len(data) < n:
        chunk = sock.recv(n - len(data))
        if not chunk:
            return None
        data += chunk
    return data


def parse_query(msg):
    """(id, flags, qname labels, qtype, qclass, question bytes)."""
    qid, flags = struct.unpack("!HH", msg[:4])
    i, labels = 12, []
    while msg[i] != 0:
        n = msg[i]
        labels.append(msg[i + 1:i + 1 + n])
        i += 1 + n
    i += 1
    qtype, qclass = struct.unpack("!HH", msg[i:i + 4])
    return qid, flags, labels, qtype, qclass, msg[12:i + 4]


def wire_name(text):
    out = b""
    for label in text.split("."):
        if label:
            out += bytes([len(label)]) + label.encode()
    return out + b"\x00"


def rr(owner, rtype, rdata, ttl=60):
    # owner: wire bytes, or None for a pointer to the question name (offset 12).
    o = b"\xc0\x0c" if owner is None else owner
    return o + struct.pack("!HHIH", rtype, 1, ttl, len(rdata)) + rdata


def response(qid, qflags, question, rcode, answers):
    flags = 0x8000 | (qflags & 0x0100) | 0x0080 | rcode  # QR, RD copied, RA
    head = struct.pack("!HHHHHH", qid, flags, 1, len(answers), 0, 0)
    return head + question + b"".join(answers)


def ok_answers(name, qtype):
    if qtype == T_A:
        return [rr(None, T_A, bytes([192, 0, 2, 1]))]
    if qtype == T_AAAA:
        return [rr(None, T_AAAA, bytes.fromhex("20010db8000000000000000000000001"))]
    if qtype == T_MX:
        return [rr(None, T_MX, struct.pack("!H", 10) + wire_name("mail." + name))]
    if qtype == T_TXT:
        return [rr(None, T_TXT, b"\x05hello")]
    return []


def cname_answers(name, qtype):
    if name == "alias.test":
        return [rr(None, T_CNAME, wire_name("target.test"))]
    if name == "target.test" and qtype == T_A:
        return [rr(None, T_A, bytes([192, 0, 2, 7]))]
    if name == "chain.test":
        return [rr(None, T_CNAME, wire_name("mid.test")),
                rr(wire_name("mid.test"), T_CNAME, wire_name("alias.test"))]
    return []


def loop_answers(name):
    if name == "loop.test":
        return [rr(None, T_CNAME, wire_name("loop2.test"))]
    if name == "loop2.test":
        return [rr(None, T_CNAME, wire_name("loop.test"))]
    return []


def frame(msg):
    return struct.pack("!H", len(msg)) + msg


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        sock, mode = self.request, self.server.mode
        prefix = read_exact(sock, 2)
        if prefix is None:
            return
        msg = read_exact(sock, struct.unpack("!H", prefix)[0])
        if msg is None:
            return
        qid, qflags, labels, qtype, qclass, question = parse_query(msg)
        name = b".".join(labels).decode("ascii", "replace").lower()
        if mode == "silent":
            time.sleep(5)
            return
        if mode == "garbage":
            sock.sendall(frame(b"\xde\xad\xbe\xef" * 5))
            return
        if mode == "cut":
            sock.sendall(b"\x00\x64" + b"\x12\x34\x81\x80\x00")
            return
        if mode == "flaky":
            with seen_lock:
                first = name not in seen
                seen.add(name)
            mode = "servfail" if first else "ok"
        rcode, answers, rid = 0, [], qid
        if mode == "ok":
            answers = ok_answers(name, qtype)
        elif mode == "nxdomain":
            rcode = 3
        elif mode == "servfail":
            rcode = 2
        elif mode == "refused":
            rcode = 5
        elif mode == "cname":
            answers = cname_answers(name, qtype)
        elif mode == "loop":
            answers = loop_answers(name)
        elif mode == "mismatch":
            answers, rid = ok_answers(name, qtype), (qid + 1) % 65536
        sock.sendall(frame(response(rid, qflags, question, rcode, answers)))


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


def serve(host, port, mode):
    srv = Server((host, port), Handler)
    srv.mode = mode
    threading.Thread(target=srv.serve_forever, daemon=True).start()


def main():
    base = int(sys.argv[1])
    for i, mode in enumerate(MODES):
        serve("127.0.0.1", base + i, mode)
        serve("127.0.0.2", base + i, "ok")
    serve("127.0.0.2", base + len(MODES), "ok")
    print("ready", flush=True)
    while True:
        time.sleep(3600)


if __name__ == "__main__":
    main()
