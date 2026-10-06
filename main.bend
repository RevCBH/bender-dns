import Base
import ./src/bytes.bend as B
import ./src/types.bend as M
import ./src/name.bend as NM
import ./src/ip.bend as IP
import ./src/encode.bend as E
import ./src/decode.bend as D
import ./src/frame.bend as F
import ./src/conf.bend as CF
import ./src/answer.bend as A
import ./src/os.bend as O
import ./src/transport.bend as X
import ./src/resolver.bend as R

# A DNS client for Bend: two resolvers behind one API.
#
#   import <this package>/main.bend as P
#
#   def main() -> IO(Unit):
#     do IO<Unit>:
#       cfg : Result<&2, &2, P.Dns.Error(), P.Dns.Config()> <- P.Dns.system()
#       ...
#       r : Result<&2, &2, P.Dns.Error(), List<&2, String>> <- P.Dns.lookup_ipv4(c, "example.com")
#
# - The native stack (Dns.resolve, Dns.lookup_ipv4 / ipv6): a stub resolver
#   written in Bend. It reads /etc/resolv.conf and /etc/hosts, expands the
#   search list, and asks the nameservers (RD = 1) over TCP (RFC 7766),
#   with fresh random ids, retries over servers and attempts, and CNAME
#   re-queries. Messages are encoded and decoded by pure code; no foreign
#   code is involved. IPv4 nameservers only (Base's TCP.connect).
# - OS delegation (Dns.os_lookup): getaddrinfo, through a foreign effect;
#   honours nsswitch, mDNS, VPN split DNS. Addresses only.
# - The codec (Dns.encode, Dns.decode, Dns.query, Dns.accept, Dns.answer,
#   Dns.frame): for callers with their own transport.
#
# This file defines only `Dns.*` wrappers over the modules in src/, plus the
# ErrorKind and DataKind tags for matching (imports are not re-exported, so
# these are the whole public surface). It imports foreign code (os.bend), so
# checking it reports the defs that rely on it.
#
# Lanes: the native C lane (`bend f.bend -o f`) has no stack limit; the JS
# lane (`bend f.bend`) overflows near 20-40 thousand nested non-tail calls.
# The library walks messages, record lists, hosts files and texts with
# loops, so both lanes handle 65535-byte messages and large hosts files.

# Types
# -----
# Aliases for annotations, e.g. `Result<&2, &2, P.Dns.Error(), P.Dns.Resolved()>`.
# All are Data.

def Dns.Bytes() -> Data:
  B.Bytes()

# A domain name: its labels (byte lists), most specific first; the root is [].
def Dns.Name() -> Data:
  M.Name()

def Dns.RType() -> Data:
  M.RType

def Dns.RClass() -> Data:
  M.RClass

def Dns.Question() -> Data:
  M.Question

def Dns.RData() -> Data:
  M.RData

def Dns.Record() -> Data:
  M.Record

def Dns.Header() -> Data:
  M.Header

def Dns.Message() -> Data:
  M.Message

def Dns.Answer() -> Data:
  M.Answer

def Dns.Resolved() -> Data:
  M.Resolved

def Dns.NameError() -> Data:
  M.NameError

def Dns.DecodeError() -> Data:
  M.DecodeError

def Dns.Error() -> Data:
  M.Error

def Dns.Config() -> Data:
  R.Config

# Record types and classes
# ------------------------

def Dns.A() -> M.RType:
  M.TA{}

def Dns.NS() -> M.RType:
  M.TNS{}

def Dns.CNAME() -> M.RType:
  M.TCNAME{}

def Dns.SOA() -> M.RType:
  M.TSOA{}

def Dns.PTR() -> M.RType:
  M.TPTR{}

def Dns.MX() -> M.RType:
  M.TMX{}

def Dns.TXT() -> M.RType:
  M.TTXT{}

def Dns.AAAA() -> M.RType:
  M.TAAAA{}

def Dns.SRV() -> M.RType:
  M.TSRV{}

def Dns.OPT() -> M.RType:
  M.TOPT{}

def Dns.ANY() -> M.RType:
  M.TANY{}

def Dns.RType.of_code.pick(+c: Nat, k: Maybe<&2, M.RType>) -> M.RType:
  match k:
    case Some{t}:
      t
    case None{}:
      M.TOther{c}

# The type with this wire code (a known code gives the named type).
def Dns.RType.of_code(+code: Nat) -> M.RType:
  Dns.RType.of_code.pick(code, E.type_known(code))

def Dns.RType.code(t: M.RType) -> Nat:
  E.type_code(t)

# "A", "AAAA", "MX", ..., "TYPE65" for others.
def Dns.RType.show(t: M.RType) -> String:
  R.type_name(t)

# A type by name, case-insensitively ("a", "MX", "TYPE65"; nnn <= 65535).
def Dns.RType.parse(s: String) -> Maybe<&2, M.RType>:
  R.type_of(s)

def Dns.RType.eq(a: M.RType, b: M.RType) -> Bool:
  Nat.is_eq(E.type_code(a), E.type_code(b))

def Dns.IN() -> M.RClass:
  M.CIN{}

def Dns.RClass.of_code.pick(one: Bool, c: Nat) -> M.RClass:
  match one:
    case True{}:
      M.CIN{}
    case False{}:
      M.COther{c}

def Dns.RClass.of_code(+code: Nat) -> M.RClass:
  Dns.RClass.of_code.pick(Nat.is_eq(code, 1n), code)

def Dns.RClass.code(c: M.RClass) -> Nat:
  E.class_code(c)

# Names
# -----
# Text is dotted, one trailing dot allowed, with RFC 1035 escapes (`\.`,
# `\DDD`); labels 1..63 bytes, at most 255 bytes on the wire.

def Dns.Name.parse(s: String) -> Result<&2, &2, M.NameError, M.Name()>:
  NM.from_text(s)

# The labels joined by '.', escaped, no trailing dot; the root is ".".
def Dns.Name.show(n: M.Name()) -> String:
  NM.to_text(n)

# The same with the trailing dot ("example.com.").
def Dns.Name.fqdn(n: M.Name()) -> String:
  R.fqdn(n)

# ASCII case-insensitive equality (RFC 4343).
def Dns.Name.eq(a: M.Name(), b: M.Name()) -> Bool:
  NM.eq(a, b)

def Dns.Name.lower(n: M.Name()) -> M.Name():
  NM.lower(n)

# Valid: every label 1..63 bytes, at most 255 bytes on the wire.
def Dns.Name.ok(n: M.Name()) -> Bool:
  NM.ok(n)

# The uncompressed wire form.
def Dns.Name.wire(n: M.Name()) -> List<&2, U32>:
  NM.wire(n)

def Dns.NameError.show(e: M.NameError) -> String:
  R.name_error_show(e)

# Addresses
# ---------

def Dns.Ip.show4(a: Nat, b: Nat, c: Nat, d: Nat) -> String:
  IP.show4(a, b, c, d)

# A canonical dotted quad, as an A record's data.
def Dns.Ip.parse4(s: String) -> Maybe<&2, M.RData>:
  IP.parse4(s)

# RFC 5952 text of 8 groups.
def Dns.Ip.show6(groups: List<&2, Nat>) -> String:
  IP.show6(groups)

# RFC 4291 text, as an AAAA record's data.
def Dns.Ip.parse6(s: String) -> Maybe<&2, M.RData>:
  IP.parse6(s)

def Dns.Ip.is_ipv4(s: String) -> Bool:
  IP.is_ipv4(s)

def Dns.Ip.is_ipv6(s: String) -> Bool:
  IP.is_ipv6(s)

# Record data
# -----------
# Builders (for Dns.encode), then readers. A record's data follows its
# type: A RIpv4, AAAA RIpv6, NS / CNAME / PTR a name, MX, TXT, SOA, SRV
# their own, every other type (and OPT) raw bytes.

def Dns.ipv4(a: Nat, b: Nat, c: Nat, d: Nat) -> M.RData:
  M.RIpv4{a, b, c, d}

def Dns.ipv6(groups: List<&2, Nat>) -> M.RData:
  M.RIpv6{groups}

def Dns.name_data(n: M.Name()) -> M.RData:
  M.RName{n}

def Dns.mx(preference: Nat, exchange: M.Name()) -> M.RData:
  M.RMx{preference, exchange}

def Dns.txt(strings: List<&2, List<&2, U32>>) -> M.RData:
  M.RTxt{strings}

def Dns.soa(mname: M.Name(), rname: M.Name(), serial: Nat, refresh: Nat, retry: Nat, expire: Nat,
  minimum: Nat) -> M.RData:
  M.RSoa{mname, rname, serial, refresh, retry, expire, minimum}

def Dns.srv(priority: Nat, weight: Nat, port: Nat, target: M.Name()) -> M.RData:
  M.RSrv{priority, weight, port, target}

def Dns.raw(bytes: List<&2, U32>) -> M.RData:
  M.RRaw{bytes}

# Which form a record's data has.
type DataKind is Data:
  DIpv4{}
  DIpv6{}
  DName{}
  DMx{}
  DTxt{}
  DSoa{}
  DSrv{}
  DRaw{}

def Dns.DataKind() -> Data:
  DataKind

def Dns.RData.kind(d: M.RData) -> DataKind:
  match d:
    case M.RIpv4{a, b, c, e}:
      DIpv4{}
    case M.RIpv6{gs}:
      DIpv6{}
    case M.RName{n}:
      DName{}
    case M.RMx{p, n}:
      DMx{}
    case M.RTxt{ss}:
      DTxt{}
    case M.RSoa{mn, rn, se, rf, rt, ex, mi}:
      DSoa{}
    case M.RSrv{pr, w, po, t}:
      DSrv{}
    case M.RRaw{xs}:
      DRaw{}

# Presentation form, as dig prints it ("93.184.215.14", "10 mx.example.",
# "\"text\"", "\# 2 abcd").
def Dns.RData.show(d: M.RData) -> String:
  R.rdata_text(d)

# An A or AAAA record's address as text.
def Dns.RData.address(d: M.RData) -> Maybe<&2, String>:
  R.addr.of(d)

# The name in NS, CNAME, PTR (the name), MX (the exchange), SRV (the
# target) and SOA (mname) data.
def Dns.RData.name(d: M.RData) -> Maybe<&2, M.Name()>:
  match d:
    case M.RName{n}:
      Some{n}
    case M.RMx{p, n}:
      Some{n}
    case M.RSrv{pr, w, po, t}:
      Some{t}
    case M.RSoa{mn, rn, se, rf, rt, ex, mi}:
      Some{mn}
    case _:
      None{}

# MX preference, SRV priority.
def Dns.RData.preference(d: M.RData) -> Maybe<&2, Nat>:
  match d:
    case M.RMx{p, n}:
      Some{p}
    case M.RSrv{pr, w, po, t}:
      Some{pr}
    case _:
      None{}

# TXT character-strings (bytes each).
def Dns.RData.strings(d: M.RData) -> List<&2, List<&2, U32>>:
  match d:
    case M.RTxt{ss}:
      ss
    case _:
      Nil{}

# IPv6 groups (8 of 16 bits).
def Dns.RData.groups(d: M.RData) -> List<&2, Nat>:
  match d:
    case M.RIpv6{gs}:
      gs
    case _:
      Nil{}

# Raw data bytes (unknown types, OPT).
def Dns.RData.bytes(d: M.RData) -> List<&2, U32>:
  match d:
    case M.RRaw{xs}:
      xs
    case _:
      Nil{}

# SRV port.
def Dns.RData.port(d: M.RData) -> Maybe<&2, Nat>:
  match d:
    case M.RSrv{pr, w, po, t}:
      Some{po}
    case _:
      None{}

# SOA serial.
def Dns.RData.serial(d: M.RData) -> Maybe<&2, Nat>:
  match d:
    case M.RSoa{mn, rn, se, rf, rt, ex, mi}:
      Some{se}
    case _:
      None{}

# Records, questions, headers, messages
# -------------------------------------

def Dns.record(name: M.Name(), rtype: M.RType, rclass: M.RClass, ttl: Nat, data: M.RData) -> M.Record:
  M.Record{name, rtype, rclass, ttl, data}

def Dns.Record.name(r: M.Record) -> M.Name():
  match r:
    case M.Record{n, t, c, ttl, d}:
      n

def Dns.Record.rtype(r: M.Record) -> M.RType:
  match r:
    case M.Record{n, t, c, ttl, d}:
      t

def Dns.Record.rclass(r: M.Record) -> M.RClass:
  match r:
    case M.Record{n, t, c, ttl, d}:
      c

def Dns.Record.ttl(r: M.Record) -> Nat:
  match r:
    case M.Record{n, t, c, ttl, d}:
      ttl

def Dns.Record.data(r: M.Record) -> M.RData:
  match r:
    case M.Record{n, t, c, ttl, d}:
      d

# "owner.<TAB>TTL<TAB>IN<TAB>TYPE<TAB>data", as dig's answer section.
def Dns.Record.show(r: M.Record) -> String:
  R.record_text(r)

# A question for name and type, class IN.
def Dns.question(name: M.Name(), rtype: M.RType) -> M.Question:
  M.Question{name, rtype, M.CIN{}}

def Dns.Question.name(q: M.Question) -> M.Name():
  match q:
    case M.Question{n, t, c}:
      n

def Dns.Question.rtype(q: M.Question) -> M.RType:
  match q:
    case M.Question{n, t, c}:
      t

def Dns.Question.rclass(q: M.Question) -> M.RClass:
  match q:
    case M.Question{n, t, c}:
      c

def Dns.header(id: Nat, qr: Bool, opcode: Nat, aa: Bool, tc: Bool, rd: Bool, ra: Bool, ad: Bool, cd: Bool,
  rcode: Nat) -> M.Header:
  M.Header{id, qr, opcode, aa, tc, rd, ra, ad, cd, rcode}

def Dns.Header.id(h: M.Header) -> Nat:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      id

# QR: a response.
def Dns.Header.qr(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      qr

def Dns.Header.opcode(h: M.Header) -> Nat:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      op

# AA: authoritative.
def Dns.Header.aa(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      aa

# TC: truncated.
def Dns.Header.tc(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      tc

def Dns.Header.rd(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      rd

def Dns.Header.ra(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      ra

# AD: the server says it validated (DNSSEC); reported, not trusted.
def Dns.Header.ad(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      ad

def Dns.Header.cd(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      cd

# 0 NOERROR, 1 FORMERR, 2 SERVFAIL, 3 NXDOMAIN, 4 NOTIMP, 5 REFUSED.
def Dns.Header.rcode(h: M.Header) -> Nat:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      rc

# "NOERROR", "NXDOMAIN", ..., "RCODE9".
def Dns.rcode_name(rc: Nat) -> String:
  R.rcode_name(rc)

def Dns.message(h: M.Header, questions: List<&2, M.Question>, answers: List<&2, M.Record>,
  authority: List<&2, M.Record>, additional: List<&2, M.Record>) -> M.Message:
  M.Message{h, questions, answers, authority, additional}

def Dns.Message.header(m: M.Message) -> M.Header:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      h

def Dns.Message.questions(m: M.Message) -> List<&2, M.Question>:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      qs

def Dns.Message.answers(m: M.Message) -> List<&2, M.Record>:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      an

def Dns.Message.authority(m: M.Message) -> List<&2, M.Record>:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      ns

def Dns.Message.additional(m: M.Message) -> List<&2, M.Record>:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      ar

def Dns.Message.id(m: M.Message) -> Nat:
  Dns.Header.id(Dns.Message.header(m))

def Dns.Message.rcode(m: M.Message) -> Nat:
  A.rcode(m)

def Dns.Message.truncated(m: M.Message) -> Bool:
  A.truncated(m)

# The codec
# ---------

# The message's bytes (names uncompressed), if it is valid (every name ok,
# numbers in range, data matching types, at most 65535 bytes); else None.
def Dns.encode.pick(ok: Bool, m: M.Message) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{E.message(m)}
    case False{}:
      None{}

def Dns.encode(+m: M.Message) -> Maybe<&2, List<&2, U32>>:
  Dns.encode.pick(E.message_ok(m), m)

# Whether Dns.encode accepts the message.
def Dns.encode_ok(m: M.Message) -> Bool:
  E.message_ok(m)

# A whole message (compression pointers followed, loop-safe; trailing bytes
# are an error; unknown types kept raw).
def Dns.decode(xs: List<&2, U32>) -> Result<&2, &2, M.DecodeError, M.Message>:
  D.message(xs)

def Dns.DecodeError.show(e: M.DecodeError) -> String:
  R.decode_error_show(e)

# A standard query: RD = 1, one question (class IN), and an EDNS0 OPT record
# advertising 4096 bytes. id <= 65535; the name must be ok.
def Dns.query(id: Nat, name: M.Name(), rtype: M.RType) -> List<&2, U32>:
  E.query(id, name, rtype)

# The same without the OPT record.
def Dns.query_plain(id: Nat, name: M.Name(), rtype: M.RType) -> List<&2, U32>:
  E.query_plain(id, name, rtype)

# m answers the query (id, q): QR = 1, opcode 0, the id, exactly the
# question (the name case-insensitively). The rcode is not judged.
def Dns.accept(id: Nat, q: M.Question, m: M.Message) -> Bool:
  A.accept(id, q, m)

# The records of rtype for name in m's answer section, through its CNAMEs.
def Dns.answer(name: M.Name(), rtype: M.RType, m: M.Message) -> M.Answer:
  A.addresses(name, rtype, m)

# The answer's records (none for an alias or nothing).
def Dns.Answer.records(a: M.Answer) -> List<&2, M.Record>:
  match a:
    case M.Found{n, rs}:
      rs
    case _:
      Nil{}

# The name the chain ended at, when it found records.
def Dns.Answer.name(a: M.Answer) -> Maybe<&2, M.Name()>:
  match a:
    case M.Found{n, rs}:
      Some{n}
    case _:
      None{}

# The CNAME target to re-query, when the chain left the answer section.
def Dns.Answer.alias(a: M.Answer) -> Maybe<&2, M.Name()>:
  match a:
    case M.Alias{t}:
      Some{t}
    case _:
      None{}

# The TCP length prefix and the message (len <= 65535).
def Dns.frame(xs: List<&2, U32>) -> List<&2, U32>:
  F.frame(xs)

def Dns.unframe.of(r: Result<&2, &2, F.FrameError, F.Framed>) -> Maybe<&2, List<&2, U32>>:
  match r:
    case Done{fr}:
      match fr:
        case F.Framed{m, rest}:
          Some{m}
    case Fail{e}:
      None{}

# The message of the first frame in xs, if xs holds a whole one.
def Dns.unframe(xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Dns.unframe.of(F.read(65535n, xs))

# One query over TCP to server:port (an IPv4 address), its response's
# bytes. The connect, send and each read must each finish within
# timeout_ms (0: no limit); see Dns.with_timeout for what a timeout leaves.
def Dns.exchange(server: String, port: Nat, query: List<&2, U32>, timeout_ms: Nat) ->
  IO(Result<&2, &2, M.Error, List<&2, U32>>):
  X.query(server, port, query, 65535n, timeout_ms)

# Configuration
# -------------

# /etc/resolv.conf (nameservers, search / domain, options ndots, timeout,
# attempts) and /etc/hosts. A missing file reads as empty; no nameserver
# means 127.0.0.1. Fails (Config) only when a file exists but cannot be read.
def Dns.system() -> IO(Result<&2, &2, M.Error, R.Config>):
  R.system()

# The same from other paths.
def Dns.load(resolv_path: String, hosts_path: String) -> IO(Result<&2, &2, M.Error, R.Config>):
  R.load(resolv_path, hosts_path)

# The config of a resolv.conf text and a hosts text.
def Dns.config(resolv_text: String, hosts_text: String) -> R.Config:
  R.from_text(resolv_text, hosts_text)

# 127.0.0.1, no search list, ndots 1, 5000 ms, 2 attempts, port 53, no hosts.
def Dns.default_config() -> R.Config:
  R.default_config()

# The nameservers (IPv4 addresses as text) to ask, in order.
def Dns.with_servers(cfg: R.Config, servers: List<&2, String>) -> R.Config:
  R.with_servers(cfg, servers)

# The nameservers' TCP port (53).
def Dns.with_port(cfg: R.Config, port: Nat) -> R.Config:
  R.with_port(cfg, port)

# Bounds each blocking step of an exchange (connect, send, each read) to ms
# milliseconds; 0: no limit. Base cannot cancel a blocked effect: the lookup
# moves on at once (to the next server, or fails with Timeout), and a socket
# the stalled step later hands back is closed, but until the peer acts or
# the OS gives up the stalled step keeps the program from ending normally
# (an explicit exit such as IO.die still ends it at once).
def Dns.with_timeout(cfg: R.Config, ms: Nat) -> R.Config:
  R.with_timeout(cfg, ms)

# How many times each server is tried per name (at least 1).
def Dns.with_attempts(cfg: R.Config, n: Nat) -> R.Config:
  R.with_attempts(cfg, n)

# The search list (suffixes, as text).
def Dns.with_search(cfg: R.Config, suffixes: List<&2, String>) -> R.Config:
  R.with_search(cfg, suffixes)

# Names with at least n dots are tried as they are first.
def Dns.with_ndots(cfg: R.Config, n: Nat) -> R.Config:
  R.with_ndots(cfg, n)

# The hosts table, from a hosts(5) text (replacing the current one).
def Dns.with_hosts(cfg: R.Config, hosts_text: String) -> R.Config:
  R.with_hosts(cfg, CF.hosts(hosts_text))

def Dns.Config.servers(cfg: R.Config) -> List<&2, String>:
  R.servers(cfg)

def Dns.Config.search(cfg: R.Config) -> List<&2, String>:
  R.search(cfg)

def Dns.Config.ndots(cfg: R.Config) -> Nat:
  R.ndots(cfg)

def Dns.Config.attempts(cfg: R.Config) -> Nat:
  R.attempts(cfg)

def Dns.Config.port(cfg: R.Config) -> Nat:
  R.port(cfg)

def Dns.Config.timeout_ms(cfg: R.Config) -> Nat:
  R.timeout_ms(cfg)

# The names a lookup of name tries, in order (the search list expansion).
def Dns.candidates(cfg: R.Config, name: String) -> List<&2, String>:
  R.candidates(cfg, name)

# Resolving
# ---------

# The records of rtype for name through the native stack: an address
# literal answers itself (A / AAAA), then the hosts table (A / AAAA), then
# each search candidate asked of each server, `attempts` times over, CNAMEs
# re-queried (at most 8). NxDomain when no candidate exists, NoData when one
# exists without the type; ServFail, Timeout, Connect, ... when servers
# failed.
def Dns.resolve(cfg: R.Config, name: String, rtype: M.RType) -> IO(Result<&2, &2, M.Error, M.Resolved>):
  R.resolve(cfg, name, rtype)

# The owner of the records (the end of the CNAME chain).
def Dns.Resolved.name(r: M.Resolved) -> M.Name():
  match r:
    case M.Resolved{n, rs}:
      n

def Dns.Resolved.records(r: M.Resolved) -> List<&2, M.Record>:
  match r:
    case M.Resolved{n, rs}:
      rs

# The IPv4 addresses of name, as dotted quads.
def Dns.lookup_ipv4(cfg: R.Config, name: String) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  R.lookup_ipv4(cfg, name)

# The IPv6 addresses of name, as RFC 5952 text.
def Dns.lookup_ipv6(cfg: R.Config, name: String) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  R.lookup_ipv6(cfg, name)

def Dns.os_lookup.of(r: Result<&1, &1, U32 & String, List<&2, String>>) -> Result<&2, &2, M.Error, List<&2, String>>:
  match r:
    case Fail{(code, message)}:
      Fail{M.Os{code, message}}
    case Done{ips}:
      Done{ips}

# The OS resolver (getaddrinfo): family 0 (IPv4 and IPv6), 4 or 6; distinct
# addresses as text, at most 32. Fails with Os{errno, text}: 2 (ENOENT) for
# a name with no address of the family, 22 (EINVAL) for a bad family, an
# empty name, or a numeric host that is not a canonical address ("127.1").
# No timeout of its own (the resolver's settings bound it); on the JS lane
# it blocks the event loop while it runs.
def Dns.os_lookup(host: String, family: U32) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  IO.bind(Result<&1, &1, U32 & String, List<&2, String>>, Result<&2, &2, M.Error, List<&2, String>>,
    O.Os.lookup(host, family), r => IO.pure(Result<&2, &2, M.Error, List<&2, String>>, Dns.os_lookup.of(r)))

# Errors
# ------
# A Dns.Error's constructors live in src/types.bend, which a consumer cannot
# name, so these tags say which error it is:
#
#   match P.Dns.Error.kind(e):
#     case P.NxDomain{}: ...
#     case P.Timeout{}: ...
#     case _: ...
#
#   BadName    the name's text is invalid (see Dns.Error.name_error)
#   NxDomain   the name does not exist (no search candidate does)
#   NoData     the name exists with no record of the type
#   ServFail   every server failed or refused (rcode: Dns.Error.rcode)
#   Malformed  a response could not be decoded
#   Mismatch   a response did not answer the query (id or question)
#   NoServers  no nameserver to ask
#   Connect    the TCP connect failed (code: errno, e.g. 111 refused)
#   Io         a send or read failed (code: errno; 90 a size limit)
#   Timeout    a step passed the config's timeout
#   Os         the OS resolver failed (code: errno for its EAI_* code)
#   Config     the configuration could not be read or used

type ErrorKind is Data:
  BadName{}
  NxDomain{}
  NoData{}
  ServFail{}
  Malformed{}
  Mismatch{}
  NoServers{}
  Connect{}
  Io{}
  Timeout{}
  Os{}
  Config{}

def Dns.ErrorKind() -> Data:
  ErrorKind

def Dns.Error.kind(e: M.Error) -> ErrorKind:
  match e:
    case M.BadName{n}:
      BadName{}
    case M.NxDomain{n}:
      NxDomain{}
    case M.NoData{n}:
      NoData{}
    case M.ServFail{rc}:
      ServFail{}
    case M.Malformed{d}:
      Malformed{}
    case M.Mismatch{}:
      Mismatch{}
    case M.NoServers{}:
      NoServers{}
    case M.Connect{c, m}:
      Connect{}
    case M.Io{c, m}:
      Io{}
    case M.Timeout{}:
      Timeout{}
    case M.Os{c, m}:
      Os{}
    case M.Config{m}:
      Config{}

# One line saying why a lookup failed.
def Dns.Error.show(e: M.Error) -> String:
  R.error_show(e)

# The errno of a Connect, Io or Os error.
def Dns.Error.code(e: M.Error) -> Maybe<&2, U32>:
  match e:
    case M.Connect{c, m}:
      Some{c}
    case M.Io{c, m}:
      Some{c}
    case M.Os{c, m}:
      Some{c}
    case _:
      None{}

# The rcode of a ServFail.
def Dns.Error.rcode(e: M.Error) -> Maybe<&2, Nat>:
  match e:
    case M.ServFail{rc}:
      Some{rc}
    case _:
      None{}

# The name of an NxDomain or NoData.
def Dns.Error.name(e: M.Error) -> Maybe<&2, String>:
  match e:
    case M.NxDomain{n}:
      Some{n}
    case M.NoData{n}:
      Some{n}
    case _:
      None{}

def Dns.Error.name_error(e: M.Error) -> Maybe<&2, M.NameError>:
  match e:
    case M.BadName{n}:
      Some{n}
    case _:
      None{}

def Dns.Error.decode_error(e: M.Error) -> Maybe<&2, M.DecodeError>:
  match e:
    case M.Malformed{d}:
      Some{d}
    case _:
      None{}
