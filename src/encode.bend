import Base
import ./bytes.bend as B
import ./types.bend as M
import ./wire.bend as W
import ./name.bend as NM

# Message encoding (RFC 1035 4.1): the bytes the client writes.
#
#   message(m)   the 12-byte header (id; the flags packed from the Header
#                fields, Z = 0; the four section counts), then the questions,
#                answers, authority and additional records. Names are written
#                uncompressed (NM.wire_onto). RDATA follows the RData
#                constructor (not the record's type: message_ok makes them
#                agree), and RDLENGTH is its computed length:
#                  RIpv4{a, b, c, d}   4 bytes
#                  RIpv6{groups}       each group as a u16 (16 bytes for 8)
#                  RName{n}            the name (NS, CNAME, PTR)
#                  RMx{p, n}           u16 preference, the name
#                  RTxt{strings}       each string as a u8 length and its bytes
#                  RSoa{...}           mname, rname, five u32s
#                  RSrv{pr, w, po, t}  three u16s, the target name
#                  RRaw{bytes}         the bytes as they are (OPT, unknown types)
#   message_ok(m)  every number in range, every name NM.ok, the types and the
#                RDATA agree, every count and RDLENGTH <= 65535, and the whole
#                message <= 65535 bytes; see "Validity" below for each rule.
#   query(id, name, qtype)
#                message(query_message(id, name, qtype)): opcode QUERY, RD = 1
#                (every other flag 0, rcode 0), one question {name, qtype, IN},
#                no answers or authority, and in the additional section one
#                EDNS0 OPT record (RFC 6891): owner the root, type OPT (41),
#                class 4096 (the UDP payload size advertised; harmless over
#                TCP), TTL 0 (extended rcode 0, version 0, DO = 0), no options
#                (RDATA empty). These are the 11 bytes 00 00 29 10 00 00 00 00
#                00 00 00 after the question.
#   query_plain(id, name, qtype)
#                the same without the OPT record (ARCOUNT 0).
#
# The laws this file serves (the decoder is the other half):
#   message_roundtrip: message_ok(m) => D.message(message(m)) == Done{m}
#   query: NM.ok(name) and type_ok(qtype) and id <= 65535
#          => message_ok(query_message(id, name, qtype)) (so query roundtrips)
#
# Codes. type_code / class_code give the wire number of a type or class;
# type_known(c) is the one table from codes back to the known types (decode
# uses it), so TOther{c} is valid only when type_known(c) == None (its code is
# not one of the eleven), and COther{c} only when c != 1. Each value then has
# exactly one wire form and one decoded form.
#
# NOTE (loops and specs): every def that walks a caller-sized list (the
# questions, the records, the IPv6 groups, the TXT strings, a byte list) is a
# loop (direct tail calls only), because the JS lane's stack overflows near
# 20-40k nested calls. The plain structural recursion each loop computes is
# `<name>.spec`, for the proofs only. The equations (each by induction on the
# list with the accumulator generalized; rev is B.rev):
#   count.go(A, xs, k) == Nat.add(List.length(&2, A, xs), k)
#   rev(U32, rev(U32, xs, acc), ys) == rev(U32, acc, List.append(xs, ys))
#       (so app(xs, ys) == List.append(xs, ys))
#   groups.go(rev(Nat, gs, acc), ys) == groups.go(acc, groups.spec(gs, ys))
#   txt.go(rev(S, ss, acc), ys) == txt.go(acc, txt.spec(ss, ys))
#   questions.go(rev(Q, qs, acc), ys) == questions.go(acc, questions.spec(qs, ys))
#   records.go(rev(R, rs, acc), ys) == records.go(acc, records.spec(rs, ys))
#   groups_ok.go(gs, ok) == Bool.and(ok, groups_ok.spec(gs))   (same for
#       strings_ok, questions_ok, records_ok)
# and so, at acc = Nil{} / ok = True{}: groups_onto == groups.spec,
# txt_onto == txt.spec, questions_onto == questions.spec, records_onto ==
# records.spec, and each *_ok == *_ok.spec. NM.wire_onto(n, ys) ==
# List.append(NM.wire.spec(n), ys) is name.bend's equation.

# Lists
# -----

# k plus the number of items in xs (a loop).
def count.go(-A: Data, xs: List<&2, A>, k: Nat) -> Nat:
  match xs:
    case Nil{}:
      k
    case Con{h, t}:
      count.go(A, t, 1n+k)

# The number of items in xs: count(A, xs) == List.length(&2, A, xs).
def count(-A: Data, xs: List<&2, A>) -> Nat:
  count.go(A, xs, 0n)

# xs ++ ys (two loops).
def app(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  B.rev(U32, B.rev(U32, xs, Nil{}), ys)

# One byte, then ys; n <= 255.
def u8_onto(n: Nat, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, W.put_u8(n), ys)

# Codes
# -----

def type_code(t: M.RType) -> Nat:
  match t:
    case M.TA{}:
      1n
    case M.TNS{}:
      2n
    case M.TCNAME{}:
      5n
    case M.TSOA{}:
      6n
    case M.TPTR{}:
      12n
    case M.TMX{}:
      15n
    case M.TTXT{}:
      16n
    case M.TAAAA{}:
      28n
    case M.TSRV{}:
      33n
    case M.TOPT{}:
      41n
    case M.TANY{}:
      255n
    case M.TOther{c}:
      c

def known.pick(hit: Bool, t: M.RType, rest: Maybe<&2, M.RType>) -> Maybe<&2, M.RType>:
  match hit:
    case True{}:
      Some{t}
    case False{}:
      rest

# The known type with code c, if any (the inverse of type_code on them).
def type_known(+c: Nat) -> Maybe<&2, M.RType>:
  known.pick(Nat.is_eq(c, 1n), M.TA{},
  known.pick(Nat.is_eq(c, 2n), M.TNS{},
  known.pick(Nat.is_eq(c, 5n), M.TCNAME{},
  known.pick(Nat.is_eq(c, 6n), M.TSOA{},
  known.pick(Nat.is_eq(c, 12n), M.TPTR{},
  known.pick(Nat.is_eq(c, 15n), M.TMX{},
  known.pick(Nat.is_eq(c, 16n), M.TTXT{},
  known.pick(Nat.is_eq(c, 28n), M.TAAAA{},
  known.pick(Nat.is_eq(c, 33n), M.TSRV{},
  known.pick(Nat.is_eq(c, 41n), M.TOPT{},
  known.pick(Nat.is_eq(c, 255n), M.TANY{},
  None{})))))))))))

def class_code(c: M.RClass) -> Nat:
  match c:
    case M.CIN{}:
      1n
    case M.COther{k}:
      k

# Header
# ------

def bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# The first flags byte: QR (128), opcode (8 each, 0..15), AA (4), TC (2), RD (1).
def flags_hi(qr: Bool, opcode: Nat, aa: Bool, tc: Bool, rd: Bool) -> Nat:
  Nat.add(Nat.mul(bit(qr), 128n), Nat.add(Nat.mul(opcode, 8n),
    Nat.add(Nat.mul(bit(aa), 4n), Nat.add(Nat.mul(bit(tc), 2n), bit(rd)))))

# The second flags byte: RA (128), Z (64, always 0), AD (32), CD (16), rcode (0..15).
def flags_lo(ra: Bool, ad: Bool, cd: Bool, rcode: Nat) -> Nat:
  Nat.add(Nat.mul(bit(ra), 128n), Nat.add(Nat.mul(bit(ad), 32n),
    Nat.add(Nat.mul(bit(cd), 16n), rcode)))

# The 12 header bytes (with the given counts), then ys.
def header_onto(h: M.Header, qd: Nat, an: Nat, ns: Nat, ar: Nat, ys: List<&2, U32>) -> List<&2, U32>:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      W.put_u16_onto(id, u8_onto(flags_hi(qr, op, aa, tc, rd), u8_onto(flags_lo(ra, ad, cd, rc),
        W.put_u16_onto(qd, W.put_u16_onto(an, W.put_u16_onto(ns, W.put_u16_onto(ar, ys)))))))

# RDATA
# -----

def groups.spec(gs: List<&2, Nat>, ys: List<&2, U32>) -> List<&2, U32>:
  match gs:
    case Nil{}:
      ys
    case Con{g, t}:
      W.put_u16_onto(g, groups.spec(t, ys))

# The groups of rgs (reversed), each as a u16, in front of ys (a loop).
def groups.go(rgs: List<&2, Nat>, ys: List<&2, U32>) -> List<&2, U32>:
  match rgs:
    case Nil{}:
      ys
    case Con{g, t}:
      groups.go(t, W.put_u16_onto(g, ys))

def groups_onto(gs: List<&2, Nat>, ys: List<&2, U32>) -> List<&2, U32>:
  groups.go(B.rev(Nat, gs, Nil{}), ys)

# One character-string: its length byte, its bytes, then ys.
def string_onto(+s: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  u8_onto(count(U32, s), app(s, ys))

def txt.spec(ss: List<&2, List<&2, U32>>, ys: List<&2, U32>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      ys
    case Con{s, t}:
      string_onto(s, txt.spec(t, ys))

def txt.go(rss: List<&2, List<&2, U32>>, ys: List<&2, U32>) -> List<&2, U32>:
  match rss:
    case Nil{}:
      ys
    case Con{s, t}:
      txt.go(t, string_onto(s, ys))

def txt_onto(ss: List<&2, List<&2, U32>>, ys: List<&2, U32>) -> List<&2, U32>:
  txt.go(B.rev(List<&2, U32>, ss, Nil{}), ys)

# The RDATA of d.
def rdata(d: M.RData) -> List<&2, U32>:
  match d:
    case M.RIpv4{a, b, c, x}:
      u8_onto(a, u8_onto(b, u8_onto(c, W.put_u8(x))))
    case M.RIpv6{gs}:
      groups_onto(gs, Nil{})
    case M.RName{n}:
      NM.wire(n)
    case M.RMx{p, n}:
      W.put_u16_onto(p, NM.wire(n))
    case M.RTxt{ss}:
      txt_onto(ss, Nil{})
    case M.RSoa{mn, rn, se, rf, rt, ex, mi}:
      NM.wire_onto(mn, NM.wire_onto(rn, W.put_u32_onto(se, W.put_u32_onto(rf,
        W.put_u32_onto(rt, W.put_u32_onto(ex, W.put_u32(mi)))))))
    case M.RSrv{pr, w, po, tg}:
      W.put_u16_onto(pr, W.put_u16_onto(w, W.put_u16_onto(po, NM.wire(tg))))
    case M.RRaw{bs}:
      bs

# Questions and records
# ---------------------

def question_onto(q: M.Question, ys: List<&2, U32>) -> List<&2, U32>:
  match q:
    case M.Question{n, t, c}:
      NM.wire_onto(n, W.put_u16_onto(type_code(t), W.put_u16_onto(class_code(c), ys)))

def questions.spec(qs: List<&2, M.Question>, ys: List<&2, U32>) -> List<&2, U32>:
  match qs:
    case Nil{}:
      ys
    case Con{q, t}:
      question_onto(q, questions.spec(t, ys))

def questions.go(rqs: List<&2, M.Question>, ys: List<&2, U32>) -> List<&2, U32>:
  match rqs:
    case Nil{}:
      ys
    case Con{q, t}:
      questions.go(t, question_onto(q, ys))

def questions_onto(qs: List<&2, M.Question>, ys: List<&2, U32>) -> List<&2, U32>:
  questions.go(B.rev(M.Question, qs, Nil{}), ys)

# Owner, type, class, TTL, RDLENGTH, RDATA, then ys.
def record_with(n: M.Name(), t: M.RType, c: M.RClass, ttl: Nat, +rd: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  NM.wire_onto(n, W.put_u16_onto(type_code(t), W.put_u16_onto(class_code(c),
    W.put_u32_onto(ttl, W.put_u16_onto(count(U32, rd), app(rd, ys))))))

def record_onto(r: M.Record, ys: List<&2, U32>) -> List<&2, U32>:
  match r:
    case M.Record{n, t, c, ttl, d}:
      record_with(n, t, c, ttl, rdata(d), ys)

def records.spec(rs: List<&2, M.Record>, ys: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      ys
    case Con{r, t}:
      record_onto(r, records.spec(t, ys))

def records.go(rrs: List<&2, M.Record>, ys: List<&2, U32>) -> List<&2, U32>:
  match rrs:
    case Nil{}:
      ys
    case Con{r, t}:
      records.go(t, record_onto(r, ys))

def records_onto(rs: List<&2, M.Record>, ys: List<&2, U32>) -> List<&2, U32>:
  records.go(B.rev(M.Record, rs, Nil{}), ys)

# Messages
# --------

# The message's bytes (no compression).
def message(m: M.Message) -> List<&2, U32>:
  match m:
    case M.Message{h, +qs, +an, +ns, +ar}:
      header_onto(h, count(M.Question, qs), count(M.Record, an), count(M.Record, ns), count(M.Record, ar),
        questions_onto(qs, records_onto(an, records_onto(ns, records_onto(ar, Nil{})))))

# The EDNS0 OPT record a query carries: root owner, payload 4096, TTL 0, no options.
def opt() -> M.Record:
  M.Record{Nil{}, M.TOPT{}, M.COther{4096n}, 0n, M.RRaw{Nil{}}}

# A query's header: opcode QUERY, RD = 1, every other flag 0, rcode 0.
def query_header(id: Nat) -> M.Header:
  M.Header{id, False{}, 0n, False{}, False{}, True{}, False{}, False{}, False{}, 0n}

def query_message(id: Nat, name: M.Name(), qtype: M.RType) -> M.Message:
  M.Message{query_header(id), [M.Question{name, qtype, M.CIN{}}], Nil{}, Nil{}, [opt()]}

def query_plain_message(id: Nat, name: M.Name(), qtype: M.RType) -> M.Message:
  M.Message{query_header(id), [M.Question{name, qtype, M.CIN{}}], Nil{}, Nil{}, Nil{}}

# A query for (name, qtype) with id: see the top of the file.
def query(id: Nat, name: M.Name(), qtype: M.RType) -> List<&2, U32>:
  message(query_message(id, name, qtype))

# The same query without the EDNS0 OPT record.
def query_plain(id: Nat, name: M.Name(), qtype: M.RType) -> List<&2, U32>:
  message(query_plain_message(id, name, qtype))

# Validity
# --------
#
# What message_ok(m) asks, and why (D.message(message(m)) == Done{m} needs
# each of these; the last conjunct is for the transport only):
#   header: id <= 65535; opcode <= 15; rcode <= 15 (each a field of fixed width)
#   counts: each section has at most 65535 entries (a u16 count)
#   names: NM.ok (labels 1..63 bytes of byte values, <= 255 wire bytes): the
#     decoder refuses anything else
#   types: TOther{c} has c <= 65535 and type_known(c) == None (else it would
#     decode as the known type); classes: COther{c} has c <= 65535 and c != 1
#   ttl: u32_ok (fits 32 bits)
#   RDATA agrees with the type: TA / RIpv4 (octets <= 255); TAAAA / RIpv6
#     (exactly 8 groups, each <= 65535); TNS, TCNAME, TPTR / RName; TMX / RMx
#     (preference <= 65535); TTXT / RTxt (each string at most 255 bytes, all
#     bytes; empty strings and an empty list are allowed and decode back);
#     TSOA / RSoa (five u32s); TSRV / RSrv (three u16s); TOPT, TANY, TOther /
#     RRaw (all bytes). Anything else (RRaw for TA, RIpv4 for TMX, ...) is
#     refused: the decoder reads RDATA by type.
#   RDLENGTH: each record's RDATA at most 65535 bytes
#   total: the whole message at most 65535 bytes (what TCP framing carries;
#     the decoder itself does not need it)

def u8_ok(n: Nat) -> Bool:
  Nat.is_le(n, 255n)

def u16_ok(n: Nat) -> Bool:
  Nat.is_le(n, 65535n)

# n < 65536 * 65536, stated so the checker never builds 2^32: the high half
# (what W.put_u32 writes first) fits 16 bits.
def u32_ok(n: Nat) -> Bool:
  Nat.is_le(Nat.div(n, 65536n), 65535n)

def free.of(k: Maybe<&2, M.RType>) -> Bool:
  match k:
    case Some{t}:
      False{}
    case None{}:
      True{}

# c is not the code of a known type.
def type_free(+c: Nat) -> Bool:
  free.of(type_known(c))

def type_ok(t: M.RType) -> Bool:
  match t:
    case M.TOther{+c}:
      u16_ok(c) && type_free(c)
    case _:
      True{}

def class_ok(c: M.RClass) -> Bool:
  match c:
    case M.COther{+k}:
      u16_ok(k) && Bool.not(Nat.is_eq(k, 1n))
    case M.CIN{}:
      True{}

def header_ok(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      u16_ok(id) && Nat.is_le(op, 15n) && Nat.is_le(rc, 15n)

def groups_ok.spec(gs: List<&2, Nat>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{g, t}:
      u16_ok(g) && groups_ok.spec(t)

def groups_ok.go(gs: List<&2, Nat>, ok: Bool) -> Bool:
  match gs:
    case Nil{}:
      ok
    case Con{g, t}:
      groups_ok.go(t, ok && u16_ok(g))

# Exactly 8 groups, each <= 65535.
def groups_ok(+gs: List<&2, Nat>) -> Bool:
  Nat.is_eq(count(Nat, gs), 8n) && groups_ok.go(gs, True{})

# A character-string: at most 255 bytes, all bytes.
def string_ok(+s: List<&2, U32>) -> Bool:
  u8_ok(count(U32, s)) && B.all_bytes(s)

def strings_ok.spec(ss: List<&2, List<&2, U32>>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      string_ok(s) && strings_ok.spec(t)

def strings_ok.go(ss: List<&2, List<&2, U32>>, ok: Bool) -> Bool:
  match ss:
    case Nil{}:
      ok
    case Con{s, t}:
      strings_ok.go(t, ok && string_ok(s))

def strings_ok(ss: List<&2, List<&2, U32>>) -> Bool:
  strings_ok.go(ss, True{})

# The RDATA d is what a record of type t carries (see above).
def data_ok(t: M.RType, d: M.RData) -> Bool:
  match t d:
    case M.TA{} M.RIpv4{a, b, c, x}:
      u8_ok(a) && u8_ok(b) && u8_ok(c) && u8_ok(x)
    case M.TAAAA{} M.RIpv6{gs}:
      groups_ok(gs)
    case M.TNS{} M.RName{n}:
      NM.ok(n)
    case M.TCNAME{} M.RName{n}:
      NM.ok(n)
    case M.TPTR{} M.RName{n}:
      NM.ok(n)
    case M.TMX{} M.RMx{p, n}:
      u16_ok(p) && NM.ok(n)
    case M.TTXT{} M.RTxt{ss}:
      strings_ok(ss)
    case M.TSOA{} M.RSoa{mn, rn, se, rf, rt, ex, mi}:
      NM.ok(mn) && NM.ok(rn) && u32_ok(se) && u32_ok(rf) && u32_ok(rt) && u32_ok(ex) && u32_ok(mi)
    case M.TSRV{} M.RSrv{pr, w, po, tg}:
      u16_ok(pr) && u16_ok(w) && u16_ok(po) && NM.ok(tg)
    case M.TOPT{} M.RRaw{bs}:
      B.all_bytes(bs)
    case M.TANY{} M.RRaw{bs}:
      B.all_bytes(bs)
    case M.TOther{c} M.RRaw{bs}:
      B.all_bytes(bs)
    case _ _:
      False{}

def question_ok(q: M.Question) -> Bool:
  match q:
    case M.Question{n, t, c}:
      NM.ok(n) && type_ok(t) && class_ok(c)

def record_ok(r: M.Record) -> Bool:
  match r:
    case M.Record{n, +t, c, ttl, +d}:
      NM.ok(n) && type_ok(t) && class_ok(c) && u32_ok(ttl) && data_ok(t, d)
        && u16_ok(count(U32, rdata(d)))

def questions_ok.spec(qs: List<&2, M.Question>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{q, t}:
      question_ok(q) && questions_ok.spec(t)

def questions_ok.go(qs: List<&2, M.Question>, ok: Bool) -> Bool:
  match qs:
    case Nil{}:
      ok
    case Con{q, t}:
      questions_ok.go(t, ok && question_ok(q))

def questions_ok(qs: List<&2, M.Question>) -> Bool:
  questions_ok.go(qs, True{})

def records_ok.spec(rs: List<&2, M.Record>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      record_ok(r) && records_ok.spec(t)

def records_ok.go(rs: List<&2, M.Record>, ok: Bool) -> Bool:
  match rs:
    case Nil{}:
      ok
    case Con{r, t}:
      records_ok.go(t, ok && record_ok(r))

def records_ok(rs: List<&2, M.Record>) -> Bool:
  records_ok.go(rs, True{})

# The section is valid and its count fits a u16.
def section_ok(+rs: List<&2, M.Record>) -> Bool:
  u16_ok(count(M.Record, rs)) && records_ok(rs)

# m can be encoded and decodes back to itself (see above).
def message_ok(+m: M.Message) -> Bool:
  match m:
    case M.Message{h, +qs, an, ns, ar}:
      header_ok(h) && u16_ok(count(M.Question, qs)) && questions_ok(qs)
        && section_ok(an) && section_ok(ns) && section_ok(ar)
        && u16_ok(count(U32, message(m)))
