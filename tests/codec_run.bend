import Base
import ../src/bytes.bend as B
import ../src/types.bend as M
import ../src/wire.bend as W
import ../src/name.bend as NM
import ../src/encode.bend as E
import ../src/decode.bend as D
import ../src/answer.bend as A
import ./fixtures.bend as FX

# Runtime tests for encode, decode and answer, on both lanes:
#   bend tests/codec_run.bend
#   bend tests/codec_run.bend -o "$BEND_OUT/codec_run" && "$BEND_OUT/codec_run"
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL: n".
# These cover what the checker cannot evaluate: every real response
# (tests/fixtures.bend, compressed) including the ones with large numbers,
# full-range numbers, every truncation and many corruptions of each real
# response, 65535-byte messages and garbage, the pointer budget, and
# caller-built lists of 70k+ items (which must not overflow the JS lane).
#
# Two messages are compared by their encodings (E.message): for valid
# messages E.message is injective (decode inverts it).

# Helpers (all loops)
# -------------------

def bytes_eq.go(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      bytes_eq.go(xs, ys, ok && U32.is_eq(x, y))
    case _ _:
      False{}

def bytes_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  bytes_eq.go(a, b, True{})

def len(xs: List<&2, U32>) -> Nat:
  NM.len(xs)

# xs ++ ys, stack-safe.
def app(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  B.rev(U32, B.rev(U32, xs, Nil{}), ys)

def fill.go(n: Nat, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      fill.go(p, b, b <> acc)

def fill(n: Nat, b: U32) -> List<&2, U32>:
  fill.go(n, b, Nil{})

def u16(n: Nat) -> List<&2, U32>:
  W.put_u16(n)

# A pointer to offset t.
def ptr(t: Nat) -> List<&2, U32>:
  W.put_u16(Nat.add(49152n, t))

# The first k cells of xs.
def prefix.go(k: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      B.rev(U32, acc, Nil{})
    case 1n+p:
      match xs:
        case Nil{}:
          B.rev(U32, acc, Nil{})
        case Con{h, t}:
          prefix.go(p, t, h <> acc)

def prefix(k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  prefix.go(k, xs, Nil{})

# xs with cell i replaced by v.
def poke.go(i: Nat, xs: List<&2, U32>, +v: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match i:
    case 0n:
      match xs:
        case Nil{}:
          B.rev(U32, acc, Nil{})
        case Con{h, t}:
          B.rev(U32, acc, v <> t)
    case 1n+p:
      match xs:
        case Nil{}:
          B.rev(U32, acc, Nil{})
        case Con{h, t}:
          poke.go(p, t, v, h <> acc)

def poke(i: Nat, xs: List<&2, U32>, v: U32) -> List<&2, U32>:
  poke.go(i, xs, v, Nil{})

# n pseudo-random bytes (the ZX81 generator: x -> (75 x + 74) mod 65537).
def noise.go(n: Nat, +x: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +y = Nat.mod(Nat.add(Nat.mul(x, 75n), 74n), 65537n)
      noise.go(p, y, U32.from_nat(Nat.mod(y, 256n)) <> acc)

def noise(n: Nat, seed: Nat) -> List<&2, U32>:
  noise.go(n, seed, Nil{})

# Result checks
# -------------

def DR() -> Type:
  Result<&2, &2, M.DecodeError, M.Message>

def err_tag(e: M.DecodeError) -> Nat:
  match e:
    case M.Short{}:
      1n
    case M.BadPointer{}:
      2n
    case M.BadLabel{}:
      3n
    case M.BadRdata{}:
      4n
    case M.Trailing{}:
      5n

def SHORT() -> Nat:
  1n

def BAD_POINTER() -> Nat:
  2n

def BAD_LABEL() -> Nat:
  3n

def BAD_RDATA() -> Nat:
  4n

def TRAILING() -> Nat:
  5n

def is_err(r: Result<&2, &2, M.DecodeError, M.Message>, tag: Nat) -> Bool:
  match r:
    case Done{m}:
      False{}
    case Fail{e}:
      Nat.is_eq(err_tag(e), tag)

def is_done(r: Result<&2, &2, M.DecodeError, M.Message>) -> Bool:
  match r:
    case Done{m}:
      True{}
    case Fail{e}:
      False{}

# r is Done{x} and x encodes as expected does.
def is_msg(r: Result<&2, &2, M.DecodeError, M.Message>, expected: M.Message) -> Bool:
  match r:
    case Done{m}:
      bytes_eq(E.message(m), E.message(expected))
    case Fail{e}:
      False{}

# m is valid and decodes from its encoding to itself.
def roundtrip(+m: M.Message) -> Bool:
  E.message_ok(m) && is_msg(D.message(E.message(m)), m)

# The fixture decodes to its message, which roundtrips.
def real(xs: List<&2, U32>, +m: M.Message) -> Bool:
  is_msg(D.message(xs), m) && roundtrip(m)

# Every proper prefix of xs (lengths k-1 down to 0) fails with Short.
def cuts.go(k: Nat, +xs: List<&2, U32>, ok: Bool) -> Bool:
  match k:
    case 0n:
      ok
    case 1n+(+p):
      cuts.go(p, xs, ok && is_err(D.message(prefix(p, xs)), SHORT()))

def cuts(+xs: List<&2, U32>) -> Bool:
  cuts.go(len(xs), xs, True{})

# Every cell of xs replaced by v in turn: the decoder returns (and, so the
# result is used, n counts the successes).
def pokes.go(i: Nat, +xs: List<&2, U32>, +v: U32, n: Nat) -> Nat:
  match i:
    case 0n:
      n
    case 1n+(+p):
      pokes.go(p, xs, v, Nat.add(n, E.bit(is_done(D.message(poke(p, xs, v))))))

def pokes(+xs: List<&2, U32>) -> Bool:
  +a = pokes.go(len(xs), xs, 255, 0n)
  +b = pokes.go(len(xs), xs, 0, 0n)
  +c = pokes.go(len(xs), xs, 192, 0n)
  Nat.is_le(Nat.add(a, Nat.add(b, c)), Nat.mul(3n, len(xs)))

def sections(r: Result<&2, &2, M.DecodeError, M.Message>) -> List<&2, Nat>:
  match r:
    case Done{m}:
      match m:
        case M.Message{h, qs, an, ns, ar}:
          [E.count(M.Question, qs), E.count(M.Record, an), E.count(M.Record, ns), E.count(M.Record, ar)]
    case Fail{e}:
      []

def nats_eq.go(a: List<&2, Nat>, b: List<&2, Nat>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      nats_eq.go(xs, ys, ok && Nat.is_eq(x, y))
    case _ _:
      False{}

def counts_are(r: Result<&2, &2, M.DecodeError, M.Message>, ks: List<&2, Nat>) -> Bool:
  nats_eq.go(sections(r), ks, True{})

def decoded(r: Result<&2, &2, M.DecodeError, M.Message>) -> M.Message:
  match r:
    case Done{m}:
      m
    case Fail{e}:
      M.Message{E.query_header(0n), Nil{}, Nil{}, Nil{}, Nil{}}

def records_bytes(rs: List<&2, M.Record>) -> List<&2, U32>:
  E.records_onto(rs, Nil{})

# The answer is Found{n, rs} with n and rs encoding as expected.
def found_is(a: M.Answer, n: M.Name(), rs: List<&2, M.Record>) -> Bool:
  match a:
    case M.Found{x, ys}:
      bytes_eq(NM.wire(x), NM.wire(n)) && bytes_eq(records_bytes(ys), records_bytes(rs))
    case _:
      False{}

def found_count(a: M.Answer, k: Nat) -> Bool:
  match a:
    case M.Found{x, ys}:
      Nat.is_eq(E.count(M.Record, ys), k)
    case _:
      False{}

def is_alias(a: M.Answer, n: M.Name()) -> Bool:
  match a:
    case M.Alias{x}:
      bytes_eq(NM.wire(x), NM.wire(n))
    case _:
      False{}

def is_nothing(a: M.Answer) -> Bool:
  match a:
    case M.Nothing{}:
      True{}
    case _:
      False{}

# Fixtures
# --------

def ex() -> M.Name():
  [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]

def github() -> M.Name():
  [[103, 105, 116, 104, 117, 98], [99, 111, 109]]

def www_github() -> M.Name():
  [[119, 119, 119], [103, 105, 116, 104, 117, 98], [99, 111, 109]]

def qa(n: M.Name()) -> M.Question:
  M.Question{n, M.TA{}, M.CIN{}}

# A response header: id 0x1234, QR RD RA, and the four counts.
def hdr(qd: Nat, an: Nat, ns: Nat, ar: Nat) -> List<&2, U32>:
  app([18, 52, 129, 128], app(u16(qd), app(u16(an), app(u16(ns), u16(ar)))))

# example.com A IN, at offset 12 (17 bytes).
def q_ex() -> List<&2, U32>:
  [7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 1, 0, 1]

# n compressed A records for example.com (16 bytes each), onto acc.
def a_recs.go(n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      a_recs.go(p, app([192, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 10, 0, U32.from_nat(Nat.div(p, 256n)), U32.from_nat(Nat.mod(p, 256n))], acc))

# A response with n A records, all pointing at the question's name.
def many_a(+n: Nat) -> List<&2, U32>:
  app(hdr(1n, n, 0n, 0n), app(q_ex(), a_recs.go(n, Nil{})))

# Pointer chains. A first record (owner root, type 99) whose RDATA, at
# offset 23, is the name "a" ([1, 97, 0]) and then k pointers, each to the
# one before (the first to the name; pointer i sits at 26 + 2 i); then n
# records (type 99, no RDATA) owned by a pointer to the last pointer. Each
# owner costs k + 1 hops of the message's budget (its length).
def chain.ptrs(k: Nat, +prev: Nat, +cur: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      chain.ptrs(p, cur, Nat.add(cur, 2n), B.rev(U32, ptr(prev), acc))

def chain.owners(n: Nat, +t: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      chain.owners(p, t, app(ptr(t), app([0, 99, 0, 1, 0, 0, 0, 0, 0, 0], acc)))

# The last pointer sits at 26 + 2 (k - 1) = 24 + 2 k.
def chain(+k: Nat, +n: Nat) -> List<&2, U32>:
  app(hdr(0n, 1n+n, 0n, 0n), app([0, 0, 99, 0, 1, 0, 0, 0, 0], app(u16(Nat.add(3n, Nat.mul(2n, k))),
    app([1, 97, 0], B.rev(U32, chain.ptrs(k, 23n, 26n, Nil{}),
      chain.owners(n, Nat.add(24n, Nat.mul(2n, k)), Nil{}))))))

# A name built back to front through pointers: in a first record's RDATA, at
# offset 23, a 63-byte label and a zero (65 bytes); then s segments, each a
# 63-byte label and a pointer to the segment before (66 bytes; segment i >= 1
# starts at 88 + 66 (i - 1)); a second record is owned by a pointer to the
# last segment. Its name is s + 1 labels of 63 bytes: 3 fit (193 bytes on
# the wire), 4 do not (257).
def long.segs(s: Nat, +prev: Nat, +cur: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case 0n:
      acc
    case 1n+p:
      long.segs(p, cur, Nat.add(cur, 66n), B.rev(U32, app([63], app(fill(63n, 120), ptr(prev))), acc))

def long.last(s: Nat) -> Nat:
  match s:
    case 0n:
      23n
    case 1n+p:
      Nat.add(88n, Nat.mul(66n, p))

def long_name(+s: Nat) -> List<&2, U32>:
  +rd = app([63], app(fill(63n, 120), Con{0, B.rev(U32, long.segs(s, 23n, 88n, Nil{}), Nil{})}))
  app(hdr(0n, 2n, 0n, 0n), app([0, 0, 99, 0, 1, 0, 0, 0, 0], app(u16(len(rd)), app(rd,
    app(ptr(long.last(s)), [0, 99, 0, 1, 0, 0, 0, 0, 0, 0])))))

# Four 63-byte labels (257 bytes with the zero).
def four_labels() -> List<&2, U32>:
  +l = app([63], fill(63n, 97))
  app(l, app(l, app(l, l)))

# Built messages
# --------------

def hd(id: Nat) -> M.Header:
  M.Header{id, True{}, 0n, False{}, False{}, True{}, True{}, False{}, False{}, 0n}

def rec(n: M.Name(), t: M.RType, d: M.RData) -> M.Record:
  M.Record{n, t, M.CIN{}, 300n, d}

# Every number at the top of its range.
def max_msg() -> M.Message:
  M.Message{M.Header{65535n, True{}, 15n, True{}, True{}, True{}, True{}, True{}, True{}, 15n},
    [M.Question{ex(), M.TOther{65535n}, M.COther{65535n}}],
    [M.Record{ex(), M.TA{}, M.CIN{}, 4294967295n, M.RIpv4{255n, 255n, 255n, 255n}},
     M.Record{ex(), M.TAAAA{}, M.COther{65535n}, 2147483648n,
       M.RIpv6{[65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n]}},
     M.Record{ex(), M.TMX{}, M.CIN{}, 4294967295n, M.RMx{65535n, ex()}},
     M.Record{ex(), M.TSRV{}, M.CIN{}, 65536n, M.RSrv{65535n, 65535n, 65535n, ex()}},
     M.Record{ex(), M.TSOA{}, M.CIN{}, 0n, M.RSoa{ex(), ex(), 4294967295n, 4294967294n, 65536n, 65535n, 16777216n}},
     M.Record{ex(), M.TOther{65535n}, M.CIN{}, 1n, M.RRaw{[255, 0, 128]}}],
    Nil{}, Nil{}}

def nk(k: U32) -> M.Name():
  [[k]]

# A 255-byte name (labels of 63, 63, 63 and 61).
def max_name() -> M.Name():
  [fill(63n, 97), fill(63n, 98), fill(63n, 99), fill(61n, 100)]

def with_raw(+k: Nat) -> M.Message:
  M.Message{hd(1n), [qa(ex())], [rec(ex(), M.TOther{99n}, M.RRaw{fill(k, 7)})], Nil{}, Nil{}}

# n strings of 255 bytes.
def strings.go(n: Nat, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      acc
    case 1n+p:
      strings.go(p, fill(255n, 120) <> acc)

def questions.go(n: Nat, acc: List<&2, M.Question>) -> List<&2, M.Question>:
  match n:
    case 0n:
      acc
    case 1n+p:
      questions.go(p, qa(ex()) <> acc)

def groups.go(n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      groups.go(p, 1n <> acc)

def big_records.go(n: Nat, acc: List<&2, M.Record>) -> List<&2, M.Record>:
  match n:
    case 0n:
      acc
    case 1n+p:
      big_records.go(p, rec(ex(), M.TA{}, M.RIpv4{1n, 2n, 3n, 4n}) <> acc)

def mx_answers(+r: Result<&2, &2, M.DecodeError, M.Message>) -> Bool:
  found_count(A.addresses([[103, 109, 97, 105, 108], [99, 111, 109]], M.TMX{}, decoded(r)), 5n)

# The cases
# ---------

def cases() -> List<(String & Bool)>:
  [
    # real responses: decode (with compression) and roundtrip uncompressed
    ("real example.com A", real(FX.example_a(), FX.example_a.msg())),
    ("real example.com AAAA", real(FX.example_aaaa(), FX.example_aaaa.msg())),
    ("real gmail.com MX", real(FX.gmail_mx(), FX.gmail_mx.msg())),
    ("real www.github.com CNAME chain", real(FX.github_cname(), FX.github_cname.msg())),
    ("real NODATA with SOA", real(FX.example_nodata(), FX.example_nodata.msg())),
    ("real example.com TXT", real(FX.example_txt(), FX.example_txt.msg())),
    ("real EDNS0 OPT", real(FX.example_a_edns(), FX.example_a_edns.msg())),
    ("real NXDOMAIN with SOA", real(FX.xmpp_nx(), FX.xmpp_nx.msg())),
    ("real PTR", real(FX.google_ptr(), FX.google_ptr.msg())),
    ("real SRV", real(FX.gmail_srv(), FX.gmail_srv.msg())),
    ("real NS x8", real(FX.github_ns(), FX.github_ns.msg())),
    ("real SOA", real(FX.example_soa(), FX.example_soa.msg())),
    ("real NXDOMAIN rcode", Nat.is_eq(A.rcode(decoded(D.message(FX.xmpp_nx()))), 3n)),
    # answers on decoded responses
    ("accept example.com A", A.accept(4660n, qa(ex()), decoded(D.message(FX.example_a())))),
    ("accept wrong id", Bool.not(A.accept(4661n, qa(ex()), decoded(D.message(FX.example_a()))))),
    ("addresses example.com A", found_is(A.addresses(ex(), M.TA{}, decoded(D.message(FX.example_a()))), ex(),
      [rec(ex(), M.TA{}, M.RIpv4{104n, 20n, 23n, 154n}), rec(ex(), M.TA{}, M.RIpv4{172n, 66n, 147n, 243n})])),
    ("addresses through CNAME", found_is(A.addresses(www_github(), M.TA{}, decoded(D.message(FX.github_cname()))),
      github(), [M.Record{github(), M.TA{}, M.CIN{}, 60n, M.RIpv4{140n, 82n, 121n, 3n}}])),
    ("addresses AAAA", found_count(A.addresses(ex(), M.TAAAA{}, decoded(D.message(FX.example_aaaa()))), 2n)),
    ("addresses MX", mx_answers(D.message(FX.gmail_mx()))),
    ("addresses NODATA", is_nothing(A.addresses(ex(), M.TA{}, decoded(D.message(FX.example_nodata()))))),
    ("addresses alias", is_alias(A.addresses(www_github(), M.TAAAA{}, decoded(D.message(FX.github_cname()))), github())),
    # every truncation fails with Short
    ("cuts example.com A", cuts(FX.example_a())),
    ("cuts AAAA", cuts(FX.example_aaaa())),
    ("cuts MX", cuts(FX.gmail_mx())),
    ("cuts CNAME", cuts(FX.github_cname())),
    ("cuts NODATA", cuts(FX.example_nodata())),
    ("cuts TXT", cuts(FX.example_txt())),
    ("cuts EDNS0", cuts(FX.example_a_edns())),
    ("cuts NXDOMAIN", cuts(FX.xmpp_nx())),
    ("cuts PTR", cuts(FX.google_ptr())),
    ("cuts SRV", cuts(FX.gmail_srv())),
    ("cuts NS", cuts(FX.github_ns())),
    ("cuts SOA", cuts(FX.example_soa())),
    # every cell set to 0xFF, 0x00, 0xC0 in turn: the decoder always returns
    ("pokes MX", pokes(FX.gmail_mx())),
    ("pokes NS", pokes(FX.github_ns())),
    ("pokes NXDOMAIN", pokes(FX.xmpp_nx())),
    ("pokes TXT", pokes(FX.example_txt())),
    # full-range numbers, names, sizes
    ("max numbers roundtrip", roundtrip(max_msg())),
    ("255-byte names roundtrip", roundtrip(M.Message{hd(9n), [qa(max_name())],
      [rec(max_name(), M.TCNAME{}, M.RName{max_name()})], Nil{}, Nil{}})),
    ("256-byte name refused", Bool.not(E.message_ok(M.Message{hd(9n), [qa(fill(64n, 97) <> max_name())], Nil{}, Nil{}, Nil{}}))),
    ("query roundtrip 255-byte name", is_msg(D.message(E.query(65535n, max_name(), M.TAAAA{})),
      E.query_message(65535n, max_name(), M.TAAAA{}))
      && E.message_ok(E.query_message(65535n, max_name(), M.TAAAA{}))),
    ("65535-byte message roundtrip", roundtrip(with_raw(65483n)) && Nat.is_eq(len(E.message(with_raw(65483n))), 65535n)),
    ("65536-byte message refused", Bool.not(E.message_ok(with_raw(65484n)))),
    ("65536-byte message still decodes", is_msg(D.message(E.message(with_raw(65484n))), with_raw(65484n))),
    ("TXT 250 x 255 roundtrip", roundtrip(M.Message{hd(1n), [qa(ex())], [rec(ex(), M.TTXT{}, M.RTxt{strings.go(250n, Nil{})})], Nil{}, Nil{}})),
    ("TXT 256-byte string refused", Bool.not(E.message_ok(M.Message{hd(1n), [qa(ex())],
      [rec(ex(), M.TTXT{}, M.RTxt{[fill(256n, 120)]})], Nil{}, Nil{}}))),
    ("4000 compressed A records", counts_are(D.message(many_a(3999n)), [1n, 3999n, 0n, 0n])
      && Nat.is_eq(len(many_a(3999n)), 64013n)),
    ("addresses over 3999 records", found_count(A.addresses(ex(), M.TA{}, decoded(D.message(many_a(3999n)))), 3999n)),
    # hostile input
    ("garbage 65535 x 0xFF", is_err(D.message(fill(65535n, 255)), BAD_POINTER())),
    ("garbage 65535 x 0x00", is_err(D.message(fill(65535n, 0)), TRAILING())),
    ("garbage 65535 x 0xC0", is_err(D.message(fill(65535n, 192)), BAD_POINTER())),
    ("garbage 65535 x 0x01", is_err(D.message(fill(65535n, 1)), SHORT())),
    ("garbage 65535 non-bytes", is_err(D.message(fill(65535n, 70000)), SHORT())),
    ("garbage 65535 noise", Bool.not(is_done(D.message(noise(65535n, 1n))))
      && Bool.not(is_done(D.message(noise(65535n, 2n)))) && Bool.not(is_done(D.message(noise(65535n, 3n))))),
    ("garbage after a header", is_err(D.message(app(hdr(0n, 0n, 0n, 0n), noise(65523n, 7n))), TRAILING())),
    ("counts past the data", is_err(D.message(app(hdr(65535n, 65535n, 65535n, 65535n), q_ex())), SHORT())),
    ("200k bytes", is_err(D.message(fill(200000n, 0)), TRAILING())),
    ("pointer chain within budget", counts_are(D.message(chain(10n, 100n)), [0n, 101n, 0n, 0n])),
    ("pointer chain over budget", is_err(D.message(chain(1000n, 3500n)), BAD_POINTER())),
    ("pointer chain 8000 deep", counts_are(D.message(chain(8000n, 1n)), [0n, 2n, 0n, 0n])),
    ("name of 3 x 63 via pointers", counts_are(D.message(long_name(2n)), [0n, 2n, 0n, 0n])),
    ("name over 255 via pointers", is_err(D.message(long_name(3n)), BAD_LABEL())
      && is_err(D.message(long_name(40n)), BAD_LABEL())),
    ("name over 255 inline", is_err(D.message(app(hdr(1n, 0n, 0n, 0n), app(four_labels(), [0, 0, 1, 0, 1]))), BAD_LABEL())),
    ("self pointer", is_err(D.message(app(hdr(1n, 0n, 0n, 0n), [192, 12, 0, 1, 0, 1])), BAD_POINTER())),
    ("forward pointer", is_err(D.message(app(hdr(1n, 0n, 0n, 0n), [192, 13, 0, 0, 1, 0, 1])), BAD_POINTER())),
    # caller-built lists far past the limits (no stack overflow on JS)
    ("70k questions refused", Bool.not(E.message_ok(M.Message{hd(1n), questions.go(70000n, Nil{}), Nil{}, Nil{}, Nil{}}))
      && Nat.is_eq(len(E.message(M.Message{hd(1n), questions.go(70000n, Nil{}), Nil{}, Nil{}, Nil{}})), 1190012n)),
    ("70k records refused", Bool.not(E.message_ok(M.Message{hd(1n), Nil{}, big_records.go(70000n, Nil{}), Nil{}, Nil{}}))),
    ("100k groups refused", Bool.not(E.message_ok(M.Message{hd(1n), Nil{}, [rec(ex(), M.TAAAA{}, M.RIpv6{groups.go(100000n, Nil{})})], Nil{}, Nil{}}))
      && Nat.is_eq(len(E.rdata(M.RIpv6{groups.go(100000n, Nil{})})), 200000n)),
    ("1000 x 255 TXT strings refused", Bool.not(E.message_ok(M.Message{hd(1n), Nil{}, [rec(ex(), M.TTXT{}, M.RTxt{strings.go(1000n, Nil{})})], Nil{}, Nil{}}))),
    ("100k-byte RRaw refused", Bool.not(E.message_ok(with_raw(100000n))))
  ]

def report(xs: List<(String & Bool)>, fails: Nat) -> IO(Unit):
  match xs:
    case Nil{}:
      match fails:
        case 0n:
          IO.print("ALL PASS")
        case 1n+p:
          IO.print("SOME FAIL: " ++ Nat.show(1n+p))
    case Con{c, t}:
      match c:
        case (name, ok):
          match ok:
            case True{}:
              do IO<Unit>:
                IO.print("PASS " ++ name)
                report(t, fails)
            case False{}:
              do IO<Unit>:
                IO.print("FAIL " ++ name)
                report(t, 1n+fails)

def main() -> IO(Unit):
  report(cases(), 0n)
