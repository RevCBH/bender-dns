import Base
import ../src/types.bend as M
import ../src/encode.bend as E
import ../src/decode.bend as D
import ./fixtures.bend as FX

# Checker-evaluated tests for decode.bend: `bend tests/decode_test.bend --check-only`
# printing ALL PROOFS CHECK is a pass (a plain run checks every def the same
# way, then prints main's Unit{}). The cases sit in one def per group (the
# checker's stack overflows on one conjunction of them all). Real responses with
# compression (tests/fixtures.bend) decode to the expected messages. The
# checker computes Nat in unary and its stack overflows (at times: it is
# close) on numbers past a few thousand, so the responses holding such
# numbers (example_aaaa's groups, gmail_srv's TTL 21600, the SOA serials of
# example_nodata, xmpp_nx and example_soa) and every full-range number are
# runtime-only (tests/codec_run.bend), which also covers every truncation,
# 65535-byte input and the pointer budget.

def R() -> Type:
  Result<&2, &2, M.DecodeError, M.Message>

def BS() -> Type:
  List<&2, U32>

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

# A response header: id 0x1234, QR RD RA, then the counts qd, an (ns = ar = 0).
def hdr(qd: U32, an: U32) -> List<&2, U32>:
  [18, 52, 129, 128, 0, qd, 0, an, 0, 0, 0, 0]

def hd() -> M.Header:
  M.Header{4660n, True{}, 0n, False{}, False{}, True{}, True{}, False{}, False{}, 0n}

def q_a(n: M.Name()) -> M.Question:
  M.Question{n, M.TA{}, M.CIN{}}

def only_qs(qs: List<&2, M.Question>) -> M.Message:
  M.Message{hd(), qs, Nil{}, Nil{}, Nil{}}

# One question for [[97]] ("a") type A, then an answer with the given owner
# name bytes, type A, class IN, ttl 7 and the given RDLENGTH and RDATA.
def ans_a(owner: List<&2, U32>, rdlen: U32, rd: List<&2, U32>) -> List<&2, U32>:
  cat(hdr(1, 1), cat([1, 97, 0, 0, 1, 0, 1], cat(owner, cat([0, 1, 0, 1, 0, 0, 0, 7, 0, rdlen], rd))))

def rec_a(n: M.Name(), a: Nat, b: Nat, c: Nat, d: Nat) -> M.Record:
  M.Record{n, M.TA{}, M.CIN{}, 7n, M.RIpv4{a, b, c, d}}

# Real responses (compressed), one def each: a conjunction of several of
# them overflows the checker's stack.
def real.example_a() -> {D.message(FX.example_a()) == Done{FX.example_a.msg()} : R()}:
  {==}

def real.gmail_mx() -> {D.message(FX.gmail_mx()) == Done{FX.gmail_mx.msg()} : R()}:
  {==}

def real.github_cname() -> {D.message(FX.github_cname()) == Done{FX.github_cname.msg()} : R()}:
  {==}

def real.example_txt() -> {D.message(FX.example_txt()) == Done{FX.example_txt.msg()} : R()}:
  {==}

def real.example_a_edns() -> {D.message(FX.example_a_edns()) == Done{FX.example_a_edns.msg()} : R()}:
  {==}

def real.google_ptr() -> {D.message(FX.google_ptr()) == Done{FX.google_ptr.msg()} : R()}:
  {==}

def real.github_ns() -> {D.message(FX.github_ns()) == Done{FX.github_ns.msg()} : R()}:
  {==}

# and re-encoded uncompressed, they decode back
def reencoded() ->
  {D.message(E.message(FX.gmail_mx.msg())) == Done{FX.gmail_mx.msg()} : R()} &
  {D.message(E.message(FX.github_cname.msg())) == Done{FX.github_cname.msg()} : R()} &
  {D.message(E.message(FX.example_a_edns.msg())) == Done{FX.example_a_edns.msg()} : R()}:
  ({==}, {==}, {==})

# pointers: to a pointer to a name (valid), to itself, forward, into the header
def pointers() ->
  {D.message(cat(hdr(3, 0), [1, 97, 0, 0, 1, 0, 1, 192, 12, 0, 1, 0, 1, 192, 19, 0, 1, 0, 1]))
    == Done{only_qs([q_a([[97]]), q_a([[97]]), q_a([[97]])])} : R()} &
  {D.message(cat(hdr(1, 0), [192, 12, 0, 1, 0, 1])) == Fail{M.BadPointer{}} : R()} &
  {D.message(cat(hdr(1, 0), [1, 97, 192, 12, 0, 1, 0, 1])) == Fail{M.BadPointer{}} : R()} &
  {D.message(cat(hdr(1, 0), [192, 14, 0, 1, 0, 1])) == Fail{M.BadPointer{}} : R()} &
  {D.message(cat(hdr(1, 0), [1, 97, 192, 200, 0, 1, 0, 1])) == Fail{M.BadPointer{}} : R()} &
  {D.message(cat(hdr(1, 0), [1, 97, 192])) == Fail{M.Short{}} : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==})

# a hop whose segment points at itself (an answer's RDATA holds [1, 98, 192, 30]
# at offset 30; the second answer's owner points there)
def hop_loop() ->
  {D.message(cat(hdr(1, 2), [1, 97, 0, 0, 1, 0, 1,
      0, 0, 99, 0, 1, 0, 0, 0, 0, 0, 4, 1, 98, 192, 30,
      192, 30, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])) == Fail{M.BadPointer{}} : R()}:
  {==}

# the same RDATA ending [1, 98, 0]: the owner is "b"
def hop_ok() ->
  {D.message(cat(hdr(1, 2), [1, 97, 0, 0, 1, 0, 1,
      0, 0, 99, 0, 1, 0, 0, 0, 0, 0, 3, 1, 98, 0,
      192, 30, 0, 255, 0, 1, 0, 0, 0, 0, 0, 0]))
    == Done{M.Message{hd(), [q_a([[97]])],
      [M.Record{Nil{}, M.TOther{99n}, M.CIN{}, 0n, M.RRaw{[1, 98, 0]}},
       M.Record{[[98]], M.TANY{}, M.CIN{}, 0n, M.RRaw{Nil{}}}], Nil{}, Nil{}}} : R()}:
  {==}

# labels: reserved bits, a pointer's second cell past 255, a length cell past 255
def labels() ->
  {D.message(cat(hdr(1, 0), [64, 0, 1, 0, 1])) == Fail{M.BadLabel{}} : R()} &
  {D.message(cat(hdr(1, 0), [128, 0, 1, 0, 1])) == Fail{M.BadLabel{}} : R()} &
  {D.message(cat(hdr(1, 0), [191, 0, 1, 0, 1])) == Fail{M.BadLabel{}} : R()} &
  {D.message(cat(hdr(1, 0), [192, 256, 0, 1, 0, 1])) == Fail{M.BadPointer{}} : R()} &
  {D.message(cat(hdr(1, 0), [256, 0, 1, 0, 1])) == Fail{M.BadLabel{}} : R()} &
  {D.message(cat(hdr(1, 0), [1, 300, 0, 0, 1, 0, 1])) == Fail{M.BadLabel{}} : R()} &
  {D.message(cat(hdr(1, 0), [63, 0, 1, 0, 1])) == Fail{M.Short{}} : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

# RDATA: right, too long, too short, past the end, bytes past 255
def rdata_len() ->
  {D.message(ans_a([192, 12], 4, [1, 2, 3, 4]))
    == Done{M.Message{hd(), [q_a([[97]])], [rec_a([[97]], 1n, 2n, 3n, 4n)], Nil{}, Nil{}}} : R()} &
  {D.message(ans_a([192, 12], 5, [1, 2, 3, 4, 5])) == Fail{M.BadRdata{}} : R()} &
  {D.message(ans_a([192, 12], 3, [1, 2, 3])) == Fail{M.BadRdata{}} : R()} &
  {D.message(ans_a([192, 12], 5, [1, 2, 3, 4])) == Fail{M.Short{}} : R()} &
  {D.message(ans_a([192, 12], 4, [1, 2, 3, 256])) == Fail{M.BadRdata{}} : R()} &
  {D.message(cat(hdr(1, 1), [1, 97, 0, 0, 1, 0, 1, 192, 12, 0, 99, 0, 1, 0, 0, 0, 0, 0, 2, 1, 256]))
    == Fail{M.BadRdata{}} : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==})

# TXT: an empty string, an empty RDATA, a string cut short
def txt() ->
  {D.message(cat(hdr(1, 1), [1, 97, 0, 0, 1, 0, 1, 192, 12, 0, 16, 0, 1, 0, 0, 0, 0, 0, 3, 0, 1, 120]))
    == Done{M.Message{hd(), [q_a([[97]])], [M.Record{[[97]], M.TTXT{}, M.CIN{}, 0n, M.RTxt{[[], [120]]}}], Nil{}, Nil{}}} : R()} &
  {D.message(cat(hdr(1, 1), [1, 97, 0, 0, 1, 0, 1, 192, 12, 0, 16, 0, 1, 0, 0, 0, 0, 0, 0]))
    == Done{M.Message{hd(), [q_a([[97]])], [M.Record{[[97]], M.TTXT{}, M.CIN{}, 0n, M.RTxt{[]}}], Nil{}, Nil{}}} : R()} &
  {D.message(cat(hdr(1, 1), [1, 97, 0, 0, 1, 0, 1, 192, 12, 0, 16, 0, 1, 0, 0, 0, 0, 0, 2, 2, 120]))
    == Fail{M.BadRdata{}} : R()}:
  ({==}, {==}, {==})

# a name in RDATA running past RDLENGTH
def rdata_name() ->
  {D.message(cat(hdr(1, 1), [1, 97, 0, 0, 1, 0, 1, 192, 12, 0, 5, 0, 1, 0, 0, 0, 0, 0, 2, 1, 98, 0]))
    == Fail{M.BadRdata{}} : R()}:
  {==}

# framing of the whole: short header, empty, trailing bytes, counts past the data
def framing() ->
  {D.message([]) == Fail{M.Short{}} : R()} &
  {D.message([18, 52, 129, 128, 0, 0, 0, 0, 0, 0, 0]) == Fail{M.Short{}} : R()} &
  {D.message(hdr(0, 0)) == Done{M.Message{hd(), Nil{}, Nil{}, Nil{}, Nil{}}} : R()} &
  {D.message(cat(hdr(0, 0), [0])) == Fail{M.Trailing{}} : R()} &
  {D.message(cat(FX.example_a(), [0])) == Fail{M.Trailing{}} : R()} &
  {D.message(hdr(1, 0)) == Fail{M.Short{}} : R()} &
  {D.message(cat(hdr(1, 0), [0, 0, 1])) == Fail{M.Short{}} : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

# flags: every bit and both 4-bit fields at their maximum (Z set is ignored)
def flags() ->
  {D.message([0, 0, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0])
    == Done{M.Message{M.Header{0n, True{}, 15n, True{}, True{}, True{}, True{}, True{}, True{}, 15n},
      Nil{}, Nil{}, Nil{}, Nil{}}} : R()} &
  {D.message([1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    == Done{M.Message{M.Header{258n, False{}, 0n, False{}, False{}, False{}, False{}, False{}, False{}, 0n},
      Nil{}, Nil{}, Nil{}, Nil{}}} : R()}:
  ({==}, {==})

# type and class codes
def codes() ->
  {D.type_of(28n) == M.TAAAA{} : M.RType} &
  {D.type_of(255n) == M.TANY{} : M.RType} &
  {D.type_of(99n) == M.TOther{99n} : M.RType} &
  {D.class_of(1n) == M.CIN{} : M.RClass} &
  {D.class_of(3n) == M.COther{3n} : M.RClass}:
  ({==}, {==}, {==}, {==}, {==})

def main() -> Unit:
  Unit{}
