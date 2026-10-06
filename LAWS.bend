# The laws of bender-dns: what its pure core must do, for every input.
# PROOF.bend proves each one (`def Laws.<name>`); the gate is `bend PROOF.bend`
# (and `bend PROOF.bend --verdict`, the BendTT kernel recheck, with Lean).
#
# The laws cover the pure modules: numbers, wire integers, names, IPv4 text,
# message encoding and decoding, TCP framing, resolv.conf candidates and
# response acceptance. The OS resolver (foreign) and the network IO are
# tested, not proven.
import Base
import ./src/bytes.bend as B
import ./src/types.bend as M
import ./src/num.bend as N
import ./src/wire.bend as W
import ./src/name.bend as NM
import ./src/ip.bend as IP
import ./src/encode.bend as E
import ./src/decode.bend as D
import ./src/frame.bend as F
import ./src/conf.bend as CF
import ./src/answer.bend as A

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def msg_id(m: M.Message) -> Nat:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      match h:
        case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
          id

def msg_qr(m: M.Message) -> Bool:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      match h:
        case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
          qr

def msg_questions(m: M.Message) -> List<&2, M.Question>:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      qs

# 1. Decimal numbers up to N.LIMIT() read back as written (resolv.conf options).
law dec_roundtrip:
  for +n: Nat
  for e: {Nat.is_le(n, N.LIMIT()) == True{} : Bool}
  {N.read(N.show(n)) == Some{n} : Maybe<&2, Nat>}

# 2. The same for hex (IPv6 groups).
law hex_roundtrip:
  for +n: Nat
  for e: {Nat.is_le(n, N.LIMIT()) == True{} : Bool}
  {N.hex_read(N.hex_show(n)) == Some{n} : Maybe<&2, Nat>}

# 3. A byte reads back from the wire, leaving the rest.
law u8_roundtrip:
  for +n: Nat
  for +rest: List<&2, U32>
  for e: {Nat.is_le(n, 255n) == True{} : Bool}
  {W.get_u8(cat(W.put_u8(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}

# 4. A 16-bit big-endian number reads back from the wire.
law u16_roundtrip:
  for +n: Nat
  for +rest: List<&2, U32>
  for e: {Nat.is_le(n, 65535n) == True{} : Bool}
  {W.get_u16(cat(W.put_u16(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}

# 5. A 32-bit big-endian number (its high half at most 65535) reads back.
law u32_roundtrip:
  for +n: Nat
  for +rest: List<&2, U32>
  for e: {Nat.is_le(Nat.div(n, 65536n), 65535n) == True{} : Bool}
  {W.get_u32(cat(W.put_u32(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}

# 6. The central law: a valid message decodes to itself.
law message_roundtrip:
  for +m: M.Message
  for e: {E.message_ok(m) == True{} : Bool}
  {D.message(E.message(m)) == Done{m} : Result<&2, &2, M.DecodeError, M.Message>}

# 7. A valid name shows as text and parses back to itself.
law name_text_roundtrip:
  for +n: M.Name()
  for e: {NM.ok(n) == True{} : Bool}
  {NM.from_text(NM.to_text(n)) == Done{n} : Result<&2, &2, M.NameError, M.Name()>}

# 8. Name comparison is reflexive.
law name_eq_refl:
  for +n: M.Name()
  {NM.eq(n, n) == True{} : Bool}

# 9. Name comparison is symmetric.
law name_eq_symm:
  for +a: M.Name()
  for +b: M.Name()
  {NM.eq(a, b) == NM.eq(b, a) : Bool}

# 10. A dotted quad shows and parses back.
law ipv4_roundtrip:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for ea: {Nat.is_le(a, 255n) == True{} : Bool}
  for eb: {Nat.is_le(b, 255n) == True{} : Bool}
  for ec: {Nat.is_le(c, 255n) == True{} : Bool}
  for ed: {Nat.is_le(d, 255n) == True{} : Bool}
  {IP.parse4(IP.show4(a, b, c, d)) == Some{M.RIpv4{a, b, c, d}} : Maybe<&2, M.RData>}

# 11. How a TCP stream arrives in pieces never changes what the frame reader sees.
law frame_split:
  for +s: F.Reader
  for +x: List<&2, U32>
  for +y: List<&2, U32>
  {F.feed(F.feed(s, x), y) == F.feed(s, cat(x, y)) : F.Reader}

# 12. A framed message reads back exactly, leaving the bytes after it.
law frame_roundtrip:
  for +xs: List<&2, U32>
  for +rest: List<&2, U32>
  for +max: Nat
  for e0: {Nat.is_le(len(xs), 65535n) == True{} : Bool}
  for e1: {Nat.is_le(len(xs), max) == True{} : Bool}
  {F.read(max, cat(F.frame(xs), rest)) == Done{F.Framed{xs, rest}}
    : Result<&2, &2, F.FrameError, F.Framed>}

# 13. An accepted response carries the query's id.
law accept_id:
  for +id: Nat
  for +q: M.Question
  for +m: M.Message
  for e: {A.accept(id, q, m) == True{} : Bool}
  {Nat.is_eq(msg_id(m), id) == True{} : Bool}

# 14. An accepted response is a response (QR set).
law accept_qr:
  for +id: Nat
  for +q: M.Question
  for +m: M.Message
  for e: {A.accept(id, q, m) == True{} : Bool}
  {msg_qr(m) == True{} : Bool}

# 15. An accepted response holds exactly the query's question.
law accept_question:
  for +id: Nat
  for +q: M.Question
  for +m: M.Message
  for e: {A.accept(id, q, m) == True{} : Bool}
  {A.one_question(q, msg_questions(m)) == True{} : Bool}

# 16. An absolute name (trailing dot) is tried alone, whatever the search list.
law candidates_absolute:
  for +conf: M.Conf
  for +name: String
  for e: {CF.ends_dot(name) == True{} : Bool}
  {CF.candidates(conf, name) == [name] : List<&2, String>}

# 17. A compression pointer to itself is refused (no loops).
law pointer_loop_refused:
  {D.message([0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 192, 12, 0, 1, 0, 1])
    == Fail{M.BadPointer{}} : Result<&2, &2, M.DecodeError, M.Message>}

# 18. A plain query decodes to the query message it was built from.
law query_example:
  {D.message(E.query_plain(7n, [[101, 120], [99, 111, 109]], M.TA{}))
    == Done{E.query_plain_message(7n, [[101, 120], [99, 111, 109]], M.TA{})}
    : Result<&2, &2, M.DecodeError, M.Message>}
