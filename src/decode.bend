import Base
import ./bytes.bend as B
import ./types.bend as M
import ./wire.bend as W
import ./name.bend as NM
import ./encode.bend as E

# Message decoding (RFC 1035 4.1), with compression pointers (4.1.4).
#
#   message(xs)  the whole message: header, questions, answers, authority,
#                additional; Fail{Trailing} if bytes are left after the last
#                record. Unknown types (and OPT, ANY) keep their RDATA as RRaw.
#
# Sequential reading. Everything is read front to back from a cursor
# Cur{rest, pos, hops}: rest is every byte not yet read, pos the offset of
# rest's first byte in the message, hops what is left of the pointer budget.
# Every reader takes a cursor and gives Done{X{value, cursor after}} or Fail.
# Numbers go through W.get_u8 / get_u16 / get_u32 on rest (pos + 1, 2 or 4);
# W gives None on a short list or a cell past 255, read as Short. Only
# names ever look at pos and hops; nothing ever indexes into rest.
#
# Names. A name is read by seg.go, a structural fold over rest (one byte per
# step; recursion on the list) through the Lab states:
#   LLen{ls}            at a length byte (ls: the labels so far, reversed)
#   LIn{more, cur, ls}  inside a label, 1 + more bytes to go (cur reversed)
#   LHi{hi, ls}         after a pointer's first byte (hi = its low 6 bits)
#   LEnd{ls}            the zero byte was read: the name is complete
#   LJump{ls, target}   a pointer was read
#   LBad{error}
# A length byte 0 ends the name, 1..63 starts a label, 192..255 starts a
# pointer, 64..191 is BadLabel (a cell past 255: BadLabel). seg.go stops at
# the first byte after LEnd / LJump and returns SegEnd{ls, rest} or
# SegJump{ls, target, rest}. For an uncompressed name that is all: the
# name is B.rev(ls) and must be NM.ok (else BadLabel), and the cursor moves
# to Cur{rest, pos + NM.wire_size(name), hops}.
#
# Pointers take a separate, bounded path (follow): the target must lie
# strictly before the start of the name or segment that holds the pointer
# (so targets strictly decrease and no loop is possible), the labels so far
# must still fit 255 bytes, and each hop spends one unit of the cursor's hop
# budget, which message() sets to the message length: so all the pointers of
# one message cost at most that many hops in total (a pointer to a pointer
# to a pointer ... shared by many names cannot multiply the work). Any of
# these failing is BadPointer (an over-long name, BadLabel). At the target,
# seg.hop reads at most HOP_ROOM bytes (a fuel, so a segment cannot run on)
# from the message's suffix there, found through the index: the suffixes at
# every CHUNK-th offset, so a lookup walks at most CHUNK + targets/CHUNK
# cells. The name read so far continues there; the cursor moves past the
# pointer (pos + wire_size(first segment) + 1).
#
# RDATA. RDLENGTH bytes are taken off rest first (take.go; Short if fewer),
# and the RDATA is read from exactly those bytes by type (names in it may
# be compressed; pos stays exact for their pointers). It must use them all:
# a short read or bytes left over is BadRdata. TXT is read by txt.go, a
# structural fold like seg.go (strings of 0..255 bytes; any number of them).
# TOPT, TANY and TOther keep the bytes (RRaw). Every cell read is checked to
# be a byte: numbers by W, labels by NM.ok, TXT strings and RRaw bytes by
# B.all_bytes (else BadRdata).
#
# Header. The flags bytes are read as two u8s and unpacked by Nat.div /
# Nat.mod (Z is ignored); header.of(id, E.flags_hi(..), E.flags_lo(..))
# gives back the fields for flags in range: a closed fact over 2^4 * 16 and
# 2^3 * 16 cases.
#
# NOTE (loops): every def here that walks the message or a list from it is
# a direct tail call (seg.go, seg.hop, txt.go, take.go, index.go, nth.go,
# drop.go, and the count loops qs.go, rs.go, g.go), so a 65535-byte message
# is safe on the JS lane. They are plain structural recursions with
# accumulators, so they are their own specs; the proofs generalize the
# accumulators.
#
# The central law and what it needs (see also encode.bend):
#   E.message_ok(m) => message(E.message(m)) == Done{m}
# by the pieces, each for every pos, hops and rest r:
#   header(Cur{E.header_onto(h, qd, an, ns, ar, r), pos, hops})
#     == Done{HeadAt{h, qd, an, ns, ar, Cur{r, 12 + pos, hops}}}
#     (header_ok(h), counts <= 65535)
#   read_name(ix, Cur{NM.wire_onto(n, r), pos, hops})
#     == Done{NameAt{n, Cur{r, Nat.add(NM.wire_size(n), pos), hops}}}   (NM.ok(n))
#     via seg.go(List.append(NM.wire.spec(n), r), LLen{acc})
#       == seg.go(r, LEnd{B.rev(n, acc)})  (induction on n), and per label l
#     seg.go(List.append(l, ys), LIn{len(l) - 1, cur, ls})
#       == seg.go(ys, LLen{B.rev(B.rev(l, cur), Nil) <> ls})  (induction on l);
#     seg.go(r, LEnd{x}) == SegEnd{x, r} (case on r)
#   questions(length(qs), ix, Cur{E.questions.spec(qs, r), pos, hops})
#     == Done{QsAt{qs, Cur{r, pos', hops}}} for the pos' the readers compute
#   records(length(rs), ix, Cur{E.records.spec(rs, r), pos, hops}) likewise,
#     per record: take.go(len(rd), List.append(rd, r), Nil) == Some{Taken{rd, r}}
#     and rdata(ix, t, Cur{E.rdata(d), p, h}) == Done{DataAt{d, Cur{Nil, p', h}}}
#     when E.data_ok(t, d) (TXT: txt.go(E.txt.spec(ss, Nil), TLen{acc})
#     == TLen{B.rev(ss, acc)}, induction on ss and each string)
#   type_of(E.type_code(t)) == t and class_of(E.class_code(c)) == c (type_ok,
#   class_ok)
# Pointers are never met (E writes none), so neither the index nor follow
# matters to the law.

# Limits
# ------

# The index keeps the message's suffix at every CHUNK-th offset.
def CHUNK() -> Nat:
  128n

# The most bytes one segment reached by a pointer may take (a whole name is
# at most 255, so 255 bytes of labels and zero, or labels and a pointer).
def HOP_ROOM() -> Nat:
  256n

# Results
# -------

# Where reading stands: the bytes left, their offset, the pointer budget.
type Cur is Data:
  Cur{rest: List<&2, U32>, pos: Nat, hops: Nat}

type NumAt is Data:
  NumAt{value: Nat, at: Cur}

type NameAt is Data:
  NameAt{name: List<&2, List<&2, U32>>, at: Cur}

type DataAt is Data:
  DataAt{data: M.RData, at: Cur}

type QAt is Data:
  QAt{question: M.Question, at: Cur}

type RecAt is Data:
  RecAt{record: M.Record, at: Cur}

type HeadAt is Data:
  HeadAt{header: M.Header, qd: Nat, an: Nat, ns: Nat, ar: Nat, at: Cur}

type QsAt is Data:
  QsAt{questions: List<&2, M.Question>, at: Cur}

type RsAt is Data:
  RsAt{records: List<&2, M.Record>, at: Cur}

# A name's labels (reversed) after following pointers, and the budget left.
type Labels is Data:
  Labels{labels: List<&2, List<&2, U32>>, left: Nat}

# k bytes taken off a list, and the bytes after them.
type Taken is Data:
  Taken{bytes: List<&2, U32>, after: List<&2, U32>}

# Numbers
# -------

def num(g: Maybe<&2, M.Got>, k: Nat, pos: Nat, h: Nat) -> Result<&2, &2, M.DecodeError, NumAt>:
  match g:
    case Some{x}:
      match x:
        case M.Got{v, r}:
          Done{NumAt{v, Cur{r, Nat.add(k, pos), h}}}
    case None{}:
      Fail{M.Short{}}

def u8(c: Cur) -> Result<&2, &2, M.DecodeError, NumAt>:
  match c:
    case Cur{xs, pos, h}:
      num(W.get_u8(xs), 1n, pos, h)

def u16(c: Cur) -> Result<&2, &2, M.DecodeError, NumAt>:
  match c:
    case Cur{xs, pos, h}:
      num(W.get_u16(xs), 2n, pos, h)

def u32(c: Cur) -> Result<&2, &2, M.DecodeError, NumAt>:
  match c:
    case Cur{xs, pos, h}:
      num(W.get_u32(xs), 4n, pos, h)

# Codes
# -----

def type_of.pick(k: Maybe<&2, M.RType>, c: Nat) -> M.RType:
  match k:
    case Some{t}:
      t
    case None{}:
      M.TOther{c}

# The type with code c: a known one, else TOther{c}.
def type_of(+c: Nat) -> M.RType:
  type_of.pick(E.type_known(c), c)

def class_of.pick(hit: Bool, c: Nat) -> M.RClass:
  match hit:
    case True{}:
      M.CIN{}
    case False{}:
      M.COther{c}

def class_of(+c: Nat) -> M.RClass:
  class_of.pick(Nat.is_eq(c, 1n), c)

# The index (for pointers)
# ------------------------

# The suffixes of xs at offsets 0, CHUNK, 2 * CHUNK, ...; k bytes to the next
# mark (a loop).
def index.go(xs: List<&2, U32>, k: Nat, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      B.rev(List<&2, U32>, acc, Nil{})
    case Con{+h, +t}:
      match k:
        case 0n:
          index.go(t, Nat.sub(CHUNK(), 1n), Con{h, t} <> acc)
        case 1n+p:
          index.go(t, p, acc)

def index(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  index.go(xs, 0n, Nil{})

# The k-th entry ([] past the end).
def nth.go(k: Nat, ix: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match k:
    case 0n:
      match ix:
        case Nil{}:
          Nil{}
        case Con{s, r}:
          s
    case 1n+p:
      match ix:
        case Nil{}:
          Nil{}
        case Con{s, r}:
          nth.go(p, r)

# xs without its first k cells.
def drop.go(k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          drop.go(p, t)

# The message from offset t on.
def suffix(ix: List<&2, List<&2, U32>>, +t: Nat) -> List<&2, U32>:
  drop.go(Nat.mod(t, CHUNK()), nth.go(Nat.div(t, CHUNK()), ix))

# Names: the label machine
# ------------------------

type Lab is Data:
  LLen{ls: List<&2, List<&2, U32>>}
  LIn{more: Nat, cur: List<&2, U32>, ls: List<&2, List<&2, U32>>}
  LHi{hi: Nat, ls: List<&2, List<&2, U32>>}
  LEnd{ls: List<&2, List<&2, U32>>}
  LJump{ls: List<&2, List<&2, U32>>, target: Nat}
  LBad{error: M.DecodeError}

# What a segment of a name came to.
type Seg is Data:
  SegEnd{ls: List<&2, List<&2, U32>>, rest: List<&2, U32>}
  SegJump{ls: List<&2, List<&2, U32>>, target: Nat, rest: List<&2, U32>}
  SegBad{error: M.DecodeError}

def len_more(lab: Bool, p: Nat, ptr: Bool, hi: Nat, ls: List<&2, List<&2, U32>>) -> Lab:
  match lab:
    case True{}:
      LIn{p, Nil{}, ls}
    case False{}:
      match ptr:
        case True{}:
          LHi{hi, ls}
        case False{}:
          LBad{M.BadLabel{}}

# A length byte's value: 0 ends the name, 1n+p <= 63 starts a label of
# 1 + p bytes, 192 + hi starts a pointer, anything else is BadLabel.
def len_value(v: Nat, ls: List<&2, List<&2, U32>>) -> Lab:
  match v:
    case 0n:
      LEnd{ls}
    case 1n+(+p):
      len_more(Nat.is_le(p, 62n), p, Nat.is_le(191n, p), Nat.sub(p, 191n), ls)

def len_byte(g: Maybe<&2, M.Got>, ls: List<&2, List<&2, U32>>) -> Lab:
  match g:
    case Some{x}:
      match x:
        case M.Got{v, r}:
          len_value(v, ls)
    case None{}:
      LBad{M.BadLabel{}}

# A byte of a label; the last one finishes it.
def in_byte(more: Nat, cur: List<&2, U32>, ls: List<&2, List<&2, U32>>, b: U32) -> Lab:
  match more:
    case 0n:
      LLen{B.rev(U32, b <> cur, Nil{}) <> ls}
    case 1n+q:
      LIn{q, b <> cur, ls}

# A pointer's second byte.
def hi_byte(hi: Nat, g: Maybe<&2, M.Got>, ls: List<&2, List<&2, U32>>) -> Lab:
  match g:
    case Some{x}:
      match x:
        case M.Got{lo, r}:
          LJump{ls, W.join16(hi, lo)}
    case None{}:
      LBad{M.BadPointer{}}

# One byte (a finished state stays as it is).
def step(st: Lab, b: U32) -> Lab:
  match st:
    case LLen{ls}:
      len_byte(W.get_u8([b]), ls)
    case LIn{m, cur, ls}:
      in_byte(m, cur, ls, b)
    case LHi{hi, ls}:
      hi_byte(hi, W.get_u8([b]), ls)
    case LEnd{ls}:
      LEnd{ls}
    case LJump{ls, t}:
      LJump{ls, t}
    case LBad{e}:
      LBad{e}

# The input ended (rest: what follows the name).
def stop(st: Lab, rest: List<&2, U32>) -> Seg:
  match st:
    case LEnd{ls}:
      SegEnd{ls, rest}
    case LJump{ls, t}:
      SegJump{ls, t, rest}
    case LBad{e}:
      SegBad{e}
    case _:
      SegBad{M.Short{}}

# Reads a name segment from xs: stops right after its zero byte or pointer
# (a structural loop over xs).
def seg.go(xs: List<&2, U32>, st: Lab) -> Seg:
  match xs:
    case Nil{}:
      stop(st, Nil{})
    case Con{b, t}:
      match st:
        case LLen{ls}:
          seg.go(t, len_byte(W.get_u8([b]), ls))
        case LIn{m, cur, ls}:
          seg.go(t, in_byte(m, cur, ls, b))
        case LHi{hi, ls}:
          seg.go(t, hi_byte(hi, W.get_u8([b]), ls))
        case LEnd{ls}:
          SegEnd{ls, Con{b, t}}
        case LJump{ls, tg}:
          SegJump{ls, tg, Con{b, t}}
        case LBad{e}:
          SegBad{e}

# Out of room: a segment that has not ended is too long.
def stop.room(st: Lab) -> Seg:
  match st:
    case LEnd{ls}:
      SegEnd{ls, Nil{}}
    case LJump{ls, t}:
      SegJump{ls, t, Nil{}}
    case LBad{e}:
      SegBad{e}
    case _:
      SegBad{M.BadLabel{}}

# A segment reached by a pointer: at most room bytes (a fuel); what follows
# it is not needed.
def seg.hop(room: Nat, xs: List<&2, U32>, st: Lab) -> Seg:
  match room:
    case 0n:
      stop.room(st)
    case 1n+r:
      match xs:
        case Nil{}:
          stop(st, Nil{})
        case Con{b, t}:
          seg.hop(r, t, step(st, b))

# Names: pointers
# ---------------

def jump(ptr_ok: Bool, size_ok: Bool, ix: List<&2, List<&2, U32>>, +tg: Nat,
  ls: List<&2, List<&2, U32>>) -> Seg:
  match ptr_ok:
    case True{}:
      match size_ok:
        case True{}:
          seg.hop(HOP_ROOM(), suffix(ix, tg), LLen{ls})
        case False{}:
          SegBad{M.BadLabel{}}
    case False{}:
      SegBad{M.BadPointer{}}

# With no hops left: a segment that still points elsewhere fails.
def follow.out(s: Seg) -> Result<&2, &2, M.DecodeError, Labels>:
  match s:
    case SegEnd{ls, r}:
      Done{Labels{ls, 0n}}
    case SegBad{e}:
      Fail{e}
    case SegJump{ls, tg, r}:
      Fail{M.BadPointer{}}

# Follows pointers from the segment s (whose own start is start) with h hops
# of budget left (a loop on the budget).
def follow(h: Nat, s: Seg, start: Nat, +ix: List<&2, List<&2, U32>>) ->
  Result<&2, &2, M.DecodeError, Labels>:
  match h:
    case 0n:
      follow.out(s)
    case 1n+p:
      match s:
        case SegEnd{ls, r}:
          Done{Labels{ls, 1n+p}}
        case SegBad{e}:
          Fail{e}
        case SegJump{+ls, +tg, r}:
          follow(p, jump(Nat.is_lt(tg, start), Nat.is_le(NM.wire_size(ls), 255n), ix, tg, ls), tg, ix)

def name.end(ok: Bool, n: M.Name(), rest: List<&2, U32>, pos: Nat, h: Nat) ->
  Result<&2, &2, M.DecodeError, NameAt>:
  match ok:
    case True{}:
      Done{NameAt{n, Cur{rest, pos, h}}}
    case False{}:
      Fail{M.BadLabel{}}

# An uncompressed name: the cursor moves past its wire form.
def name.plain(+n: M.Name(), rest: List<&2, U32>, pos: Nat, h: Nat) ->
  Result<&2, &2, M.DecodeError, NameAt>:
  name.end(NM.ok(n), n, rest, Nat.add(NM.wire_size(n), pos), h)

def name.jumped(r: Result<&2, &2, M.DecodeError, Labels>, rest: List<&2, U32>, pos: Nat) ->
  Result<&2, &2, M.DecodeError, NameAt>:
  match r:
    case Done{x}:
      match x:
        case Labels{ls, h}:
          +n = B.rev(List<&2, U32>, ls, Nil{})
          name.end(NM.ok(n), n, rest, pos, h)
    case Fail{e}:
      Fail{e}

def name.first(s: Seg, +pos: Nat, h: Nat, ix: List<&2, List<&2, U32>>) ->
  Result<&2, &2, M.DecodeError, NameAt>:
  match s:
    case SegEnd{ls, r}:
      name.plain(B.rev(List<&2, U32>, ls, Nil{}), r, pos, h)
    case SegJump{+ls, tg, r}:
      name.jumped(follow(h, SegJump{ls, tg, Nil{}}, pos, ix), r, Nat.add(1n+NM.wire_size(ls), pos))
    case SegBad{e}:
      Fail{e}

# A name at the cursor (ix: the message's index, for pointers).
def read_name(ix: List<&2, List<&2, U32>>, c: Cur) -> Result<&2, &2, M.DecodeError, NameAt>:
  match c:
    case Cur{xs, pos, h}:
      name.first(seg.go(xs, LLen{Nil{}}), pos, h, ix)

# Header
# ------

def header.of(id: Nat, +hi: Nat, +lo: Nat) -> M.Header:
  +a = Nat.mod(hi, 128n)
  +b = Nat.mod(a, 8n)
  +c = Nat.mod(lo, 128n)
  M.Header{id, Nat.is_le(128n, hi), Nat.div(a, 8n), Nat.is_le(4n, b), Nat.is_le(2n, Nat.mod(b, 4n)),
    Nat.is_eq(Nat.mod(b, 2n), 1n), Nat.is_le(128n, lo), Nat.is_le(32n, Nat.mod(c, 64n)),
    Nat.is_le(16n, Nat.mod(c, 32n)), Nat.mod(lo, 16n)}

def head.ar(id: Nat, hi: Nat, lo: Nat, qd: Nat, an: Nat, ns: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, HeadAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{ar, c}:
          Done{HeadAt{header.of(id, hi, lo), qd, an, ns, ar, c}}
    case Fail{e}:
      Fail{e}

def head.ns(id: Nat, hi: Nat, lo: Nat, qd: Nat, an: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, HeadAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{ns, c}:
          head.ar(id, hi, lo, qd, an, ns, u16(c))
    case Fail{e}:
      Fail{e}

def head.an(id: Nat, hi: Nat, lo: Nat, qd: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, HeadAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{an, c}:
          head.ns(id, hi, lo, qd, an, u16(c))
    case Fail{e}:
      Fail{e}

def head.qd(id: Nat, hi: Nat, lo: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, HeadAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{qd, c}:
          head.an(id, hi, lo, qd, u16(c))
    case Fail{e}:
      Fail{e}

def head.lo(id: Nat, hi: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, HeadAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{lo, c}:
          head.qd(id, hi, lo, u16(c))
    case Fail{e}:
      Fail{e}

def head.hi(id: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, HeadAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{hi, c}:
          head.lo(id, hi, u8(c))
    case Fail{e}:
      Fail{e}

def head.id(r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, HeadAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{id, c}:
          head.hi(id, u8(c))
    case Fail{e}:
      Fail{e}

# The 12 header bytes: the header and the four counts.
def header(c: Cur) -> Result<&2, &2, M.DecodeError, HeadAt>:
  head.id(u16(c))

# Questions
# ---------

def q.cls(n: M.Name(), t: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, QAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{cl, c}:
          Done{QAt{M.Question{n, type_of(t), class_of(cl)}, c}}
    case Fail{e}:
      Fail{e}

def q.typ(n: M.Name(), r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, QAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{t, c}:
          q.cls(n, t, u16(c))
    case Fail{e}:
      Fail{e}

def q.name(r: Result<&2, &2, M.DecodeError, NameAt>) -> Result<&2, &2, M.DecodeError, QAt>:
  match r:
    case Done{x}:
      match x:
        case NameAt{n, c}:
          q.typ(n, u16(c))
    case Fail{e}:
      Fail{e}

def question(ix: List<&2, List<&2, U32>>, c: Cur) -> Result<&2, &2, M.DecodeError, QAt>:
  q.name(read_name(ix, c))

# The questions read so far (reversed), or the first failure.
type QSt is Data:
  QOk{at: Cur, acc: List<&2, M.Question>}
  QErr{error: M.DecodeError}

def qs.next(r: Result<&2, &2, M.DecodeError, QAt>, acc: List<&2, M.Question>) -> QSt:
  match r:
    case Done{x}:
      match x:
        case QAt{q, c}:
          QOk{c, q <> acc}
    case Fail{e}:
      QErr{e}

def qs.step(ix: List<&2, List<&2, U32>>, st: QSt) -> QSt:
  match st:
    case QOk{c, acc}:
      qs.next(question(ix, c), acc)
    case QErr{e}:
      QErr{e}

# k more questions (a loop; after a failure the steps do nothing).
def qs.go(k: Nat, +ix: List<&2, List<&2, U32>>, st: QSt) -> QSt:
  match k:
    case 0n:
      st
    case 1n+p:
      qs.go(p, ix, qs.step(ix, st))

def qs.end(st: QSt) -> Result<&2, &2, M.DecodeError, QsAt>:
  match st:
    case QOk{c, acc}:
      Done{QsAt{B.rev(M.Question, acc, Nil{}), c}}
    case QErr{e}:
      Fail{e}

# k questions.
def questions(k: Nat, ix: List<&2, List<&2, U32>>, c: Cur) -> Result<&2, &2, M.DecodeError, QsAt>:
  qs.end(qs.go(k, ix, QOk{c, Nil{}}))

# RDATA
# -----

def rd.done(d: M.RData, c: Cur) -> Result<&2, &2, M.DecodeError, DataAt>:
  Done{DataAt{d, c}}

# A, AAAA

def ip4.d(a: Nat, b: Nat, c3: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{d, c}:
          rd.done(M.RIpv4{a, b, c3, d}, c)
    case Fail{e}:
      Fail{e}

def ip4.c(a: Nat, b: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{v, c}:
          ip4.d(a, b, v, u8(c))
    case Fail{e}:
      Fail{e}

def ip4.b(a: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{v, c}:
          ip4.c(a, v, u8(c))
    case Fail{e}:
      Fail{e}

def ip4.a(r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{v, c}:
          ip4.b(v, u8(c))
    case Fail{e}:
      Fail{e}

def rd.a(c: Cur) -> Result<&2, &2, M.DecodeError, DataAt>:
  ip4.a(u8(c))

# The groups read so far (reversed), or the first failure.
type GSt is Data:
  GOk{at: Cur, acc: List<&2, Nat>}
  GErr{error: M.DecodeError}

def g.next(r: Result<&2, &2, M.DecodeError, NumAt>, acc: List<&2, Nat>) -> GSt:
  match r:
    case Done{x}:
      match x:
        case NumAt{v, c}:
          GOk{c, v <> acc}
    case Fail{e}:
      GErr{e}

def g.step(st: GSt) -> GSt:
  match st:
    case GOk{c, acc}:
      g.next(u16(c), acc)
    case GErr{e}:
      GErr{e}

def g.go(k: Nat, st: GSt) -> GSt:
  match k:
    case 0n:
      st
    case 1n+p:
      g.go(p, g.step(st))

def g.end(st: GSt) -> Result<&2, &2, M.DecodeError, DataAt>:
  match st:
    case GOk{c, acc}:
      rd.done(M.RIpv6{B.rev(Nat, acc, Nil{})}, c)
    case GErr{e}:
      Fail{e}

# Eight u16 groups.
def rd.aaaa(c: Cur) -> Result<&2, &2, M.DecodeError, DataAt>:
  g.end(g.go(8n, GOk{c, Nil{}}))

# NS, CNAME, PTR, MX, SRV, SOA

def rd.name(r: Result<&2, &2, M.DecodeError, NameAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NameAt{n, c}:
          rd.done(M.RName{n}, c)
    case Fail{e}:
      Fail{e}

def mx.name(p: Nat, r: Result<&2, &2, M.DecodeError, NameAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NameAt{n, c}:
          rd.done(M.RMx{p, n}, c)
    case Fail{e}:
      Fail{e}

def rd.mx(ix: List<&2, List<&2, U32>>, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{p, c}:
          mx.name(p, read_name(ix, c))
    case Fail{e}:
      Fail{e}

def srv.name(pr: Nat, w: Nat, po: Nat, r: Result<&2, &2, M.DecodeError, NameAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NameAt{n, c}:
          rd.done(M.RSrv{pr, w, po, n}, c)
    case Fail{e}:
      Fail{e}

def srv.po(ix: List<&2, List<&2, U32>>, pr: Nat, w: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{po, c}:
          srv.name(pr, w, po, read_name(ix, c))
    case Fail{e}:
      Fail{e}

def srv.w(ix: List<&2, List<&2, U32>>, pr: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{w, c}:
          srv.po(ix, pr, w, u16(c))
    case Fail{e}:
      Fail{e}

def rd.srv(ix: List<&2, List<&2, U32>>, r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{pr, c}:
          srv.w(ix, pr, u16(c))
    case Fail{e}:
      Fail{e}

def soa.mi(mn: M.Name(), rn: M.Name(), se: Nat, rf: Nat, rt: Nat, ex: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{mi, c}:
          rd.done(M.RSoa{mn, rn, se, rf, rt, ex, mi}, c)
    case Fail{e}:
      Fail{e}

def soa.ex(mn: M.Name(), rn: M.Name(), se: Nat, rf: Nat, rt: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{ex, c}:
          soa.mi(mn, rn, se, rf, rt, ex, u32(c))
    case Fail{e}:
      Fail{e}

def soa.rt(mn: M.Name(), rn: M.Name(), se: Nat, rf: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{rt, c}:
          soa.ex(mn, rn, se, rf, rt, u32(c))
    case Fail{e}:
      Fail{e}

def soa.rf(mn: M.Name(), rn: M.Name(), se: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{rf, c}:
          soa.rt(mn, rn, se, rf, u32(c))
    case Fail{e}:
      Fail{e}

def soa.se(mn: M.Name(), rn: M.Name(), r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{se, c}:
          soa.rf(mn, rn, se, u32(c))
    case Fail{e}:
      Fail{e}

def soa.rn(mn: M.Name(), r: Result<&2, &2, M.DecodeError, NameAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NameAt{rn, c}:
          soa.se(mn, rn, u32(c))
    case Fail{e}:
      Fail{e}

def rd.soa(ix: List<&2, List<&2, U32>>, r: Result<&2, &2, M.DecodeError, NameAt>) -> Result<&2, &2, M.DecodeError, DataAt>:
  match r:
    case Done{x}:
      match x:
        case NameAt{mn, c}:
          soa.rn(mn, read_name(ix, c))
    case Fail{e}:
      Fail{e}

# TXT: character-strings, each a length byte (0..255) and that many bytes.

type Txt is Data:
  TLen{acc: List<&2, List<&2, U32>>}                                # at a length byte
  TIn{more: Nat, cur: List<&2, U32>, acc: List<&2, List<&2, U32>>}  # 1 + more bytes to go
  TBad{error: M.DecodeError}

def txt.len(g: Maybe<&2, M.Got>, acc: List<&2, List<&2, U32>>) -> Txt:
  match g:
    case Some{x}:
      match x:
        case M.Got{v, r}:
          match v:
            case 0n:
              TLen{Nil{} <> acc}
            case 1n+p:
              TIn{p, Nil{}, acc}
    case None{}:
      TBad{M.BadRdata{}}

def txt.str(ok: Bool, s: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> Txt:
  match ok:
    case True{}:
      TLen{s <> acc}
    case False{}:
      TBad{M.BadRdata{}}

def txt.in(more: Nat, cur: List<&2, U32>, acc: List<&2, List<&2, U32>>, b: U32) -> Txt:
  match more:
    case 0n:
      +s = B.rev(U32, b <> cur, Nil{})
      txt.str(B.all_bytes(s), s, acc)
    case 1n+q:
      TIn{q, b <> cur, acc}

def txt.step(st: Txt, b: U32) -> Txt:
  match st:
    case TLen{acc}:
      txt.len(W.get_u8([b]), acc)
    case TIn{m, cur, acc}:
      txt.in(m, cur, acc, b)
    case TBad{e}:
      TBad{e}

# Every byte of the RDATA (a structural loop).
def txt.go(xs: List<&2, U32>, st: Txt) -> Txt:
  match xs:
    case Nil{}:
      st
    case Con{b, t}:
      txt.go(t, txt.step(st, b))

def txt.end(st: Txt, pos: Nat, h: Nat) -> Result<&2, &2, M.DecodeError, DataAt>:
  match st:
    case TLen{acc}:
      rd.done(M.RTxt{B.rev(List<&2, U32>, acc, Nil{})}, Cur{Nil{}, pos, h})
    case TIn{m, cur, acc}:
      Fail{M.BadRdata{}}
    case TBad{e}:
      Fail{e}

def rd.txt(c: Cur) -> Result<&2, &2, M.DecodeError, DataAt>:
  match c:
    case Cur{xs, pos, h}:
      txt.end(txt.go(xs, TLen{Nil{}}), pos, h)

# Raw

def raw.of(ok: Bool, xs: List<&2, U32>, pos: Nat, h: Nat) -> Result<&2, &2, M.DecodeError, DataAt>:
  match ok:
    case True{}:
      rd.done(M.RRaw{xs}, Cur{Nil{}, pos, h})
    case False{}:
      Fail{M.BadRdata{}}

def rd.raw(c: Cur) -> Result<&2, &2, M.DecodeError, DataAt>:
  match c:
    case Cur{+xs, pos, h}:
      raw.of(B.all_bytes(xs), xs, pos, h)

# The RDATA of a record of type t (the cursor holds exactly its bytes).
def rdata(+ix: List<&2, List<&2, U32>>, t: M.RType, c: Cur) -> Result<&2, &2, M.DecodeError, DataAt>:
  match t:
    case M.TA{}:
      rd.a(c)
    case M.TAAAA{}:
      rd.aaaa(c)
    case M.TNS{}:
      rd.name(read_name(ix, c))
    case M.TCNAME{}:
      rd.name(read_name(ix, c))
    case M.TPTR{}:
      rd.name(read_name(ix, c))
    case M.TMX{}:
      rd.mx(ix, u16(c))
    case M.TTXT{}:
      rd.txt(c)
    case M.TSOA{}:
      rd.soa(ix, read_name(ix, c))
    case M.TSRV{}:
      rd.srv(ix, u16(c))
    case _:
      rd.raw(c)

# Records
# -------

# k cells off xs, reversed onto acc, then the cells after them (a loop).
def take.go(k: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, Taken>:
  match k:
    case 0n:
      Some{Taken{B.rev(U32, acc, Nil{}), xs}}
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case Con{b, t}:
          take.go(p, t, b <> acc)

# Inside RDATA the bytes are bounded by RDLENGTH: running out is BadRdata.
def rdata_error(e: M.DecodeError) -> M.DecodeError:
  match e:
    case M.Short{}:
      M.BadRdata{}
    case _:
      e

def rec.fin(n: M.Name(), t: M.RType, cl: Nat, ttl: Nat, d: M.RData, left: List<&2, U32>, after: Cur) ->
  Result<&2, &2, M.DecodeError, RecAt>:
  match left:
    case Nil{}:
      Done{RecAt{M.Record{n, t, class_of(cl), ttl, d}, after}}
    case Con{b, rest}:
      Fail{M.BadRdata{}}

def rec.data(n: M.Name(), t: M.RType, cl: Nat, ttl: Nat, r: Result<&2, &2, M.DecodeError, DataAt>,
  after: List<&2, U32>, pos: Nat) -> Result<&2, &2, M.DecodeError, RecAt>:
  match r:
    case Done{x}:
      match x:
        case DataAt{d, c}:
          match c:
            case Cur{left, p, h}:
              rec.fin(n, t, cl, ttl, d, left, Cur{after, pos, h})
    case Fail{e}:
      Fail{rdata_error(e)}

def rec.take(ix: List<&2, List<&2, U32>>, n: M.Name(), +t: M.RType, cl: Nat, ttl: Nat, k: Nat,
  tk: Maybe<&2, Taken>, +pos: Nat, h: Nat) -> Result<&2, &2, M.DecodeError, RecAt>:
  match tk:
    case Some{x}:
      match x:
        case Taken{rd, after}:
          rec.data(n, t, cl, ttl, rdata(ix, t, Cur{rd, pos, h}), after, Nat.add(k, pos))
    case None{}:
      Fail{M.Short{}}

def rec.len(ix: List<&2, List<&2, U32>>, n: M.Name(), t: Nat, cl: Nat, ttl: Nat,
  r: Result<&2, &2, M.DecodeError, NumAt>) -> Result<&2, &2, M.DecodeError, RecAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{+k, c}:
          match c:
            case Cur{xs, pos, h}:
              rec.take(ix, n, type_of(t), cl, ttl, k, take.go(k, xs, Nil{}), pos, h)
    case Fail{e}:
      Fail{e}

def rec.ttl(ix: List<&2, List<&2, U32>>, n: M.Name(), t: Nat, cl: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, RecAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{ttl, c}:
          rec.len(ix, n, t, cl, ttl, u16(c))
    case Fail{e}:
      Fail{e}

def rec.cls(ix: List<&2, List<&2, U32>>, n: M.Name(), t: Nat, r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, RecAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{cl, c}:
          rec.ttl(ix, n, t, cl, u32(c))
    case Fail{e}:
      Fail{e}

def rec.typ(ix: List<&2, List<&2, U32>>, n: M.Name(), r: Result<&2, &2, M.DecodeError, NumAt>) ->
  Result<&2, &2, M.DecodeError, RecAt>:
  match r:
    case Done{x}:
      match x:
        case NumAt{t, c}:
          rec.cls(ix, n, t, u16(c))
    case Fail{e}:
      Fail{e}

def rec.name(ix: List<&2, List<&2, U32>>, r: Result<&2, &2, M.DecodeError, NameAt>) ->
  Result<&2, &2, M.DecodeError, RecAt>:
  match r:
    case Done{x}:
      match x:
        case NameAt{n, c}:
          rec.typ(ix, n, u16(c))
    case Fail{e}:
      Fail{e}

# One resource record.
def record(+ix: List<&2, List<&2, U32>>, c: Cur) -> Result<&2, &2, M.DecodeError, RecAt>:
  rec.name(ix, read_name(ix, c))

# The records read so far (reversed), or the first failure.
type RSt is Data:
  ROk{at: Cur, acc: List<&2, M.Record>}
  RErr{error: M.DecodeError}

def rs.next(r: Result<&2, &2, M.DecodeError, RecAt>, acc: List<&2, M.Record>) -> RSt:
  match r:
    case Done{x}:
      match x:
        case RecAt{rec, c}:
          ROk{c, rec <> acc}
    case Fail{e}:
      RErr{e}

def rs.step(ix: List<&2, List<&2, U32>>, st: RSt) -> RSt:
  match st:
    case ROk{c, acc}:
      rs.next(record(ix, c), acc)
    case RErr{e}:
      RErr{e}

# k more records (a loop; after a failure the steps do nothing).
def rs.go(k: Nat, +ix: List<&2, List<&2, U32>>, st: RSt) -> RSt:
  match k:
    case 0n:
      st
    case 1n+p:
      rs.go(p, ix, rs.step(ix, st))

def rs.end(st: RSt) -> Result<&2, &2, M.DecodeError, RsAt>:
  match st:
    case ROk{c, acc}:
      Done{RsAt{B.rev(M.Record, acc, Nil{}), c}}
    case RErr{e}:
      Fail{e}

# k records.
def records(k: Nat, ix: List<&2, List<&2, U32>>, c: Cur) -> Result<&2, &2, M.DecodeError, RsAt>:
  rs.end(rs.go(k, ix, ROk{c, Nil{}}))

# Messages
# --------

def m.end(m: M.Message, c: Cur) -> Result<&2, &2, M.DecodeError, M.Message>:
  match c:
    case Cur{rest, p, h}:
      match rest:
        case Nil{}:
          Done{m}
        case Con{b, t}:
          Fail{M.Trailing{}}

def m.ar(h: M.Header, qs: List<&2, M.Question>, an: List<&2, M.Record>, ns: List<&2, M.Record>,
  r: Result<&2, &2, M.DecodeError, RsAt>) -> Result<&2, &2, M.DecodeError, M.Message>:
  match r:
    case Done{x}:
      match x:
        case RsAt{ar, c}:
          m.end(M.Message{h, qs, an, ns, ar}, c)
    case Fail{e}:
      Fail{e}

def m.ns(+ix: List<&2, List<&2, U32>>, h: M.Header, qs: List<&2, M.Question>, an: List<&2, M.Record>, k: Nat,
  r: Result<&2, &2, M.DecodeError, RsAt>) -> Result<&2, &2, M.DecodeError, M.Message>:
  match r:
    case Done{x}:
      match x:
        case RsAt{ns, c}:
          m.ar(h, qs, an, ns, records(k, ix, c))
    case Fail{e}:
      Fail{e}

def m.an(+ix: List<&2, List<&2, U32>>, h: M.Header, qs: List<&2, M.Question>, kns: Nat, kar: Nat,
  r: Result<&2, &2, M.DecodeError, RsAt>) -> Result<&2, &2, M.DecodeError, M.Message>:
  match r:
    case Done{x}:
      match x:
        case RsAt{an, c}:
          m.ns(ix, h, qs, an, kar, records(kns, ix, c))
    case Fail{e}:
      Fail{e}

def m.qs(+ix: List<&2, List<&2, U32>>, h: M.Header, kan: Nat, kns: Nat, kar: Nat,
  r: Result<&2, &2, M.DecodeError, QsAt>) -> Result<&2, &2, M.DecodeError, M.Message>:
  match r:
    case Done{x}:
      match x:
        case QsAt{qs, c}:
          m.an(ix, h, qs, kns, kar, records(kan, ix, c))
    case Fail{e}:
      Fail{e}

def m.head(+ix: List<&2, List<&2, U32>>, r: Result<&2, &2, M.DecodeError, HeadAt>) ->
  Result<&2, &2, M.DecodeError, M.Message>:
  match r:
    case Done{x}:
      match x:
        case HeadAt{h, qd, an, ns, ar, c}:
          m.qs(ix, h, an, ns, ar, questions(qd, ix, c))
    case Fail{e}:
      Fail{e}

# The whole message (see the top of the file).
def message(+xs: List<&2, U32>) -> Result<&2, &2, M.DecodeError, M.Message>:
  m.head(index(xs), header(Cur{xs, 0n, NM.len(xs)}))
