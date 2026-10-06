import Base
import ./bytes.bend as B
import ./types.bend as M
import ./wire.bend as W

# DNS over TCP framing (RFC 1035 4.2.2, RFC 7766 8): every message is
# preceded by its length as a big-endian u16.
#
#   frame(xs)    W.put_u16(len(xs)) ++ xs; the caller keeps len(xs) <= 65535
#   init(max)    a reader expecting one frame whose message holds at most
#                max bytes (a longer announced length fails with TooLarge
#                as soon as the prefix is read)
#   step(s, b)   all the logic, one byte at a time
#   feed(s, xs)  plain structural fold: feed(s, []) = s and
#                feed(s, h <> t) = feed(step(s, h), t) (through feed.go,
#                the list first for the termination check)
#   done(s)      the frame is complete or the reader failed: stop reading
#   finish(s)    at the end of input: Done{Framed{message, rest}}, rest
#                being every byte after the frame; or why there is none
#
# The two prefix bytes are kept as they came and read once, by W.get_u16,
# when the second arrives (so the length goes through W, and a cell that is
# not a byte fails with NotByte). The message is accumulated reversed and
# reversed once when its last byte arrives; bytes after it are the rest,
# kept reversed and reversed by finish. A zero-length frame is complete as
# soon as its prefix is read.
#
# Laws:
#   feed_split: feed(feed(s, a), b) == feed(s, a ++ b)
#     (induction on a: feed.go(h <> t, s) = feed.go(t, step(s, h)))
#   roundtrip: len(xs) <= 65535 and len(xs) <= m =>
#     finish(feed(init(m), frame(xs) ++ rest)) == Done{Framed{xs, rest}}
#     Lemmas: W's u16 law at n = len(xs) (rest = []); len(xs) ==
#     List.length(xs) (len.go(xs, k) == Nat.add(List.length(xs), k));
#     for a nonempty xs, by induction with acc generalized:
#       feed.go(xs ++ rest, Body{List.length(xs) - 1, acc})
#         == feed.go(rest, Complete{B.rev(U32, B.rev(U32, xs, acc), Nil), Nil})
#     i.e. the body phase consumes exactly len(xs) bytes, then every byte is
#     rest: feed.go(rest, Complete{m, r}) == Complete{m, B.rev(U32, rest, r)};
#     and B.rev(U32, B.rev(U32, xs, Nil), Nil) == xs.
#
# NOTE (loops): feed.go and every list walk here are direct tail calls, so a
# 65535-byte frame (or a much longer hostile stream) is safe on the JS lane.

# A frame read whole: the message, and the bytes after it.
type Framed is Data:
  Framed{message: List<&2, U32>, rest: List<&2, U32>}

# Why no frame was read.
type FrameError is Data:
  Cut{}                     # the input ended inside the frame
  TooLarge{length: Nat}     # the announced length is over the reader's max
  NotByte{}                 # a prefix cell past 255

# The reader's state.
type Reader is Data:
  Prefix0{max: Nat}                                  # nothing read yet
  Prefix1{max: Nat, hi: U32}                         # the first prefix byte read
  Body{more: Nat, acc: List<&2, U32>}                # 1 + more bytes to go; acc reversed
  Complete{message: List<&2, U32>, rest: List<&2, U32>}  # rest reversed
  Failed{error: FrameError}                          # every later byte is ignored

# The number of cells in xs (a loop): len.go(xs, k) == List.length(xs) + k.
def len.go(xs: List<&2, U32>, k: Nat) -> Nat:
  match xs:
    case Nil{}:
      k
    case Con{h, t}:
      len.go(t, 1n+k)

def len(xs: List<&2, U32>) -> Nat:
  len.go(xs, 0n)

# The message with its length prefix; len(xs) <= 65535.
def frame(+xs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, W.put_u16(len(xs)), xs)

# Reading
# -------

def init(max: Nat) -> Reader:
  Prefix0{max}

def body.start(fits: Bool, +n: Nat) -> Reader:
  match fits:
    case True{}:
      match n:
        case 0n:
          Complete{Nil{}, Nil{}}
        case 1n+p:
          Body{p, Nil{}}
    case False{}:
      Failed{TooLarge{n}}

# The announced length, read from the prefix.
def length(max: Nat, g: Maybe<&2, M.Got>) -> Reader:
  match g:
    case Some{x}:
      match x:
        case M.Got{+n, r}:
          body.start(Nat.is_le(n, max), n)
    case None{}:
      Failed{NotByte{}}

# One message byte (more bytes follow it): the last one completes the frame.
def body.byte(more: Nat, acc: List<&2, U32>, b: U32) -> Reader:
  match more:
    case 0n:
      Complete{B.rev(U32, b <> acc, Nil{}), Nil{}}
    case 1n+p:
      Body{p, b <> acc}

def step(s: Reader, b: U32) -> Reader:
  match s:
    case Prefix0{max}:
      Prefix1{max, b}
    case Prefix1{max, hi}:
      length(max, W.get_u16([hi, b]))
    case Body{more, acc}:
      body.byte(more, acc, b)
    case Complete{m, rest}:
      Complete{m, b <> rest}
    case Failed{e}:
      Failed{e}

# Every byte of xs in order (a fold; the list first for termination).
def feed.go(xs: List<&2, U32>, s: Reader) -> Reader:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      feed.go(t, step(s, h))

def feed(s: Reader, xs: List<&2, U32>) -> Reader:
  feed.go(xs, s)

# The frame is complete or the reader failed: no more bytes are needed.
def done(s: Reader) -> Bool:
  match s:
    case Complete{m, r}:
      True{}
    case Failed{e}:
      True{}
    case _:
      False{}

# At the end of input.
def finish(s: Reader) -> Result<&2, &2, FrameError, Framed>:
  match s:
    case Complete{m, rest}:
      Done{Framed{m, B.rev(U32, rest, Nil{})}}
    case Failed{e}:
      Fail{e}
    case _:
      Fail{Cut{}}

# One frame read from xs, its message at most max bytes.
def read(max: Nat, xs: List<&2, U32>) -> Result<&2, &2, FrameError, Framed>:
  finish(feed(init(max), xs))
