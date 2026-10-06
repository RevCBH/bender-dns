import Base
import ./bytes.bend as B
import ./types.bend as M

# Big-endian wire integers on byte lists: the only place a DNS number becomes
# bytes or bytes become a number.
#
#   put_u8(n)  = [n]                                  (n <= 255)
#   put_u16(n) = [n / 256, n % 256]                   (n <= 65535)
#   put_u32(n) = put_u16(n / 65536) ++ put_u16(n % 65536)   (n < 65536 * 65536)
#   get_*(xs)  = Some{Got{value, rest}} when xs starts with enough cells that
#                are all bytes (B.class is not Invalid); None otherwise.
#
# Every put is a fixed-length list literal (no append, no recursion), so
# `put_u16(n) ++ rest` reduces definitionally to `Con{hi, Con{lo, rest}}` and
# a get applied to it reduces to the byte tests and the join on symbolic
# cells. Numbers cross between Nat and U32 only through U32.from_nat /
# U32.to_nat (both native at runtime). The laws
#   n <= 255   => get_u8(put_u8(n) ++ rest)   == Some{Got{n, rest}}
#   n <= 65535 => get_u16(put_u16(n) ++ rest) == Some{Got{n, rest}}
#   n < 65536 * 65536 => get_u32(put_u32(n) ++ rest) == Some{Got{n, rest}}
# need three lemmas (none of them about this file):
#   (a) n <= 255 => U32.to_nat(U32.from_nat(n)) == n
#   (b) n <= 255 => is_byte(U32.from_nat(n)) == True
#       (both closed facts over 256 values: prove a Bool enumeration
#       `all k <= 255. P(k)` by {==}, then extract P(n) by induction)
#   (c) Nat.add(Nat.mul(Nat.div(n, d), d), Nat.mod(n, d)) == n and
#       Nat.mod(n, d) < d for d >= 1, and n < d * d => Nat.div(n, d) < d
#       (Nat.divmod.go by induction, the accumulators generalized)
# u16 is then (a), (b) at div(n, 256) and mod(n, 256), and (c) at d = 256;
# u32 is the u16 fact at div(n, 65536) and mod(n, 65536) (both <= 65535 by
# (c) at d = 65536), and (c) again.

# A cell is a byte: 0..255 (by the classifier, not by a comparison).
def is_byte(+b: U32) -> Bool:
  B.Class.is_byte(B.class(b))

# Joining
# -------

# The value of two big-endian bytes (hi, lo each <= 255).
def join16(hi: Nat, lo: Nat) -> Nat:
  Nat.add(Nat.mul(hi, 256n), lo)

# The value of two big-endian 16-bit halves (each <= 65535).
def join32(hi: Nat, lo: Nat) -> Nat:
  Nat.add(Nat.mul(hi, 65536n), lo)

# Putting
# -------

# One byte; n <= 255.
def put_u8(n: Nat) -> List<&2, U32>:
  [U32.from_nat(n)]

# Two bytes, most significant first, then ys; n <= 65535.
def put_u16_onto(+n: Nat, ys: List<&2, U32>) -> List<&2, U32>:
  Con{U32.from_nat(Nat.div(n, 256n)), Con{U32.from_nat(Nat.mod(n, 256n)), ys}}

# Two bytes, most significant first; n <= 65535.
def put_u16(+n: Nat) -> List<&2, U32>:
  put_u16_onto(n, Nil{})

# Four bytes, most significant first, then ys; n < 65536 * 65536.
def put_u32_onto(+n: Nat, ys: List<&2, U32>) -> List<&2, U32>:
  put_u16_onto(Nat.div(n, 65536n), put_u16_onto(Nat.mod(n, 65536n), ys))

# Four bytes, most significant first; n < 65536 * 65536.
def put_u32(+n: Nat) -> List<&2, U32>:
  put_u32_onto(n, Nil{})

# Getting
# -------

def got(ok: Bool, value: Nat, rest: List<&2, U32>) -> Maybe<&2, M.Got>:
  match ok:
    case True{}:
      Some{M.Got{value, rest}}
    case False{}:
      None{}

# The first cell as a number, and the cells after it.
def get_u8(xs: List<&2, U32>) -> Maybe<&2, M.Got>:
  match xs:
    case Con{+a, t}:
      got(is_byte(a), U32.to_nat(a), t)
    case Nil{}:
      None{}

# The first two cells as a big-endian number, and the cells after them.
def get_u16(xs: List<&2, U32>) -> Maybe<&2, M.Got>:
  match xs:
    case Con{+a, Con{+b, t}}:
      got(is_byte(a) && is_byte(b), join16(U32.to_nat(a), U32.to_nat(b)), t)
    case _:
      None{}

# The first four cells as a big-endian number, and the cells after them.
def get_u32(xs: List<&2, U32>) -> Maybe<&2, M.Got>:
  match xs:
    case Con{+a, Con{+b, Con{+c, Con{+d, t}}}}:
      got(is_byte(a) && is_byte(b) && is_byte(c) && is_byte(d),
        join32(join16(U32.to_nat(a), U32.to_nat(b)), join16(U32.to_nat(c), U32.to_nat(d))), t)
    case _:
      None{}
