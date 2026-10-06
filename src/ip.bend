import Base
import ./bytes.bend as B
import ./num.bend as N
import ./types.bend as M
import ./wire.bend as W

# IPv4 and IPv6 addresses as text.
#
#   show4(a, b, c, d)  "a.b.c.d", each octet N.show (no leading zeros)
#   parse4(s)          Some{RIpv4{a, b, c, d}} for a canonical dotted quad:
#                      exactly four pieces between dots, each one or more
#                      decimal digits, no leading zero (except "0" itself),
#                      value <= 255; None otherwise
#   show6(gs)          RFC 5952: each group N.hex_show (lowercase, no leading
#                      zeros), joined by ':', the longest run of two or more
#                      zero groups (the first such run on a tie) written "::"
#   parse6(s)          RFC 4291 2.2 text: eight groups of 1..4 hex digits
#                      (either case) separated by ':', or fewer around one
#                      "::" standing for one or more zero groups; the last
#                      32 bits may be written as a dotted quad (parse4), as
#                      in "::ffff:192.0.2.1". Some{RIpv6{8 groups}} or None.
#                      No zone index ("%eth0").
#
# Laws: a, b, c, d <= 255 => parse4(show4(a, b, c, d)) == Some{RIpv4{a, b, c, d}};
# for 8 groups each <= 65535, parse6(show6(gs)) == Some{RIpv6{gs}}.
#
# Pieces. Both parsers first cut the text into the pieces between separators
# with one fold (cut.go: one Cut step per char), which yields them reversed
# (the last piece first); parse4 then matches exactly four. Fold equations
# (by induction on the string, the state generalized):
#   cut.go(String.append(a, b), sep, st) == cut.go(b, sep, cut.go(a, sep, st))
#   no char of a is a separator =>
#     cut.go(a, sep, Cut{cur, acc}) == Cut{String.reverse.go(a, cur), acc}
# Every char of N.show(n) is a digit (class Digit), never '.' or ':'; with
# N's read(show(n)) law and "show(n) has no leading zero" (its most
# significant digit is nonzero for n >= 1: dec_inc never leaves a top 0),
# parse4(show4(..)) follows.
#
# NOTE (loops): every def walking the text or a group list is a loop (a
# direct tail call); hostile text of any length is safe on the JS lane.
# N.read / N.hex_read saturate, so a long digit run cannot overflow a Nat.
#
# NOTE (classifier use): chars are classified by B.char_class; '.' (a Tchar)
# is told from the other Tchars by Char.is_eq, in is_dot only. ':' has its
# own class (B.Colon).

# Chars
# -----

def is_dot.of(k: B.Class, +c: Char) -> Bool:
  match k:
    case B.Tchar{}:
      Char.is_eq(c, '.')
    case _:
      False{}

def is_dot(+c: Char) -> Bool:
  is_dot.of(B.char_class(c), c)

def is_colon.of(k: B.Class) -> Bool:
  match k:
    case B.Colon{}:
      True{}
    case _:
      False{}

def is_colon(+c: Char) -> Bool:
  is_colon.of(B.char_class(c))

def is_zero_digit(k: B.Class) -> Bool:
  match k:
    case B.Digit{v}:
      Nat.is_eq(v, 0n)
    case _:
      False{}

# Cutting text into pieces
# ------------------------

type Sep is Data:
  SepDot{}
  SepColon{}

def is_sep(sep: Sep, +c: Char) -> Bool:
  match sep:
    case SepDot{}:
      is_dot(c)
    case SepColon{}:
      is_colon(c)

# The piece so far (reversed), and the finished pieces (the newest first).
type Cut is Data:
  Cut{cur: String, acc: List<&2, String>}

def cut.char(hit: Bool, c: Char, cur: String, acc: List<&2, String>) -> Cut:
  match hit:
    case True{}:
      Cut{SNil{}, String.reverse(cur) <> acc}
    case False{}:
      Cut{SCon{c, cur}, acc}

def cut.step(+sep: Sep, st: Cut, +c: Char) -> Cut:
  match st:
    case Cut{cur, acc}:
      cut.char(is_sep(sep, c), c, cur, acc)

# One cut step per char (a fold).
def cut.go(s: String, +sep: Sep, st: Cut) -> Cut:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      cut.go(t, sep, cut.step(sep, st, c))

def cut.end(st: Cut) -> List<&2, String>:
  match st:
    case Cut{cur, acc}:
      String.reverse(cur) <> acc

# The pieces of s between separators, the last first: "" gives [""], and
# "a.b" gives ["b", "a"].
def cut(sep: Sep, s: String) -> List<&2, String>:
  cut.end(cut.go(s, sep, Cut{SNil{}, Nil{}}))

# IPv4
# ----

def show4(a: Nat, b: Nat, c: Nat, d: Nat) -> String:
  N.show(a) ++ "." ++ N.show(b) ++ "." ++ N.show(c) ++ "." ++ N.show(d)

# One char, or a first char other than '0'.
def no_lead_zero(s: String) -> Bool:
  match s:
    case SCon{c, SCon{d, r}}:
      Bool.not(is_zero_digit(B.char_class(c)))
    case _:
      True{}

def octet.of(m: Maybe<&2, Nat>, nlz: Bool) -> Maybe<&2, Nat>:
  match m nlz:
    case Some{+v} True{}:
      N.bound.pick(Nat.is_le(v, 255n), v)
    case _ _:
      None{}

# A decimal octet: digits, no leading zero, at most 255.
def octet(+p: String) -> Maybe<&2, Nat>:
  octet.of(N.read(p), no_lead_zero(p))

def quad(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>, d: Maybe<&2, Nat>) ->
  Maybe<&2, M.RData>:
  match a b c d:
    case Some{x} Some{y} Some{z} Some{w}:
      Some{M.RIpv4{x, y, z, w}}
    case _ _ _ _:
      None{}

# The pieces, the last first.
def quad.of(ps: List<&2, String>) -> Maybe<&2, M.RData>:
  match ps:
    case Con{d, Con{c, Con{b, Con{a, Nil{}}}}}:
      quad(octet(a), octet(b), octet(c), octet(d))
    case _:
      None{}

# A canonical dotted quad.
def parse4(s: String) -> Maybe<&2, M.RData>:
  quad.of(cut(SepDot{}, s))

def is_some_data(m: Maybe<&2, M.RData>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

# s is a canonical dotted quad.
def is_ipv4(s: String) -> Bool:
  is_some_data(parse4(s))

# IPv6: showing
# -------------

# Scanning for the longest zero run: the index i of the next group, the
# current run (start, length) and the best run so far (start, length).
type Run is Data:
  Run{i: Nat, cs: Nat, cl: Nat, bs: Nat, bl: Nat}

def run.best(longer: Bool, i: Nat, +cs: Nat, +cl: Nat, bs: Nat, bl: Nat) -> Run:
  match longer:
    case True{}:
      Run{1n+i, cs, cl, cs, cl}
    case False{}:
      Run{1n+i, cs, cl, bs, bl}

def run.zero(+i: Nat, cs: Nat, cl: Nat, +bs: Nat, +bl: Nat) -> Run:
  match cl:
    case 0n:
      run.best(Nat.is_lt(bl, 1n), i, i, 1n, bs, bl)
    case 1n+(+p):
      run.best(Nat.is_lt(bl, 2n+p), i, cs, 2n+p, bs, bl)

def run.step(r: Run, +g: Nat) -> Run:
  match r:
    case Run{i, cs, cl, bs, bl}:
      match g:
        case 0n:
          run.zero(i, cs, cl, bs, bl)
        case 1n+p:
          Run{1n+i, 0n, 0n, bs, bl}

def run.go(gs: List<&2, Nat>, r: Run) -> Run:
  match gs:
    case Nil{}:
      r
    case Con{g, t}:
      run.go(t, run.step(r, g))

# The groups joined by ':', each in hex, reversed, prepended to acc.
def hexes.go(gs: List<&2, Nat>, acc: String) -> String:
  match gs:
    case Nil{}:
      acc
    case Con{g, t}:
      hexes.go(t, String.reverse.go(N.hex_show(g), SCon{':', acc}))

# The groups joined by ':', each in hex.
def hexes(gs: List<&2, Nat>) -> String:
  match gs:
    case Nil{}:
      SNil{}
    case Con{g, t}:
      String.reverse(hexes.go(t, String.reverse(N.hex_show(g))))

# The first k groups (a loop; acc reversed).
def take.go(k: Nat, gs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      B.rev(Nat, acc, Nil{})
    case 1n+p:
      match gs:
        case Nil{}:
          B.rev(Nat, acc, Nil{})
        case Con{g, t}:
          take.go(p, t, g <> acc)

# All but the first k groups.
def drop(k: Nat, gs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      gs
    case 1n+p:
      match gs:
        case Nil{}:
          Nil{}
        case Con{g, t}:
          drop(p, t)

def show6.run(r: Run, +gs: List<&2, Nat>) -> String:
  match r:
    case Run{i, cs, cl, +bs, bl}:
      match bl:
        case 0n:
          hexes(gs)
        case 1n:
          hexes(gs)
        case 2n+p:
          hexes(take.go(bs, gs, Nil{})) ++ "::" ++ hexes(drop(Nat.add(bs, 2n+p), gs))

# RFC 5952 text of the groups (see the top of the file).
def show6(+gs: List<&2, Nat>) -> String:
  show6.run(run.go(gs, Run{0n, 0n, 0n, 0n, 0n}), gs)

# IPv6: parsing
# -------------

# Looking for the first "::". Before it: the text so far (reversed) and
# whether a ':' is pending (seen, not yet kept). After it: the text before
# it, and the text after it so far (reversed).
type Find is Data:
  Before{acc: String, colon: Bool}
  After{left: String, acc: String}

def find.before(colon: Bool, hit: Bool, c: Char, acc: String) -> Find:
  match colon hit:
    case True{} True{}:
      After{String.reverse(acc), SNil{}}
    case False{} True{}:
      Before{acc, True{}}
    case True{} False{}:
      Before{SCon{c, SCon{':', acc}}, False{}}
    case False{} False{}:
      Before{SCon{c, acc}, False{}}

def find.step(st: Find, +c: Char) -> Find:
  match st:
    case Before{acc, colon}:
      find.before(colon, is_colon(c), c, acc)
    case After{l, acc}:
      After{l, SCon{c, acc}}

def find.go(s: String, st: Find) -> Find:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      find.go(t, find.step(st, c))

# The text split at the first "::": (s, None) when there is none, else
# (before, Some{after}).
type Halves is Data:
  Halves{left: String, right: Maybe<&2, String>}

def find.end(st: Find) -> Halves:
  match st:
    case Before{acc, colon}:
      match colon:
        case True{}:
          Halves{String.reverse(SCon{':', acc}), None{}}
        case False{}:
          Halves{String.reverse(acc), None{}}
    case After{l, acc}:
      Halves{l, Some{String.reverse(acc)}}

def halves(s: String) -> Halves:
  find.end(find.go(s, Before{SNil{}, False{}}))

# At most four chars.
def short4(s: String) -> Bool:
  match s:
    case SCon{a, SCon{b, SCon{c, SCon{d, SCon{e, t}}}}}:
      False{}
    case _:
      True{}

def group.of(ok: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

# 1..4 hex digits.
def group(+p: String) -> Maybe<&2, Nat>:
  group.of(short4(p), N.hex_read(p))

def has_dot.go(s: String, found: Bool) -> Bool:
  match s:
    case SNil{}:
      found
    case SCon{c, t}:
      has_dot.go(t, found || is_dot(c))

# The groups of a list (reversed pieces), consed in front of acc: in order.
def groups.add(g: Maybe<&2, Nat>, acc: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match g acc:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

def groups.go(ps: List<&2, String>, acc: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match ps:
    case Nil{}:
      acc
    case Con{p, t}:
      groups.go(t, groups.add(group(p), acc))

# A dotted quad as the last two groups.
def quad_groups(m: Maybe<&2, M.RData>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case Some{q}:
      match q:
        case M.RIpv4{a, b, c, d}:
          Some{[W.join16(a, b), W.join16(c, d)]}
        case _:
          None{}
    case None{}:
      None{}

# The last piece: a dotted quad (two groups) when it has a dot and v4 is
# allowed, else one hex group.
def last.of(dot: Bool, +p: String) -> Maybe<&2, List<&2, Nat>>:
  match dot:
    case True{}:
      quad_groups(parse4(p))
    case False{}:
      groups.add(group(p), Some{Nil{}})

# The groups of one side's pieces (the last first). v4: the last piece may
# be a dotted quad.
def side.of(v4: Bool, ps: List<&2, String>) -> Maybe<&2, List<&2, Nat>>:
  match ps:
    case Con{+p, t}:
      groups.go(t, last.of(v4 && has_dot.go(p, False{}), p))
    case Nil{}:
      Some{Nil{}}

# The groups of one side of the text: "" holds none.
def side(v4: Bool, s: String) -> Maybe<&2, List<&2, Nat>>:
  match s:
    case SNil{}:
      Some{Nil{}}
    case SCon{c, t}:
      side.of(v4, cut(SepColon{}, SCon{c, t}))

# Count of a group list (a loop).
def count.go(gs: List<&2, Nat>, k: Nat) -> Nat:
  match gs:
    case Nil{}:
      k
    case Con{g, t}:
      count.go(t, 1n+k)

def zeros(k: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      0n <> zeros(p)

def eight.pick(ok: Bool, gs: List<&2, Nat>) -> Maybe<&2, M.RData>:
  match ok:
    case True{}:
      Some{M.RIpv6{gs}}
    case False{}:
      None{}

# Exactly eight groups.
def eight(m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, M.RData>:
  match m:
    case Some{+gs}:
      eight.pick(Nat.is_eq(count.go(gs, 0n), 8n), gs)
    case None{}:
      None{}

def fill.pick(ok: Bool, +k: Nat, l: List<&2, Nat>, r: List<&2, Nat>) -> Maybe<&2, M.RData>:
  match ok:
    case True{}:
      Some{M.RIpv6{List.append(&2, Nat, l, List.append(&2, Nat, zeros(Nat.sub(8n, k)), r))}}
    case False{}:
      None{}

# Both sides of a "::": at most seven groups between them, zeros between.
def fill(l: Maybe<&2, List<&2, Nat>>, r: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, M.RData>:
  match l r:
    case Some{+ls} Some{+rs}:
      fill.pick(Nat.is_le(Nat.add(count.go(ls, 0n), count.go(rs, 0n)), 7n),
        Nat.add(count.go(ls, 0n), count.go(rs, 0n)), ls, rs)
    case _ _:
      None{}

def parse6.of(h: Halves) -> Maybe<&2, M.RData>:
  match h:
    case Halves{l, r}:
      match r:
        case None{}:
          eight(side(True{}, l))
        case Some{rt}:
          fill(side(False{}, l), side(True{}, rt))

# RFC 4291 text (see the top of the file).
def parse6(s: String) -> Maybe<&2, M.RData>:
  parse6.of(halves(s))

# s is IPv6 text.
def is_ipv6(s: String) -> Bool:
  is_some_data(parse6(s))
