import Base
import ./bytes.bend as B
import ./num.bend as N
import ./types.bend as M
import ./wire.bend as W

# Domain names (M.Name: a list of labels, each a byte list, root = []).
#
#   ok(n)          every label 1..63 cells, every cell a byte, and the wire
#                  form (wire_size) at most 255 bytes
#   wire(n)        each label as W.put_u8(length) ++ label, then W.put_u8(0)
#   lower(n)       ASCII 'A'..'Z' bytes to 'a'..'z'; every other byte kept
#   eq(a, b)       the same labels, ASCII case-insensitively
#   to_text(n)     labels joined by '.', no trailing dot; the root is "."
#   from_text(s)   the inverse: dotted text, one trailing dot allowed
#
# Text escapes (RFC 1035 5.1). to_text writes a byte as itself when it is
# visible ASCII other than '.' and '\'; '.' and '\' as "\." and "\\"; any
# other byte (space, controls, 0x7F, 0x80..0xFF) as "\DDD", three decimal
# digits (N.show, left-padded with '0'). from_text reads a visible ASCII char
# as its byte, "\DDD" (three digits, value <= 255) as that byte, and "\X"
# for any other ASCII char X as X's byte; an unescaped char that is not
# visible ASCII is BadChar, and a bad or cut escape BadEscape. So
#   ok(n) => from_text(to_text(n)) == Done{n}
# for every name, escapes included.
#
# from_text is three folds and a check, each total and small:
#   1. split.go: the chars, one Split step each, cut at every '.' that is not
#      escaped. The pieces come out reversed (the last piece first), each
#      piece still in escape syntax ('\' kept). A '\' takes the next char
#      into the piece whatever it is, so "\." does not cut.
#   2. trim: [".", "."]-shaped input (two empty pieces, the text ".") is the
#      root; otherwise one final empty piece (a trailing dot) is dropped when
#      there are at least two pieces.
#   3. labels.go: each piece through the escape decoder (unesc.go, one Unesc
#      step per char), consed in front: since the pieces are reversed, the
#      labels come out in order. When several pieces fail, the leftmost
#      piece's error is kept.
#   4. check: ok(n) gives Done{n}; else the first label that is empty
#      (EmptyLabel) or too long (LabelTooLong), else NameTooLong.
#
# NOTE (loops and specs): every def that walks a name, a label or a text is a
# loop (direct tail calls only), because the JS lane's stack holds only about
# 20-40k nested calls and a caller may build a name of any size. The plain
# structural recursion each loop computes is `<name>.spec`, for the proofs
# only. The equations, each by induction on the first list or string with the
# other arguments generalized (rev is B.rev, rgo is String.reverse.go):
#   len.go(xs, k) == Nat.add(List.length(xs), k)
#   labels_ok.go(n, b) == Bool.and(b, labels_ok.spec(n))
#   wire_size.go(n, k) == Nat.add(wire_size.spec(n), k)
#   rev(wire.rev(n, acc), ys) == rev(acc, List.append(wire.spec(n), ys))
#   rev(lower_label.rev(l, acc), ys) == rev(acc, List.append(lower_label.spec(l), ys))
#   rev(lower.rev(n, acc), ys) == rev(acc, List.append(lower.spec(n), ys))
#   rgo(escape.rev(l, acc), s) == rgo(acc, String.append(escape.spec(l), s))
#   rgo(tail.rev(n, acc), s) == rgo(acc, String.append(tail.spec(n), s))
# and so, at acc = Nil / SNil (with xs ++ [] == xs, s ++ "" == s):
#   len == List.length, labels_ok == labels_ok.spec, wire_size ==
#   wire_size.spec, wire == wire.spec (wire_onto(n, ys) == wire.spec(n) ++ ys),
#   lower_label == lower_label.spec, lower == lower.spec, to_text == to_text.spec.
# split.go, unesc.go, labels.go and eq.go are folds of a step over their
# input and are proven about directly (fold(a ++ b, s) == fold(b, fold(a, s))).
#
# Lemmas the laws need (besides the equations above):
#   - wire/decode: W's u8 law at each label length (<= 63 by ok).
#   - eq reflexive: Nat.is_eq(k, k) == True; symmetric: Nat.is_eq(a, b) ==
#     Nat.is_eq(b, a); both by induction on the Nat, then on the lists with
#     the Bool accumulator generalized.
#   - from_text(to_text(n)): per byte b of a label (is_byte(b) by ok),
#     unesc.go(escape1(b), UPlain{acc}) == UPlain{b <> acc}: for a literal
#     byte by computation (Char.to_u32(Char.from_u32(b)) == b is
#     definitional, and char_class(Char.from_u32(b)) is class(b)); for
#     "\DDD" by N's read(show(v)) law plus padding (or a closed enumeration
#     over the 256 byte values) and U32.from_nat(U32.to_nat(b)) == b for a
#     byte b; and split.go leaves each escaped label in one piece (no escape
#     form has an unescaped '.').

# Lengths
# -------

# k plus the number of cells in xs (a loop).
def len.go(xs: List<&2, U32>, k: Nat) -> Nat:
  match xs:
    case Nil{}:
      k
    case Con{h, t}:
      len.go(t, 1n+k)

# The number of cells in xs: len(xs) == List.length(xs).
def len(xs: List<&2, U32>) -> Nat:
  len.go(xs, 0n)

# Validity
# --------

# 1..63 cells, all bytes.
def label_ok(+l: List<&2, U32>) -> Bool:
  +k = len(l)
  Nat.is_le(1n, k) && Nat.is_le(k, 63n) && B.all_bytes(l)

def labels_ok.spec(n: M.Name()) -> Bool:
  match n:
    case Nil{}:
      True{}
    case Con{l, t}:
      label_ok(l) && labels_ok.spec(t)

def labels_ok.go(n: M.Name(), ok: Bool) -> Bool:
  match n:
    case Nil{}:
      ok
    case Con{l, t}:
      labels_ok.go(t, ok && label_ok(l))

# Every label is 1..63 bytes.
def labels_ok(n: M.Name()) -> Bool:
  labels_ok.go(n, True{})

# The bytes of n on the wire: one length byte and the cells per label, and
# the final zero.
def wire_size.spec(n: M.Name()) -> Nat:
  match n:
    case Nil{}:
      1n
    case Con{l, t}:
      Nat.add(1n+len(l), wire_size.spec(t))

def wire_size.go(n: M.Name(), k: Nat) -> Nat:
  match n:
    case Nil{}:
      1n+k
    case Con{l, t}:
      wire_size.go(t, Nat.add(1n+len(l), k))

def wire_size(n: M.Name()) -> Nat:
  wire_size.go(n, 0n)

# A name DNS can carry: labels 1..63 bytes, at most 255 bytes on the wire.
def ok(+n: M.Name()) -> Bool:
  labels_ok(n) && Nat.is_le(wire_size(n), 255n)

# Wire form
# ---------

def wire.spec(n: M.Name()) -> List<&2, U32>:
  match n:
    case Nil{}:
      W.put_u8(0n)
    case Con{+l, t}:
      List.append(&2, U32, W.put_u8(len(l)), List.append(&2, U32, l, wire.spec(t)))

# The wire bytes of n, reversed, prepended to acc (a loop).
def wire.rev(n: M.Name(), acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Nil{}:
      B.rev(U32, W.put_u8(0n), acc)
    case Con{+l, t}:
      wire.rev(t, B.rev(U32, l, B.rev(U32, W.put_u8(len(l)), acc)))

# The wire form of n (uncompressed), then ys.
def wire_onto(n: M.Name(), ys: List<&2, U32>) -> List<&2, U32>:
  B.rev(U32, wire.rev(n, Nil{}), ys)

# The wire form of n (uncompressed): wire(n) == wire.spec(n).
def wire(n: M.Name()) -> List<&2, U32>:
  wire_onto(n, Nil{})

# Case folding
# ------------
#
# NOTE (classifier use): as in bender-http's headers.bend, a byte b is an
# uppercase ASCII letter exactly when class(b) is a letter, class(b + 32) is
# a letter and class((b + 32) + 32) is not ('A'..'Z' go to 'a'..'z' and then
# to High; 'a'..'z' go to High at once). Lowering adds 32, so lowering twice
# is lowering once by definition.

def is_letter(k: B.Class) -> Bool:
  match k:
    case B.HexLetter{v}:
      True{}
    case B.Letter{}:
      True{}
    case _:
      False{}

def up32(x: U32) -> U32:
  (x + 32 : U32)

# 'A'..'Z'.
def is_upper(+b: U32) -> Bool:
  is_letter(B.class(b)) && is_letter(B.class(up32(b)))
    && Bool.not(is_letter(B.class(up32(up32(b)))))

def lower_byte.pick(up: Bool, +b: U32) -> U32:
  match up:
    case True{}:
      up32(b)
    case False{}:
      b

# 'A'..'Z' to 'a'..'z'; every other cell unchanged.
def lower_byte(+b: U32) -> U32:
  lower_byte.pick(is_upper(b), b)

def lower_label.spec(l: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      lower_byte(b) <> lower_label.spec(t)

def lower_label.rev(l: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Nil{}:
      acc
    case Con{b, t}:
      lower_label.rev(t, lower_byte(b) <> acc)

def lower_label(l: List<&2, U32>) -> List<&2, U32>:
  B.rev(U32, lower_label.rev(l, Nil{}), Nil{})

def lower.spec(n: M.Name()) -> M.Name():
  match n:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      lower_label(l) <> lower.spec(t)

def lower.rev(n: M.Name(), acc: M.Name()) -> M.Name():
  match n:
    case Nil{}:
      acc
    case Con{l, t}:
      lower.rev(t, lower_label(l) <> acc)

# Every label lowered (ASCII letters only).
def lower(n: M.Name()) -> M.Name():
  B.rev(List<&2, U32>, lower.rev(n, Nil{}), Nil{})

# Equality
# --------

# The same byte, ASCII case-insensitively (compared as numbers).
def byte_eq(+x: U32, +y: U32) -> Bool:
  Nat.is_eq(U32.to_nat(lower_byte(x)), U32.to_nat(lower_byte(y)))

# ok and the labels a and b are equal (a loop over both).
def label_eq.go(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xt} Con{y, yt}:
      label_eq.go(xt, yt, ok && byte_eq(x, y))
    case _ _:
      False{}

def label_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  label_eq.go(a, b, True{})

# ok and the names a and b are equal (a loop over both).
def eq.go(a: M.Name(), b: M.Name(), ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xt} Con{y, yt}:
      eq.go(xt, yt, ok && label_eq(x, y))
    case _ _:
      False{}

# The same name, ASCII case-insensitively (RFC 4343).
def eq(a: M.Name(), b: M.Name()) -> Bool:
  eq.go(a, b, True{})

# Text chars
# ----------
#
# NOTE (classifier use): text chars are classified once, by tchar, from
# B.char_class. '.' (a Tchar) and '\' (a Delim) are told apart from their
# classmates by Char.is_eq against the literal, inside those two branches
# only.
type TChar is Data:
  TDot{}        # .
  TBack{}       # \
  TDigit{}      # 0-9
  TVis{}        # any other visible ASCII char
  TSpace{}      # space and the ASCII controls (0x00-0x1F, 0x7F)
  TBad{}        # not ASCII

def tchar.pick(hit: Bool, k: TChar) -> TChar:
  match hit:
    case True{}:
      k
    case False{}:
      TVis{}

def tchar.of(k: B.Class, +c: Char) -> TChar:
  match k:
    case B.Digit{v}:
      TDigit{}
    case B.Tchar{}:
      tchar.pick(Char.is_eq(c, '.'), TDot{})
    case B.Delim{}:
      tchar.pick(Char.is_eq(c, '\\'), TBack{})
    case B.HexLetter{v}:
      TVis{}
    case B.Letter{}:
      TVis{}
    case B.Colon{}:
      TVis{}
    case B.Semi{}:
      TVis{}
    case B.Slash{}:
      TVis{}
    case B.High{}:
      TBad{}
    case B.Invalid{}:
      TBad{}
    case _:
      TSpace{}

def tchar(+c: Char) -> TChar:
  tchar.of(B.char_class(c), c)

# Showing
# -------

# A one-char string of the byte b.
def lit(b: U32) -> String:
  SCon{Char.from_u32(b), SNil{}}

# Decimal digits left-padded with '0' to three.
def pad3(s: String) -> String:
  match s:
    case SCon{a, SNil{}}:
      SCon{'0', SCon{'0', SCon{a, SNil{}}}}
    case SCon{a, SCon{b, SNil{}}}:
      SCon{'0', SCon{a, SCon{b, SNil{}}}}
    case _:
      s

# "\DDD" for the byte b (b <= 255).
def ddd(b: U32) -> String:
  SCon{'\\', pad3(N.show(U32.to_nat(b)))}

def escape1.mark(hit: Bool, +b: U32) -> String:
  match hit:
    case True{}:
      SCon{'\\', lit(b)}
    case False{}:
      lit(b)

def escape1.of(k: B.Class, +b: U32) -> String:
  match k:
    case B.Digit{v}:
      lit(b)
    case B.HexLetter{v}:
      lit(b)
    case B.Letter{}:
      lit(b)
    case B.Colon{}:
      lit(b)
    case B.Semi{}:
      lit(b)
    case B.Slash{}:
      lit(b)
    case B.Tchar{}:
      escape1.mark(Char.is_eq(Char.from_u32(b), '.'), b)
    case B.Delim{}:
      escape1.mark(Char.is_eq(Char.from_u32(b), '\\'), b)
    case B.Invalid{}:
      "\\999"
    case _:
      ddd(b)

# One byte as text: itself, "\." / "\\", or "\DDD". A cell past 255 (not a
# byte; never in an ok name) is "\999", which from_text refuses.
def escape1(+b: U32) -> String:
  escape1.of(B.class(b), b)

def escape.spec(l: List<&2, U32>) -> String:
  match l:
    case Nil{}:
      SNil{}
    case Con{b, t}:
      String.append(escape1(b), escape.spec(t))

# The text of l, reversed, prepended to acc (a loop).
def escape.rev(l: List<&2, U32>, acc: String) -> String:
  match l:
    case Nil{}:
      acc
    case Con{b, t}:
      escape.rev(t, String.reverse.go(escape1(b), acc))

# The labels after the first: each as '.' then its text.
def tail.spec(n: M.Name()) -> String:
  match n:
    case Nil{}:
      SNil{}
    case Con{l, t}:
      SCon{'.', String.append(escape.spec(l), tail.spec(t))}

def tail.rev(n: M.Name(), acc: String) -> String:
  match n:
    case Nil{}:
      acc
    case Con{l, t}:
      tail.rev(t, escape.rev(l, SCon{'.', acc}))

def to_text.spec(n: M.Name()) -> String:
  match n:
    case Nil{}:
      "."
    case Con{l, t}:
      String.append(escape.spec(l), tail.spec(t))

# The labels joined by '.', escaped; no trailing dot; the root is ".".
def to_text(n: M.Name()) -> String:
  match n:
    case Nil{}:
      "."
    case Con{l, t}:
      String.reverse(tail.rev(t, escape.rev(l, SNil{})))

# Reading: 1. cutting at unescaped dots
# -------------------------------------

# esc: the previous char was an unescaped '\'; cur: the piece so far,
# reversed; acc: the finished pieces, the newest first.
type Split is Data:
  Split{esc: Bool, cur: String, acc: List<&2, String>}

def split.char(esc: Bool, k: TChar, c: Char, cur: String, acc: List<&2, String>) -> Split:
  match esc k:
    case True{} _:
      Split{False{}, SCon{c, cur}, acc}
    case False{} TBack{}:
      Split{True{}, SCon{c, cur}, acc}
    case False{} TDot{}:
      Split{False{}, SNil{}, String.reverse(cur) <> acc}
    case False{} _:
      Split{False{}, SCon{c, cur}, acc}

def split.step(st: Split, +c: Char) -> Split:
  match st:
    case Split{e, cur, acc}:
      split.char(e, tchar(c), c, cur, acc)

# One split step per char (a fold).
def split.go(s: String, st: Split) -> Split:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      split.go(t, split.step(st, c))

def split.end(st: Split) -> List<&2, String>:
  match st:
    case Split{e, cur, acc}:
      String.reverse(cur) <> acc

# The pieces of s between unescaped dots, the last piece first.
def pieces(s: String) -> List<&2, String>:
  split.end(split.go(s, Split{False{}, SNil{}, Nil{}}))

# The text "." (pieces "", "") is the root; one trailing dot is dropped.
def trim(+ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Con{SNil{}, Con{SNil{}, Nil{}}}:
      Nil{}
    case Con{SNil{}, Con{p, t}}:
      p <> t
    case _:
      ps

# Reading: 2. escapes
# -------------------

# The bytes of a piece so far (reversed), and where an escape stands.
type Unesc is Data:
  UPlain{acc: List<&2, U32>}                      # between escapes
  UEsc{acc: List<&2, U32>}                        # after '\'
  UDig1{acc: List<&2, U32>, a: Char}              # after '\' and one digit
  UDig2{acc: List<&2, U32>, a: Char, b: Char}     # after '\' and two digits
  UBad{error: M.NameError}

def unesc.byte(ok: Bool, v: Nat, acc: List<&2, U32>) -> Unesc:
  match ok:
    case True{}:
      UPlain{U32.from_nat(v) <> acc}
    case False{}:
      UBad{M.BadEscape{}}

# The value of "\DDD": at most 255.
def unesc.ddd(m: Maybe<&2, Nat>, acc: List<&2, U32>) -> Unesc:
  match m:
    case Some{+v}:
      unesc.byte(Nat.is_le(v, 255n), v, acc)
    case None{}:
      UBad{M.BadEscape{}}

def unesc.plain(k: TChar, c: Char, acc: List<&2, U32>) -> Unesc:
  match k:
    case TBack{}:
      UEsc{acc}
    case TSpace{}:
      UBad{M.BadChar{}}
    case TBad{}:
      UBad{M.BadChar{}}
    case _:
      UPlain{Char.to_u32(c) <> acc}

def unesc.esc(k: TChar, c: Char, acc: List<&2, U32>) -> Unesc:
  match k:
    case TDigit{}:
      UDig1{acc, c}
    case TBad{}:
      UBad{M.BadChar{}}
    case _:
      UPlain{Char.to_u32(c) <> acc}

def unesc.dig1(k: TChar, c: Char, acc: List<&2, U32>, a: Char) -> Unesc:
  match k:
    case TDigit{}:
      UDig2{acc, a, c}
    case _:
      UBad{M.BadEscape{}}

def unesc.dig2(k: TChar, c: Char, acc: List<&2, U32>, a: Char, b: Char) -> Unesc:
  match k:
    case TDigit{}:
      unesc.ddd(N.read(SCon{a, SCon{b, SCon{c, SNil{}}}}), acc)
    case _:
      UBad{M.BadEscape{}}

def unesc.step(st: Unesc, +c: Char) -> Unesc:
  match st:
    case UPlain{acc}:
      unesc.plain(tchar(c), c, acc)
    case UEsc{acc}:
      unesc.esc(tchar(c), c, acc)
    case UDig1{acc, a}:
      unesc.dig1(tchar(c), c, acc, a)
    case UDig2{acc, a, b}:
      unesc.dig2(tchar(c), c, acc, a, b)
    case UBad{e}:
      UBad{e}

# One unesc step per char (a fold).
def unesc.go(s: String, st: Unesc) -> Unesc:
  match s:
    case SNil{}:
      st
    case SCon{c, t}:
      unesc.go(t, unesc.step(st, c))

def unesc.end(st: Unesc) -> Result<&2, &2, M.NameError, List<&2, U32>>:
  match st:
    case UPlain{acc}:
      Done{B.rev(U32, acc, Nil{})}
    case UBad{e}:
      Fail{e}
    case _:
      Fail{M.BadEscape{}}

# The bytes of one piece (escapes resolved).
def label_of(p: String) -> Result<&2, &2, M.NameError, List<&2, U32>>:
  unesc.end(unesc.go(p, UPlain{Nil{}}))

# Reading: 3. labels and the check
# --------------------------------

def labels.add(x: Result<&2, &2, M.NameError, List<&2, U32>>,
  r: Result<&2, &2, M.NameError, M.Name()>) -> Result<&2, &2, M.NameError, M.Name()>:
  match x r:
    case Done{l} Done{ls}:
      Done{l <> ls}
    case Done{l} Fail{e}:
      Fail{e}
    case Fail{e} _:
      Fail{e}

# The pieces (the last first) as labels consed onto r: in order.
def labels.go(ps: List<&2, String>, r: Result<&2, &2, M.NameError, M.Name()>) ->
  Result<&2, &2, M.NameError, M.Name()>:
  match ps:
    case Nil{}:
      r
    case Con{p, t}:
      labels.go(t, labels.add(label_of(p), r))

def why.label.pick(ok: Bool) -> Maybe<&2, M.NameError>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{M.LabelTooLong{}}

def why.label(k: Nat) -> Maybe<&2, M.NameError>:
  match k:
    case 0n:
      Some{M.EmptyLabel{}}
    case 1n+p:
      why.label.pick(Nat.is_le(1n+p, 63n))

def why.first(a: Maybe<&2, M.NameError>, b: Maybe<&2, M.NameError>) -> Maybe<&2, M.NameError>:
  match a:
    case Some{e}:
      Some{e}
    case None{}:
      b

# The first label's fault (empty, too long), else NameTooLong.
def why.go(n: M.Name(), found: Maybe<&2, M.NameError>) -> M.NameError:
  match n:
    case Nil{}:
      Maybe.default(&2, M.NameError, found, M.NameTooLong{})
    case Con{l, t}:
      why.go(t, why.first(found, why.label(len(l))))

def check.pick(good: Bool, +n: M.Name()) -> Result<&2, &2, M.NameError, M.Name()>:
  match good:
    case True{}:
      Done{n}
    case False{}:
      Fail{why.go(n, None{})}

def check(+n: M.Name()) -> Result<&2, &2, M.NameError, M.Name()>:
  check.pick(ok(n), n)

def from_text.check(r: Result<&2, &2, M.NameError, M.Name()>) -> Result<&2, &2, M.NameError, M.Name()>:
  match r:
    case Done{+n}:
      check(n)
    case Fail{e}:
      Fail{e}

# Dotted text to a name (see the top of the file); Done{n} only when ok(n).
def from_text(s: String) -> Result<&2, &2, M.NameError, M.Name()>:
  from_text.check(labels.go(trim(pieces(s)), Done{Nil{}}))
