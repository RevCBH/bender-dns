# Laws 3, 4 and 5: big-endian wire integers read back as written.
#
# Exported lemmas (for the message and frame provers):
#   U32 (structural; never computes with a large literal):
#     nat_cmp_word(m, a, b)  Nat.cmp(to_nat a, to_nat b) == Word.cmp(m, a, b)
#     notmax / inc_to_nat    a word below another is not all ones; inc adds one
#     u32_to_from(n, h)      n <= 255 => U32.to_nat(U32.from_nat(n)) == n
#     u32_lt256(n, h)        n <= 255 => U32.is_lt(U32.from_nat(n), 256) == True
#     is_byte_of_lt(b, h)    U32.is_lt(b, 256) == True => W.is_byte(b) == True
#     byte_from_nat(n, h)    n <= 255 => W.is_byte(U32.from_nat(n)) == True
#   divmod (Nat.divmod.go by induction, accumulators generalized):
#     divmod_eq(n, b)        div(n, 1+b) * (1+b) + mod(n, 1+b) == n
#     mod_le(n, b)           mod(n, 1+b) <= b
#     div_mono(a, c, b, h)   a <= c => div(a, 1+b) <= div(c, 1+b)
#     mod256_le, div256_le (n <= 65535), mod65536_le
#   wire:
#     u16_hi_byte, u16_lo_byte, u16_join   the two cells of x <= 65535
#     u8_get_put, u16_get_put, u32_get_put the laws, with +params
# Hypotheses are {Nat.is_le(n, k) == True{} : Bool}, as in LAWS.bend.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/types.bend as M
import ../src/wire.bend as W

# Bool facts
# ----------

def wbdisc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def wfalse_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : wbdisc(_)
  Unit{}

def wtrue_false(e: {True{} == False{} : Bool}) -> Empty:
  wfalse_true(Equal.sym(Bool, True{}, False{}, e))

# Nat order
# ---------

def le_zero_any(k: Nat) -> {Cmp.is_le(Nat.cmp(0n, k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++q:
      {==}

# is_le(1+p, k) is is_lt(p, k).
def le_succ_is_lt(p: Nat, k: Nat) -> {Cmp.is_le(Nat.cmp(1n+p, k)) == Cmp.is_lt(Nat.cmp(p, k)) : Bool}:
  match p k:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      le_zero_any(q)
    case 1n++pp 0n:
      {==}
    case 1n++pp 1n++q:
      le_succ_is_lt(pp, q)

def lt_zero_false(n: Nat) -> {Cmp.is_lt(Nat.cmp(n, 0n)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++r:
      {==}

# is_lt(n, 1+k) is is_le(n, k).
def lt_succ_is_le(n: Nat, k: Nat) -> {Cmp.is_lt(Nat.cmp(n, 1n+k)) == Cmp.is_le(Nat.cmp(n, k)) : Bool}:
  match n k:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++np 0n:
      lt_zero_false(np)
    case 1n++np 1n++q:
      lt_succ_is_le(np, q)

def le_of_succ_le(p: Nat, k: Nat, h: {Nat.is_le(1n+p, k) == True{} : Bool}) -> {Nat.is_le(p, k) == True{} : Bool}:
  match p k:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++pp 0n:
      Empty.absurd({Nat.is_le(1n+pp, 0n) == True{} : Bool}, wfalse_true(h))
    case 1n++pp 1n++q:
      le_of_succ_le(pp, q, h)

# Words
# -----

# The value of a low bit b under the value x of the higher bits.
def bitn(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(x)
    case True{}:
      1n+Nat.double(x)

def dbl_cmp(ab: Bool, bb: Bool, x: Nat, y: Nat) -> {Nat.cmp(bitn(ab, x), bitn(bb, y)) == Word.cmp.fin(ab, bb, Nat.cmp(x, y)) : Cmp}:
  match ab bb x y:
    case False{} False{} 0n 0n:
      {==}
    case False{} False{} 0n 1n++yp:
      {==}
    case False{} False{} 1n++xp 0n:
      {==}
    case False{} False{} 1n++xp 1n++yp:
      dbl_cmp(False{}, False{}, xp, yp)
    case False{} True{} 0n 0n:
      {==}
    case False{} True{} 0n 1n++yp:
      {==}
    case False{} True{} 1n++xp 0n:
      {==}
    case False{} True{} 1n++xp 1n++yp:
      dbl_cmp(False{}, True{}, xp, yp)
    case True{} False{} 0n 0n:
      {==}
    case True{} False{} 0n 1n++yp:
      {==}
    case True{} False{} 1n++xp 0n:
      {==}
    case True{} False{} 1n++xp 1n++yp:
      dbl_cmp(True{}, False{}, xp, yp)
    case True{} True{} 0n 0n:
      {==}
    case True{} True{} 0n 1n++yp:
      {==}
    case True{} True{} 1n++xp 0n:
      {==}
    case True{} True{} 1n++xp 1n++yp:
      dbl_cmp(True{}, True{}, xp, yp)

# Word.cmp is Nat.cmp of the values.
def nat_cmp_word(m: Nat, a: Word(m), b: Word(m)) -> {Nat.cmp(Word.to_nat(m, a), Word.to_nat(m, b)) == Word.cmp(m, a, b) : Cmp}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %nat_cmp_word(p, at, bt) : {Nat.cmp(Word.to_nat(1n+p, WCon{False{}, at}), Word.to_nat(1n+p, WCon{False{}, bt})) == Word.cmp.fin(False{}, False{}, _) : Cmp}
          dbl_cmp(False{}, False{}, Word.to_nat(p, at), Word.to_nat(p, bt))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          %nat_cmp_word(p, at, bt) : {Nat.cmp(Word.to_nat(1n+p, WCon{False{}, at}), Word.to_nat(1n+p, WCon{True{}, bt})) == Word.cmp.fin(False{}, True{}, _) : Cmp}
          dbl_cmp(False{}, True{}, Word.to_nat(p, at), Word.to_nat(p, bt))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          %nat_cmp_word(p, at, bt) : {Nat.cmp(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{False{}, bt})) == Word.cmp.fin(True{}, False{}, _) : Cmp}
          dbl_cmp(True{}, False{}, Word.to_nat(p, at), Word.to_nat(p, bt))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %nat_cmp_word(p, at, bt) : {Nat.cmp(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{True{}, bt})) == Word.cmp.fin(True{}, True{}, _) : Cmp}
          dbl_cmp(True{}, True{}, Word.to_nat(p, at), Word.to_nat(p, bt))

# All bits set.
def wmax(m: Nat, w: Word(m)) -> Bool:
  match m:
    case 0n:
      True{}
    case 1n++p:
      match w:
        case WCon{False{}, t}:
          False{}
        case WCon{True{}, +t}:
          wmax(p, t)

def fin_lt(c: Cmp, vb: Bool, h: {Cmp.is_lt(Word.cmp.fin(True{}, vb, c)) == True{} : Bool}) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c vb:
    case LT{} False{}:
      {==}
    case LT{} True{}:
      {==}
    case EQ{} False{}:
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, wfalse_true(h))
    case EQ{} True{}:
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, wfalse_true(h))
    case GT{} False{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, wfalse_true(h))
    case GT{} True{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, wfalse_true(h))

# A word below another is not all ones.
def notmax(m: Nat, w: Word(m), v: Word(m), h: {Cmp.is_lt(Word.cmp(m, w, v)) == True{} : Bool}) -> {wmax(m, w) == False{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({wmax(0n, w) == False{} : Bool}, wfalse_true(h))
    case 1n++p:
      match w v:
        case WCon{False{}, +wt} WCon{vb, +vt}:
          {==}
        case WCon{True{}, +wt} WCon{vb, +vt}:
          notmax(p, wt, vt, fin_lt(Word.cmp(p, wt, vt), vb, h))

# Incrementing a word that is not all ones adds one to its value.
def inc_to_nat(m: Nat, w: Word(m), h: {wmax(m, w) == False{} : Bool}) -> {Word.to_nat(m, Word.inc(m, w)) == 1n+Word.to_nat(m, w) : Nat}:
  match m:
    case 0n:
      Empty.absurd({Word.to_nat(0n, Word.inc(0n, w)) == 1n+Word.to_nat(0n, w) : Nat}, wtrue_false(h))
    case 1n++p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Nat, Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t), inc_to_nat(p, t, h)) : {Nat.double(_) == 2n+Nat.double(Word.to_nat(p, t)) : Nat}
          {==}

# U32
# ---

def u32w(u: U32) -> Word(32n):
  match u:
    case U32{w}:
      w

def u32_eta(u: U32) -> {U32{u32w(u)} == u : U32}:
  match u:
    case U32{w}:
      {==}

def u32w_inc(u: U32) -> {Word.inc(32n, u32w(u)) == u32w(U32.inc(u)) : Word(32n)}:
  match u:
    case U32{w}:
      {==}

def wn(n: Nat) -> Word(32n):
  u32w(U32.from_nat(n))

def word_lt255(p: Nat, ih: {Word.to_nat(32n, wn(p)) == p : Nat}, hp: {Cmp.is_lt(Nat.cmp(p, 255n)) == True{} : Bool}) -> {Cmp.is_lt(Word.cmp(32n, wn(p), u32w(255))) == True{} : Bool}:
  %nat_cmp_word(32n, wn(p), u32w(255)) : {Cmp.is_lt(_) == True{} : Bool}
  %Equal.sym(Nat, Word.to_nat(32n, wn(p)), p, ih) : {Cmp.is_lt(Nat.cmp(_, Word.to_nat(32n, u32w(255)))) == True{} : Bool}
  hp

def succ_le_lt(p: Nat, k: Nat, h: {Nat.is_le(1n+p, k) == True{} : Bool}) -> {Cmp.is_lt(Nat.cmp(p, k)) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_lt(Nat.cmp(p, k)), Cmp.is_le(Nat.cmp(1n+p, k)), True{},
    Equal.sym(Bool, Cmp.is_le(Nat.cmp(1n+p, k)), Cmp.is_lt(Nat.cmp(p, k)), le_succ_is_lt(p, k)), h)

# Below 256 the word of from_nat(n) has value n.
def word_to_from(n: Nat, +h: {Nat.is_le(n, 255n) == True{} : Bool}) -> {Word.to_nat(32n, wn(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %u32w_inc(U32.from_nat(p)) : {Word.to_nat(32n, _) == 1n+p : Nat}
      %word_to_from(p, le_of_succ_le(p, 255n, h)) : {Word.to_nat(32n, Word.inc(32n, wn(p))) == 1n+_ : Nat}
      inc_to_nat(32n, wn(p), notmax(32n, wn(p), u32w(255),
    word_lt255(p, word_to_from(p, le_of_succ_le(p, 255n, h)), succ_le_lt(p, 255n, h))))

def pick_byte(c: Bool, x: B.Class, y: B.Class, hx: {B.Class.is_byte(x) == True{} : Bool}, hy: {B.Class.is_byte(y) == True{} : Bool}) -> {B.Class.is_byte(Bool.pick(B.Class, c, x, y)) == True{} : Bool}:
  match c:
    case False{}:
      hy
    case True{}:
      hx

def visible_byte(+b: U32) -> {B.Class.is_byte(B.class.visible(b)) == True{} : Bool}:
  pick_byte(B.in_range(b, 48, 57), B.Digit{U32.to_nat((b - 48 : U32))}, Bool.pick(B.Class, B.in_range(b, 97, 102), B.HexLetter{U32.to_nat((b - 87 : U32))}, Bool.pick(B.Class, B.in_range(b, 65, 70), B.HexLetter{U32.to_nat((b - 55 : U32))}, Bool.pick(B.Class, B.in_range(b, 97, 122) || B.in_range(b, 65, 90), B.Letter{}, Bool.pick(B.Class, B.is_tchar_mark(b), B.Tchar{}, B.Delim{})))), {==},
    pick_byte(B.in_range(b, 97, 102), B.HexLetter{U32.to_nat((b - 87 : U32))}, Bool.pick(B.Class, B.in_range(b, 65, 70), B.HexLetter{U32.to_nat((b - 55 : U32))}, Bool.pick(B.Class, B.in_range(b, 97, 122) || B.in_range(b, 65, 90), B.Letter{}, Bool.pick(B.Class, B.is_tchar_mark(b), B.Tchar{}, B.Delim{}))), {==},
    pick_byte(B.in_range(b, 65, 70), B.HexLetter{U32.to_nat((b - 55 : U32))}, Bool.pick(B.Class, B.in_range(b, 97, 122) || B.in_range(b, 65, 90), B.Letter{}, Bool.pick(B.Class, B.is_tchar_mark(b), B.Tchar{}, B.Delim{})), {==},
    pick_byte(B.in_range(b, 97, 122) || B.in_range(b, 65, 90), B.Letter{}, Bool.pick(B.Class, B.is_tchar_mark(b), B.Tchar{}, B.Delim{}), {==},
    pick_byte(B.is_tchar_mark(b), B.Tchar{}, B.Delim{}, {==},
    {==})))))

def ascii_byte(+b: U32) -> {B.Class.is_byte(B.class.ascii(b)) == True{} : Bool}:
  pick_byte(U32.is_eq(b, 13), B.Cr{}, Bool.pick(B.Class, U32.is_eq(b, 10), B.Lf{}, Bool.pick(B.Class, U32.is_eq(b, 9), B.Htab{}, Bool.pick(B.Class, U32.is_eq(b, 32), B.Sp{}, Bool.pick(B.Class, U32.is_eq(b, 58), B.Colon{}, Bool.pick(B.Class, U32.is_eq(b, 59), B.Semi{}, Bool.pick(B.Class, U32.is_eq(b, 47), B.Slash{}, Bool.pick(B.Class, U32.is_lt(b, 32) || U32.is_eq(b, 127), B.Ctl{}, B.class.visible(b)))))))), {==},
    pick_byte(U32.is_eq(b, 10), B.Lf{}, Bool.pick(B.Class, U32.is_eq(b, 9), B.Htab{}, Bool.pick(B.Class, U32.is_eq(b, 32), B.Sp{}, Bool.pick(B.Class, U32.is_eq(b, 58), B.Colon{}, Bool.pick(B.Class, U32.is_eq(b, 59), B.Semi{}, Bool.pick(B.Class, U32.is_eq(b, 47), B.Slash{}, Bool.pick(B.Class, U32.is_lt(b, 32) || U32.is_eq(b, 127), B.Ctl{}, B.class.visible(b))))))), {==},
    pick_byte(U32.is_eq(b, 9), B.Htab{}, Bool.pick(B.Class, U32.is_eq(b, 32), B.Sp{}, Bool.pick(B.Class, U32.is_eq(b, 58), B.Colon{}, Bool.pick(B.Class, U32.is_eq(b, 59), B.Semi{}, Bool.pick(B.Class, U32.is_eq(b, 47), B.Slash{}, Bool.pick(B.Class, U32.is_lt(b, 32) || U32.is_eq(b, 127), B.Ctl{}, B.class.visible(b)))))), {==},
    pick_byte(U32.is_eq(b, 32), B.Sp{}, Bool.pick(B.Class, U32.is_eq(b, 58), B.Colon{}, Bool.pick(B.Class, U32.is_eq(b, 59), B.Semi{}, Bool.pick(B.Class, U32.is_eq(b, 47), B.Slash{}, Bool.pick(B.Class, U32.is_lt(b, 32) || U32.is_eq(b, 127), B.Ctl{}, B.class.visible(b))))), {==},
    pick_byte(U32.is_eq(b, 58), B.Colon{}, Bool.pick(B.Class, U32.is_eq(b, 59), B.Semi{}, Bool.pick(B.Class, U32.is_eq(b, 47), B.Slash{}, Bool.pick(B.Class, U32.is_lt(b, 32) || U32.is_eq(b, 127), B.Ctl{}, B.class.visible(b)))), {==},
    pick_byte(U32.is_eq(b, 59), B.Semi{}, Bool.pick(B.Class, U32.is_eq(b, 47), B.Slash{}, Bool.pick(B.Class, U32.is_lt(b, 32) || U32.is_eq(b, 127), B.Ctl{}, B.class.visible(b))), {==},
    pick_byte(U32.is_eq(b, 47), B.Slash{}, Bool.pick(B.Class, U32.is_lt(b, 32) || U32.is_eq(b, 127), B.Ctl{}, B.class.visible(b)), {==},
    pick_byte(U32.is_lt(b, 32) || U32.is_eq(b, 127), B.Ctl{}, B.class.visible(b), {==},
    visible_byte(b)))))))))

# A cell below 256 is a byte.
def is_byte_of_lt(+b: U32, h: {U32.is_lt(b, 256) == True{} : Bool}) -> {W.is_byte(b) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_lt(b, 256), True{}, h) : {B.Class.is_byte(Bool.pick(B.Class, _, Bool.pick(B.Class, U32.is_lt(b, 128), B.class.ascii(b), B.High{}), B.Invalid{})) == True{} : Bool}
  pick_byte(U32.is_lt(b, 128), B.class.ascii(b), B.High{}, ascii_byte(b), {==})

# (a) n <= 255 => U32.to_nat(U32.from_nat(n)) == n
def u32_to_from(+n: Nat, h: {Nat.is_le(n, 255n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(n)) == n : Nat}:
  %u32_eta(U32.from_nat(n)) : {U32.to_nat(_) == n : Nat}
  word_to_from(n, h)

def u32_lt256(+n: Nat, +h: {Nat.is_le(n, 255n) == True{} : Bool}) -> {U32.is_lt(U32.from_nat(n), 256) == True{} : Bool}:
  %u32_eta(U32.from_nat(n)) : {U32.is_lt(_, 256) == True{} : Bool}
  %nat_cmp_word(32n, wn(n), u32w(256)) : {Cmp.is_lt(_) == True{} : Bool}
  %Equal.sym(Nat, Word.to_nat(32n, wn(n)), n, word_to_from(n, h)) : {Cmp.is_lt(Nat.cmp(_, Word.to_nat(32n, u32w(256)))) == True{} : Bool}
  Equal.trans(Bool, Cmp.is_lt(Nat.cmp(n, 256n)), Cmp.is_le(Nat.cmp(n, 255n)), True{}, lt_succ_is_le(n, 255n), h)

# (b) n <= 255 => W.is_byte(U32.from_nat(n)) == True
def byte_from_nat(+n: Nat, h: {Nat.is_le(n, 255n) == True{} : Bool}) -> {W.is_byte(U32.from_nat(n)) == True{} : Bool}:
  is_byte_of_lt(U32.from_nat(n), u32_lt256(n, h))

# Nat arithmetic
# --------------

def wadd_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %wadd_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def wadd_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %wadd_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def wadd_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, wadd_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), wadd_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %wadd_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def wle_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      wle_refl(p)

def wle_succ(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, wfalse_true(h))
    case 1n++p 1n++q:
      wle_succ(p, q, h)

def wle_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n++r:
      {==}
    case 0n 1n++q 0n:
      {==}
    case 0n 1n++q 1n++r:
      {==}
    case 1n++p 0n 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, wfalse_true(h1))
    case 1n++p 0n 1n++r:
      Empty.absurd({Nat.is_le(1n+p, 1n+r) == True{} : Bool}, wfalse_true(h1))
    case 1n++p 1n++q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, wfalse_true(h2))
    case 1n++p 1n++q 1n++r:
      wle_trans(p, q, r, h1, h2)

def le_add_l(m: Nat, +r: Nat) -> {Nat.is_le(r, Nat.add(m, r)) == True{} : Bool}:
  match m:
    case 0n:
      wle_refl(r)
    case 1n++mp:
      wle_succ(r, Nat.add(mp, r), le_add_l(mp, r))

# Division and remainder
# ----------------------
#
# Nat.divmod(n, 1+b) runs Nat.divmod.go(n, b, 0, 0); go(n, m, d, r) keeps
# m + r == b (r counts up to b, m down to 0) and d the quotient so far.

# The value q * (1+b) + r' of go's result (q, r').
def dmv(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), 1n+b), Nat.mod.fin(Nat.divmod.go(n, m, d, r)))

def dm_arith_carry(np: Nat, +dd: Nat, +b: Nat, +r: Nat, h: {r == b : Nat}) -> {Nat.add(np, Nat.add(Nat.add(1n+b, dd), 0n)) == 1n+Nat.add(np, Nat.add(dd, r)) : Nat}:
  %Equal.sym(Nat, r, b, h) : {Nat.add(np, Nat.add(Nat.add(1n+b, dd), 0n)) == 1n+Nat.add(np, Nat.add(dd, _)) : Nat}
  %wadd_comm(b, dd) : {Nat.add(np, Nat.add(Nat.add(1n+b, dd), 0n)) == 1n+Nat.add(np, _) : Nat}
  %wadd_zero(Nat.add(b, dd)) : {Nat.add(np, Nat.add(Nat.add(1n+b, dd), 0n)) == 1n+Nat.add(np, _) : Nat}
  wadd_succ(np, Nat.add(Nat.add(b, dd), 0n))

def dm_arith_step(np: Nat, +dd: Nat, +r: Nat) -> {Nat.add(np, Nat.add(dd, 1n+r)) == 1n+Nat.add(np, Nat.add(dd, r)) : Nat}:
  %Equal.sym(Nat, Nat.add(dd, 1n+r), 1n+Nat.add(dd, r), wadd_succ(dd, r)) : {Nat.add(np, _) == 1n+Nat.add(np, Nat.add(dd, r)) : Nat}
  wadd_succ(np, Nat.add(dd, r))

# q * (1+b) + r' == n + d * (1+b) + r, for (q, r') = go(n, m, d, r) and m + r == b.
def dm_go_eq(n: Nat, +m: Nat, +d: Nat, +r: Nat, +b: Nat, +h: {Nat.add(m, r) == b : Nat}) -> {dmv(n, m, d, r, b) == Nat.add(n, Nat.add(Nat.mul(d, 1n+b), r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++np:
      match m:
        case 0n:
          Equal.trans(Nat, dmv(np, r, 1n+d, 0n, b), Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+b), 0n)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)),
            dm_go_eq(np, r, 1n+d, 0n, b, Equal.trans(Nat, Nat.add(r, 0n), r, b, wadd_zero(r), h)),
            dm_arith_carry(np, Nat.mul(d, 1n+b), b, r, h))
        case 1n++mp:
          Equal.trans(Nat, dmv(np, mp, d, 1n+r, b), Nat.add(np, Nat.add(Nat.mul(d, 1n+b), 1n+r)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)),
            dm_go_eq(np, mp, d, 1n+r, b, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), b, wadd_succ(mp, r), h)),
            dm_arith_step(np, Nat.mul(d, 1n+b), r))

# The remainder of go is at most b.
def dm_go_mod_le(n: Nat, +m: Nat, +d: Nat, +r: Nat, +b: Nat, +h: {Nat.add(m, r) == b : Nat}) -> {Nat.is_le(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), b) == True{} : Bool}:
  match n:
    case 0n:
      %h : {Nat.is_le(r, _) == True{} : Bool}
      le_add_l(m, r)
    case 1n++np:
      match m:
        case 0n:
          dm_go_mod_le(np, r, 1n+d, 0n, b, Equal.trans(Nat, Nat.add(r, 0n), r, b, wadd_zero(r), h))
        case 1n++mp:
          dm_go_mod_le(np, mp, d, 1n+r, b, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), b, wadd_succ(mp, r), h))

# The quotient of go is at least d.
def dm_go_div_ge(k: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(d, Nat.div.fin(Nat.divmod.go(k, m, d, r))) == True{} : Bool}:
  match k:
    case 0n:
      wle_refl(d)
    case 1n++kp:
      match m:
        case 0n:
          le_of_succ_le(d, Nat.div.fin(Nat.divmod.go(kp, r, 1n+d, 0n)), dm_go_div_ge(kp, r, 1n+d, 0n))
        case 1n++mp:
          dm_go_div_ge(kp, mp, d, 1n+r)

# The quotient of go is monotone in n.
def dm_go_div_mono(a: Nat, b: Nat, +m: Nat, +d: Nat, +r: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.div.fin(Nat.divmod.go(a, m, d, r)), Nat.div.fin(Nat.divmod.go(b, m, d, r))) == True{} : Bool}:
  match a b:
    case 0n 0n:
      wle_refl(d)
    case 0n 1n++bq:
      dm_go_div_ge(1n+bq, m, d, r)
    case 1n++ap 0n:
      Empty.absurd({Nat.is_le(Nat.div.fin(Nat.divmod.go(1n+ap, m, d, r)), Nat.div.fin(Nat.divmod.go(0n, m, d, r))) == True{} : Bool}, wfalse_true(h))
    case 1n++ap 1n++bq:
      match m:
        case 0n:
          dm_go_div_mono(ap, bq, r, 1n+d, 0n, h)
        case 1n++mp:
          dm_go_div_mono(ap, bq, mp, d, 1n+r, h)

# (c) div(n, 1+b) * (1+b) + mod(n, 1+b) == n
def divmod_eq(+n: Nat, +b: Nat) -> {Nat.add(Nat.mul(Nat.div(n, 1n+b), 1n+b), Nat.mod(n, 1n+b)) == n : Nat}:
  Equal.trans(Nat, dmv(n, b, 0n, 0n, b), Nat.add(n, 0n), n, dm_go_eq(n, b, 0n, 0n, b, wadd_zero(b)), wadd_zero(n))

# (c) mod(n, 1+b) <= b
def mod_le(n: Nat, +b: Nat) -> {Nat.is_le(Nat.mod(n, 1n+b), b) == True{} : Bool}:
  dm_go_mod_le(n, b, 0n, 0n, b, wadd_zero(b))

# (c) a <= c => div(a, 1+b) <= div(c, 1+b)
def div_mono(a: Nat, c: Nat, +b: Nat, h: {Nat.is_le(a, c) == True{} : Bool}) -> {Nat.is_le(Nat.div(a, 1n+b), Nat.div(c, 1n+b)) == True{} : Bool}:
  dm_go_div_mono(a, c, b, 0n, 0n, h)

def mod256_le(n: Nat) -> {Nat.is_le(Nat.mod(n, 256n), 255n) == True{} : Bool}:
  mod_le(n, 255n)

# n <= 65535 => div(n, 256) <= 255 (div(65535, 256) == 255 by computation).
def div256_le(+n: Nat, h: {Nat.is_le(n, 65535n) == True{} : Bool}) -> {Nat.is_le(Nat.div(n, 256n), 255n) == True{} : Bool}:
  wle_trans(Nat.div(n, 256n), Nat.div(65535n, 256n), 255n, div_mono(n, 65535n, 255n, h), {==})

# Law 3
# -----

def u8_get_put(+n: Nat, +rest: List<&2, U32>, +e: {Nat.is_le(n, 255n) == True{} : Bool}) -> {W.get_u8(Laws.cat(W.put_u8(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}:
  %Equal.sym(Bool, W.is_byte(U32.from_nat(n)), True{}, byte_from_nat(n, e)) : {W.got(_, U32.to_nat(U32.from_nat(n)), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(n)), n, u32_to_from(n, e)) : {W.got(True{}, _, rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  {==}

# 16 bits
# -------

# The two bytes of x <= 65535 are bytes.
def u16_hi_byte(+x: Nat, +h: {Nat.is_le(x, 65535n) == True{} : Bool}) -> {W.is_byte(U32.from_nat(Nat.div(x, 256n))) == True{} : Bool}:
  byte_from_nat(Nat.div(x, 256n), div256_le(x, h))

def u16_lo_byte(+x: Nat) -> {W.is_byte(U32.from_nat(Nat.mod(x, 256n))) == True{} : Bool}:
  byte_from_nat(Nat.mod(x, 256n), mod256_le(x))

# The two bytes of x <= 65535 join back to x.
def u16_join(+x: Nat, +h: {Nat.is_le(x, 65535n) == True{} : Bool}) -> {W.join16(U32.to_nat(U32.from_nat(Nat.div(x, 256n))), U32.to_nat(U32.from_nat(Nat.mod(x, 256n)))) == x : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.div(x, 256n))), Nat.div(x, 256n), u32_to_from(Nat.div(x, 256n), div256_le(x, h))) : {W.join16(_, U32.to_nat(U32.from_nat(Nat.mod(x, 256n)))) == x : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.mod(x, 256n))), Nat.mod(x, 256n), u32_to_from(Nat.mod(x, 256n), mod256_le(x))) : {W.join16(Nat.div(x, 256n), _) == x : Nat}
  divmod_eq(x, 255n)

def u16_get_put(+n: Nat, +rest: List<&2, U32>, +e: {Nat.is_le(n, 65535n) == True{} : Bool}) -> {W.get_u16(Laws.cat(W.put_u16(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}:
  %Equal.sym(Bool, W.is_byte(U32.from_nat(Nat.div(n, 256n))), True{}, u16_hi_byte(n, e)) : {W.got(_ && W.is_byte(U32.from_nat(Nat.mod(n, 256n))), W.join16(U32.to_nat(U32.from_nat(Nat.div(n, 256n))), U32.to_nat(U32.from_nat(Nat.mod(n, 256n)))), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Bool, W.is_byte(U32.from_nat(Nat.mod(n, 256n))), True{}, u16_lo_byte(n)) : {W.got(True{} && _, W.join16(U32.to_nat(U32.from_nat(Nat.div(n, 256n))), U32.to_nat(U32.from_nat(Nat.mod(n, 256n)))), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Nat, W.join16(U32.to_nat(U32.from_nat(Nat.div(n, 256n))), U32.to_nat(U32.from_nat(Nat.mod(n, 256n)))), n, u16_join(n, e)) : {W.got(True{} && True{}, _, rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  {==}

# 32 bits
# -------

def mod65536_le(n: Nat) -> {Nat.is_le(Nat.mod(n, 65536n), 65535n) == True{} : Bool}:
  mod_le(n, 65535n)

def u32_get_put(+n: Nat, +rest: List<&2, U32>, +e: {Nat.is_le(Nat.div(n, 65536n), 65535n) == True{} : Bool}) -> {W.get_u32(Laws.cat(W.put_u32(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}:
  %Equal.sym(Bool, W.is_byte(U32.from_nat(Nat.div(Nat.div(n, 65536n), 256n))), True{}, u16_hi_byte(Nat.div(n, 65536n), e)) : {W.got(_ && W.is_byte(U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n))) && W.is_byte(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))) && W.is_byte(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))), W.join32(W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.div(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n)))), W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))))), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Bool, W.is_byte(U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n))), True{}, u16_lo_byte(Nat.div(n, 65536n))) : {W.got(True{} && _ && W.is_byte(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))) && W.is_byte(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))), W.join32(W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.div(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n)))), W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))))), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Bool, W.is_byte(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))), True{}, u16_hi_byte(Nat.mod(n, 65536n), mod65536_le(n))) : {W.got(True{} && True{} && _ && W.is_byte(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))), W.join32(W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.div(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n)))), W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))))), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Bool, W.is_byte(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))), True{}, u16_lo_byte(Nat.mod(n, 65536n))) : {W.got(True{} && True{} && True{} && _, W.join32(W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.div(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n)))), W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))))), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Nat, W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.div(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.div(n, 65536n), 256n)))), Nat.div(n, 65536n), u16_join(Nat.div(n, 65536n), e)) : {W.got(True{} && True{} && True{} && True{}, W.join32(_, W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n))))), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Nat, W.join16(U32.to_nat(U32.from_nat(Nat.div(Nat.mod(n, 65536n), 256n))), U32.to_nat(U32.from_nat(Nat.mod(Nat.mod(n, 65536n), 256n)))), Nat.mod(n, 65536n), u16_join(Nat.mod(n, 65536n), mod65536_le(n))) : {W.got(True{} && True{} && True{} && True{}, W.join32(Nat.div(n, 65536n), _), rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  %Equal.sym(Nat, W.join32(Nat.div(n, 65536n), Nat.mod(n, 65536n)), n, divmod_eq(n, 65535n)) : {W.got(True{} && True{} && True{} && True{}, _, rest) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}
  {==}

def Laws.u8_roundtrip(n, rest, e):
  u8_get_put(n, rest, e)

def Laws.u16_roundtrip(n, rest, e):
  u16_get_put(n, rest, e)

def Laws.u32_roundtrip(n, rest, e):
  u32_get_put(n, rest, e)
