# Laws 7, 8 and 9: names as text, and name comparison.
#
# eq (laws 8, 9): label_eq.go / eq.go by induction on the lists with the Bool
# accumulator generalized; per byte only Nat.is_eq(k, k) and Nat.is_eq
# symmetry are needed (byte_eq compares Nat values of lowered bytes).
#
# from_text(to_text(n)) (law 7), for n = Con{l, t} (the root computes):
#   to_text_spec       to_text == to_text.spec (escape.rev / tail.rev equations)
#   pieces_text        pieces(to_text.spec(Con{l, t})) == rp(t, escape.spec(l), [])
#                      (split_label: an escaped label is one piece; sb per byte)
#   trim_rp            trim keeps those pieces (labels are nonempty, trim_esc)
#   labels_rp          labels.go reads each piece back to its label
#                      (unesc_label / label_of_esc; ub per byte)
#   then check(n) == Done{n} by ok(n).
# Per byte b with class k (ub, sb, trim_esc; one case per B.Class constructor):
# a literal byte is definitional (Char.to_u32(Char.from_u32(b)) == b, tc
# rewrites the text class), "\." / "\\" through the Char.is_eq hit, and
# "\DDD" by a closed enumeration of the 256 byte values (ddd_unesc,
# ddd_split) plus two Word facts proven here for every U32:
#   u32_from_to   U32.from_nat(U32.to_nat(b)) == b
#   le255         class(b) a byte class => U32.to_nat(b) <= 255
#                 (wcmp / u32cmp: Word.cmp is Nat.cmp of the values)
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/types.bend as M
import ../src/num.bend as N
import ../src/name.bend as NM

# Nat equality
# ------------

def is_eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      is_eq_refl(p)

def is_eq_symm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      is_eq_symm(ap, bp)

# Labels and names
# ----------------

def byte_eq_refl(+x: U32) -> {True{} == NM.byte_eq(x, x) : Bool}:
  Equal.sym(Bool, NM.byte_eq(x, x), True{}, is_eq_refl(U32.to_nat(NM.lower_byte(x))))

def byte_eq_symm(+x: U32, +y: U32) -> {NM.byte_eq(x, y) == NM.byte_eq(y, x) : Bool}:
  is_eq_symm(U32.to_nat(NM.lower_byte(x)), U32.to_nat(NM.lower_byte(y)))

def label_eq_refl(l: List<&2, U32>, ok: Bool) -> {NM.label_eq.go(l, l, ok) == ok : Bool}:
  match l ok:
    case Nil{} _:
      {==}
    case Con{+x, t} True{}:
      %byte_eq_refl(x) : {NM.label_eq.go(t, t, _) == True{} : Bool}
      label_eq_refl(t, True{})
    case Con{+x, t} False{}:
      label_eq_refl(t, False{})

def label_eq_symm(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> {NM.label_eq.go(a, b, ok) == NM.label_eq.go(b, a, ok) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      {==}
    case Con{x, xt} Nil{}:
      {==}
    case Con{+x, xt} Con{+y, yt}:
      %byte_eq_symm(x, y) : {NM.label_eq.go(xt, yt, Bool.and(ok, NM.byte_eq(x, y))) == NM.label_eq.go(yt, xt, Bool.and(ok, _)) : Bool}
      label_eq_symm(xt, yt, Bool.and(ok, NM.byte_eq(x, y)))

def label_eq_refl1(+l: List<&2, U32>) -> {True{} == NM.label_eq(l, l) : Bool}:
  Equal.sym(Bool, NM.label_eq(l, l), True{}, label_eq_refl(l, True{}))

def eq_go_refl(n: M.Name(), ok: Bool) -> {NM.eq.go(n, n, ok) == ok : Bool}:
  match n ok:
    case Nil{} _:
      {==}
    case Con{+x, t} True{}:
      %label_eq_refl1(x) : {NM.eq.go(t, t, _) == True{} : Bool}
      eq_go_refl(t, True{})
    case Con{+x, t} False{}:
      eq_go_refl(t, False{})

def eq_go_symm(a: M.Name(), b: M.Name(), ok: Bool) -> {NM.eq.go(a, b, ok) == NM.eq.go(b, a, ok) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      {==}
    case Con{x, xt} Nil{}:
      {==}
    case Con{+x, xt} Con{+y, yt}:
      %label_eq_symm(x, y, True{}) : {NM.eq.go(xt, yt, Bool.and(ok, NM.label_eq(x, y))) == NM.eq.go(yt, xt, Bool.and(ok, _)) : Bool}
      eq_go_symm(xt, yt, Bool.and(ok, NM.label_eq(x, y)))

def Laws.name_eq_refl(n):
  eq_go_refl(n, True{})

def Laws.name_eq_symm(a, b):
  eq_go_symm(a, b, True{})

# Bool facts
# ----------

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

# Anything from {False == True}.
def absurd_ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, (%e : bool_disc(_); Unit{}))

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      absurd_ft({False{} == True{} : Bool}, e)

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      absurd_ft({b == True{} : Bool}, e)

# The last of three conjuncts (either grouping of a && b && c).
def and3_c(a: Bool, b: Bool, -c: Bool, e: {a && b && c == True{} : Bool}) -> {c == True{} : Bool}:
  match a b:
    case True{} True{}:
      e
    case True{} False{}:
      absurd_ft({c == True{} : Bool}, e)
    case False{} _:
      absurd_ft({c == True{} : Bool}, e)

def and_true(a: Bool) -> {a == Bool.and(a, True{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Nat order
# ---------

def le_zero(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def lt_zero(-A: Type, v: Nat, e: {Nat.is_lt(v, 0n) == True{} : Bool}) -> A:
  match v:
    case 0n:
      absurd_ft(A, e)
    case 1n+p:
      absurd_ft(A, e)

# v < k + 1: v <= k.
def lt_succ_le(v: Nat, k: Nat, e: {Nat.is_lt(v, 1n+k) == True{} : Bool}) -> {Nat.is_le(v, k) == True{} : Bool}:
  match v k:
    case 0n _:
      le_zero(k)
    case 1n+vp 0n:
      lt_zero({Nat.is_le(1n+vp, 0n) == True{} : Bool}, vp, e)
    case 1n+vp 1n+kp:
      lt_succ_le(vp, kp, e)

# Comparing doubled numbers (a word's bits, low first)
# -----------------------------------------------------

def cmp_dd(a: Nat, b: Nat) -> {Nat.cmp(Nat.double(a), Nat.double(b)) == Nat.cmp(a, b) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      cmp_dd(ap, bp)

def cmp_d1(a: Nat, b: Nat) -> {Nat.cmp(Nat.double(a), 1n+Nat.double(b)) == Word.cmp.fin(False{}, True{}, Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      cmp_d1(ap, bp)

def cmp_1d(a: Nat, b: Nat) -> {Nat.cmp(1n+Nat.double(a), Nat.double(b)) == Word.cmp.fin(True{}, False{}, Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      cmp_1d(ap, bp)

def fin_ff(t: Cmp) -> {t == Word.cmp.fin(False{}, False{}, t) : Cmp}:
  match t:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def fin_tt(t: Cmp) -> {t == Word.cmp.fin(True{}, True{}, t) : Cmp}:
  match t:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Word.cmp is Nat.cmp of the values.
def wcmp(+n: Nat, a: Word(n), b: Word(n)) -> {Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) == Word.cmp(n, a, b) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %wcmp(p, at, bt) : {Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) == Word.cmp.fin(False{}, False{}, _) : Cmp}
          %fin_ff(Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) : {Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) == _ : Cmp}
          cmp_dd(Word.to_nat(p, at), Word.to_nat(p, bt))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          %wcmp(p, at, bt) : {Nat.cmp(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))) == Word.cmp.fin(False{}, True{}, _) : Cmp}
          cmp_d1(Word.to_nat(p, at), Word.to_nat(p, bt))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          %wcmp(p, at, bt) : {Nat.cmp(1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) == Word.cmp.fin(True{}, False{}, _) : Cmp}
          cmp_1d(Word.to_nat(p, at), Word.to_nat(p, bt))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %wcmp(p, at, bt) : {Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) == Word.cmp.fin(True{}, True{}, _) : Cmp}
          %fin_tt(Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt))) : {Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))) == _ : Cmp}
          cmp_dd(Word.to_nat(p, at), Word.to_nat(p, bt))

def u32cmp(a: U32, b: U32) -> {Nat.cmp(U32.to_nat(a), U32.to_nat(b)) == U32.cmp(a, b) : Cmp}:
  match a b:
    case U32{x} U32{y}:
      wcmp(32n, x, y)

# A word from a number, by increments from zero (U32.from_nat on words)
# ----------------------------------------------------------------------

def wfn(+m: Nat, n: Nat) -> Word(m):
  match n:
    case 0n:
      Word.zero(m)
    case 1n+p:
      Word.inc(m, wfn(m, p))

def from_nat_w(n: Nat) -> {U32.from_nat(n) == U32{wfn(32n, n)} : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %from_nat_w(p) : {U32.inc(U32.from_nat(p)) == U32.inc(_) : U32}
      {==}

def wfn_double(+m: Nat, k: Nat) -> {wfn(1n+m, Nat.double(k)) == WCon{False{}, wfn(m, k)} : Word(1n+m)}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %wfn_double(m, p) : {Word.inc(1n+m, Word.inc(1n+m, wfn(1n+m, Nat.double(p)))) == Word.inc(1n+m, Word.inc(1n+m, _)) : Word(1n+m)}
      {==}

def wfn_to_nat(+m: Nat, w: Word(m)) -> {wfn(m, Word.to_nat(m, w)) == w : Word(m)}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          %wfn_to_nat(p, t) : {wfn(1n+p, Nat.double(Word.to_nat(p, t))) == WCon{False{}, _} : Word(1n+p)}
          wfn_double(p, Word.to_nat(p, t))
        case WCon{True{}, +t}:
          %wfn_to_nat(p, t) : {wfn(1n+p, 1n+Nat.double(Word.to_nat(p, t))) == WCon{True{}, _} : Word(1n+p)}
          %wfn_double(p, Word.to_nat(p, t)) : {Word.inc(1n+p, wfn(1n+p, Nat.double(Word.to_nat(p, t)))) == Word.inc(1n+p, _) : Word(1n+p)}
          {==}

# U32.from_nat(U32.to_nat(b)) == b, for every U32.
def u32_from_to(b: U32) -> {U32.from_nat(U32.to_nat(b)) == b : U32}:
  match b:
    case U32{+w}:
      Equal.trans(U32, U32.from_nat(Word.to_nat(32n, w)), U32{wfn(32n, Word.to_nat(32n, w))}, U32{w},
        from_nat_w(Word.to_nat(32n, w)),
        Equal.cong(Word(32n), U32, x => U32{x}, wfn(32n, Word.to_nat(32n, w)), w, wfn_to_nat(32n, w)))

# Bytes are below 256
# -------------------

def byte_lt.go(t: Bool, +b: U32, et: {U32.is_lt(b, 256) == t : Bool}, h: {B.Class.is_byte(B.class(b)) == True{} : Bool}) -> {t == True{} : Bool}:
  match t:
    case True{}:
      {==}
    case False{}:
      %et : {B.Class.is_byte(Bool.pick(B.Class, _, Bool.pick(B.Class, U32.is_lt(b, 128), B.class.ascii(b), B.High{}), B.Invalid{})) == True{} : Bool}
      h

def lt_nat(+b: U32, lt: {U32.is_lt(b, 256) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(b), 256n) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_lt(Nat.cmp(U32.to_nat(b), U32.to_nat(256))), Cmp.is_lt(U32.cmp(b, 256)), True{},
    Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), Nat.cmp(U32.to_nat(b), U32.to_nat(256)), U32.cmp(b, 256), u32cmp(b, 256)), lt)

# A cell whose class is a byte class has a value at most 255.
def le255(+b: U32, -k: B.Class, e: {B.class(b) == k : B.Class}, eb: {B.Class.is_byte(k) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(b), 255n) == True{} : Bool}:
  lt_succ_le(U32.to_nat(b), 255n, lt_nat(b, byte_lt.go(U32.is_lt(b, 256), b, {==},
    Equal.trans(Bool, B.Class.is_byte(B.class(b)), B.Class.is_byte(k), True{},
      Equal.cong(B.Class, Bool, x => B.Class.is_byte(x), B.class(b), k, e), eb))))

# "DDD" for each byte value (a closed enumeration of 0..255)
# ----------------------------------------------------------

def ddd_unesc(v: Nat, -acc: List<&2, U32>, e: {Nat.is_le(v, 255n) == True{} : Bool}) -> {NM.UPlain{U32.from_nat(v) <> acc} == NM.unesc.go(NM.pad3(N.show(v)), NM.UEsc{acc}) : NM.Unesc}:
  match v:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n:
      {==}
    case 33n:
      {==}
    case 34n:
      {==}
    case 35n:
      {==}
    case 36n:
      {==}
    case 37n:
      {==}
    case 38n:
      {==}
    case 39n:
      {==}
    case 40n:
      {==}
    case 41n:
      {==}
    case 42n:
      {==}
    case 43n:
      {==}
    case 44n:
      {==}
    case 45n:
      {==}
    case 46n:
      {==}
    case 47n:
      {==}
    case 48n:
      {==}
    case 49n:
      {==}
    case 50n:
      {==}
    case 51n:
      {==}
    case 52n:
      {==}
    case 53n:
      {==}
    case 54n:
      {==}
    case 55n:
      {==}
    case 56n:
      {==}
    case 57n:
      {==}
    case 58n:
      {==}
    case 59n:
      {==}
    case 60n:
      {==}
    case 61n:
      {==}
    case 62n:
      {==}
    case 63n:
      {==}
    case 64n:
      {==}
    case 65n:
      {==}
    case 66n:
      {==}
    case 67n:
      {==}
    case 68n:
      {==}
    case 69n:
      {==}
    case 70n:
      {==}
    case 71n:
      {==}
    case 72n:
      {==}
    case 73n:
      {==}
    case 74n:
      {==}
    case 75n:
      {==}
    case 76n:
      {==}
    case 77n:
      {==}
    case 78n:
      {==}
    case 79n:
      {==}
    case 80n:
      {==}
    case 81n:
      {==}
    case 82n:
      {==}
    case 83n:
      {==}
    case 84n:
      {==}
    case 85n:
      {==}
    case 86n:
      {==}
    case 87n:
      {==}
    case 88n:
      {==}
    case 89n:
      {==}
    case 90n:
      {==}
    case 91n:
      {==}
    case 92n:
      {==}
    case 93n:
      {==}
    case 94n:
      {==}
    case 95n:
      {==}
    case 96n:
      {==}
    case 97n:
      {==}
    case 98n:
      {==}
    case 99n:
      {==}
    case 100n:
      {==}
    case 101n:
      {==}
    case 102n:
      {==}
    case 103n:
      {==}
    case 104n:
      {==}
    case 105n:
      {==}
    case 106n:
      {==}
    case 107n:
      {==}
    case 108n:
      {==}
    case 109n:
      {==}
    case 110n:
      {==}
    case 111n:
      {==}
    case 112n:
      {==}
    case 113n:
      {==}
    case 114n:
      {==}
    case 115n:
      {==}
    case 116n:
      {==}
    case 117n:
      {==}
    case 118n:
      {==}
    case 119n:
      {==}
    case 120n:
      {==}
    case 121n:
      {==}
    case 122n:
      {==}
    case 123n:
      {==}
    case 124n:
      {==}
    case 125n:
      {==}
    case 126n:
      {==}
    case 127n:
      {==}
    case 128n:
      {==}
    case 129n:
      {==}
    case 130n:
      {==}
    case 131n:
      {==}
    case 132n:
      {==}
    case 133n:
      {==}
    case 134n:
      {==}
    case 135n:
      {==}
    case 136n:
      {==}
    case 137n:
      {==}
    case 138n:
      {==}
    case 139n:
      {==}
    case 140n:
      {==}
    case 141n:
      {==}
    case 142n:
      {==}
    case 143n:
      {==}
    case 144n:
      {==}
    case 145n:
      {==}
    case 146n:
      {==}
    case 147n:
      {==}
    case 148n:
      {==}
    case 149n:
      {==}
    case 150n:
      {==}
    case 151n:
      {==}
    case 152n:
      {==}
    case 153n:
      {==}
    case 154n:
      {==}
    case 155n:
      {==}
    case 156n:
      {==}
    case 157n:
      {==}
    case 158n:
      {==}
    case 159n:
      {==}
    case 160n:
      {==}
    case 161n:
      {==}
    case 162n:
      {==}
    case 163n:
      {==}
    case 164n:
      {==}
    case 165n:
      {==}
    case 166n:
      {==}
    case 167n:
      {==}
    case 168n:
      {==}
    case 169n:
      {==}
    case 170n:
      {==}
    case 171n:
      {==}
    case 172n:
      {==}
    case 173n:
      {==}
    case 174n:
      {==}
    case 175n:
      {==}
    case 176n:
      {==}
    case 177n:
      {==}
    case 178n:
      {==}
    case 179n:
      {==}
    case 180n:
      {==}
    case 181n:
      {==}
    case 182n:
      {==}
    case 183n:
      {==}
    case 184n:
      {==}
    case 185n:
      {==}
    case 186n:
      {==}
    case 187n:
      {==}
    case 188n:
      {==}
    case 189n:
      {==}
    case 190n:
      {==}
    case 191n:
      {==}
    case 192n:
      {==}
    case 193n:
      {==}
    case 194n:
      {==}
    case 195n:
      {==}
    case 196n:
      {==}
    case 197n:
      {==}
    case 198n:
      {==}
    case 199n:
      {==}
    case 200n:
      {==}
    case 201n:
      {==}
    case 202n:
      {==}
    case 203n:
      {==}
    case 204n:
      {==}
    case 205n:
      {==}
    case 206n:
      {==}
    case 207n:
      {==}
    case 208n:
      {==}
    case 209n:
      {==}
    case 210n:
      {==}
    case 211n:
      {==}
    case 212n:
      {==}
    case 213n:
      {==}
    case 214n:
      {==}
    case 215n:
      {==}
    case 216n:
      {==}
    case 217n:
      {==}
    case 218n:
      {==}
    case 219n:
      {==}
    case 220n:
      {==}
    case 221n:
      {==}
    case 222n:
      {==}
    case 223n:
      {==}
    case 224n:
      {==}
    case 225n:
      {==}
    case 226n:
      {==}
    case 227n:
      {==}
    case 228n:
      {==}
    case 229n:
      {==}
    case 230n:
      {==}
    case 231n:
      {==}
    case 232n:
      {==}
    case 233n:
      {==}
    case 234n:
      {==}
    case 235n:
      {==}
    case 236n:
      {==}
    case 237n:
      {==}
    case 238n:
      {==}
    case 239n:
      {==}
    case 240n:
      {==}
    case 241n:
      {==}
    case 242n:
      {==}
    case 243n:
      {==}
    case 244n:
      {==}
    case 245n:
      {==}
    case 246n:
      {==}
    case 247n:
      {==}
    case 248n:
      {==}
    case 249n:
      {==}
    case 250n:
      {==}
    case 251n:
      {==}
    case 252n:
      {==}
    case 253n:
      {==}
    case 254n:
      {==}
    case 255n:
      {==}
    case 256n+p:
      absurd_ft({NM.UPlain{U32.from_nat(256n+p) <> acc} == NM.unesc.go(NM.pad3(N.show(256n+p)), NM.UEsc{acc}) : NM.Unesc}, e)

def ddd_split(v: Nat, -cur: String, -acc: List<&2, String>, e: {Nat.is_le(v, 255n) == True{} : Bool}) -> {NM.Split{False{}, String.reverse.go(NM.pad3(N.show(v)), cur), acc} == NM.split.go(NM.pad3(N.show(v)), NM.Split{True{}, cur, acc}) : NM.Split}:
  match v:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n:
      {==}
    case 33n:
      {==}
    case 34n:
      {==}
    case 35n:
      {==}
    case 36n:
      {==}
    case 37n:
      {==}
    case 38n:
      {==}
    case 39n:
      {==}
    case 40n:
      {==}
    case 41n:
      {==}
    case 42n:
      {==}
    case 43n:
      {==}
    case 44n:
      {==}
    case 45n:
      {==}
    case 46n:
      {==}
    case 47n:
      {==}
    case 48n:
      {==}
    case 49n:
      {==}
    case 50n:
      {==}
    case 51n:
      {==}
    case 52n:
      {==}
    case 53n:
      {==}
    case 54n:
      {==}
    case 55n:
      {==}
    case 56n:
      {==}
    case 57n:
      {==}
    case 58n:
      {==}
    case 59n:
      {==}
    case 60n:
      {==}
    case 61n:
      {==}
    case 62n:
      {==}
    case 63n:
      {==}
    case 64n:
      {==}
    case 65n:
      {==}
    case 66n:
      {==}
    case 67n:
      {==}
    case 68n:
      {==}
    case 69n:
      {==}
    case 70n:
      {==}
    case 71n:
      {==}
    case 72n:
      {==}
    case 73n:
      {==}
    case 74n:
      {==}
    case 75n:
      {==}
    case 76n:
      {==}
    case 77n:
      {==}
    case 78n:
      {==}
    case 79n:
      {==}
    case 80n:
      {==}
    case 81n:
      {==}
    case 82n:
      {==}
    case 83n:
      {==}
    case 84n:
      {==}
    case 85n:
      {==}
    case 86n:
      {==}
    case 87n:
      {==}
    case 88n:
      {==}
    case 89n:
      {==}
    case 90n:
      {==}
    case 91n:
      {==}
    case 92n:
      {==}
    case 93n:
      {==}
    case 94n:
      {==}
    case 95n:
      {==}
    case 96n:
      {==}
    case 97n:
      {==}
    case 98n:
      {==}
    case 99n:
      {==}
    case 100n:
      {==}
    case 101n:
      {==}
    case 102n:
      {==}
    case 103n:
      {==}
    case 104n:
      {==}
    case 105n:
      {==}
    case 106n:
      {==}
    case 107n:
      {==}
    case 108n:
      {==}
    case 109n:
      {==}
    case 110n:
      {==}
    case 111n:
      {==}
    case 112n:
      {==}
    case 113n:
      {==}
    case 114n:
      {==}
    case 115n:
      {==}
    case 116n:
      {==}
    case 117n:
      {==}
    case 118n:
      {==}
    case 119n:
      {==}
    case 120n:
      {==}
    case 121n:
      {==}
    case 122n:
      {==}
    case 123n:
      {==}
    case 124n:
      {==}
    case 125n:
      {==}
    case 126n:
      {==}
    case 127n:
      {==}
    case 128n:
      {==}
    case 129n:
      {==}
    case 130n:
      {==}
    case 131n:
      {==}
    case 132n:
      {==}
    case 133n:
      {==}
    case 134n:
      {==}
    case 135n:
      {==}
    case 136n:
      {==}
    case 137n:
      {==}
    case 138n:
      {==}
    case 139n:
      {==}
    case 140n:
      {==}
    case 141n:
      {==}
    case 142n:
      {==}
    case 143n:
      {==}
    case 144n:
      {==}
    case 145n:
      {==}
    case 146n:
      {==}
    case 147n:
      {==}
    case 148n:
      {==}
    case 149n:
      {==}
    case 150n:
      {==}
    case 151n:
      {==}
    case 152n:
      {==}
    case 153n:
      {==}
    case 154n:
      {==}
    case 155n:
      {==}
    case 156n:
      {==}
    case 157n:
      {==}
    case 158n:
      {==}
    case 159n:
      {==}
    case 160n:
      {==}
    case 161n:
      {==}
    case 162n:
      {==}
    case 163n:
      {==}
    case 164n:
      {==}
    case 165n:
      {==}
    case 166n:
      {==}
    case 167n:
      {==}
    case 168n:
      {==}
    case 169n:
      {==}
    case 170n:
      {==}
    case 171n:
      {==}
    case 172n:
      {==}
    case 173n:
      {==}
    case 174n:
      {==}
    case 175n:
      {==}
    case 176n:
      {==}
    case 177n:
      {==}
    case 178n:
      {==}
    case 179n:
      {==}
    case 180n:
      {==}
    case 181n:
      {==}
    case 182n:
      {==}
    case 183n:
      {==}
    case 184n:
      {==}
    case 185n:
      {==}
    case 186n:
      {==}
    case 187n:
      {==}
    case 188n:
      {==}
    case 189n:
      {==}
    case 190n:
      {==}
    case 191n:
      {==}
    case 192n:
      {==}
    case 193n:
      {==}
    case 194n:
      {==}
    case 195n:
      {==}
    case 196n:
      {==}
    case 197n:
      {==}
    case 198n:
      {==}
    case 199n:
      {==}
    case 200n:
      {==}
    case 201n:
      {==}
    case 202n:
      {==}
    case 203n:
      {==}
    case 204n:
      {==}
    case 205n:
      {==}
    case 206n:
      {==}
    case 207n:
      {==}
    case 208n:
      {==}
    case 209n:
      {==}
    case 210n:
      {==}
    case 211n:
      {==}
    case 212n:
      {==}
    case 213n:
      {==}
    case 214n:
      {==}
    case 215n:
      {==}
    case 216n:
      {==}
    case 217n:
      {==}
    case 218n:
      {==}
    case 219n:
      {==}
    case 220n:
      {==}
    case 221n:
      {==}
    case 222n:
      {==}
    case 223n:
      {==}
    case 224n:
      {==}
    case 225n:
      {==}
    case 226n:
      {==}
    case 227n:
      {==}
    case 228n:
      {==}
    case 229n:
      {==}
    case 230n:
      {==}
    case 231n:
      {==}
    case 232n:
      {==}
    case 233n:
      {==}
    case 234n:
      {==}
    case 235n:
      {==}
    case 236n:
      {==}
    case 237n:
      {==}
    case 238n:
      {==}
    case 239n:
      {==}
    case 240n:
      {==}
    case 241n:
      {==}
    case 242n:
      {==}
    case 243n:
      {==}
    case 244n:
      {==}
    case 245n:
      {==}
    case 246n:
      {==}
    case 247n:
      {==}
    case 248n:
      {==}
    case 249n:
      {==}
    case 250n:
      {==}
    case 251n:
      {==}
    case 252n:
      {==}
    case 253n:
      {==}
    case 254n:
      {==}
    case 255n:
      {==}
    case 256n+p:
      absurd_ft({NM.Split{False{}, String.reverse.go(NM.pad3(N.show(256n+p)), cur), acc} == NM.split.go(NM.pad3(N.show(256n+p)), NM.Split{True{}, cur, acc}) : NM.Split}, e)
# One byte's escape, read back
# ----------------------------

# The text classifier on the char of b, given b's class.
def tc(+b: U32, -k: B.Class, e: {B.class(b) == k : B.Class}) -> {NM.tchar.of(k, Char.from_u32(b)) == NM.tchar(Char.from_u32(b)) : NM.TChar}:
  %e : {NM.tchar.of(_, Char.from_u32(b)) == NM.tchar(Char.from_u32(b)) : NM.TChar}
  {==}

def ub_ddd(+b: U32, -acc: List<&2, U32>, le: {Nat.is_le(U32.to_nat(b), 255n) == True{} : Bool}) -> {NM.UPlain{b <> acc} == NM.unesc.go(NM.ddd(b), NM.UPlain{acc}) : NM.Unesc}:
  %ddd_unesc(U32.to_nat(b), acc, le) : {NM.UPlain{b <> acc} == _ : NM.Unesc}
  %u32_from_to(b) : {NM.UPlain{_ <> acc} == NM.UPlain{U32.from_nat(U32.to_nat(b)) <> acc} : NM.Unesc}
  {==}

def ub_dot(hit: Bool, +b: U32, -acc: List<&2, U32>, e: {B.class(b) == B.Tchar{} : B.Class}, eh: {hit == Char.is_eq(Char.from_u32(b), '.') : Bool}) -> {NM.UPlain{b <> acc} == NM.unesc.go(NM.escape1.mark(hit, b), NM.UPlain{acc}) : NM.Unesc}:
  match hit:
    case True{}:
      %tc(b, B.Tchar{}, e) : {NM.UPlain{b <> acc} == NM.unesc.esc(_, Char.from_u32(b), acc) : NM.Unesc}
      %eh : {NM.UPlain{b <> acc} == NM.unesc.esc(NM.tchar.pick(_, NM.TDot{}), Char.from_u32(b), acc) : NM.Unesc}
      {==}
    case False{}:
      %tc(b, B.Tchar{}, e) : {NM.UPlain{b <> acc} == NM.unesc.plain(_, Char.from_u32(b), acc) : NM.Unesc}
      %eh : {NM.UPlain{b <> acc} == NM.unesc.plain(NM.tchar.pick(_, NM.TDot{}), Char.from_u32(b), acc) : NM.Unesc}
      {==}

def sb_dot(hit: Bool, +b: U32, -cur: String, -acc: List<&2, String>, e: {B.class(b) == B.Tchar{} : B.Class}, eh: {hit == Char.is_eq(Char.from_u32(b), '.') : Bool}) -> {NM.Split{False{}, String.reverse.go(NM.escape1.mark(hit, b), cur), acc} == NM.split.go(NM.escape1.mark(hit, b), NM.Split{False{}, cur, acc}) : NM.Split}:
  match hit:
    case True{}:
      {==}
    case False{}:
      %tc(b, B.Tchar{}, e) : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, _, Char.from_u32(b), cur, acc) : NM.Split}
      %eh : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, NM.tchar.pick(_, NM.TDot{}), Char.from_u32(b), cur, acc) : NM.Split}
      {==}

def trim_dot(hit: Bool, +b: U32, -s: String, -ps: List<&2, String>) -> {Con{String.append(NM.escape1.mark(hit, b), s), ps} == NM.trim(Con{String.append(NM.escape1.mark(hit, b), s), ps}) : List<&2, String>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ub_back(hit: Bool, +b: U32, -acc: List<&2, U32>, e: {B.class(b) == B.Delim{} : B.Class}, eh: {hit == Char.is_eq(Char.from_u32(b), '\\') : Bool}) -> {NM.UPlain{b <> acc} == NM.unesc.go(NM.escape1.mark(hit, b), NM.UPlain{acc}) : NM.Unesc}:
  match hit:
    case True{}:
      %tc(b, B.Delim{}, e) : {NM.UPlain{b <> acc} == NM.unesc.esc(_, Char.from_u32(b), acc) : NM.Unesc}
      %eh : {NM.UPlain{b <> acc} == NM.unesc.esc(NM.tchar.pick(_, NM.TBack{}), Char.from_u32(b), acc) : NM.Unesc}
      {==}
    case False{}:
      %tc(b, B.Delim{}, e) : {NM.UPlain{b <> acc} == NM.unesc.plain(_, Char.from_u32(b), acc) : NM.Unesc}
      %eh : {NM.UPlain{b <> acc} == NM.unesc.plain(NM.tchar.pick(_, NM.TBack{}), Char.from_u32(b), acc) : NM.Unesc}
      {==}

def sb_back(hit: Bool, +b: U32, -cur: String, -acc: List<&2, String>, e: {B.class(b) == B.Delim{} : B.Class}, eh: {hit == Char.is_eq(Char.from_u32(b), '\\') : Bool}) -> {NM.Split{False{}, String.reverse.go(NM.escape1.mark(hit, b), cur), acc} == NM.split.go(NM.escape1.mark(hit, b), NM.Split{False{}, cur, acc}) : NM.Split}:
  match hit:
    case True{}:
      {==}
    case False{}:
      %tc(b, B.Delim{}, e) : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, _, Char.from_u32(b), cur, acc) : NM.Split}
      %eh : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, NM.tchar.pick(_, NM.TBack{}), Char.from_u32(b), cur, acc) : NM.Split}
      {==}

def trim_back(hit: Bool, +b: U32, -s: String, -ps: List<&2, String>) -> {Con{String.append(NM.escape1.mark(hit, b), s), ps} == NM.trim(Con{String.append(NM.escape1.mark(hit, b), s), ps}) : List<&2, String>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

# Reading back the escape of a byte b (class k) puts b on the piece.
def ub(k: B.Class, +b: U32, -acc: List<&2, U32>, e: {B.class(b) == k : B.Class}, eb: {B.Class.is_byte(k) == True{} : Bool}) -> {NM.UPlain{b <> acc} == NM.unesc.go(NM.escape1.of(k, b), NM.UPlain{acc}) : NM.Unesc}:
  match k:
    case B.Digit{v}:
      %tc(b, B.Digit{v}, e) : {NM.UPlain{b <> acc} == NM.unesc.plain(_, Char.from_u32(b), acc) : NM.Unesc}
      {==}
    case B.HexLetter{v}:
      %tc(b, B.HexLetter{v}, e) : {NM.UPlain{b <> acc} == NM.unesc.plain(_, Char.from_u32(b), acc) : NM.Unesc}
      {==}
    case B.Letter{}:
      %tc(b, B.Letter{}, e) : {NM.UPlain{b <> acc} == NM.unesc.plain(_, Char.from_u32(b), acc) : NM.Unesc}
      {==}
    case B.Colon{}:
      %tc(b, B.Colon{}, e) : {NM.UPlain{b <> acc} == NM.unesc.plain(_, Char.from_u32(b), acc) : NM.Unesc}
      {==}
    case B.Semi{}:
      %tc(b, B.Semi{}, e) : {NM.UPlain{b <> acc} == NM.unesc.plain(_, Char.from_u32(b), acc) : NM.Unesc}
      {==}
    case B.Slash{}:
      %tc(b, B.Slash{}, e) : {NM.UPlain{b <> acc} == NM.unesc.plain(_, Char.from_u32(b), acc) : NM.Unesc}
      {==}
    case B.Tchar{}:
      ub_dot(Char.is_eq(Char.from_u32(b), '.'), b, acc, e, {==})
    case B.Delim{}:
      ub_back(Char.is_eq(Char.from_u32(b), '\\'), b, acc, e, {==})
    case B.Sp{}:
      ub_ddd(b, acc, le255(b, B.Sp{}, e, eb))
    case B.Htab{}:
      ub_ddd(b, acc, le255(b, B.Htab{}, e, eb))
    case B.Cr{}:
      ub_ddd(b, acc, le255(b, B.Cr{}, e, eb))
    case B.Lf{}:
      ub_ddd(b, acc, le255(b, B.Lf{}, e, eb))
    case B.Ctl{}:
      ub_ddd(b, acc, le255(b, B.Ctl{}, e, eb))
    case B.High{}:
      ub_ddd(b, acc, le255(b, B.High{}, e, eb))
    case B.Invalid{}:
      absurd_ft({NM.UPlain{b <> acc} == NM.unesc.go(NM.escape1.of(B.Invalid{}, b), NM.UPlain{acc}) : NM.Unesc}, eb)

# Cutting the escape of a byte b (class k) at dots keeps it in the piece.
def sb(k: B.Class, +b: U32, -cur: String, -acc: List<&2, String>, e: {B.class(b) == k : B.Class}, eb: {B.Class.is_byte(k) == True{} : Bool}) -> {NM.Split{False{}, String.reverse.go(NM.escape1.of(k, b), cur), acc} == NM.split.go(NM.escape1.of(k, b), NM.Split{False{}, cur, acc}) : NM.Split}:
  match k:
    case B.Digit{v}:
      %tc(b, B.Digit{v}, e) : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, _, Char.from_u32(b), cur, acc) : NM.Split}
      {==}
    case B.HexLetter{v}:
      %tc(b, B.HexLetter{v}, e) : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, _, Char.from_u32(b), cur, acc) : NM.Split}
      {==}
    case B.Letter{}:
      %tc(b, B.Letter{}, e) : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, _, Char.from_u32(b), cur, acc) : NM.Split}
      {==}
    case B.Colon{}:
      %tc(b, B.Colon{}, e) : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, _, Char.from_u32(b), cur, acc) : NM.Split}
      {==}
    case B.Semi{}:
      %tc(b, B.Semi{}, e) : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, _, Char.from_u32(b), cur, acc) : NM.Split}
      {==}
    case B.Slash{}:
      %tc(b, B.Slash{}, e) : {NM.Split{False{}, SCon{Char.from_u32(b), cur}, acc} == NM.split.char(False{}, _, Char.from_u32(b), cur, acc) : NM.Split}
      {==}
    case B.Tchar{}:
      sb_dot(Char.is_eq(Char.from_u32(b), '.'), b, cur, acc, e, {==})
    case B.Delim{}:
      sb_back(Char.is_eq(Char.from_u32(b), '\\'), b, cur, acc, e, {==})
    case B.Sp{}:
      ddd_split(U32.to_nat(b), SCon{'\\', cur}, acc, le255(b, B.Sp{}, e, eb))
    case B.Htab{}:
      ddd_split(U32.to_nat(b), SCon{'\\', cur}, acc, le255(b, B.Htab{}, e, eb))
    case B.Cr{}:
      ddd_split(U32.to_nat(b), SCon{'\\', cur}, acc, le255(b, B.Cr{}, e, eb))
    case B.Lf{}:
      ddd_split(U32.to_nat(b), SCon{'\\', cur}, acc, le255(b, B.Lf{}, e, eb))
    case B.Ctl{}:
      ddd_split(U32.to_nat(b), SCon{'\\', cur}, acc, le255(b, B.Ctl{}, e, eb))
    case B.High{}:
      ddd_split(U32.to_nat(b), SCon{'\\', cur}, acc, le255(b, B.High{}, e, eb))
    case B.Invalid{}:
      absurd_ft({NM.Split{False{}, String.reverse.go(NM.escape1.of(B.Invalid{}, b), cur), acc} == NM.split.go(NM.escape1.of(B.Invalid{}, b), NM.Split{False{}, cur, acc}) : NM.Split}, eb)

# A piece that starts with a byte's escape is not empty: trim keeps the list.
def trim_esc(k: B.Class, +b: U32, -s: String, -ps: List<&2, String>) -> {Con{String.append(NM.escape1.of(k, b), s), ps} == NM.trim(Con{String.append(NM.escape1.of(k, b), s), ps}) : List<&2, String>}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
      {==}
    case B.Letter{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Tchar{}:
      trim_dot(Char.is_eq(Char.from_u32(b), '.'), b, s, ps)
    case B.Delim{}:
      trim_back(Char.is_eq(Char.from_u32(b), '\\'), b, s, ps)
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      {==}
    case B.Lf{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

# Strings and lists
# -----------------

def sapp_nil(s: String) -> {s == String.append(s, SNil{}) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Equal.cong(String, String, x => SCon{c, x}, t, String.append(t, SNil{}), sapp_nil(t))

def sapp_assoc(a: String, -b: String, -c: String) -> {String.append(a, String.append(b, c)) == String.append(String.append(a, b), c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(t, String.append(b, c)), String.append(String.append(t, b), c), sapp_assoc(t, b, c))

# String.reverse.go(a, cur) is reverse(a) ++ cur.
def rgo_app2(a: String, -s: String, cur: String) -> {String.reverse.go(s, String.reverse.go(a, cur)) == String.reverse.go(String.append(a, s), cur) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rgo_app2(t, s, SCon{h, cur})

def rgo_rgo(a: String, acc: String, -y: String) -> {String.reverse.go(acc, String.append(a, y)) == String.reverse.go(String.reverse.go(a, acc), y) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rgo_rgo(t, SCon{h, acc}, y)

def srev_rev(+s: String) -> {s == String.reverse(String.reverse(s)) : String}:
  Equal.trans(String, s, String.append(s, SNil{}), String.reverse(String.reverse(s)), sapp_nil(s), rgo_rgo(s, SNil{}, SNil{}))

def srev_rev_r(+s: String) -> {String.reverse(String.reverse(s)) == s : String}:
  Equal.sym(String, s, String.reverse(String.reverse(s)), srev_rev(s))

def cat_nil(-A: Data, xs: List<&2, A>) -> {xs == List.append(&2, A, xs, Nil{}) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, x => Con{h, x}, t, List.append(&2, A, t, Nil{}), cat_nil(A, t))

def rev_rev_onto(-A: Data, xs: List<&2, A>, acc: List<&2, A>, -ys: List<&2, A>) -> {B.rev(A, acc, List.append(&2, A, xs, ys)) == B.rev(A, B.rev(A, xs, acc), ys) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_rev_onto(A, t, h <> acc, ys)

def rev_rev(-A: Data, +xs: List<&2, A>) -> {xs == B.rev(A, B.rev(A, xs, Nil{}), Nil{}) : List<&2, A>}:
  Equal.trans(List<&2, A>, xs, List.append(&2, A, xs, Nil{}), B.rev(A, B.rev(A, xs, Nil{}), Nil{}), cat_nil(A, xs), rev_rev_onto(A, xs, Nil{}, Nil{}))

# Folds over appended text
# ------------------------

def split_app(a: String, -s: String, st: NM.Split) -> {NM.split.go(s, NM.split.go(a, st)) == NM.split.go(String.append(a, s), st) : NM.Split}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      split_app(t, s, NM.split.step(st, c))

def unesc_app(a: String, -s: String, st: NM.Unesc) -> {NM.unesc.go(s, NM.unesc.go(a, st)) == NM.unesc.go(String.append(a, s), st) : NM.Unesc}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      unesc_app(t, s, NM.unesc.step(st, c))

# Loop equations
# --------------

def and_true_r(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def all_bytes_go(xs: List<&2, U32>, +ok: Bool) -> {Bool.and(ok, B.all_bytes.spec(xs)) == B.all_bytes.go(xs, ok) : Bool}:
  match xs:
    case Nil{}:
      and_true_r(ok)
    case Con{+h, t}:
      Equal.trans(Bool, Bool.and(ok, Bool.and(B.Class.is_byte(B.class(h)), B.all_bytes.spec(t))),
        Bool.and(Bool.and(ok, B.Class.is_byte(B.class(h))), B.all_bytes.spec(t)), B.all_bytes.go(t, Bool.and(ok, B.Class.is_byte(B.class(h)))),
        and_assoc(ok, B.Class.is_byte(B.class(h)), B.all_bytes.spec(t)), all_bytes_go(t, Bool.and(ok, B.Class.is_byte(B.class(h)))))

def labels_ok_go(n: M.Name(), +ok: Bool) -> {Bool.and(ok, NM.labels_ok.spec(n)) == NM.labels_ok.go(n, ok) : Bool}:
  match n:
    case Nil{}:
      and_true_r(ok)
    case Con{+l, t}:
      Equal.trans(Bool, Bool.and(ok, Bool.and(NM.label_ok(l), NM.labels_ok.spec(t))),
        Bool.and(Bool.and(ok, NM.label_ok(l)), NM.labels_ok.spec(t)), NM.labels_ok.go(t, Bool.and(ok, NM.label_ok(l))),
        and_assoc(ok, NM.label_ok(l), NM.labels_ok.spec(t)), labels_ok_go(t, Bool.and(ok, NM.label_ok(l))))

def bytes_of(+l: List<&2, U32>, e: {NM.label_ok(l) == True{} : Bool}) -> {B.all_bytes.spec(l) == True{} : Bool}:
  Equal.trans(Bool, B.all_bytes.spec(l), B.all_bytes.go(l, True{}), True{}, all_bytes_go(l, True{}),
    and3_c(Nat.is_le(1n, NM.len(l)), Nat.is_le(NM.len(l), 63n), B.all_bytes(l), e))

def lsn(+n: M.Name(), e: {NM.ok(n) == True{} : Bool}) -> {NM.labels_ok.spec(n) == True{} : Bool}:
  Equal.trans(Bool, NM.labels_ok.spec(n), NM.labels_ok.go(n, True{}), True{}, labels_ok_go(n, True{}),
    and_l(NM.labels_ok(n), Nat.is_le(NM.wire_size(n), 255n), e))

def escape_rev_eq(l: List<&2, U32>, +acc: String, -s: String) -> {String.reverse.go(acc, String.append(NM.escape.spec(l), s)) == String.reverse.go(NM.escape.rev(l, acc), s) : String}:
  match l:
    case Nil{}:
      {==}
    case Con{+b, t}:
      %sapp_assoc(NM.escape1(b), NM.escape.spec(t), s) : {String.reverse.go(acc, _) == String.reverse.go(NM.escape.rev(t, String.reverse.go(NM.escape1(b), acc)), s) : String}
      Equal.trans(String, String.reverse.go(acc, String.append(NM.escape1(b), String.append(NM.escape.spec(t), s))),
        String.reverse.go(String.reverse.go(NM.escape1(b), acc), String.append(NM.escape.spec(t), s)),
        String.reverse.go(NM.escape.rev(t, String.reverse.go(NM.escape1(b), acc)), s),
        rgo_rgo(NM.escape1(b), acc, String.append(NM.escape.spec(t), s)),
        escape_rev_eq(t, String.reverse.go(NM.escape1(b), acc), s))

def tail_rev_eq(n: M.Name(), +acc: String, -s: String) -> {String.reverse.go(acc, String.append(NM.tail.spec(n), s)) == String.reverse.go(NM.tail.rev(n, acc), s) : String}:
  match n:
    case Nil{}:
      {==}
    case Con{+l, t}:
      %sapp_assoc(NM.escape.spec(l), NM.tail.spec(t), s) : {String.reverse.go(SCon{'.', acc}, _) == String.reverse.go(NM.tail.rev(t, NM.escape.rev(l, SCon{'.', acc})), s) : String}
      Equal.trans(String, String.reverse.go(SCon{'.', acc}, String.append(NM.escape.spec(l), String.append(NM.tail.spec(t), s))),
        String.reverse.go(NM.escape.rev(l, SCon{'.', acc}), String.append(NM.tail.spec(t), s)),
        String.reverse.go(NM.tail.rev(t, NM.escape.rev(l, SCon{'.', acc})), s),
        escape_rev_eq(l, SCon{'.', acc}, String.append(NM.tail.spec(t), s)),
        tail_rev_eq(t, NM.escape.rev(l, SCon{'.', acc}), s))

def to_text_spec(+n: M.Name()) -> {NM.to_text.spec(n) == NM.to_text(n) : String}:
  match n:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      %Equal.sym(String, NM.tail.spec(t), String.append(NM.tail.spec(t), SNil{}), sapp_nil(NM.tail.spec(t))) : {String.append(NM.escape.spec(l), _) == NM.to_text(Con{l, t}) : String}
      Equal.trans(String, String.reverse.go(SNil{}, String.append(NM.escape.spec(l), String.append(NM.tail.spec(t), SNil{}))),
        String.reverse.go(NM.escape.rev(l, SNil{}), String.append(NM.tail.spec(t), SNil{})),
        String.reverse.go(NM.tail.rev(t, NM.escape.rev(l, SNil{})), SNil{}),
        escape_rev_eq(l, SNil{}, String.append(NM.tail.spec(t), SNil{})),
        tail_rev_eq(t, NM.escape.rev(l, SNil{}), SNil{}))

# A label's text, cut and read back
# ---------------------------------

def split_label(l: List<&2, U32>, +cur: String, +acc: List<&2, String>, +ok: {B.all_bytes.spec(l) == True{} : Bool})
  -> {NM.Split{False{}, String.reverse.go(NM.escape.spec(l), cur), acc} == NM.split.go(NM.escape.spec(l), NM.Split{False{}, cur, acc}) : NM.Split}:
  match l:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %split_app(NM.escape1(b), NM.escape.spec(t), NM.Split{False{}, cur, acc}) : {NM.Split{False{}, String.reverse.go(String.append(NM.escape1(b), NM.escape.spec(t)), cur), acc} == _ : NM.Split}
      %sb(B.class(b), b, cur, acc, {==}, and_l(B.Class.is_byte(B.class(b)), B.all_bytes.spec(t), ok)) : {NM.Split{False{}, String.reverse.go(String.append(NM.escape1(b), NM.escape.spec(t)), cur), acc} == NM.split.go(NM.escape.spec(t), _) : NM.Split}
      %rgo_app2(NM.escape1(b), NM.escape.spec(t), cur) : {NM.Split{False{}, _, acc} == NM.split.go(NM.escape.spec(t), NM.Split{False{}, String.reverse.go(NM.escape1(b), cur), acc}) : NM.Split}
      split_label(t, String.reverse.go(NM.escape1(b), cur), acc, and_r(B.Class.is_byte(B.class(b)), B.all_bytes.spec(t), ok))

def unesc_label(l: List<&2, U32>, +acc: List<&2, U32>, +ok: {B.all_bytes.spec(l) == True{} : Bool})
  -> {NM.UPlain{B.rev(U32, l, acc)} == NM.unesc.go(NM.escape.spec(l), NM.UPlain{acc}) : NM.Unesc}:
  match l:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %unesc_app(NM.escape1(b), NM.escape.spec(t), NM.UPlain{acc}) : {NM.UPlain{B.rev(U32, t, b <> acc)} == _ : NM.Unesc}
      %ub(B.class(b), b, acc, {==}, and_l(B.Class.is_byte(B.class(b)), B.all_bytes.spec(t), ok)) : {NM.UPlain{B.rev(U32, t, b <> acc)} == NM.unesc.go(NM.escape.spec(t), _) : NM.Unesc}
      unesc_label(t, b <> acc, and_r(B.Class.is_byte(B.class(b)), B.all_bytes.spec(t), ok))

def label_of_esc(+l: List<&2, U32>, +ok: {B.all_bytes.spec(l) == True{} : Bool}) -> {Done{l} == NM.label_of(NM.escape.spec(l)) : Result<&2, &2, M.NameError, List<&2, U32>>}:
  %unesc_label(l, Nil{}, ok) : {Done{l} == NM.unesc.end(_) : Result<&2, &2, M.NameError, List<&2, U32>>}
  %rev_rev(U32, l) : {Done{l} == Done{_} : Result<&2, &2, M.NameError, List<&2, U32>>}
  {==}

# A label's text starts with a char: trim leaves the pieces alone.
def trim_label(l: List<&2, U32>, -acc: List<&2, String>, e: {NM.label_ok(l) == True{} : Bool})
  -> {Con{NM.escape.spec(l), acc} == NM.trim(Con{NM.escape.spec(l), acc}) : List<&2, String>}:
  match l:
    case Nil{}:
      absurd_ft({Con{NM.escape.spec(Nil{}), acc} == NM.trim(Con{NM.escape.spec(Nil{}), acc}) : List<&2, String>}, e)
    case Con{+b, r}:
      trim_esc(B.class(b), b, NM.escape.spec(r), acc)

# The name's pieces
# -----------------

# The pieces split.end gives for the labels t after a piece p, newest first.
def rp(t: M.Name(), p: String, acc: List<&2, String>) -> List<&2, String>:
  match t:
    case Nil{}:
      p <> acc
    case Con{l, t2}:
      rp(t2, NM.escape.spec(l), p <> acc)

def split_tail(t: M.Name(), +cur: String, +acc: List<&2, String>, +ok: {NM.labels_ok.spec(t) == True{} : Bool})
  -> {rp(t, String.reverse(cur), acc) == NM.split.end(NM.split.go(NM.tail.spec(t), NM.Split{False{}, cur, acc})) : List<&2, String>}:
  match t:
    case Nil{}:
      {==}
    case Con{+l, t2}:
      %split_app(NM.escape.spec(l), NM.tail.spec(t2), NM.Split{False{}, SNil{}, String.reverse(cur) <> acc}) : {rp(t2, NM.escape.spec(l), String.reverse(cur) <> acc) == NM.split.end(_) : List<&2, String>}
      %split_label(l, SNil{}, String.reverse(cur) <> acc, bytes_of(l, and_l(NM.label_ok(l), NM.labels_ok.spec(t2), ok))) : {rp(t2, NM.escape.spec(l), String.reverse(cur) <> acc) == NM.split.end(NM.split.go(NM.tail.spec(t2), _)) : List<&2, String>}
      %srev_rev_r(NM.escape.spec(l)) : {rp(t2, _, String.reverse(cur) <> acc) == NM.split.end(NM.split.go(NM.tail.spec(t2), NM.Split{False{}, String.reverse.go(NM.escape.spec(l), SNil{}), String.reverse(cur) <> acc})) : List<&2, String>}
      split_tail(t2, String.reverse.go(NM.escape.spec(l), SNil{}), String.reverse(cur) <> acc, and_r(NM.label_ok(l), NM.labels_ok.spec(t2), ok))

def pieces_text(+l: List<&2, U32>, +t: M.Name(), +ok: {NM.labels_ok.spec(Con{l, t}) == True{} : Bool})
  -> {rp(t, NM.escape.spec(l), Nil{}) == NM.pieces(NM.to_text.spec(Con{l, t})) : List<&2, String>}:
  %split_app(NM.escape.spec(l), NM.tail.spec(t), NM.Split{False{}, SNil{}, Nil{}}) : {rp(t, NM.escape.spec(l), Nil{}) == NM.split.end(_) : List<&2, String>}
  %split_label(l, SNil{}, Nil{}, bytes_of(l, and_l(NM.label_ok(l), NM.labels_ok.spec(t), ok))) : {rp(t, NM.escape.spec(l), Nil{}) == NM.split.end(NM.split.go(NM.tail.spec(t), _)) : List<&2, String>}
  %srev_rev_r(NM.escape.spec(l)) : {rp(t, _, Nil{}) == NM.split.end(NM.split.go(NM.tail.spec(t), NM.Split{False{}, String.reverse.go(NM.escape.spec(l), SNil{}), Nil{}})) : List<&2, String>}
  split_tail(t, String.reverse.go(NM.escape.spec(l), SNil{}), Nil{}, and_r(NM.label_ok(l), NM.labels_ok.spec(t), ok))

def trim_rp(t: M.Name(), +l: List<&2, U32>, -acc: List<&2, String>, +ok: {NM.labels_ok.spec(Con{l, t}) == True{} : Bool})
  -> {rp(t, NM.escape.spec(l), acc) == NM.trim(rp(t, NM.escape.spec(l), acc)) : List<&2, String>}:
  match t:
    case Nil{}:
      trim_label(l, acc, and_l(NM.label_ok(l), NM.labels_ok.spec(Nil{}), ok))
    case Con{+l2, +t2}:
      trim_rp(t2, l2, NM.escape.spec(l) <> acc, and_r(NM.label_ok(l), NM.labels_ok.spec(Con{l2, t2}), ok))

def labels_cons(+l: List<&2, U32>, -acc: List<&2, String>, -x: M.Name(), +ok: {B.all_bytes.spec(l) == True{} : Bool})
  -> {NM.labels.go(acc, Done{l <> x}) == NM.labels.go(NM.escape.spec(l) <> acc, Done{x}) : Result<&2, &2, M.NameError, M.Name()>}:
  %label_of_esc(l, ok) : {NM.labels.go(acc, Done{l <> x}) == NM.labels.go(acc, NM.labels.add(_, Done{x})) : Result<&2, &2, M.NameError, M.Name()>}
  {==}

def labels_rp(t: M.Name(), +l: List<&2, U32>, -acc: List<&2, String>, -ls: M.Name(), +ok: {NM.labels_ok.spec(Con{l, t}) == True{} : Bool})
  -> {NM.labels.go(acc, Done{Con{l, List.append(&2, List<&2, U32>, t, ls)}}) == NM.labels.go(rp(t, NM.escape.spec(l), acc), Done{ls}) : Result<&2, &2, M.NameError, M.Name()>}:
  match t:
    case Nil{}:
      labels_cons(l, acc, ls, bytes_of(l, and_l(NM.label_ok(l), NM.labels_ok.spec(Nil{}), ok)))
    case Con{+l2, +t2}:
      Equal.trans(Result<&2, &2, M.NameError, M.Name()>,
        NM.labels.go(acc, Done{Con{l, Con{l2, List.append(&2, List<&2, U32>, t2, ls)}}}),
        NM.labels.go(NM.escape.spec(l) <> acc, Done{Con{l2, List.append(&2, List<&2, U32>, t2, ls)}}),
        NM.labels.go(rp(t2, NM.escape.spec(l2), NM.escape.spec(l) <> acc), Done{ls}),
        labels_cons(l, acc, Con{l2, List.append(&2, List<&2, U32>, t2, ls)}, bytes_of(l, and_l(NM.label_ok(l), NM.labels_ok.spec(Con{l2, t2}), ok))),
        labels_rp(t2, l2, NM.escape.spec(l) <> acc, ls, and_r(NM.label_ok(l), NM.labels_ok.spec(Con{l2, t2}), ok)))

# Law 7
# -----

def text_roundtrip_con(+l: List<&2, U32>, +t: M.Name(), +e: {NM.ok(Con{l, t}) == True{} : Bool})
  -> {NM.from_text(NM.to_text(Con{l, t})) == Done{Con{l, t}} : Result<&2, &2, M.NameError, M.Name()>}:
  %to_text_spec(Con{l, t}) : {NM.from_text.check(NM.labels.go(NM.trim(NM.pieces(_)), Done{Nil{}})) == Done{Con{l, t}} : Result<&2, &2, M.NameError, M.Name()>}
  %pieces_text(l, t, lsn(Con{l, t}, e)) : {NM.from_text.check(NM.labels.go(NM.trim(_), Done{Nil{}})) == Done{Con{l, t}} : Result<&2, &2, M.NameError, M.Name()>}
  %trim_rp(t, l, Nil{}, lsn(Con{l, t}, e)) : {NM.from_text.check(NM.labels.go(_, Done{Nil{}})) == Done{Con{l, t}} : Result<&2, &2, M.NameError, M.Name()>}
  %labels_rp(t, l, Nil{}, Nil{}, lsn(Con{l, t}, e)) : {NM.from_text.check(_) == Done{Con{l, t}} : Result<&2, &2, M.NameError, M.Name()>}
  %cat_nil(List<&2, U32>, t) : {NM.from_text.check(NM.labels.go(Nil{}, Done{Con{l, _}})) == Done{Con{l, t}} : Result<&2, &2, M.NameError, M.Name()>}
  %Equal.sym(Bool, NM.ok(Con{l, t}), True{}, e) : {NM.check.pick(_, Con{l, t}) == Done{Con{l, t}} : Result<&2, &2, M.NameError, M.Name()>}
  {==}

def Laws.name_text_roundtrip(n, e):
  match n:
    case Nil{}:
      {==}
    case Con{l, t}:
      text_roundtrip_con(l, t, e)
