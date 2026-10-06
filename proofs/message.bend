# Law 6 (message_roundtrip): a valid message decodes to itself.
#
# The plan (decode.bend's and encode.bend's headers):
#   1. header:  D.header(Cur{E.header_onto(h, qd, an, ns, ar, r), pos, hp})
#               == Done{HeadAt{h, qd, an, ns, ar, Cur{r, 12 + pos, hp}}}
#   2. names:   D.read_name(ix, Cur{NM.wire_onto(n, r), pos, hp})
#               == Done{NameAt{n, Cur{r, wire_size(n) + pos, hp}}}       (NM.ok(n))
#   3. the counted loops qs.go / rs.go over E.questions.spec / E.records.spec
#   4. one record: take.go, rdata by type, type_of / class_of
#   5. the encoder's loop/.spec equations
# The wire facts are laws 3-5, proven in proofs/wire.bend (imported as WP:
# u8_get_put, u16_get_put, u32_get_put).
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/types.bend as M
import ../src/wire.bend as W
import ../src/name.bend as NM
import ../src/encode.bend as E
import ../src/decode.bend as D
import ../proofs/wire.bend as WP

def BL() -> Data:
  List<&2, U32>

def NL() -> Data:
  List<&2, List<&2, U32>>

# Bool facts
# ----------

def mr_bdisc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def mr_false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : mr_bdisc(_)
  Unit{}

def mr_absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, mr_false_true(e))

def mr_and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      mr_absurd({False{} == True{} : Bool}, e)

def mr_and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      mr_absurd({b == True{} : Bool}, e)

def mr_not_true(a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      mr_absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# Nat facts
# ---------

def mr_add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mr_add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def mr_add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mr_add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def mr_le_zero(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def mr_le_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      mr_le_zero(c)
    case 1n+ap 0n _:
      mr_absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, e1)
    case 1n+ap 1n+bp 0n:
      mr_absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, e2)
    case 1n+ap 1n+bp 1n+cp:
      mr_le_trans(ap, bp, cp, e1, e2)

def mr_eq_true(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      mr_absurd({0n == 1n+bp : Nat}, e)
    case 1n+ap 0n:
      mr_absurd({1n+ap == 0n : Nat}, e)
    case 1n+ap 1n+bp:
      %mr_eq_true(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

# Lists
# -----

def mr_app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mr_app_nil(A, t) : {Con{h, List.append(&2, A, t, Nil{})} == Con{h, _} : List<&2, A>}
      {==}

def mr_app_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>)
  -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mr_app_assoc(A, t, ys, zs) : {Con{h, List.append(&2, A, List.append(&2, A, t, ys), zs)} == Con{h, _} : List<&2, A>}
      {==}

def mr_rev_rev(-A: Data, xs: List<&2, A>, acc: List<&2, A>, -ys: List<&2, A>)
  -> {B.rev(A, B.rev(A, xs, acc), ys) == B.rev(A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      mr_rev_rev(A, t, h <> acc, ys)

# rev is an involution.
def mr_rev_inv(-A: Data, +xs: List<&2, A>) -> {B.rev(A, B.rev(A, xs, Nil{}), Nil{}) == xs : List<&2, A>}:
  %mr_app_nil(A, xs) : {B.rev(A, B.rev(A, xs, Nil{}), Nil{}) == _ : List<&2, A>}
  mr_rev_rev(A, xs, Nil{}, Nil{})

def mr_count_go(-A: Data, xs: List<&2, A>, +k: Nat) -> {E.count.go(A, xs, k) == Nat.add(List.length(&2, A, xs), k) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %mr_add_succ(List.length(&2, A, t), k) : {E.count.go(A, t, 1n+k) == _ : Nat}
      mr_count_go(A, t, 1n+k)

def mr_count(-A: Data, +xs: List<&2, A>) -> {E.count(A, xs) == List.length(&2, A, xs) : Nat}:
  %mr_add_zero(List.length(&2, A, xs)) : {E.count(A, xs) == _ : Nat}
  mr_count_go(A, xs, 0n)

def mr_len_go(xs: BL(), +k: Nat) -> {NM.len.go(xs, k) == Nat.add(List.length(&2, U32, xs), k) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %mr_add_succ(List.length(&2, U32, t), k) : {NM.len.go(t, 1n+k) == _ : Nat}
      mr_len_go(t, 1n+k)

def mr_len(+xs: BL()) -> {NM.len(xs) == List.length(&2, U32, xs) : Nat}:
  %mr_add_zero(List.length(&2, U32, xs)) : {NM.len(xs) == _ : Nat}
  mr_len_go(xs, 0n)

def mr_app(xs: BL(), -ys: BL()) -> {E.app(xs, ys) == List.append(&2, U32, xs, ys) : BL()}:
  mr_rev_rev(U32, xs, Nil{}, ys)

def mr_wire_rev_tail(+l: BL(), +w: BL(), +acc: BL(), +ys: BL())
  -> {B.rev(U32, B.rev(U32, W.put_u8(NM.len(l)), acc), List.append(&2, U32, l, List.append(&2, U32, w, ys)))
      == B.rev(U32, acc, List.append(&2, U32, List.append(&2, U32, W.put_u8(NM.len(l)), List.append(&2, U32, l, w)), ys)) : BL()}:
  %mr_app_assoc(U32, l, w, ys) : {B.rev(U32, B.rev(U32, W.put_u8(NM.len(l)), acc), _)
      == B.rev(U32, acc, List.append(&2, U32, List.append(&2, U32, W.put_u8(NM.len(l)), List.append(&2, U32, l, w)), ys)) : BL()}
  mr_rev_rev(U32, W.put_u8(NM.len(l)), acc, List.append(&2, U32, List.append(&2, U32, l, w), ys))

# Wire integers (laws 3-5, from proofs/wire.bend)
# ----------------------------------------------------

def mr_u8(n: Nat, rest: BL(), e: {Nat.is_le(n, 255n) == True{} : Bool})
  -> {W.get_u8(Laws.cat(W.put_u8(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}:
  WP.u8_get_put(n, rest, e)

def mr_u16(n: Nat, rest: BL(), e: {Nat.is_le(n, 65535n) == True{} : Bool})
  -> {W.get_u16(Laws.cat(W.put_u16(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}:
  WP.u16_get_put(n, rest, e)

def mr_u32(n: Nat, rest: BL(), e: {Nat.is_le(Nat.div(n, 65536n), 65535n) == True{} : Bool})
  -> {W.get_u32(Laws.cat(W.put_u32(n), rest)) == Some{M.Got{n, rest}} : Maybe<&2, M.Got>}:
  WP.u32_get_put(n, rest, e)

def MG() -> Data:
  Maybe<&2, M.Got>

def mr_u8s(+n: Nat, +rest: BL(), +e: {Nat.is_le(n, 255n) == True{} : Bool})
  -> {Some{M.Got{n, rest}} == W.get_u8(Laws.cat(W.put_u8(n), rest)) : MG()}:
  Equal.sym(MG(), W.get_u8(Laws.cat(W.put_u8(n), rest)), Some{M.Got{n, rest}}, mr_u8(n, rest, e))

def mr_u16s(+n: Nat, +rest: BL(), +e: {Nat.is_le(n, 65535n) == True{} : Bool})
  -> {Some{M.Got{n, rest}} == W.get_u16(Laws.cat(W.put_u16(n), rest)) : MG()}:
  Equal.sym(MG(), W.get_u16(Laws.cat(W.put_u16(n), rest)), Some{M.Got{n, rest}}, mr_u16(n, rest, e))

def mr_u32s(+n: Nat, +rest: BL(), +e: {Nat.is_le(Nat.div(n, 65536n), 65535n) == True{} : Bool})
  -> {Some{M.Got{n, rest}} == W.get_u32(Laws.cat(W.put_u32(n), rest)) : MG()}:
  Equal.sym(MG(), W.get_u32(Laws.cat(W.put_u32(n), rest)), Some{M.Got{n, rest}}, mr_u32(n, rest, e))

# Names (lemma 2)
# ---------------

# NM.wire_onto(n, ys) == NM.wire.spec(n) ++ ys (name.bend's equation).
def mr_wire_rev(+n: NL(), +acc: BL(), +ys: BL())
  -> {B.rev(U32, NM.wire.rev(n, acc), ys) == B.rev(U32, acc, List.append(&2, U32, NM.wire.spec(n), ys)) : BL()}:
  match n:
    case Nil{}:
      mr_rev_rev(U32, W.put_u8(0n), acc, ys)
    case Con{+l, +t}:
      Equal.trans(BL(), B.rev(U32, NM.wire.rev(t, B.rev(U32, l, B.rev(U32, W.put_u8(NM.len(l)), acc))), ys),
        B.rev(U32, B.rev(U32, l, B.rev(U32, W.put_u8(NM.len(l)), acc)), List.append(&2, U32, NM.wire.spec(t), ys)),
        B.rev(U32, acc, List.append(&2, U32, NM.wire.spec(l <> t), ys)),
        mr_wire_rev(t, B.rev(U32, l, B.rev(U32, W.put_u8(NM.len(l)), acc)), ys),
        Equal.trans(BL(), B.rev(U32, B.rev(U32, l, B.rev(U32, W.put_u8(NM.len(l)), acc)), List.append(&2, U32, NM.wire.spec(t), ys)),
          B.rev(U32, B.rev(U32, W.put_u8(NM.len(l)), acc), List.append(&2, U32, l, List.append(&2, U32, NM.wire.spec(t), ys))),
          B.rev(U32, acc, List.append(&2, U32, NM.wire.spec(l <> t), ys)),
          mr_rev_rev(U32, l, B.rev(U32, W.put_u8(NM.len(l)), acc), List.append(&2, U32, NM.wire.spec(t), ys)),
          mr_wire_rev_tail(l, NM.wire.spec(t), acc, ys)))

def mr_wire_onto(+n: NL(), +ys: BL()) -> {NM.wire_onto(n, ys) == List.append(&2, U32, NM.wire.spec(n), ys) : BL()}:
  mr_wire_rev(n, Nil{}, ys)

def mr_labels_ok_go(n: NL(), b: Bool) -> {NM.labels_ok.go(n, b) == Bool.and(b, NM.labels_ok.spec(n)) : Bool}:
  match n:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{+l, +t}:
      match b:
        case True{}:
          mr_labels_ok_go(t, NM.label_ok(l))
        case False{}:
          mr_labels_ok_go(t, False{})

def mr_ok_spec(+n: NL(), e: {NM.ok(n) == True{} : Bool}) -> {NM.labels_ok.spec(n) == True{} : Bool}:
  %mr_labels_ok_go(n, True{}) : {_ == True{} : Bool}
  mr_and_l(NM.labels_ok(n), Nat.is_le(NM.wire_size(n), 255n), e)

# The bytes of one label, after its length byte.
def mr_seg_label(t: BL(), +b: U32, +cur: BL(), +ls: NL(), +ys: BL())
  -> {D.seg.go(List.append(&2, U32, b <> t, ys), D.LIn{List.length(&2, U32, t), cur, ls})
      == D.seg.go(ys, D.LLen{B.rev(U32, B.rev(U32, t, b <> cur), Nil{}) <> ls}) : D.Seg}:
  match t:
    case Nil{}:
      {==}
    case Con{+b2, +t2}:
      mr_seg_label(t2, b2, b <> cur, ls, ys)

def mr_seg_end(+r: BL(), +x: NL()) -> {D.seg.go(r, D.LEnd{x}) == D.SegEnd{x, r} : D.Seg}:
  match r:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# A label's length: 1 + the length of its tail.
def mr_label_len(+x: U32, +lt: BL()) -> {NM.len(x <> lt) == 1n+List.length(&2, U32, lt) : Nat}:
  mr_len(x <> lt)

def mr_label_le63(+x: U32, +lt: BL(), e: {NM.label_ok(x <> lt) == True{} : Bool})
  -> {Nat.is_le(NM.len(x <> lt), 63n) == True{} : Bool}:
  mr_and_r(Nat.is_le(1n, NM.len(x <> lt)), Nat.is_le(NM.len(x <> lt), 63n),
    mr_and_l(Bool.and(Nat.is_le(1n, NM.len(x <> lt)), Nat.is_le(NM.len(x <> lt), 63n)), B.all_bytes(x <> lt), e))

def mr_label_le62(+x: U32, +lt: BL(), e: {NM.label_ok(x <> lt) == True{} : Bool})
  -> {Nat.is_le(List.length(&2, U32, lt), 62n) == True{} : Bool}:
  %mr_label_len(x, lt) : {Nat.is_le(_, 63n) == True{} : Bool}
  mr_label_le63(x, lt, e)

def mr_label_le255(+x: U32, +lt: BL(), e: {NM.label_ok(x <> lt) == True{} : Bool})
  -> {Nat.is_le(NM.len(x <> lt), 255n) == True{} : Bool}:
  mr_le_trans(NM.len(x <> lt), 63n, 255n, mr_label_le63(x, lt, e), {==})

# The labels of an uncompressed name, up to its zero byte.
def mr_seg_name(n: NL(), +acc: NL(), +r: BL(), +e: {NM.labels_ok.spec(n) == True{} : Bool})
  -> {D.seg.go(List.append(&2, U32, NM.wire.spec(n), r), D.LLen{acc}) == D.seg.go(r, D.LEnd{B.rev(List<&2, U32>, n, acc)}) : D.Seg}:
  match n:
    case Nil{}:
      {==}
    case Con{l, +t}:
      match l:
        case Nil{}:
          mr_absurd({D.seg.go(List.append(&2, U32, NM.wire.spec(Nil{} <> t), r), D.LLen{acc})
            == D.seg.go(r, D.LEnd{B.rev(List<&2, U32>, Nil{} <> t, acc)}) : D.Seg}, e)
        case Con{+x, +lt}:
          +el = mr_and_l(NM.label_ok(x <> lt), NM.labels_ok.spec(t), e)
          +et = mr_and_r(NM.label_ok(x <> lt), NM.labels_ok.spec(t), e)
          %mr_seg_name(t, (x <> lt) <> acc, r, et) : {D.seg.go(List.append(&2, U32, NM.wire.spec((x <> lt) <> t), r), D.LLen{acc}) == _ : D.Seg}
          %mr_rev_inv(U32, x <> lt) : {D.seg.go(List.append(&2, U32, NM.wire.spec((x <> lt) <> t), r), D.LLen{acc}) == D.seg.go(List.append(&2, U32, NM.wire.spec(t), r), D.LLen{_ <> acc}) : D.Seg}
          %mr_seg_label(lt, x, Nil{}, acc, List.append(&2, U32, NM.wire.spec(t), r)) : {D.seg.go(List.append(&2, U32, NM.wire.spec((x <> lt) <> t), r), D.LLen{acc}) == _ : D.Seg}
          %mr_app_assoc(U32, x <> lt, NM.wire.spec(t), r) : {D.seg.go(List.append(&2, U32, NM.wire.spec((x <> lt) <> t), r), D.LLen{acc}) == D.seg.go(_, D.LIn{List.length(&2, U32, lt), Nil{}, acc}) : D.Seg}
          %mr_label_le62(x, lt, el) : {D.seg.go(List.append(&2, U32, NM.wire.spec((x <> lt) <> t), r), D.LLen{acc}) == D.seg.go(List.append(&2, U32, List.append(&2, U32, x <> lt, NM.wire.spec(t)), r), D.len_more(_, List.length(&2, U32, lt), Nat.is_le(191n, List.length(&2, U32, lt)), Nat.sub(List.length(&2, U32, lt), 191n), acc)) : D.Seg}
          %mr_label_len(x, lt) : {D.seg.go(List.append(&2, U32, NM.wire.spec((x <> lt) <> t), r), D.LLen{acc}) == D.seg.go(List.append(&2, U32, List.append(&2, U32, x <> lt, NM.wire.spec(t)), r), D.len_value(_, acc)) : D.Seg}
          %mr_u8(NM.len(x <> lt), Nil{}, mr_label_le255(x, lt, el)) : {D.seg.go(List.append(&2, U32, NM.wire.spec((x <> lt) <> t), r), D.LLen{acc}) == D.seg.go(List.append(&2, U32, List.append(&2, U32, x <> lt, NM.wire.spec(t)), r), D.len_byte(_, acc)) : D.Seg}
          {==}

def IX() -> Data:
  List<&2, List<&2, U32>>

def NameRes() -> Data:
  Result<&2, &2, M.DecodeError, D.NameAt>

# An uncompressed name reads back, the cursor past it (lemma 2).
def mr_read_name(-ix: IX(), +n: NL(), +r: BL(), +pos: Nat, +hp: Nat, +e: {NM.ok(n) == True{} : Bool})
  -> {D.read_name(ix, D.Cur{NM.wire_onto(n, r), pos, hp}) == Done{D.NameAt{n, D.Cur{r, Nat.add(NM.wire_size(n), pos), hp}}} : NameRes()}:
  %e : {D.read_name(ix, D.Cur{NM.wire_onto(n, r), pos, hp}) == D.name.end(_, n, r, Nat.add(NM.wire_size(n), pos), hp) : NameRes()}
  %mr_rev_inv(List<&2, U32>, n) : {D.read_name(ix, D.Cur{NM.wire_onto(n, r), pos, hp}) == D.name.plain(_, r, pos, hp) : NameRes()}
  %mr_seg_end(r, B.rev(List<&2, U32>, n, Nil{})) : {D.read_name(ix, D.Cur{NM.wire_onto(n, r), pos, hp}) == D.name.first(_, pos, hp, ix) : NameRes()}
  %mr_seg_name(n, Nil{}, r, mr_ok_spec(n, e)) : {D.read_name(ix, D.Cur{NM.wire_onto(n, r), pos, hp}) == D.name.first(_, pos, hp, ix) : NameRes()}
  %mr_wire_onto(n, r) : {D.read_name(ix, D.Cur{NM.wire_onto(n, r), pos, hp}) == D.name.first(D.seg.go(_, D.LLen{Nil{}}), pos, hp, ix) : NameRes()}
  {==}

# Division (for the header's flags)
# ---------------------------------

def NN() -> Type:
  Nat & Nat

def mr_add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      %mr_add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# Fewer than m + 1 units: no wrap.
def mr_dm_small(n: Nat, m: Nat, +d: Nat, +r: Nat, e: {Nat.is_le(n, m) == True{} : Bool})
  -> {Nat.divmod.go(n, m, d, r) == (d, Nat.add(n, r)) : NN()}:
  match n m:
    case 0n _:
      {==}
    case 1n+(+np) 0n:
      mr_absurd({Nat.divmod.go(1n+np, 0n, d, r) == (d, Nat.add(1n+np, r)) : NN()}, e)
    case 1n+(+np) 1n+(+mp):
      %mr_add_succ(np, r) : {Nat.divmod.go(np, mp, d, 1n+r) == (d, _) : NN()}
      mr_dm_small(np, mp, d, 1n+r, e)

# m + 1 units: one wrap.
def mr_dm_block(m: Nat, +n: Nat, +d: Nat, +r: Nat)
  -> {Nat.divmod.go(Nat.add(1n+m, n), m, d, r) == Nat.divmod.go(n, Nat.add(m, r), 1n+d, 0n) : NN()}:
  match m:
    case 0n:
      {==}
    case 1n+(+mp):
      %mr_add_succ(mp, r) : {Nat.divmod.go(Nat.add(1n+mp, n), mp, d, 1n+r) == Nat.divmod.go(n, _, 1n+d, 0n) : NN()}
      mr_dm_block(mp, n, d, 1n+r)

def mr_dm(q: Nat, +bp: Nat, +s: Nat, +d: Nat, +e: {Nat.is_le(s, bp) == True{} : Bool})
  -> {Nat.divmod.go(Nat.add(Nat.mul(q, 1n+bp), s), bp, d, 0n) == (Nat.add(q, d), s) : NN()}:
  match q:
    case 0n:
      %mr_add_zero(s) : {Nat.divmod.go(s, bp, d, 0n) == (d, _) : NN()}
      mr_dm_small(s, bp, d, 0n, e)
    case 1n+(+qp):
      %mr_add_succ(qp, d) : {Nat.divmod.go(Nat.add(Nat.mul(1n+qp, 1n+bp), s), bp, d, 0n) == (_, s) : NN()}
      %mr_dm(qp, bp, s, 1n+d, e) : {Nat.divmod.go(Nat.add(Nat.mul(1n+qp, 1n+bp), s), bp, d, 0n) == _ : NN()}
      %mr_add_zero(bp) : {Nat.divmod.go(Nat.add(Nat.mul(1n+qp, 1n+bp), s), bp, d, 0n)
        == Nat.divmod.go(Nat.add(Nat.mul(qp, 1n+bp), s), _, 1n+d, 0n) : NN()}
      %mr_dm_block(bp, Nat.add(Nat.mul(qp, 1n+bp), s), d, 0n) : {Nat.divmod.go(Nat.add(Nat.mul(1n+qp, 1n+bp), s), bp, d, 0n) == _ : NN()}
      %mr_add_assoc(1n+bp, Nat.mul(qp, 1n+bp), s) : {Nat.divmod.go(Nat.add(Nat.mul(1n+qp, 1n+bp), s), bp, d, 0n)
        == Nat.divmod.go(_, bp, d, 0n) : NN()}
      {==}

def mr_mod(+q: Nat, +bp: Nat, +s: Nat, +e: {Nat.is_le(s, bp) == True{} : Bool})
  -> {Nat.mod(Nat.add(Nat.mul(q, 1n+bp), s), 1n+bp) == s : Nat}:
  Equal.cong(NN(), Nat, x => Nat.mod.fin(x), Nat.divmod.go(Nat.add(Nat.mul(q, 1n+bp), s), bp, 0n, 0n),
    (Nat.add(q, 0n), s), mr_dm(q, bp, s, 0n, e))

def mr_div(+q: Nat, +bp: Nat, +s: Nat, +e: {Nat.is_le(s, bp) == True{} : Bool})
  -> {Nat.div(Nat.add(Nat.mul(q, 1n+bp), s), 1n+bp) == q : Nat}:
  %mr_add_zero(q) : {Nat.div(Nat.add(Nat.mul(q, 1n+bp), s), 1n+bp) == _ : Nat}
  Equal.cong(NN(), Nat, x => Nat.div.fin(x), Nat.divmod.go(Nat.add(Nat.mul(q, 1n+bp), s), bp, 0n, 0n),
    (Nat.add(q, 0n), s), mr_dm(q, bp, s, 0n, e))

# x <= k: k + 1 <= x is False.
def mr_le_not_gt(x: Nat, k: Nat, e: {Nat.is_le(x, k) == True{} : Bool}) -> {Nat.is_le(1n+k, x) == False{} : Bool}:
  match x k:
    case 0n _:
      {==}
    case 1n+(+xp) 0n:
      mr_absurd({Nat.is_le(1n, 1n+xp) == False{} : Bool}, e)
    case 1n+(+xp) 1n+(+kp):
      mr_le_not_gt(xp, kp, e)

def mr_le7(k: Nat) -> {Nat.is_le(7n, Nat.add(Nat.mul(k, 8n), 7n)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+kp):
      {==}

# a <= k and t <= 7: 8a + t <= 8k + 7.
def mr_bound8(a: Nat, +k: Nat, +t: Nat, +e1: {Nat.is_le(a, k) == True{} : Bool}, +e2: {Nat.is_le(t, 7n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(a, 8n), t), Nat.add(Nat.mul(k, 8n), 7n)) == True{} : Bool}:
  match a k:
    case 0n _:
      mr_le_trans(t, 7n, Nat.add(Nat.mul(k, 8n), 7n), e2, mr_le7(k))
    case 1n+(+ap) 0n:
      mr_absurd({Nat.is_le(Nat.add(Nat.mul(1n+ap, 8n), t), 7n) == True{} : Bool}, e1)
    case 1n+(+ap) 1n+(+kp):
      mr_bound8(ap, kp, t, e1, e2)

# The header's flags (lemma 1)
# ----------------------------

def mr_t3(aa: Bool, tc: Bool, rd: Bool) -> Nat:
  Nat.add(Nat.mul(E.bit(aa), 4n), Nat.add(Nat.mul(E.bit(tc), 2n), E.bit(rd)))

def mr_s7(op: Nat, aa: Bool, tc: Bool, rd: Bool) -> Nat:
  Nat.add(Nat.mul(op, 8n), mr_t3(aa, tc, rd))

def mr_u(cd: Bool, rc: Nat) -> Nat:
  Nat.add(Nat.mul(E.bit(cd), 16n), rc)

def mr_v(ad: Bool, cd: Bool, rc: Nat) -> Nat:
  Nat.add(Nat.mul(E.bit(ad), 32n), mr_u(cd, rc))

def mr_t3_le(aa: Bool, tc: Bool, rd: Bool) -> {Nat.is_le(mr_t3(aa, tc, rd), 7n) == True{} : Bool}:
  match aa tc rd:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def mr_t3_aa(aa: Bool, tc: Bool, rd: Bool) -> {Nat.is_le(4n, mr_t3(aa, tc, rd)) == aa : Bool}:
  match aa tc rd:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def mr_t3_tc(aa: Bool, tc: Bool, rd: Bool) -> {Nat.is_le(2n, Nat.mod(mr_t3(aa, tc, rd), 4n)) == tc : Bool}:
  match aa tc rd:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def mr_t3_rd(aa: Bool, tc: Bool, rd: Bool) -> {Nat.is_eq(Nat.mod(mr_t3(aa, tc, rd), 2n), 1n) == rd : Bool}:
  match aa tc rd:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def mr_s7_le(+op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.is_le(mr_s7(op, aa, tc, rd), 127n) == True{} : Bool}:
  mr_bound8(op, 15n, mr_t3(aa, tc, rd), eop, mr_t3_le(aa, tc, rd))

def mr_hi_mod(+qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n) == mr_s7(op, aa, tc, rd) : Nat}:
  mr_mod(E.bit(qr), 127n, mr_s7(op, aa, tc, rd), mr_s7_le(op, aa, tc, rd, eop))

def mr_hi_qr(qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)) == qr : Bool}:
  match qr:
    case True{}:
      mr_le_zero(mr_s7(op, aa, tc, rd))
    case False{}:
      mr_le_not_gt(mr_s7(op, aa, tc, rd), 127n, mr_s7_le(op, aa, tc, rd, eop))

def mr_hi_le(qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.is_le(E.flags_hi(qr, op, aa, tc, rd), 255n) == True{} : Bool}:
  match qr:
    case True{}:
      mr_s7_le(op, aa, tc, rd, eop)
    case False{}:
      mr_le_trans(mr_s7(op, aa, tc, rd), 127n, 255n, mr_s7_le(op, aa, tc, rd, eop), {==})

def mr_u_le(cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool}) -> {Nat.is_le(mr_u(cd, rc), 31n) == True{} : Bool}:
  match cd:
    case True{}:
      erc
    case False{}:
      mr_le_trans(rc, 15n, 31n, erc, {==})

def mr_v_le(ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool}) -> {Nat.is_le(mr_v(ad, cd, rc), 63n) == True{} : Bool}:
  match ad:
    case True{}:
      mr_u_le(cd, rc, erc)
    case False{}:
      mr_le_trans(mr_u(cd, rc), 31n, 63n, mr_u_le(cd, rc, erc), {==})

def mr_v_le127(+ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool}) -> {Nat.is_le(mr_v(ad, cd, rc), 127n) == True{} : Bool}:
  mr_le_trans(mr_v(ad, cd, rc), 63n, 127n, mr_v_le(ad, cd, rc, erc), {==})

def mr_lo_mod(+ra: Bool, +ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n) == mr_v(ad, cd, rc) : Nat}:
  mr_mod(E.bit(ra), 127n, mr_v(ad, cd, rc), mr_v_le127(ad, cd, rc, erc))

def mr_lo_ra(ra: Bool, +ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.is_le(128n, E.flags_lo(ra, ad, cd, rc)) == ra : Bool}:
  match ra:
    case True{}:
      mr_le_zero(mr_v(ad, cd, rc))
    case False{}:
      mr_le_not_gt(mr_v(ad, cd, rc), 127n, mr_v_le127(ad, cd, rc, erc))

def mr_lo_le(ra: Bool, +ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.is_le(E.flags_lo(ra, ad, cd, rc), 255n) == True{} : Bool}:
  match ra:
    case True{}:
      mr_v_le127(ad, cd, rc, erc)
    case False{}:
      mr_le_trans(mr_v(ad, cd, rc), 127n, 255n, mr_v_le127(ad, cd, rc, erc), {==})

def mr_v_mod64(+ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.mod(mr_v(ad, cd, rc), 64n) == mr_v(ad, cd, rc) : Nat}:
  mr_mod(0n, 63n, mr_v(ad, cd, rc), mr_v_le(ad, cd, rc, erc))

def mr_v_ad(ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.is_le(32n, mr_v(ad, cd, rc)) == ad : Bool}:
  match ad:
    case True{}:
      mr_le_zero(mr_u(cd, rc))
    case False{}:
      mr_le_not_gt(mr_u(cd, rc), 31n, mr_u_le(cd, rc, erc))

def mr_v_mod32(+ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.mod(mr_v(ad, cd, rc), 32n) == mr_u(cd, rc) : Nat}:
  mr_mod(E.bit(ad), 31n, mr_u(cd, rc), mr_u_le(cd, rc, erc))

def mr_u_cd(cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool}) -> {Nat.is_le(16n, mr_u(cd, rc)) == cd : Bool}:
  match cd:
    case True{}:
      mr_le_zero(rc)
    case False{}:
      mr_le_not_gt(rc, 15n, erc)

def mr_lo_rc(ra: Bool, ad: Bool, cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.mod(E.flags_lo(ra, ad, cd, rc), 16n) == rc : Nat}:
  match ra ad cd:
    case True{} True{} True{}:
      mr_mod(11n, 15n, rc, erc)
    case True{} True{} False{}:
      mr_mod(10n, 15n, rc, erc)
    case True{} False{} True{}:
      mr_mod(9n, 15n, rc, erc)
    case True{} False{} False{}:
      mr_mod(8n, 15n, rc, erc)
    case False{} True{} True{}:
      mr_mod(3n, 15n, rc, erc)
    case False{} True{} False{}:
      mr_mod(2n, 15n, rc, erc)
    case False{} False{} True{}:
      mr_mod(1n, 15n, rc, erc)
    case False{} False{} False{}:
      mr_mod(0n, 15n, rc, erc)

# The flags' second field byte, inner value t3, under mod(hi, 128) and mod 8.
def mr_hi_b(+qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n) == mr_t3(aa, tc, rd) : Nat}:
  Equal.trans(Nat, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), Nat.mod(mr_s7(op, aa, tc, rd), 8n), mr_t3(aa, tc, rd),
    Equal.cong(Nat, Nat, x => Nat.mod(x, 8n), Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), mr_s7(op, aa, tc, rd), mr_hi_mod(qr, op, aa, tc, rd, eop)),
    mr_mod(op, 7n, mr_t3(aa, tc, rd), mr_t3_le(aa, tc, rd)))

def mr_hi_op(+qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n) == op : Nat}:
  Equal.trans(Nat, Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), Nat.div(mr_s7(op, aa, tc, rd), 8n), op,
    Equal.cong(Nat, Nat, x => Nat.div(x, 8n), Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), mr_s7(op, aa, tc, rd), mr_hi_mod(qr, op, aa, tc, rd, eop)),
    mr_div(op, 7n, mr_t3(aa, tc, rd), mr_t3_le(aa, tc, rd)))

def mr_hi_aa(+qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.is_le(4n, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n)) == aa : Bool}:
  Equal.trans(Bool, Nat.is_le(4n, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n)), Nat.is_le(4n, mr_t3(aa, tc, rd)), aa,
    Equal.cong(Nat, Bool, x => Nat.is_le(4n, x), Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), mr_t3(aa, tc, rd), mr_hi_b(qr, op, aa, tc, rd, eop)),
    mr_t3_aa(aa, tc, rd))

def mr_hi_tc(+qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.is_le(2n, Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 4n)) == tc : Bool}:
  Equal.trans(Bool, Nat.is_le(2n, Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 4n)), Nat.is_le(2n, Nat.mod(mr_t3(aa, tc, rd), 4n)), tc,
    Equal.cong(Nat, Bool, x => Nat.is_le(2n, Nat.mod(x, 4n)), Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), mr_t3(aa, tc, rd), mr_hi_b(qr, op, aa, tc, rd, eop)),
    mr_t3_tc(aa, tc, rd))

def mr_hi_rd(+qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +eop: {Nat.is_le(op, 15n) == True{} : Bool})
  -> {Nat.is_eq(Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 2n), 1n) == rd : Bool}:
  Equal.trans(Bool, Nat.is_eq(Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 2n), 1n), Nat.is_eq(Nat.mod(mr_t3(aa, tc, rd), 2n), 1n), rd,
    Equal.cong(Nat, Bool, x => Nat.is_eq(Nat.mod(x, 2n), 1n), Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), mr_t3(aa, tc, rd), mr_hi_b(qr, op, aa, tc, rd, eop)),
    mr_t3_rd(aa, tc, rd))

def mr_lo_ad(+ra: Bool, +ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.is_le(32n, Nat.mod(Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), 64n)) == ad : Bool}:
  Equal.trans(Bool, Nat.is_le(32n, Nat.mod(Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), 64n)), Nat.is_le(32n, Nat.mod(mr_v(ad, cd, rc), 64n)), ad,
    Equal.cong(Nat, Bool, x => Nat.is_le(32n, Nat.mod(x, 64n)), Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), mr_v(ad, cd, rc), mr_lo_mod(ra, ad, cd, rc, erc)),
    Equal.trans(Bool, Nat.is_le(32n, Nat.mod(mr_v(ad, cd, rc), 64n)), Nat.is_le(32n, mr_v(ad, cd, rc)), ad,
      Equal.cong(Nat, Bool, x => Nat.is_le(32n, x), Nat.mod(mr_v(ad, cd, rc), 64n), mr_v(ad, cd, rc), mr_v_mod64(ad, cd, rc, erc)),
      mr_v_ad(ad, cd, rc, erc)))

def mr_lo_cd(+ra: Bool, +ad: Bool, +cd: Bool, +rc: Nat, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {Nat.is_le(16n, Nat.mod(Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), 32n)) == cd : Bool}:
  Equal.trans(Bool, Nat.is_le(16n, Nat.mod(Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), 32n)), Nat.is_le(16n, Nat.mod(mr_v(ad, cd, rc), 32n)), cd,
    Equal.cong(Nat, Bool, x => Nat.is_le(16n, Nat.mod(x, 32n)), Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), mr_v(ad, cd, rc), mr_lo_mod(ra, ad, cd, rc, erc)),
    Equal.trans(Bool, Nat.is_le(16n, Nat.mod(mr_v(ad, cd, rc), 32n)), Nat.is_le(16n, mr_u(cd, rc)), cd,
      Equal.cong(Nat, Bool, x => Nat.is_le(16n, x), Nat.mod(mr_v(ad, cd, rc), 32n), mr_u(cd, rc), mr_v_mod32(ad, cd, rc, erc)),
      mr_u_cd(cd, rc, erc)))

# header.of unpacks the packed flags.
def mr_header_of(+id: Nat, +qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +ra: Bool, +ad: Bool, +cd: Bool, +rc: Nat,
  +eop: {Nat.is_le(op, 15n) == True{} : Bool}, +erc: {Nat.is_le(rc, 15n) == True{} : Bool})
  -> {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc} : M.Header}:
  %mr_hi_qr(qr, op, aa, tc, rd, eop) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, _, op, aa, tc, rd, ra, ad, cd, rc} : M.Header}
  %mr_hi_op(qr, op, aa, tc, rd, eop) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)), _, aa, tc, rd, ra, ad, cd, rc} : M.Header}
  %mr_hi_aa(qr, op, aa, tc, rd, eop) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)), Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), _, tc, rd, ra, ad, cd, rc} : M.Header}
  %mr_hi_tc(qr, op, aa, tc, rd, eop) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)), Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), Nat.is_le(4n, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n)), _, rd, ra, ad, cd, rc} : M.Header}
  %mr_hi_rd(qr, op, aa, tc, rd, eop) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)), Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), Nat.is_le(4n, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n)), Nat.is_le(2n, Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 4n)), _, ra, ad, cd, rc} : M.Header}
  %mr_lo_ra(ra, ad, cd, rc, erc) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)), Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), Nat.is_le(4n, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n)), Nat.is_le(2n, Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 4n)), Nat.is_eq(Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 2n), 1n), _, ad, cd, rc} : M.Header}
  %mr_lo_ad(ra, ad, cd, rc, erc) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)), Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), Nat.is_le(4n, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n)), Nat.is_le(2n, Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 4n)), Nat.is_eq(Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 2n), 1n), Nat.is_le(128n, E.flags_lo(ra, ad, cd, rc)), _, cd, rc} : M.Header}
  %mr_lo_cd(ra, ad, cd, rc, erc) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)), Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), Nat.is_le(4n, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n)), Nat.is_le(2n, Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 4n)), Nat.is_eq(Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 2n), 1n), Nat.is_le(128n, E.flags_lo(ra, ad, cd, rc)), Nat.is_le(32n, Nat.mod(Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), 64n)), _, rc} : M.Header}
  %mr_lo_rc(ra, ad, cd, rc, erc) : {D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)) == M.Header{id, Nat.is_le(128n, E.flags_hi(qr, op, aa, tc, rd)), Nat.div(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), Nat.is_le(4n, Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n)), Nat.is_le(2n, Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 4n)), Nat.is_eq(Nat.mod(Nat.mod(Nat.mod(E.flags_hi(qr, op, aa, tc, rd), 128n), 8n), 2n), 1n), Nat.is_le(128n, E.flags_lo(ra, ad, cd, rc)), Nat.is_le(32n, Nat.mod(Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), 64n)), Nat.is_le(16n, Nat.mod(Nat.mod(E.flags_lo(ra, ad, cd, rc), 128n), 32n)), _} : M.Header}
  {==}

def HeadRes() -> Data:
  Result<&2, &2, M.DecodeError, D.HeadAt>

# The 12 header bytes read back (lemma 1).
def mr_header(+id: Nat, +qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +ra: Bool, +ad: Bool, +cd: Bool, +rc: Nat,
  +qd: Nat, +an: Nat, +ns: Nat, +ar: Nat, +ys: BL(), +pos: Nat, +hp: Nat,
  +eid: {Nat.is_le(id, 65535n) == True{} : Bool}, +eop: {Nat.is_le(op, 15n) == True{} : Bool}, +erc: {Nat.is_le(rc, 15n) == True{} : Bool},
  +eqd: {Nat.is_le(qd, 65535n) == True{} : Bool}, +ean: {Nat.is_le(an, 65535n) == True{} : Bool}, +ens: {Nat.is_le(ns, 65535n) == True{} : Bool}, +ear: {Nat.is_le(ar, 65535n) == True{} : Bool})
  -> {D.header(D.Cur{E.header_onto(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qd, an, ns, ar, ys), pos, hp}) == Done{D.HeadAt{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}:
  %mr_header_of(id, qr, op, aa, tc, rd, ra, ad, cd, rc, eop, erc) : {D.header(D.Cur{E.header_onto(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qd, an, ns, ar, ys), pos, hp}) == Done{D.HeadAt{_, qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}
  %mr_u16s(id, E.u8_onto(E.flags_hi(qr, op, aa, tc, rd), E.u8_onto(E.flags_lo(ra, ad, cd, rc), W.put_u16_onto(qd, W.put_u16_onto(an, W.put_u16_onto(ns, W.put_u16_onto(ar, ys)))))), eid) : {D.head.id(D.num(_, 2n, pos, hp)) == Done{D.HeadAt{D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)), qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}
  %mr_u8s(E.flags_hi(qr, op, aa, tc, rd), E.u8_onto(E.flags_lo(ra, ad, cd, rc), W.put_u16_onto(qd, W.put_u16_onto(an, W.put_u16_onto(ns, W.put_u16_onto(ar, ys))))), mr_hi_le(qr, op, aa, tc, rd, eop)) : {D.head.hi(id, D.num(_, 1n, Nat.add(2n, pos), hp)) == Done{D.HeadAt{D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)), qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}
  %mr_u8s(E.flags_lo(ra, ad, cd, rc), W.put_u16_onto(qd, W.put_u16_onto(an, W.put_u16_onto(ns, W.put_u16_onto(ar, ys)))), mr_lo_le(ra, ad, cd, rc, erc)) : {D.head.lo(id, E.flags_hi(qr, op, aa, tc, rd), D.num(_, 1n, Nat.add(3n, pos), hp)) == Done{D.HeadAt{D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)), qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}
  %mr_u16s(qd, W.put_u16_onto(an, W.put_u16_onto(ns, W.put_u16_onto(ar, ys))), eqd) : {D.head.qd(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc), D.num(_, 2n, Nat.add(4n, pos), hp)) == Done{D.HeadAt{D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)), qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}
  %mr_u16s(an, W.put_u16_onto(ns, W.put_u16_onto(ar, ys)), ean) : {D.head.an(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc), qd, D.num(_, 2n, Nat.add(6n, pos), hp)) == Done{D.HeadAt{D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)), qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}
  %mr_u16s(ns, W.put_u16_onto(ar, ys), ens) : {D.head.ns(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc), qd, an, D.num(_, 2n, Nat.add(8n, pos), hp)) == Done{D.HeadAt{D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)), qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}
  %mr_u16s(ar, ys, ear) : {D.head.ar(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc), qd, an, ns, D.num(_, 2n, Nat.add(10n, pos), hp)) == Done{D.HeadAt{D.header.of(id, E.flags_hi(qr, op, aa, tc, rd), E.flags_lo(ra, ad, cd, rc)), qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} : HeadRes()}
  {==}

# The encoder's loops (lemma 5)
# -----------------------------

def mr_groups_go(xs: List<&2, Nat>, +acc: List<&2, Nat>, +ys: BL())
  -> {E.groups.go(B.rev(Nat, xs, acc), ys) == E.groups.go(acc, E.groups.spec(xs, ys)) : BL()}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mr_groups_go(t, h <> acc, ys)

def mr_groups_onto(+xs: List<&2, Nat>, +ys: BL()) -> {E.groups_onto(xs, ys) == E.groups.spec(xs, ys) : BL()}:
  mr_groups_go(xs, Nil{}, ys)

def mr_txt_go(xs: List<&2, List<&2, U32>>, +acc: List<&2, List<&2, U32>>, +ys: BL())
  -> {E.txt.go(B.rev(List<&2, U32>, xs, acc), ys) == E.txt.go(acc, E.txt.spec(xs, ys)) : BL()}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mr_txt_go(t, h <> acc, ys)

def mr_txt_onto(+xs: List<&2, List<&2, U32>>, +ys: BL()) -> {E.txt_onto(xs, ys) == E.txt.spec(xs, ys) : BL()}:
  mr_txt_go(xs, Nil{}, ys)

def mr_questions_go(xs: List<&2, M.Question>, +acc: List<&2, M.Question>, +ys: BL())
  -> {E.questions.go(B.rev(M.Question, xs, acc), ys) == E.questions.go(acc, E.questions.spec(xs, ys)) : BL()}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mr_questions_go(t, h <> acc, ys)

def mr_questions_onto(+xs: List<&2, M.Question>, +ys: BL()) -> {E.questions_onto(xs, ys) == E.questions.spec(xs, ys) : BL()}:
  mr_questions_go(xs, Nil{}, ys)

def mr_records_go(xs: List<&2, M.Record>, +acc: List<&2, M.Record>, +ys: BL())
  -> {E.records.go(B.rev(M.Record, xs, acc), ys) == E.records.go(acc, E.records.spec(xs, ys)) : BL()}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mr_records_go(t, h <> acc, ys)

def mr_records_onto(+xs: List<&2, M.Record>, +ys: BL()) -> {E.records_onto(xs, ys) == E.records.spec(xs, ys) : BL()}:
  mr_records_go(xs, Nil{}, ys)

def mr_groups_ok_go(xs: List<&2, Nat>, b: Bool) -> {E.groups_ok.go(xs, b) == Bool.and(b, E.groups_ok.spec(xs)) : Bool}:
  match xs:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{+h, +t}:
      match b:
        case True{}:
          mr_groups_ok_go(t, E.u16_ok(h))
        case False{}:
          mr_groups_ok_go(t, False{})

def mr_strings_ok_go(xs: List<&2, List<&2, U32>>, b: Bool) -> {E.strings_ok.go(xs, b) == Bool.and(b, E.strings_ok.spec(xs)) : Bool}:
  match xs:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{+h, +t}:
      match b:
        case True{}:
          mr_strings_ok_go(t, E.string_ok(h))
        case False{}:
          mr_strings_ok_go(t, False{})

def mr_questions_ok_go(xs: List<&2, M.Question>, b: Bool) -> {E.questions_ok.go(xs, b) == Bool.and(b, E.questions_ok.spec(xs)) : Bool}:
  match xs:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{+h, +t}:
      match b:
        case True{}:
          mr_questions_ok_go(t, E.question_ok(h))
        case False{}:
          mr_questions_ok_go(t, False{})

def mr_records_ok_go(xs: List<&2, M.Record>, b: Bool) -> {E.records_ok.go(xs, b) == Bool.and(b, E.records_ok.spec(xs)) : Bool}:
  match xs:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{+h, +t}:
      match b:
        case True{}:
          mr_records_ok_go(t, E.record_ok(h))
        case False{}:
          mr_records_ok_go(t, False{})

# RDATA pieces (lemma 4)
# ----------------------

def mr_read_name_s(-ix: IX(), +n: NL(), +r: BL(), +pos: Nat, +hp: Nat, +e: {NM.ok(n) == True{} : Bool})
  -> {Done{D.NameAt{n, D.Cur{r, Nat.add(NM.wire_size(n), pos), hp}}} == D.read_name(ix, D.Cur{NM.wire_onto(n, r), pos, hp}) : NameRes()}:
  Equal.sym(NameRes(), D.read_name(ix, D.Cur{NM.wire_onto(n, r), pos, hp}), Done{D.NameAt{n, D.Cur{r, Nat.add(NM.wire_size(n), pos), hp}}},
    mr_read_name(ix, n, r, pos, hp, e))

def mr_gpos(gs: List<&2, Nat>, p: Nat) -> Nat:
  match gs:
    case Nil{}:
      p
    case Con{g, t}:
      mr_gpos(t, Nat.add(2n, p))

# The IPv6 groups, each a u16.
def mr_groups(gs: List<&2, Nat>, +acc: List<&2, Nat>, +p: Nat, +h: Nat, +ys: BL(), +e: {E.groups_ok.spec(gs) == True{} : Bool})
  -> {D.g.go(List.length(&2, Nat, gs), D.GOk{D.Cur{E.groups.spec(gs, ys), p, h}, acc})
      == D.GOk{D.Cur{ys, mr_gpos(gs, p), h}, B.rev(Nat, gs, acc)} : D.GSt}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      %mr_u16s(g, E.groups.spec(t, ys), mr_and_l(E.u16_ok(g), E.groups_ok.spec(t), e)) :
        {D.g.go(List.length(&2, Nat, t), D.g.next(D.num(_, 2n, p, h), acc))
          == D.GOk{D.Cur{ys, mr_gpos(g <> t, p), h}, B.rev(Nat, g <> t, acc)} : D.GSt}
      mr_groups(t, g <> acc, Nat.add(2n, p), h, ys, mr_and_r(E.u16_ok(g), E.groups_ok.spec(t), e))

# The bytes of one character-string, after its length byte.
def mr_txt_in(t: BL(), +b: U32, +cur: BL(), +acc: NL(), +ys: BL())
  -> {D.txt.go(List.append(&2, U32, b <> t, ys), D.TIn{List.length(&2, U32, t), cur, acc})
      == D.txt.go(ys, D.txt.str(B.all_bytes(B.rev(U32, B.rev(U32, t, b <> cur), Nil{})), B.rev(U32, B.rev(U32, t, b <> cur), Nil{}), acc)) : D.Txt}:
  match t:
    case Nil{}:
      {==}
    case Con{+b2, +t2}:
      mr_txt_in(t2, b2, b <> cur, acc, ys)

def mr_count_s(-A: Data, +xs: List<&2, A>) -> {List.length(&2, A, xs) == E.count(A, xs) : Nat}:
  Equal.sym(Nat, E.count(A, xs), List.length(&2, A, xs), mr_count(A, xs))

def mr_app_s(+xs: BL(), +ys: BL()) -> {List.append(&2, U32, xs, ys) == E.app(xs, ys) : BL()}:
  Equal.sym(BL(), E.app(xs, ys), List.append(&2, U32, xs, ys), mr_app(xs, ys))

# One character-string.
def mr_txt_str(s: BL(), +acc: NL(), +ys: BL(), +e: {E.string_ok(s) == True{} : Bool})
  -> {D.txt.go(E.string_onto(s, ys), D.TLen{acc}) == D.txt.go(ys, D.TLen{s <> acc}) : D.Txt}:
  match s:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      +ec = mr_and_l(E.u8_ok(E.count(U32, b <> t)), B.all_bytes(b <> t), e)
      +eb = mr_and_r(E.u8_ok(E.count(U32, b <> t)), B.all_bytes(b <> t), e)
      %mr_u8s(E.count(U32, b <> t), Nil{}, ec) : {D.txt.go(E.app(b <> t, ys), D.txt.len(_, acc)) == D.txt.go(ys, D.TLen{(b <> t) <> acc}) : D.Txt}
      %mr_count_s(U32, b <> t) : {D.txt.go(E.app(b <> t, ys), D.txt.len(Some{M.Got{_, Nil{}}}, acc)) == D.txt.go(ys, D.TLen{(b <> t) <> acc}) : D.Txt}
      %mr_app_s(b <> t, ys) : {D.txt.go(_, D.TIn{List.length(&2, U32, t), Nil{}, acc}) == D.txt.go(ys, D.TLen{(b <> t) <> acc}) : D.Txt}
      %eb : {D.txt.go(List.append(&2, U32, b <> t, ys), D.TIn{List.length(&2, U32, t), Nil{}, acc}) == D.txt.go(ys, D.txt.str(_, b <> t, acc)) : D.Txt}
      %mr_rev_inv(U32, b <> t) : {D.txt.go(List.append(&2, U32, b <> t, ys), D.TIn{List.length(&2, U32, t), Nil{}, acc}) == D.txt.go(ys, D.txt.str(B.all_bytes(_), _, acc)) : D.Txt}
      mr_txt_in(t, b, Nil{}, acc, ys)

# The character-strings of a TXT record.
def mr_txt(ss: NL(), +acc: NL(), +ys: BL(), +e: {E.strings_ok.spec(ss) == True{} : Bool})
  -> {D.txt.go(E.txt.spec(ss, ys), D.TLen{acc}) == D.txt.go(ys, D.TLen{B.rev(List<&2, U32>, ss, acc)}) : D.Txt}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      %mr_txt(t, s <> acc, ys, mr_and_r(E.string_ok(s), E.strings_ok.spec(t), e)) : {D.txt.go(E.txt.spec(s <> t, ys), D.TLen{acc}) == _ : D.Txt}
      mr_txt_str(s, acc, E.txt.spec(t, ys), mr_and_l(E.string_ok(s), E.strings_ok.spec(t), e))

def RecRes() -> Data:
  Result<&2, &2, M.DecodeError, D.RecAt>

def mr_groups_spec(+gs: List<&2, Nat>, +e: {E.groups_ok.go(gs, True{}) == True{} : Bool}) -> {E.groups_ok.spec(gs) == True{} : Bool}:
  %mr_groups_ok_go(gs, True{}) : {_ == True{} : Bool}
  e

def mr_strings_spec(+ss: NL(), +e: {E.strings_ok(ss) == True{} : Bool}) -> {E.strings_ok.spec(ss) == True{} : Bool}:
  %mr_strings_ok_go(ss, True{}) : {_ == True{} : Bool}
  e

# The RDATA of a valid record reads back by its type, using all its bytes.
def mr_rec_data(-ix: IX(), t: M.RType, d: M.RData, +n: NL(), +cl: Nat, +ttl: Nat, +after: BL(), +pos: Nat, +p: Nat, +h: Nat,
  +e: {E.data_ok(t, d) == True{} : Bool})
  -> {D.rec.data(n, t, cl, ttl, D.rdata(ix, t, D.Cur{E.rdata(d), p, h}), after, pos)
      == Done{D.RecAt{M.Record{n, t, D.class_of(cl), ttl, d}, D.Cur{after, pos, h}}} : RecRes()}:
  match t:
    case M.TA{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          %mr_u8s(a, E.u8_onto(b, E.u8_onto(c3, W.put_u8(x))), mr_and_l(E.u8_ok(a), E.u8_ok(b), mr_and_l(Bool.and(E.u8_ok(a), E.u8_ok(b)), E.u8_ok(c3), mr_and_l(Bool.and(Bool.and(E.u8_ok(a), E.u8_ok(b)), E.u8_ok(c3)), E.u8_ok(x), e)))) : {D.rec.data(n, M.TA{}, cl, ttl, D.ip4.a(D.num(_, 1n, p, h)), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u8s(b, E.u8_onto(c3, W.put_u8(x)), mr_and_r(E.u8_ok(a), E.u8_ok(b), mr_and_l(Bool.and(E.u8_ok(a), E.u8_ok(b)), E.u8_ok(c3), mr_and_l(Bool.and(Bool.and(E.u8_ok(a), E.u8_ok(b)), E.u8_ok(c3)), E.u8_ok(x), e)))) : {D.rec.data(n, M.TA{}, cl, ttl, D.ip4.b(a, D.num(_, 1n, Nat.add(1n, p), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u8s(c3, W.put_u8(x), mr_and_r(Bool.and(E.u8_ok(a), E.u8_ok(b)), E.u8_ok(c3), mr_and_l(Bool.and(Bool.and(E.u8_ok(a), E.u8_ok(b)), E.u8_ok(c3)), E.u8_ok(x), e))) : {D.rec.data(n, M.TA{}, cl, ttl, D.ip4.c(a, b, D.num(_, 1n, Nat.add(2n, p), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u8s(x, Nil{}, mr_and_r(Bool.and(Bool.and(E.u8_ok(a), E.u8_ok(b)), E.u8_ok(c3)), E.u8_ok(x), e)) : {D.rec.data(n, M.TA{}, cl, ttl, D.ip4.d(a, b, c3, D.num(_, 1n, Nat.add(3n, p), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}
          {==}
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TA{}, cl, ttl, D.rdata(ix, M.TA{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TA{}, cl, ttl, D.rdata(ix, M.TA{}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TA{}, cl, ttl, D.rdata(ix, M.TA{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TA{}, cl, ttl, D.rdata(ix, M.TA{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TA{}, cl, ttl, D.rdata(ix, M.TA{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TA{}, cl, ttl, D.rdata(ix, M.TA{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TA{}, cl, ttl, D.rdata(ix, M.TA{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TA{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TNS{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TNS{}, cl, ttl, D.rdata(ix, M.TNS{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TNS{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TNS{}, cl, ttl, D.rdata(ix, M.TNS{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TNS{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          %mr_read_name_s(ix, nm, Nil{}, p, h, e) : {D.rec.data(n, M.TNS{}, cl, ttl, D.rd.name(_), after, pos) == Done{D.RecAt{M.Record{n, M.TNS{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}
          {==}
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TNS{}, cl, ttl, D.rdata(ix, M.TNS{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TNS{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TNS{}, cl, ttl, D.rdata(ix, M.TNS{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TNS{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TNS{}, cl, ttl, D.rdata(ix, M.TNS{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TNS{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TNS{}, cl, ttl, D.rdata(ix, M.TNS{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TNS{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TNS{}, cl, ttl, D.rdata(ix, M.TNS{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TNS{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TCNAME{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TCNAME{}, cl, ttl, D.rdata(ix, M.TCNAME{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TCNAME{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TCNAME{}, cl, ttl, D.rdata(ix, M.TCNAME{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TCNAME{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          %mr_read_name_s(ix, nm, Nil{}, p, h, e) : {D.rec.data(n, M.TCNAME{}, cl, ttl, D.rd.name(_), after, pos) == Done{D.RecAt{M.Record{n, M.TCNAME{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}
          {==}
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TCNAME{}, cl, ttl, D.rdata(ix, M.TCNAME{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TCNAME{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TCNAME{}, cl, ttl, D.rdata(ix, M.TCNAME{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TCNAME{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TCNAME{}, cl, ttl, D.rdata(ix, M.TCNAME{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TCNAME{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TCNAME{}, cl, ttl, D.rdata(ix, M.TCNAME{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TCNAME{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TCNAME{}, cl, ttl, D.rdata(ix, M.TCNAME{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TCNAME{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TSOA{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TSOA{}, cl, ttl, D.rdata(ix, M.TSOA{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TSOA{}, cl, ttl, D.rdata(ix, M.TSOA{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TSOA{}, cl, ttl, D.rdata(ix, M.TSOA{}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TSOA{}, cl, ttl, D.rdata(ix, M.TSOA{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TSOA{}, cl, ttl, D.rdata(ix, M.TSOA{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          %mr_read_name_s(ix, mn, NM.wire_onto(rn, W.put_u32_onto(se, W.put_u32_onto(rf, W.put_u32_onto(rt, W.put_u32_onto(ex, W.put_u32(mi)))))), p, h, mr_and_l(NM.ok(mn), NM.ok(rn), mr_and_l(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se), mr_and_l(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex)), E.u32_ok(mi), e))))))) : {D.rec.data(n, M.TSOA{}, cl, ttl, D.rd.soa(ix, _), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_read_name_s(ix, rn, W.put_u32_onto(se, W.put_u32_onto(rf, W.put_u32_onto(rt, W.put_u32_onto(ex, W.put_u32(mi))))), Nat.add(NM.wire_size(mn), p), h, mr_and_r(NM.ok(mn), NM.ok(rn), mr_and_l(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se), mr_and_l(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex)), E.u32_ok(mi), e))))))) : {D.rec.data(n, M.TSOA{}, cl, ttl, D.soa.rn(mn, _), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u32s(se, W.put_u32_onto(rf, W.put_u32_onto(rt, W.put_u32_onto(ex, W.put_u32(mi)))), mr_and_r(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se), mr_and_l(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex)), E.u32_ok(mi), e)))))) : {D.rec.data(n, M.TSOA{}, cl, ttl, D.soa.se(mn, rn, D.num(_, 4n, Nat.add(NM.wire_size(rn), Nat.add(NM.wire_size(mn), p)), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u32s(rf, W.put_u32_onto(rt, W.put_u32_onto(ex, W.put_u32(mi))), mr_and_r(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex)), E.u32_ok(mi), e))))) : {D.rec.data(n, M.TSOA{}, cl, ttl, D.soa.rf(mn, rn, se, D.num(_, 4n, Nat.add(4n, Nat.add(NM.wire_size(rn), Nat.add(NM.wire_size(mn), p))), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u32s(rt, W.put_u32_onto(ex, W.put_u32(mi)), mr_and_r(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex)), E.u32_ok(mi), e)))) : {D.rec.data(n, M.TSOA{}, cl, ttl, D.soa.rt(mn, rn, se, rf, D.num(_, 4n, Nat.add(4n, Nat.add(4n, Nat.add(NM.wire_size(rn), Nat.add(NM.wire_size(mn), p)))), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u32s(ex, W.put_u32(mi), mr_and_r(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex)), E.u32_ok(mi), e))) : {D.rec.data(n, M.TSOA{}, cl, ttl, D.soa.ex(mn, rn, se, rf, rt, D.num(_, 4n, Nat.add(4n, Nat.add(4n, Nat.add(4n, Nat.add(NM.wire_size(rn), Nat.add(NM.wire_size(mn), p))))), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u32s(mi, Nil{}, mr_and_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(mn), NM.ok(rn)), E.u32_ok(se)), E.u32_ok(rf)), E.u32_ok(rt)), E.u32_ok(ex)), E.u32_ok(mi), e)) : {D.rec.data(n, M.TSOA{}, cl, ttl, D.soa.mi(mn, rn, se, rf, rt, ex, D.num(_, 4n, Nat.add(4n, Nat.add(4n, Nat.add(4n, Nat.add(4n, Nat.add(NM.wire_size(rn), Nat.add(NM.wire_size(mn), p)))))), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}
          {==}
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TSOA{}, cl, ttl, D.rdata(ix, M.TSOA{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TSOA{}, cl, ttl, D.rdata(ix, M.TSOA{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSOA{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TPTR{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TPTR{}, cl, ttl, D.rdata(ix, M.TPTR{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TPTR{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TPTR{}, cl, ttl, D.rdata(ix, M.TPTR{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TPTR{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          %mr_read_name_s(ix, nm, Nil{}, p, h, e) : {D.rec.data(n, M.TPTR{}, cl, ttl, D.rd.name(_), after, pos) == Done{D.RecAt{M.Record{n, M.TPTR{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}
          {==}
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TPTR{}, cl, ttl, D.rdata(ix, M.TPTR{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TPTR{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TPTR{}, cl, ttl, D.rdata(ix, M.TPTR{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TPTR{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TPTR{}, cl, ttl, D.rdata(ix, M.TPTR{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TPTR{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TPTR{}, cl, ttl, D.rdata(ix, M.TPTR{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TPTR{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TPTR{}, cl, ttl, D.rdata(ix, M.TPTR{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TPTR{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TMX{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TMX{}, cl, ttl, D.rdata(ix, M.TMX{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TMX{}, cl, ttl, D.rdata(ix, M.TMX{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TMX{}, cl, ttl, D.rdata(ix, M.TMX{}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          %mr_u16s(pr, NM.wire(nm), mr_and_l(E.u16_ok(pr), NM.ok(nm), e)) : {D.rec.data(n, M.TMX{}, cl, ttl, D.rd.mx(ix, D.num(_, 2n, p, h)), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_read_name_s(ix, nm, Nil{}, Nat.add(2n, p), h, mr_and_r(E.u16_ok(pr), NM.ok(nm), e)) : {D.rec.data(n, M.TMX{}, cl, ttl, D.mx.name(pr, _), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}
          {==}
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TMX{}, cl, ttl, D.rdata(ix, M.TMX{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TMX{}, cl, ttl, D.rdata(ix, M.TMX{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TMX{}, cl, ttl, D.rdata(ix, M.TMX{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TMX{}, cl, ttl, D.rdata(ix, M.TMX{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TMX{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TTXT{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TTXT{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TTXT{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TTXT{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TTXT{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          +es = mr_strings_spec(ss, e)
          %mr_rev_inv(List<&2, U32>, ss) : {D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TTXT{}, D.class_of(cl), ttl, M.RTxt{_}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_txt(ss, Nil{}, Nil{}, es) : {D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == D.rec.data(n, M.TTXT{}, cl, ttl, D.txt.end(_, p, h), after, pos) : RecRes()}
          %mr_txt_onto(ss, Nil{}) : {D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == D.rec.data(n, M.TTXT{}, cl, ttl, D.txt.end(D.txt.go(_, D.TLen{Nil{}}), p, h), after, pos) : RecRes()}
          {==}
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TTXT{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TTXT{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TTXT{}, cl, ttl, D.rdata(ix, M.TTXT{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TTXT{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TAAAA{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TAAAA{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          +e8 = Equal.trans(Nat, List.length(&2, Nat, gs), E.count(Nat, gs), 8n, mr_count_s(Nat, gs), mr_eq_true(E.count(Nat, gs), 8n, mr_and_l(Nat.is_eq(E.count(Nat, gs), 8n), E.groups_ok.go(gs, True{}), e)))
          +es = mr_groups_spec(gs, mr_and_r(Nat.is_eq(E.count(Nat, gs), 8n), E.groups_ok.go(gs, True{}), e))
          %mr_rev_inv(Nat, gs) : {D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TAAAA{}, D.class_of(cl), ttl, M.RIpv6{_}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_groups(gs, Nil{}, p, h, Nil{}, es) : {D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == D.rec.data(n, M.TAAAA{}, cl, ttl, D.g.end(_), after, pos) : RecRes()}
          %mr_groups_onto(gs, Nil{}) : {D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == D.rec.data(n, M.TAAAA{}, cl, ttl, D.g.end(D.g.go(List.length(&2, Nat, gs), D.GOk{D.Cur{_, p, h}, Nil{}})), after, pos) : RecRes()}
          %e8 : {D.rec.data(n, M.TAAAA{}, cl, ttl, D.g.end(D.g.go(_, D.GOk{D.Cur{E.groups_onto(gs, Nil{}), p, h}, Nil{}})), after, pos) == D.rec.data(n, M.TAAAA{}, cl, ttl, D.g.end(D.g.go(List.length(&2, Nat, gs), D.GOk{D.Cur{E.groups_onto(gs, Nil{}), p, h}, Nil{}})), after, pos) : RecRes()}
          {==}
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TAAAA{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TAAAA{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TAAAA{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TAAAA{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TAAAA{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TAAAA{}, cl, ttl, D.rdata(ix, M.TAAAA{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TAAAA{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TSRV{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TSRV{}, cl, ttl, D.rdata(ix, M.TSRV{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TSRV{}, cl, ttl, D.rdata(ix, M.TSRV{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TSRV{}, cl, ttl, D.rdata(ix, M.TSRV{}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TSRV{}, cl, ttl, D.rdata(ix, M.TSRV{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TSRV{}, cl, ttl, D.rdata(ix, M.TSRV{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TSRV{}, cl, ttl, D.rdata(ix, M.TSRV{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          %mr_u16s(pr, W.put_u16_onto(w, W.put_u16_onto(po, NM.wire(tg))), mr_and_l(E.u16_ok(pr), E.u16_ok(w), mr_and_l(Bool.and(E.u16_ok(pr), E.u16_ok(w)), E.u16_ok(po), mr_and_l(Bool.and(Bool.and(E.u16_ok(pr), E.u16_ok(w)), E.u16_ok(po)), NM.ok(tg), e)))) : {D.rec.data(n, M.TSRV{}, cl, ttl, D.rd.srv(ix, D.num(_, 2n, p, h)), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u16s(w, W.put_u16_onto(po, NM.wire(tg)), mr_and_r(E.u16_ok(pr), E.u16_ok(w), mr_and_l(Bool.and(E.u16_ok(pr), E.u16_ok(w)), E.u16_ok(po), mr_and_l(Bool.and(Bool.and(E.u16_ok(pr), E.u16_ok(w)), E.u16_ok(po)), NM.ok(tg), e)))) : {D.rec.data(n, M.TSRV{}, cl, ttl, D.srv.w(ix, pr, D.num(_, 2n, Nat.add(2n, p), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_u16s(po, NM.wire(tg), mr_and_r(Bool.and(E.u16_ok(pr), E.u16_ok(w)), E.u16_ok(po), mr_and_l(Bool.and(Bool.and(E.u16_ok(pr), E.u16_ok(w)), E.u16_ok(po)), NM.ok(tg), e))) : {D.rec.data(n, M.TSRV{}, cl, ttl, D.srv.po(ix, pr, w, D.num(_, 2n, Nat.add(4n, p), h)), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}
          %mr_read_name_s(ix, tg, Nil{}, Nat.add(6n, p), h, mr_and_r(Bool.and(Bool.and(E.u16_ok(pr), E.u16_ok(w)), E.u16_ok(po)), NM.ok(tg), e)) : {D.rec.data(n, M.TSRV{}, cl, ttl, D.srv.name(pr, w, po, _), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}
          {==}
        case M.RRaw{+bs}:
          mr_absurd({D.rec.data(n, M.TSRV{}, cl, ttl, D.rdata(ix, M.TSRV{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TSRV{}, D.class_of(cl), ttl, M.RRaw{bs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
    case M.TOPT{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TOPT{}, cl, ttl, D.rdata(ix, M.TOPT{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOPT{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TOPT{}, cl, ttl, D.rdata(ix, M.TOPT{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOPT{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TOPT{}, cl, ttl, D.rdata(ix, M.TOPT{}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOPT{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TOPT{}, cl, ttl, D.rdata(ix, M.TOPT{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOPT{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TOPT{}, cl, ttl, D.rdata(ix, M.TOPT{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOPT{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TOPT{}, cl, ttl, D.rdata(ix, M.TOPT{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOPT{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TOPT{}, cl, ttl, D.rdata(ix, M.TOPT{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOPT{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          %e : {D.rec.data(n, M.TOPT{}, cl, ttl, D.rdata(ix, M.TOPT{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == D.rec.data(n, M.TOPT{}, cl, ttl, D.raw.of(_, bs, p, h), after, pos) : RecRes()}
          {==}
    case M.TANY{}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TANY{}, cl, ttl, D.rdata(ix, M.TANY{}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TANY{}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TANY{}, cl, ttl, D.rdata(ix, M.TANY{}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TANY{}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TANY{}, cl, ttl, D.rdata(ix, M.TANY{}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TANY{}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TANY{}, cl, ttl, D.rdata(ix, M.TANY{}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TANY{}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TANY{}, cl, ttl, D.rdata(ix, M.TANY{}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TANY{}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TANY{}, cl, ttl, D.rdata(ix, M.TANY{}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TANY{}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TANY{}, cl, ttl, D.rdata(ix, M.TANY{}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TANY{}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          %e : {D.rec.data(n, M.TANY{}, cl, ttl, D.rdata(ix, M.TANY{}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == D.rec.data(n, M.TANY{}, cl, ttl, D.raw.of(_, bs, p, h), after, pos) : RecRes()}
          {==}
    case M.TOther{+tc}:
      match d:
        case M.RIpv4{+a, +b, +c3, +x}:
          mr_absurd({D.rec.data(n, M.TOther{tc}, cl, ttl, D.rdata(ix, M.TOther{tc}, D.Cur{E.rdata(M.RIpv4{a, b, c3, x}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOther{tc}, D.class_of(cl), ttl, M.RIpv4{a, b, c3, x}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RIpv6{+gs}:
          mr_absurd({D.rec.data(n, M.TOther{tc}, cl, ttl, D.rdata(ix, M.TOther{tc}, D.Cur{E.rdata(M.RIpv6{gs}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOther{tc}, D.class_of(cl), ttl, M.RIpv6{gs}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RName{+nm}:
          mr_absurd({D.rec.data(n, M.TOther{tc}, cl, ttl, D.rdata(ix, M.TOther{tc}, D.Cur{E.rdata(M.RName{nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOther{tc}, D.class_of(cl), ttl, M.RName{nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RMx{+pr, +nm}:
          mr_absurd({D.rec.data(n, M.TOther{tc}, cl, ttl, D.rdata(ix, M.TOther{tc}, D.Cur{E.rdata(M.RMx{pr, nm}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOther{tc}, D.class_of(cl), ttl, M.RMx{pr, nm}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RTxt{+ss}:
          mr_absurd({D.rec.data(n, M.TOther{tc}, cl, ttl, D.rdata(ix, M.TOther{tc}, D.Cur{E.rdata(M.RTxt{ss}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOther{tc}, D.class_of(cl), ttl, M.RTxt{ss}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSoa{+mn, +rn, +se, +rf, +rt, +ex, +mi}:
          mr_absurd({D.rec.data(n, M.TOther{tc}, cl, ttl, D.rdata(ix, M.TOther{tc}, D.Cur{E.rdata(M.RSoa{mn, rn, se, rf, rt, ex, mi}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOther{tc}, D.class_of(cl), ttl, M.RSoa{mn, rn, se, rf, rt, ex, mi}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RSrv{+pr, +w, +po, +tg}:
          mr_absurd({D.rec.data(n, M.TOther{tc}, cl, ttl, D.rdata(ix, M.TOther{tc}, D.Cur{E.rdata(M.RSrv{pr, w, po, tg}), p, h}), after, pos) == Done{D.RecAt{M.Record{n, M.TOther{tc}, D.class_of(cl), ttl, M.RSrv{pr, w, po, tg}}, D.Cur{after, pos, h}}} : RecRes()}, e)
        case M.RRaw{+bs}:
          %e : {D.rec.data(n, M.TOther{tc}, cl, ttl, D.rdata(ix, M.TOther{tc}, D.Cur{E.rdata(M.RRaw{bs}), p, h}), after, pos) == D.rec.data(n, M.TOther{tc}, cl, ttl, D.raw.of(_, bs, p, h), after, pos) : RecRes()}
          {==}

# Codes
# -----

def mr_free(k: Maybe<&2, M.RType>, e: {E.free.of(k) == True{} : Bool}) -> {None{} == k : Maybe<&2, M.RType>}:
  match k:
    case None{}:
      {==}
    case Some{x}:
      mr_absurd({None{} == Some{x} : Maybe<&2, M.RType>}, e)

def mr_type_of(t: M.RType, +e: {E.type_ok(t) == True{} : Bool}) -> {D.type_of(E.type_code(t)) == t : M.RType}:
  match t:
    case M.TA{}:
      {==}
    case M.TNS{}:
      {==}
    case M.TCNAME{}:
      {==}
    case M.TSOA{}:
      {==}
    case M.TPTR{}:
      {==}
    case M.TMX{}:
      {==}
    case M.TTXT{}:
      {==}
    case M.TAAAA{}:
      {==}
    case M.TSRV{}:
      {==}
    case M.TOPT{}:
      {==}
    case M.TANY{}:
      {==}
    case M.TOther{+c}:
      %mr_free(E.type_known(c), mr_and_r(E.u16_ok(c), E.type_free(c), e)) : {D.type_of.pick(_, c) == M.TOther{c} : M.RType}
      {==}

def mr_type_of_s(+t: M.RType, +e: {E.type_ok(t) == True{} : Bool}) -> {t == D.type_of(E.type_code(t)) : M.RType}:
  Equal.sym(M.RType, D.type_of(E.type_code(t)), t, mr_type_of(t, e))

def mr_type_code_ok(t: M.RType, +e: {E.type_ok(t) == True{} : Bool}) -> {Nat.is_le(E.type_code(t), 65535n) == True{} : Bool}:
  match t:
    case M.TA{}:
      {==}
    case M.TNS{}:
      {==}
    case M.TCNAME{}:
      {==}
    case M.TSOA{}:
      {==}
    case M.TPTR{}:
      {==}
    case M.TMX{}:
      {==}
    case M.TTXT{}:
      {==}
    case M.TAAAA{}:
      {==}
    case M.TSRV{}:
      {==}
    case M.TOPT{}:
      {==}
    case M.TANY{}:
      {==}
    case M.TOther{+c}:
      mr_and_l(E.u16_ok(c), E.type_free(c), e)

def mr_class_of(c: M.RClass, +e: {E.class_ok(c) == True{} : Bool}) -> {D.class_of(E.class_code(c)) == c : M.RClass}:
  match c:
    case M.CIN{}:
      {==}
    case M.COther{+k}:
      %Equal.sym(Bool, Nat.is_eq(k, 1n), False{}, mr_not_true(Nat.is_eq(k, 1n), mr_and_r(E.u16_ok(k), Bool.not(Nat.is_eq(k, 1n)), e))) :
        {D.class_of.pick(_, k) == M.COther{k} : M.RClass}
      {==}

def mr_class_code_ok(c: M.RClass, +e: {E.class_ok(c) == True{} : Bool}) -> {Nat.is_le(E.class_code(c), 65535n) == True{} : Bool}:
  match c:
    case M.CIN{}:
      {==}
    case M.COther{+k}:
      mr_and_l(E.u16_ok(k), Bool.not(Nat.is_eq(k, 1n)), e)

# Records (lemma 4)
# -----------------

def TakeM() -> Data:
  Maybe<&2, D.Taken>

def mr_take(xs: BL(), +acc: BL(), +ys: BL())
  -> {D.take.go(List.length(&2, U32, xs), List.append(&2, U32, xs, ys), acc) == Some{D.Taken{B.rev(U32, B.rev(U32, xs, acc), Nil{}), ys}} : TakeM()}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mr_take(t, h <> acc, ys)

def mr_take_c(+rd: BL(), +ys: BL()) -> {D.take.go(E.count(U32, rd), E.app(rd, ys), Nil{}) == Some{D.Taken{rd, ys}} : TakeM()}:
  %mr_rev_inv(U32, rd) : {D.take.go(E.count(U32, rd), E.app(rd, ys), Nil{}) == Some{D.Taken{_, ys}} : TakeM()}
  %mr_count_s(U32, rd) : {D.take.go(_, E.app(rd, ys), Nil{}) == Some{D.Taken{B.rev(U32, B.rev(U32, rd, Nil{}), Nil{}), ys}} : TakeM()}
  %mr_app_s(rd, ys) : {D.take.go(List.length(&2, U32, rd), _, Nil{}) == Some{D.Taken{B.rev(U32, B.rev(U32, rd, Nil{}), Nil{}), ys}} : TakeM()}
  mr_take(rd, Nil{}, ys)

def mr_take_s(+rd: BL(), +ys: BL()) -> {Some{D.Taken{rd, ys}} == D.take.go(E.count(U32, rd), E.app(rd, ys), Nil{}) : TakeM()}:
  Equal.sym(TakeM(), D.take.go(E.count(U32, rd), E.app(rd, ys), Nil{}), Some{D.Taken{rd, ys}}, mr_take_c(rd, ys))

# Where a record ends.
def mr_rpos(r: M.Record, pos: Nat) -> Nat:
  match r:
    case M.Record{n, t, c, ttl, d}:
      Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))))))

# One record reads back, the cursor past it.
def mr_record(-ix: IX(), r: M.Record, +ys: BL(), +pos: Nat, +hp: Nat, +e: {E.record_ok(r) == True{} : Bool})
  -> {D.record(ix, D.Cur{E.record_onto(r, ys), pos, hp}) == Done{D.RecAt{r, D.Cur{ys, mr_rpos(r, pos), hp}}} : RecRes()}:
  match r:
    case M.Record{+n, +t, +c, +ttl, +d}:
      %mr_class_of(c, mr_and_r(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), mr_and_l(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d)), E.u16_ok(E.count(U32, E.rdata(d))), e))))) : {D.record(ix, D.Cur{E.record_onto(M.Record{n, t, c, ttl, d}, ys), pos, hp}) == Done{D.RecAt{M.Record{n, t, _, ttl, d}, D.Cur{ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), hp}}} : RecRes()}
      %mr_read_name_s(ix, n, W.put_u16_onto(E.type_code(t), W.put_u16_onto(E.class_code(c), W.put_u32_onto(ttl, W.put_u16_onto(E.count(U32, E.rdata(d)), E.app(E.rdata(d), ys))))), pos, hp, mr_and_l(NM.ok(n), E.type_ok(t), mr_and_l(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), mr_and_l(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d)), E.u16_ok(E.count(U32, E.rdata(d))), e)))))) : {D.rec.name(ix, _) == Done{D.RecAt{M.Record{n, t, D.class_of(E.class_code(c)), ttl, d}, D.Cur{ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), hp}}} : RecRes()}
      %mr_u16s(E.type_code(t), W.put_u16_onto(E.class_code(c), W.put_u32_onto(ttl, W.put_u16_onto(E.count(U32, E.rdata(d)), E.app(E.rdata(d), ys)))), mr_type_code_ok(t, mr_and_r(NM.ok(n), E.type_ok(t), mr_and_l(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), mr_and_l(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d)), E.u16_ok(E.count(U32, E.rdata(d))), e))))))) : {D.rec.typ(ix, n, D.num(_, 2n, Nat.add(NM.wire_size(n), pos), hp)) == Done{D.RecAt{M.Record{n, t, D.class_of(E.class_code(c)), ttl, d}, D.Cur{ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), hp}}} : RecRes()}
      %mr_u16s(E.class_code(c), W.put_u32_onto(ttl, W.put_u16_onto(E.count(U32, E.rdata(d)), E.app(E.rdata(d), ys))), mr_class_code_ok(c, mr_and_r(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), mr_and_l(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d)), E.u16_ok(E.count(U32, E.rdata(d))), e)))))) : {D.rec.cls(ix, n, E.type_code(t), D.num(_, 2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)), hp)) == Done{D.RecAt{M.Record{n, t, D.class_of(E.class_code(c)), ttl, d}, D.Cur{ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), hp}}} : RecRes()}
      %mr_u32s(ttl, W.put_u16_onto(E.count(U32, E.rdata(d)), E.app(E.rdata(d), ys)), mr_and_r(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d)), E.u16_ok(E.count(U32, E.rdata(d))), e)))) : {D.rec.ttl(ix, n, E.type_code(t), E.class_code(c), D.num(_, 4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))), hp)) == Done{D.RecAt{M.Record{n, t, D.class_of(E.class_code(c)), ttl, d}, D.Cur{ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), hp}}} : RecRes()}
      %mr_u16s(E.count(U32, E.rdata(d)), E.app(E.rdata(d), ys), mr_and_r(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d)), E.u16_ok(E.count(U32, E.rdata(d))), e)) : {D.rec.len(ix, n, E.type_code(t), E.class_code(c), ttl, D.num(_, 2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))), hp)) == Done{D.RecAt{M.Record{n, t, D.class_of(E.class_code(c)), ttl, d}, D.Cur{ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), hp}}} : RecRes()}
      %mr_take_s(E.rdata(d), ys) : {D.rec.take(ix, n, D.type_of(E.type_code(t)), E.class_code(c), ttl, E.count(U32, E.rdata(d)), _, Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))))), hp) == Done{D.RecAt{M.Record{n, t, D.class_of(E.class_code(c)), ttl, d}, D.Cur{ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), hp}}} : RecRes()}
      %mr_type_of_s(t, mr_and_r(NM.ok(n), E.type_ok(t), mr_and_l(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), mr_and_l(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl), mr_and_l(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d)), E.u16_ok(E.count(U32, E.rdata(d))), e)))))) : {D.rec.data(n, _, E.class_code(c), ttl, D.rdata(ix, _, D.Cur{E.rdata(d), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))))), hp}), ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))))))) == Done{D.RecAt{M.Record{n, t, D.class_of(E.class_code(c)), ttl, d}, D.Cur{ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), hp}}} : RecRes()}
      mr_rec_data(ix, t, d, n, E.class_code(c), ttl, ys, Nat.add(E.count(U32, E.rdata(d)), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))))), Nat.add(2n, Nat.add(4n, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))))), hp, mr_and_r(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c)), E.u32_ok(ttl)), E.data_ok(t, d)), E.u16_ok(E.count(U32, E.rdata(d))), e)))


# Questions and sections (lemma 3)
# --------------------------------

def QRes() -> Data:
  Result<&2, &2, M.DecodeError, D.QAt>

def mr_qpos(q: M.Question, pos: Nat) -> Nat:
  match q:
    case M.Question{n, t, c}:
      Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)))

# One question reads back.
def mr_question(-ix: IX(), q: M.Question, +ys: BL(), +pos: Nat, +hp: Nat, +e: {E.question_ok(q) == True{} : Bool})
  -> {D.question(ix, D.Cur{E.question_onto(q, ys), pos, hp}) == Done{D.QAt{q, D.Cur{ys, mr_qpos(q, pos), hp}}} : QRes()}:
  match q:
    case M.Question{+n, +t, +c}:
      %mr_type_of(t, mr_and_r(NM.ok(n), E.type_ok(t), mr_and_l(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), e))) : {D.question(ix, D.Cur{E.question_onto(M.Question{n, t, c}, ys), pos, hp}) == Done{D.QAt{M.Question{n, _, c}, D.Cur{ys, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))), hp}}} : QRes()}
      %mr_class_of(c, mr_and_r(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), e)) : {D.question(ix, D.Cur{E.question_onto(M.Question{n, t, c}, ys), pos, hp}) == Done{D.QAt{M.Question{n, D.type_of(E.type_code(t)), _}, D.Cur{ys, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))), hp}}} : QRes()}
      %mr_read_name_s(ix, n, W.put_u16_onto(E.type_code(t), W.put_u16_onto(E.class_code(c), ys)), pos, hp, mr_and_l(NM.ok(n), E.type_ok(t), mr_and_l(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), e))) : {D.q.name(_) == Done{D.QAt{M.Question{n, D.type_of(E.type_code(t)), D.class_of(E.class_code(c))}, D.Cur{ys, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))), hp}}} : QRes()}
      %mr_u16s(E.type_code(t), W.put_u16_onto(E.class_code(c), ys), mr_type_code_ok(t, mr_and_r(NM.ok(n), E.type_ok(t), mr_and_l(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), e)))) : {D.q.typ(n, D.num(_, 2n, Nat.add(NM.wire_size(n), pos), hp)) == Done{D.QAt{M.Question{n, D.type_of(E.type_code(t)), D.class_of(E.class_code(c))}, D.Cur{ys, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))), hp}}} : QRes()}
      %mr_u16s(E.class_code(c), ys, mr_class_code_ok(c, mr_and_r(Bool.and(NM.ok(n), E.type_ok(t)), E.class_ok(c), e))) : {D.q.cls(n, E.type_code(t), D.num(_, 2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos)), hp)) == Done{D.QAt{M.Question{n, D.type_of(E.type_code(t)), D.class_of(E.class_code(c))}, D.Cur{ys, Nat.add(2n, Nat.add(2n, Nat.add(NM.wire_size(n), pos))), hp}}} : QRes()}
      {==}

def mr_question_s(-ix: IX(), +q: M.Question, +ys: BL(), +pos: Nat, +hp: Nat, +e: {E.question_ok(q) == True{} : Bool})
  -> {Done{D.QAt{q, D.Cur{ys, mr_qpos(q, pos), hp}}} == D.question(ix, D.Cur{E.question_onto(q, ys), pos, hp}) : QRes()}:
  Equal.sym(QRes(), D.question(ix, D.Cur{E.question_onto(q, ys), pos, hp}), Done{D.QAt{q, D.Cur{ys, mr_qpos(q, pos), hp}}}, mr_question(ix, q, ys, pos, hp, e))

def mr_record_s(-ix: IX(), +r: M.Record, +ys: BL(), +pos: Nat, +hp: Nat, +e: {E.record_ok(r) == True{} : Bool})
  -> {Done{D.RecAt{r, D.Cur{ys, mr_rpos(r, pos), hp}}} == D.record(ix, D.Cur{E.record_onto(r, ys), pos, hp}) : RecRes()}:
  Equal.sym(RecRes(), D.record(ix, D.Cur{E.record_onto(r, ys), pos, hp}), Done{D.RecAt{r, D.Cur{ys, mr_rpos(r, pos), hp}}}, mr_record(ix, r, ys, pos, hp, e))

def QsRes() -> Data:
  Result<&2, &2, M.DecodeError, D.QsAt>

def mr_qspos(xs: List<&2, M.Question>, p: Nat) -> Nat:
  match xs:
    case Nil{}:
      p
    case Con{x, t}:
      mr_qspos(t, mr_qpos(x, p))

# The counted loop over a section.
def mr_qs(xs: List<&2, M.Question>, -ix: IX(), +acc: List<&2, M.Question>, +ys: BL(), +p: Nat, +hp: Nat, +e: {E.questions_ok.spec(xs) == True{} : Bool})
  -> {D.qs.go(List.length(&2, M.Question, xs), ix, D.QOk{D.Cur{E.questions.spec(xs, ys), p, hp}, acc})
      == D.QOk{D.Cur{ys, mr_qspos(xs, p), hp}, B.rev(M.Question, xs, acc)} : D.QSt}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %mr_question_s(ix, x, E.questions.spec(t, ys), p, hp, mr_and_l(E.question_ok(x), E.questions_ok.spec(t), e)) :
        {D.qs.go(List.length(&2, M.Question, t), ix, D.qs.next(_, acc))
          == D.QOk{D.Cur{ys, mr_qspos(x <> t, p), hp}, B.rev(M.Question, x <> t, acc)} : D.QSt}
      mr_qs(t, ix, x <> acc, ys, mr_qpos(x, p), hp, mr_and_r(E.question_ok(x), E.questions_ok.spec(t), e))

def mr_questions(-ix: IX(), +xs: List<&2, M.Question>, +ys: BL(), +p: Nat, +hp: Nat, +e: {E.questions_ok(xs) == True{} : Bool})
  -> {D.questions(E.count(M.Question, xs), ix, D.Cur{E.questions_onto(xs, ys), p, hp}) == Done{D.QsAt{xs, D.Cur{ys, mr_qspos(xs, p), hp}}} : QsRes()}:
  +es = Equal.trans(Bool, E.questions_ok.spec(xs), E.questions_ok.go(xs, True{}), True{},
    Equal.sym(Bool, E.questions_ok.go(xs, True{}), E.questions_ok.spec(xs), mr_questions_ok_go(xs, True{})), e)
  %mr_rev_inv(M.Question, xs) : {D.questions(E.count(M.Question, xs), ix, D.Cur{E.questions_onto(xs, ys), p, hp}) == Done{D.QsAt{_, D.Cur{ys, mr_qspos(xs, p), hp}}} : QsRes()}
  %mr_qs(xs, ix, Nil{}, ys, p, hp, es) : {D.questions(E.count(M.Question, xs), ix, D.Cur{E.questions_onto(xs, ys), p, hp}) == D.qs.end(_) : QsRes()}
  %mr_questions_onto(xs, ys) : {D.questions(E.count(M.Question, xs), ix, D.Cur{E.questions_onto(xs, ys), p, hp})
    == D.qs.end(D.qs.go(List.length(&2, M.Question, xs), ix, D.QOk{D.Cur{_, p, hp}, Nil{}})) : QsRes()}
  %mr_count(M.Question, xs) : {D.questions(E.count(M.Question, xs), ix, D.Cur{E.questions_onto(xs, ys), p, hp})
    == D.qs.end(D.qs.go(_, ix, D.QOk{D.Cur{E.questions_onto(xs, ys), p, hp}, Nil{}})) : QsRes()}
  {==}

def mr_questions_s(-ix: IX(), +xs: List<&2, M.Question>, +ys: BL(), +p: Nat, +hp: Nat, +e: {E.questions_ok(xs) == True{} : Bool})
  -> {Done{D.QsAt{xs, D.Cur{ys, mr_qspos(xs, p), hp}}} == D.questions(E.count(M.Question, xs), ix, D.Cur{E.questions_onto(xs, ys), p, hp}) : QsRes()}:
  Equal.sym(QsRes(), D.questions(E.count(M.Question, xs), ix, D.Cur{E.questions_onto(xs, ys), p, hp}), Done{D.QsAt{xs, D.Cur{ys, mr_qspos(xs, p), hp}}},
    mr_questions(ix, xs, ys, p, hp, e))

def RsRes() -> Data:
  Result<&2, &2, M.DecodeError, D.RsAt>

def mr_rspos(xs: List<&2, M.Record>, p: Nat) -> Nat:
  match xs:
    case Nil{}:
      p
    case Con{x, t}:
      mr_rspos(t, mr_rpos(x, p))

# The counted loop over a section.
def mr_rs(xs: List<&2, M.Record>, -ix: IX(), +acc: List<&2, M.Record>, +ys: BL(), +p: Nat, +hp: Nat, +e: {E.records_ok.spec(xs) == True{} : Bool})
  -> {D.rs.go(List.length(&2, M.Record, xs), ix, D.ROk{D.Cur{E.records.spec(xs, ys), p, hp}, acc})
      == D.ROk{D.Cur{ys, mr_rspos(xs, p), hp}, B.rev(M.Record, xs, acc)} : D.RSt}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %mr_record_s(ix, x, E.records.spec(t, ys), p, hp, mr_and_l(E.record_ok(x), E.records_ok.spec(t), e)) :
        {D.rs.go(List.length(&2, M.Record, t), ix, D.rs.next(_, acc))
          == D.ROk{D.Cur{ys, mr_rspos(x <> t, p), hp}, B.rev(M.Record, x <> t, acc)} : D.RSt}
      mr_rs(t, ix, x <> acc, ys, mr_rpos(x, p), hp, mr_and_r(E.record_ok(x), E.records_ok.spec(t), e))

def mr_records(-ix: IX(), +xs: List<&2, M.Record>, +ys: BL(), +p: Nat, +hp: Nat, +e: {E.records_ok(xs) == True{} : Bool})
  -> {D.records(E.count(M.Record, xs), ix, D.Cur{E.records_onto(xs, ys), p, hp}) == Done{D.RsAt{xs, D.Cur{ys, mr_rspos(xs, p), hp}}} : RsRes()}:
  +es = Equal.trans(Bool, E.records_ok.spec(xs), E.records_ok.go(xs, True{}), True{},
    Equal.sym(Bool, E.records_ok.go(xs, True{}), E.records_ok.spec(xs), mr_records_ok_go(xs, True{})), e)
  %mr_rev_inv(M.Record, xs) : {D.records(E.count(M.Record, xs), ix, D.Cur{E.records_onto(xs, ys), p, hp}) == Done{D.RsAt{_, D.Cur{ys, mr_rspos(xs, p), hp}}} : RsRes()}
  %mr_rs(xs, ix, Nil{}, ys, p, hp, es) : {D.records(E.count(M.Record, xs), ix, D.Cur{E.records_onto(xs, ys), p, hp}) == D.rs.end(_) : RsRes()}
  %mr_records_onto(xs, ys) : {D.records(E.count(M.Record, xs), ix, D.Cur{E.records_onto(xs, ys), p, hp})
    == D.rs.end(D.rs.go(List.length(&2, M.Record, xs), ix, D.ROk{D.Cur{_, p, hp}, Nil{}})) : RsRes()}
  %mr_count(M.Record, xs) : {D.records(E.count(M.Record, xs), ix, D.Cur{E.records_onto(xs, ys), p, hp})
    == D.rs.end(D.rs.go(_, ix, D.ROk{D.Cur{E.records_onto(xs, ys), p, hp}, Nil{}})) : RsRes()}
  {==}

def mr_records_s(-ix: IX(), +xs: List<&2, M.Record>, +ys: BL(), +p: Nat, +hp: Nat, +e: {E.records_ok(xs) == True{} : Bool})
  -> {Done{D.RsAt{xs, D.Cur{ys, mr_rspos(xs, p), hp}}} == D.records(E.count(M.Record, xs), ix, D.Cur{E.records_onto(xs, ys), p, hp}) : RsRes()}:
  Equal.sym(RsRes(), D.records(E.count(M.Record, xs), ix, D.Cur{E.records_onto(xs, ys), p, hp}), Done{D.RsAt{xs, D.Cur{ys, mr_rspos(xs, p), hp}}},
    mr_records(ix, xs, ys, p, hp, e))

def MRes() -> Data:
  Result<&2, &2, M.DecodeError, M.Message>

def mr_header_s(+id: Nat, +qr: Bool, +op: Nat, +aa: Bool, +tc: Bool, +rd: Bool, +ra: Bool, +ad: Bool, +cd: Bool, +rc: Nat,
  +qd: Nat, +an: Nat, +ns: Nat, +ar: Nat, +ys: BL(), +pos: Nat, +hp: Nat,
  +eid: {Nat.is_le(id, 65535n) == True{} : Bool}, +eop: {Nat.is_le(op, 15n) == True{} : Bool}, +erc: {Nat.is_le(rc, 15n) == True{} : Bool},
  +eqd: {Nat.is_le(qd, 65535n) == True{} : Bool}, +ean: {Nat.is_le(an, 65535n) == True{} : Bool}, +ens: {Nat.is_le(ns, 65535n) == True{} : Bool}, +ear: {Nat.is_le(ar, 65535n) == True{} : Bool})
  -> {Done{D.HeadAt{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}} == D.header(D.Cur{E.header_onto(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qd, an, ns, ar, ys), pos, hp}) : HeadRes()}:
  Equal.sym(HeadRes(), D.header(D.Cur{E.header_onto(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qd, an, ns, ar, ys), pos, hp}), Done{D.HeadAt{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qd, an, ns, ar, D.Cur{ys, Nat.add(12n, pos), hp}}},
    mr_header(id, qr, op, aa, tc, rd, ra, ad, cd, rc, qd, an, ns, ar, ys, pos, hp, eid, eop, erc, eqd, ean, ens, ear))

# The whole message, for any index and hop budget (pointers are never met).
def mr_message(-ix: IX(), +hp: Nat, m: M.Message, +e: {E.message_ok(m) == True{} : Bool})
  -> {D.m.head(ix, D.header(D.Cur{E.message(m), 0n, hp})) == Done{m} : MRes()}:
  match m:
    case M.Message{h, +qs, +an, +ns, +ar}:
      match h:
        case M.Header{+id, +qr, +op, +aa, +tc, +rd, +ra, +ad, +cd, +rc}:
          +eh = mr_and_l(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs)), mr_and_l(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs), mr_and_l(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an), mr_and_l(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e))))))
          %mr_header_s(id, qr, op, aa, tc, rd, ra, ad, cd, rc, E.count(M.Question, qs), E.count(M.Record, an), E.count(M.Record, ns), E.count(M.Record, ar), E.questions_onto(qs, E.records_onto(an, E.records_onto(ns, E.records_onto(ar, Nil{})))), 0n, hp,
            mr_and_l(E.u16_ok(id), Nat.is_le(op, 15n), mr_and_l(Bool.and(E.u16_ok(id), Nat.is_le(op, 15n)), Nat.is_le(rc, 15n), eh)), mr_and_r(E.u16_ok(id), Nat.is_le(op, 15n), mr_and_l(Bool.and(E.u16_ok(id), Nat.is_le(op, 15n)), Nat.is_le(rc, 15n), eh)), mr_and_r(Bool.and(E.u16_ok(id), Nat.is_le(op, 15n)), Nat.is_le(rc, 15n), eh), mr_and_r(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs)), mr_and_l(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs), mr_and_l(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an), mr_and_l(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e)))))), mr_and_l(E.u16_ok(E.count(M.Record, an)), E.records_ok(an), mr_and_r(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an), mr_and_l(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e))))), mr_and_l(E.u16_ok(E.count(M.Record, ns)), E.records_ok(ns), mr_and_r(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e)))), mr_and_l(E.u16_ok(E.count(M.Record, ar)), E.records_ok(ar), mr_and_r(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e)))) :
            {D.m.head(ix, _) == Done{M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}} : MRes()}
          %mr_questions_s(ix, qs, E.records_onto(an, E.records_onto(ns, E.records_onto(ar, Nil{}))), Nat.add(12n, 0n), hp, mr_and_r(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs), mr_and_l(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an), mr_and_l(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e)))))) : {D.m.qs(ix, M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, E.count(M.Record, an), E.count(M.Record, ns), E.count(M.Record, ar), _) == Done{M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}} : MRes()}
          %mr_records_s(ix, an, E.records_onto(ns, E.records_onto(ar, Nil{})), mr_qspos(qs, Nat.add(12n, 0n)), hp, mr_and_r(E.u16_ok(E.count(M.Record, an)), E.records_ok(an), mr_and_r(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an), mr_and_l(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e)))))) : {D.m.an(ix, M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, E.count(M.Record, ns), E.count(M.Record, ar), _) == Done{M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}} : MRes()}
          %mr_records_s(ix, ns, E.records_onto(ar, Nil{}), mr_rspos(an, mr_qspos(qs, Nat.add(12n, 0n))), hp, mr_and_r(E.u16_ok(E.count(M.Record, ns)), E.records_ok(ns), mr_and_r(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e))))) : {D.m.ns(ix, M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, E.count(M.Record, ar), _) == Done{M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}} : MRes()}
          %mr_records_s(ix, ar, Nil{}, mr_rspos(ns, mr_rspos(an, mr_qspos(qs, Nat.add(12n, 0n)))), hp, mr_and_r(E.u16_ok(E.count(M.Record, ar)), E.records_ok(ar), mr_and_r(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar), mr_and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(E.header_ok(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}), E.u16_ok(E.count(M.Question, qs))), E.questions_ok(qs)), E.section_ok(an)), E.section_ok(ns)), E.section_ok(ar)), E.u16_ok(E.count(U32, E.message(M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}))), e)))) : {D.m.ar(M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, _) == Done{M.Message{M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}, qs, an, ns, ar}} : MRes()}
          {==}

def Laws.message_roundtrip(m, e):
  mr_message(D.index(E.message(m)), NM.len(E.message(m)), m, e)

