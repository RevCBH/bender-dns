# Laws 13-16: accepting a response, and an absolute name's candidates.
#
# accept(id, q, m) is the conjunction accept.header(id, h) && one_question(q,
# qs); laws 13-15 eliminate the conjunction and unfold accept.header. Law 16
# rewrites ends_dot(name) to True, after which candidates is [name] by
# computation (cand.pick(True, ...) = [name]).
import Base
import ../LAWS.bend as Laws
import ../src/types.bend as M
import ../src/conf.bend as CF
import ../src/answer.bend as A

# Bool facts
# ----------

def ac_bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ac_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : ac_bool_disc(_)
  Unit{}

def ac_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ac_false_ne_true(e))

def ac_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, ac_false_ne_true(e))

def ac_or_true_r(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Accepting
# ---------

# The question conjunct of an accepted message.
def ac_question(+id: Nat, +q: M.Question, +m: M.Message, e: {A.accept(id, q, m) == True{} : Bool})
  -> {A.one_question(q, Laws.msg_questions(m)) == True{} : Bool}:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      ac_and_r(A.accept.header(id, h), A.one_question(q, qs), e)

# The header conjunct holds QR and the id (it is (qr && op == 0) && rid == id).
def ac_header_qr(+id: Nat, +rid: Nat, +qr: Bool, +op: Nat,
  e: {Bool.and(Bool.and(qr, Nat.is_eq(op, 0n)), Nat.is_eq(rid, id)) == True{} : Bool})
  -> {qr == True{} : Bool}:
  ac_and_l(qr, Nat.is_eq(op, 0n),
    ac_and_l(Bool.and(qr, Nat.is_eq(op, 0n)), Nat.is_eq(rid, id), e))

def ac_header_id(+id: Nat, +rid: Nat, +qr: Bool, +op: Nat,
  e: {Bool.and(Bool.and(qr, Nat.is_eq(op, 0n)), Nat.is_eq(rid, id)) == True{} : Bool})
  -> {Nat.is_eq(rid, id) == True{} : Bool}:
  ac_and_r(Bool.and(qr, Nat.is_eq(op, 0n)), Nat.is_eq(rid, id), e)

def Laws.accept_id(id, q, m, e):
  match m:
    case M.Message{h, qs, an, ns, ar}:
      match h:
        case M.Header{rid, qr, op, aa, tc, rd, ra, ad, cd, rc}:
          ac_header_id(id, rid, qr, op,
            ac_and_l(A.accept.header(id, M.Header{rid, qr, op, aa, tc, rd, ra, ad, cd, rc}), A.one_question(q, qs), e))

def Laws.accept_qr(id, q, m, e):
  match m:
    case M.Message{h, qs, an, ns, ar}:
      match h:
        case M.Header{rid, qr, op, aa, tc, rd, ra, ad, cd, rc}:
          ac_header_qr(id, rid, qr, op,
            ac_and_l(A.accept.header(id, M.Header{rid, qr, op, aa, tc, rd, ra, ad, cd, rc}), A.one_question(q, qs), e))

def Laws.accept_question(id, q, m, e):
  ac_question(id, q, m, e)

# Candidates
# ----------

def Laws.candidates_absolute(conf, name, e):
  match conf:
    case M.Conf{ns, ss, nd, t, at}:
      %Equal.sym(Bool, CF.ends_dot(name), True{}, e) : {CF.cand.pick(Bool.or(CF.is_empty(name), _), Nat.is_le(nd, CF.dots.go(name, 0n)), ss, name) == [name] : List<&2, String>}
      %Equal.sym(Bool, Bool.or(CF.is_empty(name), True{}), True{}, ac_or_true_r(CF.is_empty(name))) : {CF.cand.pick(_, Nat.is_le(nd, CF.dots.go(name, 0n)), ss, name) == [name] : List<&2, String>}
      {==}
