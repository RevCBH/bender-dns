import Base
import ./bytes.bend as B
import ./types.bend as M
import ./name.bend as NM
import ./encode.bend as E

# Responses: does one answer the query, and what does it answer.
#
#   accept(id, q, m)   m is a response (QR = 1) to a standard query (opcode
#                      0) with the query's id, holding exactly one question,
#                      the query's: the same name (NM.eq, ASCII
#                      case-insensitively, RFC 4343), the same type and class
#                      (compared by code). The rcode and TC are not judged
#                      here (rcode(m), truncated(m)).
#   addresses(name, t, m)
#                      follows the CNAME chain from name within m's answer
#                      section: at each name, the answers owned by it (NM.eq)
#                      of type t (any type when t is TANY; a CNAME counts
#                      when t is TCNAME) are Found{name, those answers, in
#                      order}; else its CNAME (the first one, if several) is
#                      followed; else the chain has left the answer section:
#                      Alias{name} if at least one CNAME was followed (the
#                      resolver re-queries name), Nothing{} if none. At most
#                      MAX_HOPS CNAMEs are followed; a longer chain (or a
#                      loop) is Nothing{}. Only the answer section is read.
#
# Laws: accept(id, q, m) == True => the header's id is id and the questions
# are [p] with question_eq(q, p) (by unfolding: accept is the conjunction);
# addresses(name, t, m) == Found{n, rs} => every record of rs is an answer of
# m owned by n (NM.eq) and n is name or reached from it by the answers'
# CNAMEs (chain.go only ever moves to a CNAME's target, and matching keeps
# only owners NM.eq to the current name).
#
# NOTE (loops): matching.go and cname.go walk the answer section with
# direct tail calls (a response can hold thousands of records); chain.go is a
# loop on the hop count.

def MAX_HOPS() -> Nat:
  16n

# Header facts
# ------------

def header(m: M.Message) -> M.Header:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      h

def header.rcode(h: M.Header) -> Nat:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      rc

def header.tc(h: M.Header) -> Bool:
  match h:
    case M.Header{id, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      tc

# The response code (0 NOERROR, 2 SERVFAIL, 3 NXDOMAIN, 5 REFUSED, ...).
def rcode(m: M.Message) -> Nat:
  header.rcode(header(m))

# TC: the response was truncated.
def truncated(m: M.Message) -> Bool:
  header.tc(header(m))

# Accepting
# ---------

def type_eq(a: M.RType, b: M.RType) -> Bool:
  Nat.is_eq(E.type_code(a), E.type_code(b))

def class_eq(a: M.RClass, b: M.RClass) -> Bool:
  Nat.is_eq(E.class_code(a), E.class_code(b))

# The same question (the name case-insensitively).
def question_eq(q: M.Question, p: M.Question) -> Bool:
  match q p:
    case M.Question{n1, t1, c1} M.Question{n2, t2, c2}:
      NM.eq(n1, n2) && type_eq(t1, t2) && class_eq(c1, c2)

# qs is exactly [p] with p the question q.
def one_question(q: M.Question, qs: List<&2, M.Question>) -> Bool:
  match qs:
    case Con{p, Nil{}}:
      question_eq(q, p)
    case _:
      False{}

def accept.header(id: Nat, h: M.Header) -> Bool:
  match h:
    case M.Header{rid, qr, op, aa, tc, rd, ra, ad, cd, rc}:
      qr && Nat.is_eq(op, 0n) && Nat.is_eq(rid, id)

# m answers the query (id, q): see the top of the file.
def accept(id: Nat, q: M.Question, m: M.Message) -> Bool:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      accept.header(id, h) && one_question(q, qs)

# Answers
# -------

# A record of type rt is wanted for t.
def wants(t: M.RType, rt: M.RType) -> Bool:
  match t:
    case M.TANY{}:
      True{}
    case _:
      type_eq(t, rt)

def is_cname(t: M.RType) -> Bool:
  match t:
    case M.TCNAME{}:
      True{}
    case _:
      False{}

def keep(hit: Bool, r: M.Record, acc: List<&2, M.Record>) -> List<&2, M.Record>:
  match hit:
    case True{}:
      r <> acc
    case False{}:
      acc

def matching.at(+r: M.Record, +name: M.Name(), +t: M.RType, acc: List<&2, M.Record>) -> List<&2, M.Record>:
  match r:
    case M.Record{n, rt, c, ttl, d}:
      keep(NM.eq(n, name) && wants(t, rt), r, acc)

# The records of rs owned by name of a type t wants, reversed onto acc (a loop).
def matching.go(rs: List<&2, M.Record>, +name: M.Name(), +t: M.RType, acc: List<&2, M.Record>) ->
  List<&2, M.Record>:
  match rs:
    case Nil{}:
      acc
    case Con{r, rest}:
      matching.go(rest, name, t, matching.at(r, name, t, acc))

def matching(rs: List<&2, M.Record>, name: M.Name(), t: M.RType) -> List<&2, M.Record>:
  B.rev(M.Record, matching.go(rs, name, t, Nil{}), Nil{})

def cname.pick(hit: Bool, d: M.RData) -> Maybe<&2, M.Name()>:
  match hit d:
    case True{} M.RName{n}:
      Some{n}
    case _ _:
      None{}

def cname.at(found: Maybe<&2, M.Name()>, r: M.Record, +name: M.Name()) -> Maybe<&2, M.Name()>:
  match found:
    case Some{n}:
      Some{n}
    case None{}:
      match r:
        case M.Record{n, rt, c, ttl, d}:
          cname.pick(NM.eq(n, name) && is_cname(rt), d)

# The target of the first CNAME in rs owned by name, if any (a loop).
def cname.go(rs: List<&2, M.Record>, +name: M.Name(), found: Maybe<&2, M.Name()>) -> Maybe<&2, M.Name()>:
  match rs:
    case Nil{}:
      found
    case Con{r, rest}:
      cname.go(rest, name, cname.at(found, r, name))

def cname(rs: List<&2, M.Record>, name: M.Name()) -> Maybe<&2, M.Name()>:
  cname.go(rs, name, None{})

# Where the chain stands: at a name (moved: a CNAME was followed), or done.
type Walk is Data:
  Walking{name: List<&2, List<&2, U32>>, moved: Bool}
  Stopped{answer: M.Answer}

def chain.at(found: List<&2, M.Record>, alias: Maybe<&2, M.Name()>, name: M.Name(), moved: Bool) -> Walk:
  match found:
    case Con{r, t}:
      Stopped{M.Found{name, Con{r, t}}}
    case Nil{}:
      match alias:
        case Some{tg}:
          Walking{tg, True{}}
        case None{}:
          match moved:
            case True{}:
              Stopped{M.Alias{name}}
            case False{}:
              Stopped{M.Nothing{}}

def chain.step(+an: List<&2, M.Record>, +t: M.RType, w: Walk) -> Walk:
  match w:
    case Walking{+name, moved}:
      chain.at(matching(an, name, t), cname(an, name), name, moved)
    case Stopped{a}:
      Stopped{a}

# k more steps (a loop; a stopped walk stays stopped).
def chain.go(k: Nat, +an: List<&2, M.Record>, +t: M.RType, w: Walk) -> Walk:
  match k:
    case 0n:
      w
    case 1n+p:
      chain.go(p, an, t, chain.step(an, t, w))

def chain.end(w: Walk) -> M.Answer:
  match w:
    case Walking{name, moved}:
      M.Nothing{}
    case Stopped{a}:
      a

# The records of type t for name, through m's CNAMEs (see the top of the file).
def addresses(name: M.Name(), t: M.RType, m: M.Message) -> M.Answer:
  match m:
    case M.Message{h, qs, an, ns, ar}:
      chain.end(chain.go(1n+MAX_HOPS(), an, t, Walking{name, False{}}))
