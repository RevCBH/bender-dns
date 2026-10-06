import Base
import ../src/types.bend as M
import ../src/name.bend as NM

# Checker-evaluated tests for name.bend: `bend tests/name_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass. tests/core_run.bend
# covers long labels, 255-byte names and hostile text at runtime.

def BS() -> Type:
  List<&2, U32>

def NmT() -> Type:
  List<&2, List<&2, U32>>

def R() -> Type:
  Result<&2, &2, M.NameError, List<&2, List<&2, U32>>>

# www.example.com
def ex() -> List<&2, List<&2, U32>>:
  [[119, 119, 119], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]

# "a.b" as one label, then "c\d", then a label of a space, a zero byte,
# 0x7F and 0xFF.
def odd() -> List<&2, List<&2, U32>>:
  [[97, 46, 98], [99, 92, 100], [32, 0, 127, 255]]

def main() ->
  # from_text
  {NM.from_text("www.example.com") == Done{ex()} : R()} &
  {NM.from_text("www.example.com.") == Done{ex()} : R()} &
  {NM.from_text(".") == Done{[]} : R()} &
  {NM.from_text("a") == Done{[[97]]} : R()} &
  {NM.from_text("A-b_9") == Done{[[65, 45, 98, 95, 57]]} : R()} &
  {NM.from_text("") == Fail{M.EmptyLabel{}} : R()} &
  {NM.from_text("..") == Fail{M.EmptyLabel{}} : R()} &
  {NM.from_text("a..b") == Fail{M.EmptyLabel{}} : R()} &
  {NM.from_text(".a") == Fail{M.EmptyLabel{}} : R()} &
  {NM.from_text("a..") == Fail{M.EmptyLabel{}} : R()} &
  {NM.from_text("a b") == Fail{M.BadChar{}} : R()} &
  {NM.from_text("a\tb") == Fail{M.BadChar{}} : R()} &
  {NM.from_text("caf\u{e9}") == Fail{M.BadChar{}} : R()} &
  {NM.from_text("\u{1F600}") == Fail{M.BadChar{}} : R()} &
  # escapes
  {NM.from_text("a\\.b") == Done{[[97, 46, 98]]} : R()} &
  {NM.from_text("a\\\\b") == Done{[[97, 92, 98]]} : R()} &
  {NM.from_text("\\032") == Done{[[32]]} : R()} &
  {NM.from_text("\\000\\255") == Done{[[0, 255]]} : R()} &
  {NM.from_text("\\ x") == Done{[[32, 120]]} : R()} &
  {NM.from_text("\\a") == Done{[[97]]} : R()} &
  {NM.from_text("\\256") == Fail{M.BadEscape{}} : R()} &
  {NM.from_text("\\25") == Fail{M.BadEscape{}} : R()} &
  {NM.from_text("\\2x5") == Fail{M.BadEscape{}} : R()} &
  {NM.from_text("a\\") == Fail{M.BadEscape{}} : R()} &
  {NM.from_text("a\\.") == Done{[[97, 46]]} : R()} &
  {NM.from_text("\\\u{e9}") == Fail{M.BadChar{}} : R()} &
  {NM.from_text("\\999") == Fail{M.BadEscape{}} : R()} &
  # leftmost error wins
  {NM.from_text("a b.\\256") == Fail{M.BadChar{}} : R()} &
  # to_text
  {NM.to_text(ex()) == "www.example.com" : String} &
  {NM.to_text([]) == "." : String} &
  {NM.to_text([[65]]) == "A" : String} &
  {NM.to_text(odd()) == "a\\.b.c\\\\d.\\032\\000\\127\\255" : String} &
  {NM.to_text([[256]]) == "\\999" : String} &
  # roundtrips
  {NM.from_text(NM.to_text(ex())) == Done{ex()} : R()} &
  {NM.from_text(NM.to_text(odd())) == Done{odd()} : R()} &
  {NM.from_text(NM.to_text([])) == Done{[]} : R()} &
  # ok
  {NM.ok(ex()) == True{} : Bool} &
  {NM.ok([]) == True{} : Bool} &
  {NM.ok([[]]) == False{} : Bool} &
  {NM.ok([[97], []]) == False{} : Bool} &
  {NM.ok([[97, 256]]) == False{} : Bool} &
  {NM.wire_size(ex()) == 17n : Nat} &
  {NM.wire_size([]) == 1n : Nat} &
  # wire
  {NM.wire(ex()) == [3, 119, 119, 119, 7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0] : BS()} &
  {NM.wire([]) == [0] : BS()} &
  {NM.wire_onto([[97]], [9, 9]) == [1, 97, 0, 9, 9] : BS()} &
  {NM.wire(ex()) == NM.wire.spec(ex()) : BS()} &
  # lower / eq
  {NM.lower([[87, 119, 90, 64, 91, 96, 123, 200]]) == [[119, 119, 122, 64, 91, 96, 123, 200]] : NmT()} &
  {NM.eq(ex(), [[87, 87, 87], [69, 120, 65, 109, 112, 76, 101], [67, 79, 77]]) == True{} : Bool} &
  {NM.eq(ex(), ex()) == True{} : Bool} &
  {NM.eq([], []) == True{} : Bool} &
  {NM.eq([[97]], [[98]]) == False{} : Bool} &
  {NM.eq([[97]], [[97], [97]]) == False{} : Bool} &
  {NM.eq([[97, 97]], [[97]]) == False{} : Bool} &
  {NM.eq([[64]], [[96]]) == False{} : Bool} &
  {NM.eq([[91]], [[123]]) == False{} : Bool} &
  {NM.eq([[200]], [[232]]) == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
