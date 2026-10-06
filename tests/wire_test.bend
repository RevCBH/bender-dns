import Base
import ../src/types.bend as M
import ../src/wire.bend as W

# Checker-evaluated tests for wire.bend: `bend tests/wire_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass. Values stay small (the
# checker computes Nat in unary); tests/core_run.bend covers the large ones.

def G() -> Type:
  Maybe<&2, M.Got>

def BS() -> Type:
  List<&2, U32>

def main() ->
  # put
  {W.put_u8(0n) == [0] : BS()} &
  {W.put_u8(255n) == [255] : BS()} &
  {W.put_u16(0n) == [0, 0] : BS()} &
  {W.put_u16(53n) == [0, 53] : BS()} &
  {W.put_u16(256n) == [1, 0] : BS()} &
  {W.put_u16(1000n) == [3, 232] : BS()} &
  {W.put_u32(0n) == [0, 0, 0, 0] : BS()} &
  {W.put_u32(300n) == [0, 0, 1, 44] : BS()} &
  {W.put_u16_onto(1n, [9]) == [0, 1, 9] : BS()} &
  {W.put_u32_onto(2n, [9]) == [0, 0, 0, 2, 9] : BS()} &
  # get
  {W.get_u8([]) == None{} : G()} &
  {W.get_u8([7, 8]) == Some{M.Got{7n, [8]}} : G()} &
  {W.get_u8([256]) == None{} : G()} &
  {W.get_u16([1, 2, 3]) == Some{M.Got{258n, [3]}} : G()} &
  {W.get_u16([1]) == None{} : G()} &
  {W.get_u16([]) == None{} : G()} &
  {W.get_u16([1, 256]) == None{} : G()} &
  {W.get_u16([4294967295, 0]) == None{} : G()} &
  {W.get_u32([0, 0, 1, 2]) == Some{M.Got{258n, []}} : G()} &
  {W.get_u32([0, 0, 0]) == None{} : G()} &
  {W.get_u32([0, 0, 0, 300, 1]) == None{} : G()} &
  # roundtrips
  {W.get_u8(List.append(&2, U32, W.put_u8(255n), [1])) == Some{M.Got{255n, [1]}} : G()} &
  {W.get_u16(List.append(&2, U32, W.put_u16(1000n), [5])) == Some{M.Got{1000n, [5]}} : G()} &
  {W.get_u16(W.put_u16(256n)) == Some{M.Got{256n, []}} : G()} &
  {W.get_u32(List.append(&2, U32, W.put_u32(300n), [7])) == Some{M.Got{300n, [7]}} : G()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
