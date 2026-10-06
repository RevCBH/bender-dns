import Base
import ../src/types.bend as M
import ../src/ip.bend as IP

# Checker-evaluated tests for ip.bend: `bend tests/ip_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass. Values stay small (the
# checker computes Nat in unary, and N.show / N.hex_show count up);
# tests/core_run.bend covers full-range addresses and hostile text.

def MR() -> Type:
  Maybe<&2, M.RData>

def v6(a: Nat, b: Nat, c: Nat, d: Nat, e: Nat, f: Nat, g: Nat, h: Nat) -> MR():
  Some{M.RIpv6{[a, b, c, d, e, f, g, h]}}

def main() ->
  # show4 / parse4
  {IP.show4(127n, 0n, 0n, 1n) == "127.0.0.1" : String} &
  {IP.show4(0n, 10n, 100n, 255n) == "0.10.100.255" : String} &
  {IP.parse4("127.0.0.1") == Some{M.RIpv4{127n, 0n, 0n, 1n}} : MR()} &
  {IP.parse4("0.10.100.255") == Some{M.RIpv4{0n, 10n, 100n, 255n}} : MR()} &
  {IP.parse4("256.0.0.1") == None{} : MR()} &
  {IP.parse4("01.0.0.1") == None{} : MR()} &
  {IP.parse4("1.2.3") == None{} : MR()} &
  {IP.parse4("1.2.3.4.5") == None{} : MR()} &
  {IP.parse4("1.2.3.") == None{} : MR()} &
  {IP.parse4(".1.2.3") == None{} : MR()} &
  {IP.parse4("1..2.3") == None{} : MR()} &
  {IP.parse4("") == None{} : MR()} &
  {IP.parse4("1.2.3.a") == None{} : MR()} &
  {IP.parse4(" 1.2.3.4") == None{} : MR()} &
  {IP.parse4("1.2.3.4 ") == None{} : MR()} &
  {IP.parse4("1.2.3.+4") == None{} : MR()} &
  {IP.parse4("0x1.2.3.4") == None{} : MR()} &
  {IP.parse4("1:2.3.4") == None{} : MR()} &
  {IP.parse4(IP.show4(1n, 22n, 0n, 200n)) == Some{M.RIpv4{1n, 22n, 0n, 200n}} : MR()} &
  {IP.is_ipv4("10.0.0.1") == True{} : Bool} &
  {IP.is_ipv4("example.com") == False{} : Bool} &
  # show6
  {IP.show6([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]) == "::" : String} &
  {IP.show6([0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]) == "::1" : String} &
  {IP.show6([1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]) == "1::" : String} &
  {IP.show6([1n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]) == "1::1" : String} &
  {IP.show6([1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n]) == "1:2:3:4:5:6:7:8" : String} &
  {IP.show6([1n, 0n, 2n, 3n, 4n, 5n, 6n, 7n]) == "1:0:2:3:4:5:6:7" : String} &
  {IP.show6([1n, 0n, 0n, 2n, 0n, 0n, 0n, 3n]) == "1:0:0:2::3" : String} &
  {IP.show6([1n, 0n, 0n, 2n, 0n, 0n, 3n, 4n]) == "1::2:0:0:3:4" : String} &
  {IP.show6([171n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]) == "ab::1" : String} &
  # parse6
  {IP.parse6("::") == v6(0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n) : MR()} &
  {IP.parse6("::1") == v6(0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n) : MR()} &
  {IP.parse6("1::") == v6(1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n) : MR()} &
  {IP.parse6("1::2") == v6(1n, 0n, 0n, 0n, 0n, 0n, 0n, 2n) : MR()} &
  {IP.parse6("1:2:3:4:5:6:7:8") == v6(1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n) : MR()} &
  {IP.parse6("1:2:3:4:5:6:7::") == v6(1n, 2n, 3n, 4n, 5n, 6n, 7n, 0n) : MR()} &
  {IP.parse6("::2:3:4:5:6:7:8") == v6(0n, 2n, 3n, 4n, 5n, 6n, 7n, 8n) : MR()} &
  {IP.parse6("AB::c") == v6(171n, 0n, 0n, 0n, 0n, 0n, 0n, 12n) : MR()} &
  {IP.parse6("0001::0") == v6(1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n) : MR()} &
  {IP.parse6("::0.0.1.2") == v6(0n, 0n, 0n, 0n, 0n, 0n, 0n, 258n) : MR()} &
  {IP.parse6("1:2:3:4:5:6:0.1.0.3") == v6(1n, 2n, 3n, 4n, 5n, 6n, 1n, 3n) : MR()} &
  {IP.parse6("") == None{} : MR()} &
  {IP.parse6(":") == None{} : MR()} &
  {IP.parse6(":::") == None{} : MR()} &
  {IP.parse6("1:::2") == None{} : MR()} &
  {IP.parse6("1::2::3") == None{} : MR()} &
  {IP.parse6(":1::") == None{} : MR()} &
  {IP.parse6("1::2:") == None{} : MR()} &
  {IP.parse6("1:2:3:4:5:6:7") == None{} : MR()} &
  {IP.parse6("1:2:3:4:5:6:7:8:9") == None{} : MR()} &
  {IP.parse6("1:2:3:4:5:6:7:8::") == None{} : MR()} &
  {IP.parse6("1:2:3:4::5:6:7:8") == None{} : MR()} &
  {IP.parse6("12345::") == None{} : MR()} &
  {IP.parse6("g::") == None{} : MR()} &
  {IP.parse6("::1.2.3") == None{} : MR()} &
  {IP.parse6("1.2.3.4::") == None{} : MR()} &
  {IP.parse6("::1%eth0") == None{} : MR()} &
  {IP.parse6("1.2.3.4") == None{} : MR()} &
  {IP.parse6(" ::1") == None{} : MR()} &
  {IP.is_ipv6("::1") == True{} : Bool} &
  {IP.is_ipv6("127.0.0.1") == False{} : Bool} &
  # roundtrips
  {IP.parse6(IP.show6([1n, 0n, 0n, 2n, 0n, 0n, 0n, 3n])) == v6(1n, 0n, 0n, 2n, 0n, 0n, 0n, 3n) : MR()} &
  {IP.parse6(IP.show6([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n])) == v6(0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n) : MR()} &
  {IP.parse6(IP.show6([1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n])) == v6(1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n) : MR()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
