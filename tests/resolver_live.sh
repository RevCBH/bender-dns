#!/usr/bin/env bash
# Live tests of the native resolver (and so of the transport) through
# examples/dig.bend and examples/host.bend, on both lanes: the JS lane
# (`bend examples/dig.bend --`) and the C lane (binaries built from them).
#
# 1. Against tests/dns_server.py's local DNS-over-TCP servers (python3;
#    127.0.0.1 ports 47350..47360, one mode each, 47361 left closed; the
#    "ok" mode on 127.0.0.2 at 47350..47361, for failover): NXDOMAIN,
#    SERVFAIL, REFUSED, a CNAME needing re-queries, a CNAME loop, a
#    mismatched id, a garbage response, a cut frame, a silent server (the
#    timeout), a closed port, and failover from each bad mode to a good
#    server.
# 2. Real lookups over TCP: systemd-resolved's stub 127.0.0.53 (skipped
#    when it does not listen on TCP), 8.8.8.8 and 1.1.1.1: example.com A and
#    AAAA, gmail.com MX, www.github.com CNAME, a nonexistent name; the
#    system configuration; and the OS resolver (--os) for comparison.
#
#   tests/resolver_live.sh          # both lanes
#   tests/resolver_live.sh js       # one lane
# Prints PASS / FAIL / SKIP per case, then ALL PASS (exit 0) or SOME FAIL
# (exit 1). Needs internet for part 2.
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$(mktemp -d)"
server=''
trap '[ -n "$server" ] && kill "$server" 2>/dev/null; rm -rf "$tmp"' EXIT
lanes=("${@:-js c}")
fails=0
base=47350
p() { echo $((base + $1)); }   # the port of mode index $1 (see dns_server.py)
OK=$(p 0) NX=$(p 1) SERVFAIL=$(p 2) REFUSED=$(p 3) CNAME=$(p 4) MISMATCH=$(p 5) GARBAGE=$(p 6)
SILENT=$(p 7) CUT=$(p 8) FLAKY=$(p 9) LOOP=$(p 10) CLOSED=$(p 11)

python3 "$root/tests/dns_server.py" "$base" >"$tmp/ready" 2>"$tmp/server.log" &
server=$!
for _ in $(seq 100); do
  grep -q ready "$tmp/ready" 2>/dev/null && break
  sleep 0.1
done
grep -q ready "$tmp/ready" || { echo "FAIL the test servers did not start"; cat "$tmp/server.log"; exit 1; }

bend "$root/examples/dig.bend" -o "$tmp/dig" >"$tmp/build" 2>&1 || { echo "FAIL build dig"; cat "$tmp/build"; exit 1; }
bend "$root/examples/host.bend" -o "$tmp/host" >"$tmp/build" 2>&1 || { echo "FAIL build host"; cat "$tmp/build"; exit 1; }

# Does systemd-resolved's stub answer on TCP here?
stub=0
python3 - <<'EOF' && stub=1
import socket, sys
try:
    socket.create_connection(("127.0.0.53", 53), timeout=2).close()
except OSError:
    sys.exit(1)
EOF

run() { # tool args... -> output in $tmp/o, exit code in $rc
  local tool="$1"; shift
  if [ "$lane" = js ]; then
    timeout 120 bend "$root/examples/$tool.bend" -- "$@" >"$tmp/out" 2>&1
  else
    timeout 120 "$tmp/$tool" "$@" >"$tmp/out" 2>&1
  fi
  rc=$?
  grep -v -e 'bend update' -e '^$' "$tmp/out" >"$tmp/o" || true
}

# expect NAME TOOL RC PATTERN... -- ARGS: exit code RC and every pattern (grep -E) found
expect() {
  local name="$1" tool="$2" want_rc="$3"; shift 3
  local pats=()
  while [ "$1" != "--" ]; do pats+=("$1"); shift; done
  shift
  local t0=${EPOCHREALTIME/./}
  run "$tool" "$@"
  local ms=$(( (${EPOCHREALTIME/./} - t0) / 1000 ))
  local ok=1
  [ "$rc" = "$want_rc" ] || ok=0
  for pat in "${pats[@]}"; do grep -qE -- "$pat" "$tmp/o" || ok=0; done
  if [ $ok = 1 ]; then
    echo "PASS [$lane] $name (${ms} ms): $(head -3 "$tmp/o" | tr '\n' ' ')"
  else
    echo "FAIL [$lane] $name (rc=$rc, want $want_rc, ${ms} ms):"; head -c 800 "$tmp/o" | sed 's/^/    /'
    fails=$((fails + 1))
  fi
}

skip() { echo "SKIP [$lane] $1"; }

QUAD='^[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}\.[0-9]{1,3}$'
V6='^[0-9a-f]{1,4}(:[0-9a-f]{0,4}){2,7}$'
L=127.0.0.1

for lane in ${lanes[@]}; do
  echo "== [$lane] local servers"
  expect "ok A" dig 0 '^192\.0\.2\.1$' -- @$L --port $OK x.test.
  expect "ok AAAA" dig 0 '^2001:db8::1$' -- @$L --port $OK x.test. AAAA
  expect "ok MX" dig 0 '^10 mail\.x\.test\.$' -- @$L --port $OK x.test. mx
  expect "ok TXT" dig 0 '^"hello"$' -- @$L --port $OK x.test. TXT
  expect "ok NODATA" dig 1 'no record of that type' -- @$L --port $OK x.test. SRV
  expect "NXDOMAIN" dig 1 'x\.test\.: no such name \(NXDOMAIN\)' -- @$L --port $NX x.test.
  expect "NXDOMAIN does not fail over" dig 1 'NXDOMAIN' -- @$L @127.0.0.2 --port $NX x.test.
  expect "SERVFAIL" dig 1 'server failure \(SERVFAIL\)' -- @$L --port $SERVFAIL +attempts 1 x.test.
  expect "REFUSED" dig 1 'server failure \(REFUSED\)' -- @$L --port $REFUSED +attempts 1 x.test.
  expect "CNAME re-queried" dig 0 '^target\.test\.$' '^192\.0\.2\.7$' -- @$L --port $CNAME alias.test.
  expect "CNAME chain, then re-query" dig 0 '^target\.test\.$' '^192\.0\.2\.7$' -- @$L --port $CNAME chain.test.
  expect "CNAME asked as CNAME" dig 0 '^target\.test\.$' -- @$L --port $CNAME alias.test. CNAME
  expect "CNAME loop: 8 re-queries at most" dig 1 'server failure \(SERVFAIL\)' -- @$L --port $LOOP loop.test.
  expect "mismatched id" dig 1 'did not match the query' -- @$L --port $MISMATCH +attempts 1 x.test.
  expect "garbage response" dig 1 'malformed response' -- @$L --port $GARBAGE +attempts 1 x.test.
  expect "cut frame" dig 1 'malformed response: the message ended early' -- @$L --port $CUT +attempts 1 x.test.
  expect "silent server: timeout" dig 1 'timed out' -- @$L --port $SILENT +timeout 1000 +attempts 1 x.test.
  expect "closed port" dig 1 'connect error 111' -- @$L --port $CLOSED +attempts 1 x.test.
  expect "SERVFAIL then the next attempt" dig 0 '^192\.0\.2\.1$' -- @$L --port $FLAKY +attempts 2 flaky-$lane.test.
  expect "failover from SERVFAIL" dig 0 '^192\.0\.2\.1$' -- @$L @127.0.0.2 --port $SERVFAIL +attempts 1 x.test.
  expect "failover from REFUSED" dig 0 '^192\.0\.2\.1$' -- @$L @127.0.0.2 --port $REFUSED +attempts 1 x.test.
  expect "failover from a mismatch" dig 0 '^192\.0\.2\.1$' -- @$L @127.0.0.2 --port $MISMATCH +attempts 1 x.test.
  expect "failover from garbage" dig 0 '^192\.0\.2\.1$' -- @$L @127.0.0.2 --port $GARBAGE +attempts 1 x.test.
  expect "failover from a cut frame" dig 0 '^192\.0\.2\.1$' -- @$L @127.0.0.2 --port $CUT +attempts 1 x.test.
  expect "failover from a timeout" dig 0 '^192\.0\.2\.1$' -- @$L @127.0.0.2 --port $SILENT +timeout 1000 +attempts 1 x.test.
  expect "failover from a closed port" dig 0 '^192\.0\.2\.1$' -- @$L @127.0.0.2 --port $CLOSED +attempts 1 x.test.
  expect "address literal" dig 0 '^192\.0\.2\.9$' -- @$L --port $CLOSED 192.0.2.9
  expect "bad name" dig 1 'bad name: empty label' -- @$L --port $OK a..b
  expect "unknown type" dig 1 'unknown type: BOGUS' -- @$L --port $OK x.test. BOGUS
  expect "usage" dig 1 'usage: dig' --

  echo "== [$lane] real resolvers over TCP"
  if [ $stub = 1 ]; then
    expect "127.0.0.53 example.com A" dig 0 "$QUAD" -- @127.0.0.53 example.com
    expect "127.0.0.53 gmail.com MX" dig 0 '^[0-9]+ [a-z0-9.-]+\.google\.com\.$' -- @127.0.0.53 gmail.com MX
  else
    skip "127.0.0.53: systemd-resolved's stub does not listen on TCP here"
  fi
  expect "8.8.8.8 example.com A" dig 0 "$QUAD" -- @8.8.8.8 example.com
  expect "1.1.1.1 example.com AAAA" dig 0 "$V6" -- @1.1.1.1 example.com AAAA
  expect "1.1.1.1 gmail.com MX" dig 0 '^[0-9]+ [a-z0-9.-]+\.google\.com\.$' -- @1.1.1.1 gmail.com MX
  expect "8.8.8.8 www.github.com CNAME" dig 0 '^github\.com\.$' -- @8.8.8.8 www.github.com CNAME
  expect "8.8.8.8 www.github.com A via the CNAME" dig 0 '^github\.com\.$' "$QUAD" -- @8.8.8.8 www.github.com
  expect "1.1.1.1 nonexistent name" dig 1 'no such name \(NXDOMAIN\)' -- @1.1.1.1 no-such-name.bender-dns.invalid.
  expect "the system configuration" dig 0 "$QUAD" -- example.com
  expect "host www.github.com 8.8.8.8" host 0 'www\.github\.com is an alias for github\.com\.' \
    'github\.com has address [0-9.]+$' -- www.github.com 8.8.8.8
  expect "host nonexistent" host 1 'not found: 3\(NXDOMAIN\)' -- no-such-name.bender-dns.invalid. 1.1.1.1
  expect "os example.com A" dig 0 "$QUAD" -- --os example.com A
  expect "os example.com" dig 0 "$QUAD" -- --os example.com

  # The native stack and getaddrinfo agree: localhost (the hosts file), and
  # example.com through the system configuration (at least one address in
  # common; the sets may be ordered differently).
  for n in localhost example.com; do
    run dig "$n"; sort -u "$tmp/o" >"$tmp/native"; nrc=$rc
    run dig --os "$n" A; sort -u "$tmp/o" >"$tmp/os"; orc=$rc
    common="$(comm -12 "$tmp/native" "$tmp/os" | grep -cE "$QUAD")"
    if [ "$nrc" = 0 ] && [ "$orc" = 0 ] && [ "$common" -gt 0 ]; then
      echo "PASS [$lane] native and os agree on $n: native $(tr '\n' ' ' <"$tmp/native")/ os $(tr '\n' ' ' <"$tmp/os")"
    else
      echo "FAIL [$lane] native and os disagree on $n (rc $nrc / $orc):"
      sed 's/^/    native /' "$tmp/native"; sed 's/^/    os     /' "$tmp/os"
      fails=$((fails + 1))
    fi
  done
done

if [ $fails = 0 ]; then echo "ALL PASS"; else echo "SOME FAIL: $fails"; exit 1; fi
