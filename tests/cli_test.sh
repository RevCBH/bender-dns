#!/usr/bin/env bash
# End-to-end CLI tests on both runtimes, using ephemeral local TCP servers.
set -euo pipefail
cd "$(dirname "$0")/.."
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
"${BEND:-bend}" cli.bend -o "$out/bender-dns"
python3 -B - "$out" "${BEND:-bend}" <<'PY'
import contextlib
import pathlib
import subprocess
import sys
import threading

sys.path.insert(0, "tests")
from dns_server import Handler, Server

out = pathlib.Path(sys.argv[1])
failures = 0


def expect(label, args, code=0, stdout=None, stderr=None, contains=None):
    global failures
    try:
        result = subprocess.run(command + args, capture_output=True, text=True, timeout=20)
        # The source runner may append a compiler update notice to stderr.
        errors = "\n".join(line for line in result.stderr.splitlines()
                           if not (line.startswith("bend ") and line.endswith("is available: run bend update")))
        assert result.returncode == code, f"exit {result.returncode}, expected {code}: {errors}"
        if stdout is not None:
            assert result.stdout == stdout, f"stdout: {result.stdout!r}"
        if contains is not None:
            assert contains in result.stdout, f"stdout: {result.stdout!r}"
        if stderr is not None:
            assert stderr in errors, f"stderr: {errors!r}"
        elif code == 0:
            assert not errors.strip(), f"unexpected stderr: {errors!r}"
    except (AssertionError, subprocess.TimeoutExpired) as error:
        print(f"FAIL [{lane}] {label}: {error}", flush=True)
        failures += 1
    else:
        print(f"PASS [{lane}] {label}", flush=True)


with contextlib.ExitStack() as stack:
    ports = {}
    for mode in ("ok", "nxdomain", "cname", "silent"):
        server = stack.enter_context(Server(("127.0.0.1", 0), Handler))
        server.mode = mode
        threading.Thread(target=server.serve_forever, daemon=True).start()
        stack.callback(server.shutdown)
        ports[mode] = str(server.server_address[1])

    for lane, command in (
        ("c", [str(out / "bender-dns")]),
        ("js", [sys.argv[2], "cli.bend", "--"]),
    ):
        for flag in ("--help", "-h"):
            expect(flag, [flag], contains="usage: bender-dns")
        expect("help after name", ["example.com", "--help"], contains="usage: bender-dns")
        expect("no arguments", [], 1, "", "usage: bender-dns")
        expect("unknown option", ["--bogus"], 1, "", "unknown option")
        expect("extra argument", ["example.com", "A", "extra"], 1, "", "too many arguments")
        expect("unknown type", ["example.com", "BOGUS"], 1, "", "unknown type")
        expect("out-of-range type", ["example.com", "TYPE65536"], 1, "", "unknown type")
        expect("bad name", ["a..b"], 1, "", "bad name")
        for option in ("--port", "--timeout", "--attempts", "--server"):
            expect(f"missing {option}", [option], 1, "", "missing its value")
        for value in ("0", "65536", "-1", "no", "", "999999999999999999999"):
            expect(f"invalid port {value!r}", ["--port", value, "x.test."], 1, "", "port must")
        for value in ("0", "4294967296", "-1", "no"):
            expect(f"invalid timeout {value}", ["--timeout", value, "x.test."], 1, "", "timeout must")
        for value in ("0", "-1", "no"):
            expect(f"invalid attempts {value}", ["--attempts", value, "x.test."], 1, "", "attempts must")
        for value in ("", "dns.example", "::1", "256.1.1.1"):
            expect(f"invalid server {value!r}", ["--server", value, "x.test."], 1, "", "IPv4 address")
        expect("empty @server", ["@", "x.test."], 1, "", "IPv4 address")
        expect("OS unsupported type", ["--os", "localhost", "MX"], 1, "", "A or AAAA")
        for option in (["@127.0.0.1"], ["--port", "53"], ["--timeout", "1"], ["--attempts", "1"]):
            expect(f"OS conflict {option[0]}", ["--os", "localhost"] + option, 1, "", "cannot be combined")
        expect("OS IPv4 literal", ["--os", "192.0.2.9", "A"], stdout="192.0.2.9\n")
        expect("OS IPv6 literal", ["--os", "2001:db8::9", "AAAA"], stdout="2001:db8::9\n")
        expect("native literal", ["192.0.2.9"], stdout="192.0.2.9\n")

        query = ["--server", "127.0.0.1", "--port", ports["ok"]]
        expect("default A", query + ["x.test."], stdout="192.0.2.1\n")
        for rtype, answer in (("AAAA", "2001:db8::1"), ("mx", "10 mail.x.test."),
                              ("TXT", '"hello"'), ("TYPE1", "192.0.2.1")):
            expect(rtype, query + ["x.test.", rtype], stdout=answer + "\n")
        expect("NODATA", query + ["x.test.", "SRV"], 1, "", "no record of that type")
        expect("short flags and options after name", ["x.test.", "-s", "127.0.0.1", "-p", ports["ok"]],
               stdout="192.0.2.1\n")
        expect("dig aliases", ["@127.0.0.1", "+tcp-port", ports["ok"], "+timeout", "2000",
                               "+attempts", "1", "x.test."], stdout="192.0.2.1\n")
        expect("repeated servers fail over", ["-s", "127.0.0.2", "@127.0.0.1", "-p", ports["ok"],
                                              "--attempts", "1", "x.test."], stdout="192.0.2.1\n")
        expect("NXDOMAIN", ["@127.0.0.1", "-p", ports["nxdomain"], "x.test."], 1, "", "NXDOMAIN")
        expect("CNAME", ["@127.0.0.1", "-p", ports["cname"], "alias.test."],
               stdout="target.test.\n192.0.2.7\n")
        expect("timeout", ["@127.0.0.1", "-p", ports["silent"], "--timeout", "100", "--attempts", "1", "x.test."],
               1, "", "timed out")

if failures:
    sys.exit(f"{failures} CLI tests failed")
print("ALL CLI TESTS PASS")
PY
