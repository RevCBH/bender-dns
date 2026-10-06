// OS resolver
// ===========

// getaddrinfo and inet_ntop through bun:ffi, the way io_sys reaches libc.
// JS's IO loop cannot park on a lookup (bendlang/bend#1148), so this lane
// blocks the loop until the resolver answers; the C lane runs it on a helper
// thread instead. Codes, texts and order match os.c: distinct addresses as
// inet_ntop text, at most 32. Starts from bender-http's dns.js.
function os_lookup_lib() {
  if (globalThis.OS_LOOKUP_LIB === undefined) {
    const ffi = require("bun:ffi");
    const mac = process.platform === "darwin";
    const lib = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6", {
      getaddrinfo: { args: ["ptr", "ptr", "ptr", "ptr"], returns: "i32" },
      freeaddrinfo: { args: ["ptr"], returns: "void" },
      gai_strerror: { args: ["i32"], returns: "cstring" },
      inet_ntop: { args: ["i32", "ptr", "ptr", "u32"], returns: "ptr" },
    }).symbols;
    // struct addrinfo: ai_addr and ai_canonname swap places on macOS.
    const eai = mac
      ? { addrfamily: 1, again: 2, fail: 4, memory: 6, nodata: 7, noname: 8, system: 11 }
      : { addrfamily: -9, again: -3, fail: -4, memory: -10, nodata: -5, noname: -2, system: -11 };
    globalThis.OS_LOOKUP_LIB = { ffi, lib, eai, mac, addr_at: mac ? 32 : 24,
      inet6: mac ? 30 : 10, eagain: mac ? 35 : 11 };
  }
  return globalThis.OS_LOOKUP_LIB;
}

function os_lookup_fail(code, text) {
  return { $: CID(Fail), error: io_tup(code >>> 0, text) };
}

function os_lookup(host, fam) {
  if (fam !== 0 && fam !== 4 && fam !== 6) {
    return os_lookup_fail(22, "the address family must be 0 (any), 4 (IPv4) or 6 (IPv6)");
  }
  if (host.length === 0 || host.includes("\0")) {
    return io_fail(22);
  }
  const { ffi, lib, eai, addr_at, inet6, eagain } = os_lookup_lib();
  const family = fam === 0 ? 0 : fam === 4 ? 2 : inet6;
  const name = new TextEncoder().encode(host + "\0");
  const hints = new Uint8Array(48);
  const view = new DataView(hints.buffer);
  view.setInt32(4, 2, true); // ai_family = AF_INET
  view.setInt32(8, 1, true); // ai_socktype = SOCK_STREAM
  const out = new BigUint64Array(1);
  // As os.c: a host the resolver reads as an IPv4 address (AI_NUMERICHOST,
  // so inet_aton's octal, hex and short forms) must be the canonical dotted
  // quad, else EINVAL, whatever the family. A host with a ':' (an IPv6
  // literal such as "::ffff:1.2.3.4", or a name) is let through.
  view.setInt32(0, 4, true); // ai_flags = AI_NUMERICHOST
  if (!host.includes(":") && lib.getaddrinfo(ffi.ptr(name), null, ffi.ptr(hints), ffi.ptr(out)) === 0) {
    lib.freeaddrinfo(Number(out[0]));
    if (io_addr(host, 0) === null) {
      return os_lookup_fail(22, "a numeric host that is not a dotted-quad IPv4 address"
        + " (the resolver would read it as octal, hex or a short form)");
    }
  }
  view.setInt32(0, 0, true);
  view.setInt32(4, family, true);
  out[0] = 0n;
  const rc = lib.getaddrinfo(ffi.ptr(name), null, ffi.ptr(hints), ffi.ptr(out));
  if (rc !== 0) {
    if (rc === eai.system) {
      return io_fail(io_sys().errno() || 5);
    }
    const code = rc === eai.again ? eagain : rc === eai.memory ? 12
      : rc === eai.fail ? 5
      : rc === eai.noname || rc === eai.nodata || rc === eai.addrfamily ? 2 : 22;
    return os_lookup_fail(code, String(lib.gai_strerror(rc)));
  }
  const head = Number(out[0]);
  const found = [];
  const text = new Uint8Array(46); // INET6_ADDRSTRLEN
  for (let ai = head; ai !== 0 && found.length < 32; ai = ffi.read.ptr(ai, 40)) {
    const sa = ffi.read.ptr(ai, addr_at);
    const af = ffi.read.i32(ai, 4);
    // sockaddr_in: the address at offset 4; sockaddr_in6 (28 bytes): at 8.
    const off = af === 2 ? 4 : af === inet6 ? 8 : -1;
    if (sa === 0 || off < 0) {
      continue;
    }
    text.fill(0);
    if (!lib.inet_ntop(af, sa + off, ffi.ptr(text), text.length)) {
      continue;
    }
    const end = text.indexOf(0);
    const ip = new TextDecoder().decode(text.subarray(0, end < 0 ? text.length : end));
    if (!found.includes(ip)) {
      found.push(ip);
    }
  }
  lib.freeaddrinfo(head);
  if (found.length === 0) {
    return os_lookup_fail(2, fam === 4 ? "no IPv4 address for this name"
      : fam === 6 ? "no IPv6 address for this name" : "no address for this name");
  }
  let xs = { $: CID(Nil) };
  for (let i = found.length; i > 0; i -= 1) {
    xs = { $: CID(Con), head: found[i - 1], tail: xs };
  }
  return io_done(xs);
}

io_eff(CID(Os.lookup), os_lookup);
