BEND ?= bend
PREFIX ?= /usr/local
BINDIR ?= $(PREFIX)/bin

.PHONY: all install clean test
all: bender-dns

bender-dns: cli.bend main.bend $(wildcard src/*.bend src/*.c src/*.js)
	$(BEND) cli.bend -o $@

install: bender-dns
	install -Dm755 bender-dns "$(DESTDIR)$(BINDIR)/bender-dns"

clean:
	rm -f bender-dns

test:
	BEND="$(BEND)" bash tests/cli_test.sh
