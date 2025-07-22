all:
	@dune build

clean:
	@dune clean

install:
	@dune install

uninstall:
	@dune uninstall

hooks:
	@git config core.hooksPath .hooks

.PHONY: all clean install uninstall doc
