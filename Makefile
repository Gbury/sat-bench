# copyright (c) 2014, guillaume bury

LOG=build.log
COMP=ocamlbuild -log $(LOG) -use-ocamlfind
FLAGS=
BIN=main.native

all: bin

bin:
	$(COMP) $(FLAGS) $(BIN)

clean:
	$(COMP) -clean

.PHONY: clean all bin test
