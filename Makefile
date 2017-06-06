# copyright (c) 2014, guillaume bury

LOG=build.log
COMP=ocamlbuild -log $(LOG) -use-ocamlfind
FLAGS=
BIN=main.native

all: bin

bin:
	$(COMP) $(FLAGS) $(BIN)

bench: bin
	./$(BIN) problems/pigeon/hole{9,8,7,6}.cnf

clean:
	$(COMP) -clean

.PHONY: clean all bin test
