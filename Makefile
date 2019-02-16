# copyright (c) 2014, guillaume bury

TIMEOUT ?= 30

all: bin

bin:
	@dune build --profile=release @all
	@ln -sf _build/default/src/main.exe main.exe

bench: bin
	./main.exe -t $(TIMEOUT) problems/pigeon/hole{6,7,8,9}.cnf

clean:
	@dune clean

.PHONY: clean all bin test
