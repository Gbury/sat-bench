# copyright (c) 2014, guillaume bury

all: bin

bin:
	@dune build --profile=release @all
	@ln -sf _build/default/src/main.exe main.exe

bench: bin
	./main.exe problems/pigeon/hole{9,8,7,6}.cnf

clean:
	@dune clean

.PHONY: clean all bin test
