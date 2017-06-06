# sat-bench
A small repo to test and benchmark different sat solvers

# Benchamrking solver

## Building

A simple `make` should be enough to build the main test executable.

## Running benchs

The produced `main.native` executable can be called using:

```
./main.native <file>
```

Additionally, it has options to select which provers to run, filtering on
the name or package of the solver.

Finally, a special command `make bench` can be used to launch the benchmarks
on a set of selected problems.


