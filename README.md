# dsr-trim

Substitution redundancy SAT proof trimming, labeling, and checking.

## Compilation

Use the provided `Makefile` to compile both `dsr-trim` and `lsr-check`. Type

```bash
make
```

to compile both, or the name of the executable following `make` to compile just one (e.g. `make dsr-trim`). To clean up, type

```bash
make clean
```

## References and related work

`dsr-trim` and the DSR/LSR proof formats were introduced in [the paper](https://repositum.tuwien.at/bitstream/20.500.12708/200791/1/Codel-2024-Verified%20Substitution%20Redundancy%20Checking-vor.pdf):

"Verified Substitution Redundancy Checking." Cayden Codel, Jeremy Avigad, Marijn Heule. In FMCAD 2024.

`dsr-trim` is far from the first SAT clausal proof checker.
The first widely-adopted proof checker is arguably [`drat-trim`](https://github.com/marijnheule/drat-trim),
which checks DRAT proofs.


## A note on file naming convention

To maintain historical consistency with [`drat-trim`](https://github.com/marijnheule/drat-trim) and [`dpr-trim`](https://github.com/marijnheule/dpr-trim), we use hyphens for the top-level executables `dsr-trim` and `lsr-check`.
However, all other files use the author's preference for underscores in file names (e.g. `cnf_parser.c`).