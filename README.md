# dsr-check

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

## A note on file naming convention.

To maintain historical consistency with [`drat-trim`](https://github.com/marijnheule/drat-trim) and [`dpr-trim`](https://github.com/marijnheule/dpr-trim), we use hyphens for the top-level executables `dsr-trim` and `lsr-check`. However, supporting files use the author's preference for underscores in file names (e.g. `cnf_parser.c`).