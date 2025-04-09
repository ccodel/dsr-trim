# dsr-trim

### The next generation of SAT proof checking.

The `dsr-trim` library contains various tools for
checking, trimming, and adding proof hints
for *substitution redundancy* (SR) proofs.
Valid SR proofs show that two formulas in propositional logic are *equisatisfiable*
under a series of clause additions and deletions.
In most cases,
the proof *P* ends by adding the empty clause,
which is by definition unsatisfiable.
Since *P* maintained equisatisfiability at each step,
*P* shows that the original formula has no solutions.
In other words,
*P* is a *proof of unsatisfiability*.

Proofs of unsatisfiability
&mdash; and their associated proof-checking tools &mdash;
have been crucial for resolving open problems in mathematics,
such as the [Pythagorean triples problem](https://www.cs.utexas.edu/~marijn/publications/ptn.pdf),
a variant of the [Happy Ending Problem](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.35/LIPIcs.ITP.2024.35.pdf),
and [Schur number five](https://arxiv.org/abs/1711.08076).
The key to these results is to reduce the original problem to the satisfiability of a particular formula in propositional logic.
Then,
a *SAT solver*
either finds a truth assignment to the variables that satisfies the formula,
or it reports that no solution exists.
In that case,
the solver may output a proof of unsatisfibility in a formal *proof system*,
which then may be checked by a (verified) proof checker.

`dsr-trim` is one such (unverified) proof checker.
It accepts *deletion SR* (DSR) proofs,
and outputs *linear SR* (LSR) proofs containing unit propagation proof hints.
These hints allow proof checking to take time linear in the size of the proof.
(Hence the name "linear" SR.)
Each line consists of either a *deletion* or a clause *addition*;
addition lines may also provide a *witness* which demonstrates that the added clause will maintain equisatisfiability.
For SR,
the witness is any substitution of the boolean variables.
(Hence the name "substitution" redundancy.)

There are four tools in this library:

- [`dsr-trim`](src/dsr-trim.c): An unverified DSR proof checker. It outputs LSR proofs that can optionally be trimmed to reduce their size.
- [`lsr-check`](src/lsr-check.c): An unverified LSR proof checker. It determines whether LSR proofs are valid.
- [`compress`](src/compress.c): A tool to compress DSR/LSR proofs into a more-compact binary format.
- [`decompress`](src/decompress.c): A tool to decompress DSR/LSR proofs back into ASCII.

`dsr-trim` is far from being the first SAT proof checker.
Two of its predecessors are [`drat-trim`](https://github.com/marijnheule/drat-trim)
and [`dpr-trim`](https://github.com/marijnheule/dpr-trim),
which check DRAT and DPR proofs,
repsectively.
The SR proof system generalizes them both,
and DSR/LSR are backwards-compatible with DRAT/LRAT and DPR/LPR,
so you can use `dsr-trim` and `lsr-check` in the place of those two tools.
For more information, see the "References and related work" section below.

## Compilation

Use the [`Makefile`](Makefile) to compile everything.
The `Makefile` places the executables in the `bin/` directory
(and creates one if it doesn't exist),
and it creates symbolic links to the executables at the top-level of the project.
Any `.o` object files created during C compilation stay in the `src/` directory.

The various commands are:
```bash
make          # Compile all executables
make clean    # Remove all executables, symlinks, and .o files
make [dsr-trim | lsr-check | compress | decompress]
make long     # Compile everything, but with `long long` clause IDs
```

## Usage

Use the `--help` option on both `dsr-trim` and `lsr-check` to view an up-to-date verbose help message for that tool.
Usage is:
```
./dsr-trim  [OPTIONS] <CNF> [PROOF]
./lsr-check [OPTIONS] <CNF> [PROOF]
```
A `CNF` formula file is required.
If no `PROOF` file is provided,
`stdin` is used.

The (potentially empty) list of `[OPTIONS]` can occur anywhere in the arguments to the tool,
and each must be one of the following:
```
-h        Short help message. No proof checking occurs.
--help    Long help message. No proof checking occurs.

-q        Quiet mode. Only reqports the final result.
-v        Verbose mode. Prints additional stats and debugging information.
          All comment lines are prefixed with "c ".
-V        Verbose error mode. If a proof-checking error is encountered,
          additional information about program state is printed.

-e | -eager        Eager proof parsing. Parses entire file before checking.
-s | --streaming   Streaming. Parses the proof as it goes.

-b | --backward    (dsr-trim only, default) Perform backward checking.
-f | --forward     (dsr-trim only) Perform forward checking.

-d <dir> | --dir=<d>      Specify a common directory for CNF and PROOF.
-n <name> | --name=<n>    Specify a common file path for CNF and PROOF.

--emit-valid-formula-to=<file>

  (dsr-trim only) When the proof is VALID and not UNSAT, outputs the
  ending formula to the provided file path. This is useful for easily
  creating a new CNF formula after doing symmetry breaking.
```

## License

This project is open source under the Apache 2.0 license (see the [LICENSE](LICENSE)).

## References and related work

`dsr-trim` and the DSR/LSR proof formats were introduced in [the paper](https://repositum.tuwien.at/bitstream/20.500.12708/200791/1/Codel-2024-Verified%20Substitution%20Redundancy%20Checking-vor.pdf):

"Verified Substitution Redundancy Checking." Cayden Codel, Jeremy Avigad, Marijn Heule. In FMCAD 2024.

`dsr-trim` is far from the first SAT clausal proof checker.
The first widely-adopted proof checker is arguably [`drat-trim`](https://github.com/marijnheule/drat-trim),
which checks DRAT proofs.


## A note on file naming convention

To maintain historical consistency with [`drat-trim`](https://github.com/marijnheule/drat-trim) and [`dpr-trim`](https://github.com/marijnheule/dpr-trim), we use hyphens for the top-level executables `dsr-trim` and `lsr-check`.
However, all other files use the author's preference for underscores in file names (e.g. `cnf_parser.c`).