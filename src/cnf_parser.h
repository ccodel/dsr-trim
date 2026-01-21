/**
 * @file cnf_parser.h
 * @brief Parses CNF files and stores them in global data structures.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-11
 */

#ifndef _CNF_PARSER_H_
#define _CNF_PARSER_H_

#include <stdlib.h>
#include <stdio.h>

#define KEEP_TAUTOLOGIES      (0)
#define DELETE_TAUTOLOGIES    (1)

// Parses a single clause and stores it in `lits_db` and `formula`.
// Sorts the literals, eliminates duplicates, and checks for tautology.
// Note that it does NOT call `commit_clause()`.
// Returns 1 if it's a tautology, 0 otherwise.
int parse_clause(FILE *f);

// Parses the CNF and puts it into global data structures.
// On success, closes the FILE.
void parse_cnf(FILE *cnf_file, int delete_tautologies);

#endif /* _CNF_PARSER_H_ */