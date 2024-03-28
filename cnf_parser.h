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

// Parses the CNF and puts it into global data structures.
// On success, closes the FILE.
void parse_cnf(FILE *cnf_file);

// Prints the CNF to stdout, for debugging purposes.
void print_cnf(void); 

#endif /* _CNF_PARSER_H_ */