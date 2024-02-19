/**
 * @file cnf_parser.h
 * @brief Parses CNF files and stores them in global data structures.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-11
 */

#ifndef _CNF_PARSER_H_
#define _CNF_PARSER_H_

// Parses the CNF and puts it into global data structures.
void parse_cnf(const char *filename);

// Prints the CNF to stdout, for debugging purposes.
void print_cnf(void); 

#endif /* _CNF_PARSER_H_ */