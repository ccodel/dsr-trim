/**
 * @file sr_parser.h
 * @brief Parser for SR certificate and LSR proof files.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-19
 */

#ifndef _SR_PARSER_H_
#define _SR_PARSER_H_

#include <stdio.h>

/** Parses the SR clause and witness into global data structures.
 * 
 *  When it returns, the file f is still open and points to the next character,
 *  i.e., the zero capping the witness is consumed, but no more than that.
 * 
 *  The new clause is added to the formula "eagerly," because if the clause
 *  checks, then we would add it to the formula anyway.
 */
void parse_sr_clause_and_witness(FILE *f);

#endif /* _SR_PARSER_H_ */