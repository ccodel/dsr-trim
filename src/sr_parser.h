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

/**
 * @brief Parses the SR clause and witness into global data structures.
 * 
 * When it returns, the FILE `f` is still open and points to the next character,
 * i.e., the zero capping the witness is consumed, but no more than that.
 * 
 * The new clause is added to the formula "eagerly," because if the clause
 * checks, then we would add it to the formula anyway.
 * 
 * The min/max_clause_to_check are *not* updated, because possible witness 
 * minimization during dsr-trim might adjust the ranges. These ranges are
 * instead calculated during assume_subst().
 * 
 * @param f The file stream to read from.
 * @param line_no The 0-indexed line number, where 0 is the first SR line.
 *    In other words, if <line_id> is the reported ID of the line, then
 *    `line_no` is <line_id> - (num_cnf_clauses + 1).
 */
void parse_sr_clause_and_witness(FILE *f, srid_t line_no);

#endif /* _SR_PARSER_H_ */