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

// The witness portion of an SR certificate or proof line.
extern int *witness;
extern int witness_size;
extern int witness_alloc_size;

// If a witness is provided, the first literal of the clause is the pivot.
extern int pivot;

// Cached size of the new SR clause. Equal to get_clause_size(formula_size).
extern int new_clause_size; 

/** Witnesses in SR can have literals set to true/false, as in LRAT/LPR, or
 *  they can set variables to other literals. The point at which the witness
 *  switches to substitution is updated when an SR proof line is parsed.
 *  If no switch occurs, then subst_index is set to witness_size.
 */
extern int subst_index;

/** @brief Minimum clause to check during RAT clause checking.
 * 
 *  If a witness doesn't reduce a clause, it can be ignored during checking,
 *  since assuming its negation would provably lead to contradiction. Thus,
 *  when the SR witness is parsed, the literals set/mapped in the witness
 *  determine the min/max range of clause IDs to check. Anything outside this
 *  range is not reduced by the witness, and so can be ignored.
 * 
 *  Note that the min and max clauses are adjusted based on the literals
 *  "touched" by the witness, not their outputs under the substitution. 
 *  So for example, if (2 -> 3), then the min/max values for literal 2 are 
 *  included in the calculation, but not for literal 3.
 */
extern int min_clause_to_check;
extern int max_clause_to_check;

////////////////////////////////////////////////////////////////////////////////

// Allocates and initializes data structures maintained by the SR parser.
void init_sr_parser(void);

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