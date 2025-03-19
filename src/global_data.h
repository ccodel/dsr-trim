/**
 * @file global_data.h
 * @brief Global data used in SR proof labeling, trimming, and checking.]
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-10
 */

#ifndef _GLOBAL_DATA_H_
#define _GLOBAL_DATA_H_

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>

#include "global_types.h"
#include "range_array.h"

////////////////////////////////////////////////////////////////////////////////

// Converts a negative DIMACS clause ID to a 0-indexed clause ID.
#define FROM_RAT_CLAUSE(x)      (-(x) - 1)
#define FROM_DIMACS_CLAUSE(x)   ((x) - 1)
#define TO_DIMACS_CLAUSE(x)     ((x) + 1)
#define FROM_DIMACS_LIT(x)      (((x) < 0) ? (((-(x)) << 1) - 1) : (((x) << 1) - 2))
#define TO_DIMACS_LIT(x)        (((x) % 2) ? (((x) / -2) - 1) : (((x) / 2) + 1))

#ifdef LONGTYPE
#define CLAUSE_ABS(x)           (llabs(x))
#else
#define CLAUSE_ABS(x)           (abs(x))
#endif

#define VAR_FROM_LIT(x)         ((x) >> 1)
#define IS_POS_LIT(x)           (!((x) & 0x1))
#define IS_NEG_LIT(x)           ((x) & 0x1)
#define NEGATE_LIT(x)           ((x) ^ 0x1)

#define IS_POS_GEN(x)           (!((x) & 0x1L))
#define IS_NEG_GEN(x)           ((x) & 0x1L)
#define NEGATE_GEN(x)           ((x) ^ 0x1L)
#define GEN_INC                 (2L)

/*
 * Each LSR proof line starts with a line ID. This ID (almost always) starts
 * at one more than the number of CNF clauses. These IDs are 1-indexed, so
 * we must subtract 1 when referring to the formula data structure.
 * 
 * However, we 0-index these line IDs when referring to witnesses, hints,
 * and deletions, and we start them at 0. These macros do the conversions
 * we need, with the convention that the `line_num` is 0-indexed, while
 * the `line_id` is essentially `num_cnf_clauses`-indexed.
 */

#define LINE_ID_FROM_LINE_NUM(line_num)    ((line_num) + num_cnf_clauses + 1)
#define LINE_NUM_FROM_LINE_ID(line_id)     ((line_id) - (num_cnf_clauses + 1))
#define CLAUSE_ID_FROM_LINE_NUM(line_num)  ((line_num) + num_cnf_clauses)
#define LINE_NUM_FROM_CLAUSE_ID(clause_id) ((clause_id) - num_cnf_clauses)

////////////////////////////////////////////////////////////////////////////////

// A typed result of an evaluation under a partial assignment
// TODO: Rename, so name doesn't directly clash with SUBST_TT, etc.
typedef enum peval {
  UNASSIGNED = -1,
  TT = 0,
  FF = 1,
} peval_t;

#define NOT_REDUCED              (-4)
#define REDUCED                  (-3)
#define SATISFIED_OR_MUL         (-2)
#define CONTRADICTION            (-1)

// Under FROM_DIMACS_LIT, literals get mapped onto nonnegative values.
// For the subst_mappings, we use negative values for true and false.
#define SUBST_TT                 (-1)
#define SUBST_FF                 (-2)

/**
 * @brief Signals the end of a witness. Always included at the end when parsing.
 * 
 * We must use a terminator to indicate the end of a witness because dsr-trim
 * may minimize a witness. Since we are storing all witness information in a
 * single flat array (a `range_array_t`), we may reduce the size of the witness
 * beyond what the beginning of the next witness might suggest.
 */
#define WITNESS_TERM       (INT_MIN)

/**
 * @brief The type of a line in an SR proof file.
 *
 * Each `ADDITION_LINE` adds a redundant clause to the formula, while
 * each `DELETION_LINE` removes one or more clauses from the formula. 
 */
typedef enum line_type {
  DELETION_LINE = 10,
  ADDITION_LINE = 20
} line_type_t;

/** 
 * @brief The parsing strategy when parsing proof files.
 * 
 * Proof files can either be parsed eagerly, meaning the entire proof file
 * is read into memory before any proof lines are checked; or the proof can
 * be parsed in streaming mode, meaning that a single line is read and then
 * checked before the next line is parsed. Streaming mode is great for
 * proofs that are too large to write down to disk or store completely in
 * memory at one time, such as for extremely large proofs accompanying
 * SAT results like the Pythegorean triples or the chromatic tiling 
 * number of the plane. Otherwise, eager should be the default, as it
 * benefits from I/O caching and fetching.
 * 
 * While the parsing and storage of redundant clauses is largely the same
 * across the two proof modes, the storage of substitution witnesses,
 * LSR unit propagation hints, and deletion lines is handled differently.
 */
typedef enum parsing_strategy {
  PS_EAGER = 3,
  PS_STREAMING = 8
} parsing_strategy_t;

// The global parsing strategy. By default, `PS_EAGER` is used.
extern parsing_strategy_t p_strategy;

/**
 * @brief Each literal tracks the first and last clause it appears in.
 * 
 */
typedef struct min_max_clause_to_check {
  srid_t min_clause;
  srid_t max_clause;
} min_max_clause_t;

/* 
 * Note that the partial assignments and substitutions need to use longs for the
 * timpstamp values, since the number of lines in a proof can exceed 2^32. But
 * literals must be < 2^32, according to the DIMACS format.
 */

/** 
 * @brief A flat array of all the parsed literals under FROM_DIMACS_LIT.
 * 
 * The array stores the clauses in the CNF formula and the redundant clauses 
 * in the SR proof file. The literals are stored from left-to-right with no
 * 0-termination. Instead, the indexes into the array delineating the clauses
 * are stored in the `clauses` array.
 */
extern int *lits_db;
extern srid_t lits_db_size;       // Number of literals in the database
extern srid_t lits_db_alloc_size; // Allocated size of the database

/**
 * @brief Indexes into the `lits` array forming implicit pointers, marking clauses.
 * 
 * The size of clause i is the difference `clauses[i + 1] - clauses[i]`.
 * Allocated with `malloc()`. The pointers start at `clauses[0] = 0`.
 */
extern srid_t *formula;
extern srid_t formula_size;        // Number of clauses in the database
extern srid_t formula_alloc_size;  // Allocated size of the clauses array

// The original number of clauses in the parsed CNF formula.
// Its value is set via a call to `parse_cnf()`.
extern srid_t num_cnf_clauses;

// The original number of variables in the parsed CNF formula.
// Its value is set via a call to `parse_cnf()`.
extern uint num_cnf_vars;

/**
 * @brief The partial assignment used for unit propagation and RAT hints.
 * 
 * Initialized to the negation of the candidate clause.
 * Uses "generation bumping" to make clearing the assignment O(1).
 * Indexed by 0-indexed variables, compare value to `current_generation`.
 */
extern ullong *alpha;
extern ullong *subst_generations;
extern int *subst_mappings;

// The allocated size of `alpha`, `subst`, and `lits_first/last_clause`.
// TODO: Rename
extern int alpha_subst_alloc_size;

// The generation for alpha. Increase by (1 + RAT steps) for each proof line.
extern ullong alpha_generation;

// Generation for substitution. Assume once per SR line, clear by incrementing.
extern ullong subst_generation;

/**
 * @brief The witness portion of the SR line.
 * 
 * When the parsing strategy is `PS_STREAMING`, the `range_array_t` is cleared
 * before parsing a new witness. This ensures that memory is reused.
 * 
 * When the parsing strategy is `PS_EAGER`, the `range_array_t` works normally.
 */
extern range_array_t witnesses;

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
extern srid_t min_clause_to_check;
extern srid_t max_clause_to_check;

// Cached size of the new SR clause. Equal to get_clause_size(formula_size).
extern uint new_clause_size; 

// Maximum 0-indexed variable ID parsed so far. Used for resizing arrays.
extern uint max_var;

// Flag for whether the empty clause has been derived.
// Can be set during CNF parsing if the empty clause is added.
extern int derived_empty_clause;

////////////////////////////////////////////////////////////////////////////////

int intcmp (const void *a, const void *b);
int absintcmp (const void *a, const void *b);

// Allocates and initializes global data structures, given the size of a CNF formula.
void init_global_data(void);

// Prints either `VERIFIED UNSAT` or `VALID`, depending on whether
// the empty clause was derived (`derived_empty_clause`).
void print_proof_checking_result(void);

void set_lit_for_alpha(int lit, ullong gen);
peval_t peval_lit_under_alpha(int lit);

int map_lit_under_subst(int lit);

void insert_lit(int lit);

void perform_clause_first_last_update(srid_t clause_index);
void commit_clause(void);
void commit_clause_with_first_last_update(void);
void uncommit_clause_with_first_last_update(void);
int  is_clause_deleted(srid_t clause_index);

// Deletes a clause. Errors if the clause is already deleted.
void delete_clause(srid_t clause_index);
void soft_delete_clause(srid_t clause_index);
void soft_undelete_clause(srid_t clause_index);

int *get_clause_start_unsafe(srid_t clause_index);
int *get_clause_start(srid_t clause_index);
int *get_clause_end_unsafe(srid_t clause_index);
int *get_clause_end(srid_t clause_index);
uint get_clause_size(srid_t clause_index);

void discard_formula_after_clause(srid_t clause_index);   

int *get_witness_start(srid_t line_num);
int *get_witness_end(srid_t line_num);
int  get_witness_size(srid_t line_num);

void compute_min_max_clause_to_check(srid_t line_num);
void assume_subst(srid_t line_num);

int assume_negated_clause(srid_t clause_index, ullong gen);
int assume_negated_clause_under_subst(srid_t clause_index, ullong gen);
int reduce_clause_under_subst(srid_t clause_index);
int reduce_clause_under_RAT_witness(srid_t clause_index, int pivot);

void update_first_last_clause(int lit);

void dbg_print_assignment(void);
void dbg_print_subst(void);
void dbg_print_witness(srid_t line_num);

#endif /* _GLOBAL_DATA_H_ */