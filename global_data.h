/**
 * @file global_data.h
 * @brief Global data used in SR proof labeling, trimming, and checking.]
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-10
 */

#ifndef _GLOBAL_DATA_H_
#define _GLOBAL_DATA_H_

////////////////////////////////////////////////////////////////////////////////

#ifndef ABS
#define ABS(x)     (((x) < 0) ? -(x) : (x))
#endif

#ifndef MIN
#define MIN(x, y)  (((x) < (y)) ? (x) : (y))
#endif

#ifndef MAX
#define MAX(x, y)  (((x) > (y)) ? (x) : (y))
#endif

#ifndef MSB
#define MSB32                     (1  << 31)
#define MSB64                     (1L << 63)

#define INT_SET_BIT(s)            (1  << (s))
#define LONG_SET_BIT(s)           (1L << (s))
#endif

/** DIMACS character that starts a comment line. */
#define DIMACS_COMMENT_LINE ('c')

/** DIMACS character that starts a problem line. */
#define DIMACS_PROBLEM_LINE ('p')

#define FROM_DIMACS_LIT(x)      (((x) < 0) ? (2 * -(x) - 1) : (2 * (x) - 2))
#define TO_DIMACS_LIT(x)        (((x) % 2) ? (((x) / -2) - 1) : (((x) / 2) + 1))
#define VAR_FROM_LIT(x)         ((x) >> 1)
#define IS_POS_LIT(x)           (!((x) & 0x1))
#define IS_NEG_LIT(x)           ((x) & 0x1)
#define NEGATE_LIT(x)           ((x) ^ 0x1)

/** Resizes an "allocation size value" when the container gets full. */
#define RESIZE(x)               (((x) * 3) >> 1)

#define RESIZE_ARR(arr, alloc_size, size, data_size)       do {                \
    if (size >= alloc_size) {                                                  \
      alloc_size = RESIZE(size);                                               \
      arr = xrealloc(arr, alloc_size * data_size);                             \
    }                                                                          \
  } while (0)

#define PRINT_ERR_AND_EXIT(s)      do {                                        \
    fprintf(stderr, "c Error: %s\n", s); exit(-1);                             \
  } while (0)

#define PRINT_ERR_AND_EXIT_IF(cond, s)    do {                                 \
    if (cond) {                                                                \
      fprintf(stderr, "c Error: %s\n", s); exit(-1);                           \
    }                                                                          \
  } while (0)

#define READ_LONG_TOKEN(res, f, ptr)            do {                           \
    res = fscanf(f, "%ld ", ptr);                                              \
    PRINT_ERR_AND_EXIT_IF(res == 0, "Token was expected to be a number.");     \
    PRINT_ERR_AND_EXIT_IF(res == EOF, "EOF unexpectedly reached.");            \
    PRINT_ERR_AND_EXIT_IF(res < 0, "Other error encountered while parsing.");  \
  } while (0)

#define READ_NUMERICAL_TOKEN(res, f, ptr)       do {                           \
    res = fscanf(f, "%d ", ptr);                                               \
    PRINT_ERR_AND_EXIT_IF(res == 0, "Token was expected to be a number.");     \
    PRINT_ERR_AND_EXIT_IF(res == EOF, "EOF unexpectedly reached.");            \
    PRINT_ERR_AND_EXIT_IF(res < 0, "Other error encountered while parsing.");  \
  } while (0)

////////////////////////////////////////////////////////////////////////////////

// A typed result of an evaluation under a partial assignment
typedef enum peval {
  FF = -1,
  UNASSIGNED = 0,
  TT = 1
} peval_t;

#define NOT_REDUCED              (-4)
#define REDUCED                  (-3)
#define SATISFIED_OR_MUL         (-2)
#define CONTRADICTION            (-1)

// Under FROM_DIMACS_LIT, literals get mapped onto nonnegative values.
// For the subst_mappings, we use negative values for true and false.
#define SUBST_TT                 (-1)
#define SUBST_FF                 (-2)
#define SUBST_UNASSIGNED         (-3)

/* Note that the partial assignments and substitutions need to use longs for the
 * generation values, since the number of lines in a proof can exceed 2^32. But
 * literals must be < 2^32.
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
extern int lits_db_size;       // Number of literals in the database
extern int lits_db_alloc_size; // Allocated size of the database

/**
 * @brief Indexes into the `lits` array forming implicit pointers, marking clauses.
 * 
 * The size of clause i is the difference `clauses[i + 1] - clauses[i]`.
 * Allocated with `malloc()`. The pointers start at `clauses[0] = 0`.
 */
extern int *formula;
extern int formula_size;        // Number of clauses in the database
extern int formula_alloc_size;  // Allocated size of the clauses array

// The first clause index each literal appears in. Initialized to -1.
extern int *lits_first_clause;

// The last clause index each literal appears in. Initialized to -1.
extern int *lits_last_clause;   

/**
 * @brief The partial assignment used for unit propagation and RAT hints.
 * 
 * Initialized to the negation of the candidate clause.
 * Uses "generation bumping" to make clearing the assignment O(1).
 * Indexed by 0-indexed variables, compare value to `current_generation`.
 */
extern long *alpha;
extern long *subst_generations;
extern int *subst_mappings;
extern long *subst_taut; // Used for tautology checking when reducing under subst
extern int alpha_subst_alloc_size;

// The "generation bumping" used for tautology checking is independent from the
// global "current_generation," since tautology may be found on non-RAT clauses,
// and the taut generation array needs to be cleared after each check.
// TODO: Overflow possibility? Perhaps use ulong, or initially set to LONG_MIN.
extern long taut_generation;

// The witness portion of an SR certificate or proof line.
extern int *witness;
extern int witness_size;
extern int witness_alloc_size;

// If a witness is provided, the first literal of the clause is the pivot.
extern int pivot;

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

// Cached size of the new SR clause. Equal to get_clause_size(formula_size).
extern int new_clause_size; 

/** Witnesses in SR can have literals set to true/false, as in LRAT/LPR, or
 *  they can set variables to other literals. The point at which the witness
 *  switches to substitution is updated when an SR proof line is parsed.
 *  If no switch occurs, then subst_index is set to witness_size.
 */
extern int subst_index;

// Maximum 0-indexed variable ID parsed so far. Used for resizing arrays.
extern int max_var;

// The current generation. Increase by (1 + RAT steps) for each proof line.
extern long current_generation;

////////////////////////////////////////////////////////////////////////////////

int intcompare (const void *a, const void *b);
int absintcompare (const void *a, const void *b);

// Allocates and initializes global data structures, given the size of a CNF formula.
void init_global_data(int num_clauses, int num_vars);

void set_lit_for_alpha(int lit, long gen);
peval_t peval_lit_under_alpha(int lit);

void set_mapping_for_subst(int lit, int lit_mapping, long gen);
int get_lit_from_subst(int lit);

void set_lit_for_taut(int lit);
peval_t peval_lit_under_taut(int lit);

/** Inserts a literal into the database. Handles resizing of the appropriate global_data
 *  arrays. To mark a clause as finished, call `insert_clause`.
 * 
 *  The lit is expected to be in 0-indexed format, using FROM_DIMACS_LIT.
 */
void insert_lit(int lit);
void insert_lit_no_first_last_update(int lit);

// Caps the current clause and increments the clause count. Clauses can be empty.
void insert_clause(void);
void insert_clause_first_last_update(void);
int  is_clause_deleted(int clause_index);

// Deletes a clause. Errors if the clause is already deleted.
void delete_clause(int clause_index);    

int *get_clause_start_unsafe(int clause_index);
int *get_clause_start(int clause_index);
int  get_clause_size(int clause_index);

void assume_subst(long gen);
void assume_negated_clause(int clause_index, long gen);
int  assume_negated_clause_under_subst(int clause_index, long gen);
int  reduce_subst_mapped(int clause_index);

void update_first_last_clause(int lit);

#endif /* _GLOBAL_DATA_H_ */