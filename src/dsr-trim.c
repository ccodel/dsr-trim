/**
 * @file dsr-trim.c
 * @brief A tool for labeling and trimming SR proof certificates.
 * 
 *  `dsr-trim` checks deletion substitution redundancy (DSR) proofs and
 *  annotates them with unit propagation hints to form linear substitution
 *  redundancy (LSR) proofs, which can be checked by `lsr-check`.
 * 
 *  Roughly, DSR proofs are used to show that two propositional logic
 *  formulas are equisatisfiable, meaning that the original formula is
 *  satisfiable if and only if the derived formula is. DSR proofs do this
 *  by incrementally adding and deleting clauses from the formula. Added
 *  clauses must be redundant, i.e., adding them to the formula does not
 *  affect its satisfiability. In other words, a clause C is redundant
 *  with respect to formula F if formulas F and (F /\ C) are equisatisfiable.
 * 
 *  In most cases, DSR proofs are *unsatisfiability* proofs, meaning that
 *  the empty clause is eventually shown to be redundant. Since the empty
 *  clause is by definition unsatisfiable, this means that the original
 *  formula is unsatisfiable as well.
 * 
 *  In clausal proof systems generally, addition lines may contain witnesses
 *  that help the proof checker show that the clause is redundant. In SR,
 *  these witnesses are substitutions, which map variables to either true,
 *  false, or a literal. Intuitively, the substitution expresses how to
 *  "repair" the formula if a satisfying assignment for F doesn't satisfy C.
 * 
 *  This repository uses two distinct proof formats: DSR and LSR.
 *  DSR proofs only contain clauses and substitution witnesses, and so
 *  `dsr-trim` must perform unit propagation across the entire formula to
 *  derive hints. To do so, it maintains several data structures, such as
 *  a stack of unit literals/clauses and a record of which clauses were used
 *  in which UP derivations so that the number of hints may be minimized.
 * 
 *  More details can be found in the paper:
 * 
 *    "Verified Substitution Redundancy Checking"
 *    Cayden Codel, Jeremy Avigad, Marijn J. H. Heule
 *    In FMCAD 2024
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-12
 */

#include <string.h>
#include <getopt.h>

#include "bitmask.h"
#include "cli.h"
#include "cnf_parser.h"
#include "global_data.h"
#include "global_parsing.h"
#include "hash_table.h"
#include "lit_occ.h"
#include "logger.h"
#include "range_array.h"
#include "sr_parser.h"
#include "timer.h"
#include "xio.h"
#include "xmalloc.h"

/*
TODOs:
  - Candidate clause minimization. When marking clauses, mark literals as well.
  - Watch-pointer de-sizing. (i.e. fewer watch pointers de-size the wp array)
  - Double-check that get_clause_start() with deletions are used correctly.
      Don't want to use a deleted clause (more important for lsr-check).

Potential optimizations:
  - According to the profiler, a lot of time is spent in mark_dependencies,
      because all unit clauses must be iterated over. Instead, an array indexed
      by clauses could be maintained, and when a unit clause is involved in UP,
      its "unit_clauses" index is consulted to update a min/max value of clauses
      to mark in mark_dependencies. However, this probably won't work very well,
      because as mark_dependencies works, new clauses are marked.
  - Store the reduced clause in reduce_subst_mapped in an array. This would make
      RAT checks cheaper because rather than doing two loops over the clause,
      we can instead consult the cached substitution-mapped clause in the array.
  - Marijn's code computes the RAT set from the watch pointers. Might be more
    efficient than tracking the first/last.
*/

////////////////////////////////////////////////////////////////////////////////

// The initial allocation size for the watch pointer lists for any literal.
#define INIT_LIT_WP_ARRAY_SIZE  (4)

// The initial allocation size for tracking the multiplicity of clauses.
// This allows the checker to accept multiple copies of any clause without
// actually storing multiple copies.
// See `clause_mult_t`.
#define INIT_CLAUSE_MULT_SIZE   (16)

// When setting literals "globally" under initial unit propagation, we use the
// largest possible generation value.
#define GLOBAL_GEN   (ULLONG_MAX - 1L)

/**
 * @brief The generation value used when assuming the negation of a
 *        candidate redundant clause.
 * 
 * The unit literals assumed from the negation of the candidate redundant
 * clause must persist in `alpha` for an unknown number of reduced clauses
 * and an unknown number of UP steps. Thus, to differentiate assumed literals
 * from global unit literals, we pick the next-highest timestamp value
 * beneath `GLOBAL_GEN`.
 */
#define ASSUMED_GEN  (GLOBAL_GEN - GEN_INC)

#define MARK_USER_DEL_LUI(x)       ((x) | SRID_MSB)
#define IS_USER_DEL_LUI(x)         (((x) & SRID_MSB) && ((x) != -1))
#define LUI_FROM_USER_DEL_LUI(x)   ((x) & (~SRID_MSB))
#define IS_UNUSED_LUI(x)           ((x) & SRID_MSB)
#define IS_USED_LUI(x)             (!IS_UNUSED_LUI(x))

// The default value for `vars_unit_indexes` entries, indicating that
// the variable is unset in the `alpha` assignment and that it is
// not in the `unit_literals` array.
#define NO_UNIT_INDEX        (-1)

/**
 * @brief Returns the index into the `hints` structure corresponding to the
 *        block of unit propagation hints for the given `line_num`.
 *        Used only during backwards checking.
 * 
 * During backwards checking, we perform "global" unit propagation after
 * assuming the negation of the candidate redundant clause. We store UP
 * hints for the reduced RAT clauses first, and then at the end, we store
 * only those global unit literals needed for the RAT hint groups.
 * 
 * However, LSR proof lines expect those global unit literal hints first.
 * Thus, we store the global UP hints *after* the RAT hints. Hence the +1
 * here.
 * 
 * In other words, there are two hint groups for each line number, with
 * the RAT hints first, and then the global UP hints.
 */
#define UP_HINTS_IDX_FROM_LINE_NUM(line_num)  \
  ((((num_parsed_add_lines - 1) - (line_num)) * 2) + 1)

/**
 * @brief Returns the index into the `hints` structure corresponding to the
 *        block of RAT hints for the given `line_num`.
 *        Used only during backwards checking.
 * 
 * See the comment for `UP_HINTS_IDX_FROM_LINE_NUM`.
 */
#define RAT_HINTS_IDX_FROM_LINE_NUM(line_num) \
  (((num_parsed_add_lines - 1) - (line_num)) * 2)

#define DEL_IDX_FROM_LINE_NUM(line_num)  \
  ((num_parsed_add_lines - 1) - (line_num))

// A common swap operation in `perform_up_for_backwards_checking()`.
#define SWAP_WP_LIST_ELEMS(wp_list, clause_id, j, ignored_j)         do {      \
    if (j != ignored_j) {                                                      \
      wp_list[j] = wp_list[ignored_j];                                         \
      wp_list[ignored_j] = clause_id;                                          \
    }                                                                          \
    ignored_j++;                                                               \
  } while (0)

#define SKIP_REMAINING_UP_HINTS(iter, end) do {                                \
    while ((iter) < (end) && *(iter) > 0) (iter)++;                            \
  } while (0)

typedef enum sr_checking_mode {
  FORWARDS_CHECKING_MODE,
  BACKWARDS_CHECKING_MODE,
} checking_mode_t;

// The checking mode. By default, it is set to `BACKWARDS_CHECKING_MODE`.
static checking_mode_t ch_mode = BACKWARDS_CHECKING_MODE;

// SR trim as a state machine, for different parts of UP.
typedef enum sr_trim_up_state {
  GLOBAL_UP,
  CANDIDATE_UP,
  RAT_UP,
} up_state_t;

static up_state_t up_state = GLOBAL_UP;

// 2D array of watch pointers, indexed by literals.
// Initialized to NULL for each literal.
static srid_t **wps = NULL;

// Allocated size of the 2D array of watch pointers.
static uint wps_alloc_size = 0;

// Allocated size of watch pointer array for each literal.
// Invariant: if wps[i] == NULL, then wp_alloc_sizes[i] = 0.
static uint *wp_alloc_sizes = NULL;

// Number of watch pointers under each literal.
// Invariant: if wps[i] == NULL, then wp_sizes[i] = 0.
static uint *wp_sizes = NULL; // TODO: New name

// A list of literals, in order of when they become unit.
static int *unit_literals = NULL;

// A list of clauses, in order of when they became unit.
static srid_t *unit_clauses = NULL;
static uint units_alloc_size = 0;
static uint units_size = 0;

// Indexed by variable.
// Stores the index into `unit_literals` if that variable is set to true/false.
// The MSB is set during candidate/RAT assumption to compute the minimal set of UP hints.
static int *vars_unit_indexes = NULL;
static int vars_unit_indexes_alloc_size = 0;

static ullong *vars_dependency_markings = NULL;
static int vars_dependency_markings_alloc_size = 0;

// Index pointing at the "unprocessed" global UP literals
static uint global_up_literals_index = 0;

static uint candidate_assumed_literals_index = 0;
static uint candidate_unit_literals_index = 0;
static uint RAT_assumed_literals_index = 0;
static uint RAT_unit_literals_index = 0;

/**
 * @brief Stores the variables added as unit literals when assuming the
 *        negation of a mapped RAT clause that were originally derived
 *        via global or candidate-clause UP.
 * 
 * When we assume the negation of a RAT clause (under a substitution),
 * we want to keep track of which new unit literals/clauses we added.
 * In particular, we want to mark which variables were already units,
 * so that we may mark their assumption bit with `MARK_AS_UP_ASSUMED_VAR`.
 * That way, when we unassume the RAT clause, we can differentiate between
 * new unit literals and clearing the assumption bit of "old" ones.
 * 
 * See `assume_RAT_clause_under_subst()` and `unassume_RAT_clause()`.
 */
static int *RAT_marked_vars = NULL;
static uint RAT_marked_vars_alloc_size = 0;
static uint RAT_marked_vars_size = 0;

static FILE *dsr_file = NULL;
static FILE *lsr_file = NULL;

// The total number of addition lines parsed. Incremented by `parse_dsr_line()`.
static srid_t num_parsed_add_lines = 0;
static srid_t num_parsed_del_lines = 0;
static srid_t num_parsed_lines = 0;
static uint parsed_empty_clause = 0;

// 0-indexed current line ID.
static srid_t current_line = 0;

// Records the 0-indexed line number of the maximum line with RAT hint groups.
// This is used to reduce unhelpful deletions when the rest of the proof is
// only normal UP derivations.
static srid_t max_RAT_line = -1;

static srid_t *clause_id_map = NULL;

// Because deletion lines in the DSR format identify a clause to be deleted,
// and not a clause ID, we use a hash table to store clause IDs, where the
// hash is a commutative function of the literals. That way, permutations of
// the clause will hash to the same thing.

// The clause ID hash table, used for checking deletions.
static ht_t clause_id_ht;

// Counts the number of times a clause appears in the formula.
typedef struct clause_multiplicity {
  srid_t clause_id;
  int multiplicity;
} clause_mult_t;

// This hash table works in concert with `clause_id_t`
// and stores multiplicies of clauses with two or more copies in the formula.
static ht_t clause_mults_ht;

// Forward declare these functions, since deletion needs them
static void remove_wp_for_lit(int lit, srid_t clause);
static srid_t perform_up_for_backwards_checking(ullong gen);
static srid_t perform_up_for_forwards_checking(ullong gen);

/*
 * Backwards checking:
 */

// The highest 0-indexed line ID that each clause appears in, in the proof.
// By default, initialized to -1.
// These IDs are set during backwards checking.
// First, any clause that appears in the UP refutation of the empty clause
// is marked.
static srid_t *clauses_lui = NULL;
static uint clauses_lui_alloc_size = 0;

// Stores the index into each unit literal's watch pointer list
// to reduce duplicate checks on SAT/unit clauses during backwards checking
// unit propagation.
//
// Is kept as NULL if not doing backward checking.
// See `set_unit_literal`.
static uint *unit_literals_wp_up_indexes = NULL;

/**
 * @brief Store line hints.
 * 
 * Invariant: because RAT hints are generated before global UP hints,
 * we store RAT hint groups at (2 * line_num) and the global UP hints
 * at ((2 * line_num) + 1).
 * 
 */
static range_array_t hints;

// Stores user deletions. Is 0-indexed, but because a user might delete
// clauses before the first addition line, it is "1-indexed" with
// respect to line numbers.
static range_array_t deletions;

// Used to store user deletions during backwards checking
// (Not to be confused with `deletions`, where user deletions get
// stored during forward checking.)
static range_array_t bcu_deletions;

typedef struct line_RAT_hint_information {
  srid_t num_RAT_clauses;
  srid_t num_reduced_clauses;
} line_RAT_info_t;

static line_RAT_info_t *lines_RAT_hint_info = NULL;
static uint lines_RAT_hint_info_alloc_size = 0;
static uint num_RAT_clauses = 0;
static uint num_reduced_clauses = 0;

// Indexed by the 0-indexed `current_line`.
// Used only during backwards checking, and allocated by `add_initial_wps()`.
static fl_clause_t *lines_fl_clauses_to_check = NULL;

// Allocated by `add_initial_wps()`.
// During backwards checking, destroyed once the empty clause is derived.
// During forwards checking, the structure is updated as the proof gets checked.
static lit_occ_t lit_occ;
static bmask_t bmask;

static sr_timer_t timer;

static srid_t num_drat_lines = 0;
static srid_t num_sr_lines = 0;

// Forward declare debug printing functions.
static void dbg_print_hints(srid_t line_num);
static void dbg_print_last_used_ids(void);
static void dbg_print_up_reasons(void);
static void dbg_print_unit_literals(void);

////////////////////////////////////////////////////////////////////////////////

// Command-line options and the printing of help messages

#define FORWARD_OPT          ('f')
#define COMPRESS_PROOF_OPT   ('c')
#define EMIT_VALID_FORM_OPT  (LONG_HELP_MSG_OPT + 1)
#define DEL_UNITS_OPT        (LONG_HELP_MSG_OPT + 2)
#define DEL_IMPL_UNITS_OPT   (LONG_HELP_MSG_OPT + 3)

#define OPT_STR             ("cf" BASE_CLI_OPT_STR)

// The file where we emit a VALID formula, if `--emit-valid-formula-to` is set.
static FILE *valid_formula_file = NULL;

/*
 * CC (9/17/2025): After staring at a whiteboard for an hour, I convinced
 * myself that, while it is sometimes advantageous to delete an implied unit
 * clause, it is never advantageous to delete a true unit. This is because
 * true units force any witness/substitution to avoid mapping the true
 * unit literal to false. This property is not the case for implied units.
 * 
 * However, perhaps a proof really does need to delete true units.
 * Thus, we define both a `--delete-implied-units` option and a
 * `--delete-units` option. By default, both kinds of deletions are ignored.
 */

static int ignore_unit_deletions = 1;
static int ignore_implied_unit_deletions = 1;

// The set of "long options" for CLI argument parsing. Used by `getopt_long()`.
static struct option const longopts[] = {
  { "forward",                     no_argument, NULL, FORWARD_OPT },
  { "compress",                    no_argument, NULL, COMPRESS_PROOF_OPT },
  { "emit-valid-formula-to", required_argument, NULL, EMIT_VALID_FORM_OPT },
  { "delete-units",                no_argument, NULL, DEL_UNITS_OPT },
  { "delete-implied-units",        no_argument, NULL, DEL_IMPL_UNITS_OPT },
  BASE_LONG_OPTS_ARRAY
};

// Prints a shorter help message to the provided `FILE` stream.
static void print_short_help_msg(FILE *f) {
  char *usage_str = "Usage: ./dsr-trim [OPTIONS] <cnf> <dsr> [lsr]\n";
  fprintf(f, "%s", usage_str);
}

// Prints a longer help message to the provided `FILE` stream.
static void print_long_help_msg(FILE *f) {
  char *usage_str = "Usage: ./dsr-trim [OPTIONS] <cnf> <dsr> [lsr]\n";
  fprintf(f, "%s", usage_str);
}

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Returns `1` if there is another DSR line to be checked.
 * 
 * During backwards checking, another line can be checked if the `current_line`
 * is strictly positive. Thus, the caller must decrease `current_line` after
 * calling this function.
 * 
 * @return `1` if there is another DSR line to be checked and `0` otherwise.
 */
static int has_another_dsr_line(void) {
  if (p_strategy == PS_EAGER) {
    if (ch_mode == BACKWARDS_CHECKING_MODE) {
      return (current_line > 0);
    } else {
      // We parsed the proof already, so "yes" as long as we have a line left
      return (current_line < num_parsed_add_lines);
    }
  } else {
    return !derived_empty_clause && has_another_line(dsr_file);
  }
}

/**
 * @brief Returns a pointer to the start of the block of unit propagation
 *        hints stored for the given line number.
 * 
 * During forwards checking, we reset the `hints` structure after each line,
 * since we emit the proof lines as we go. The resetting saves memory.
 * 
 * During backwards checking, we store blocks of (RAT, UP) hints for each line.
 * 
 * @param line_num The 0-indexed line number for the stored hints.
 * @return A pointer to the start of the block of hints.
 */
static inline srid_t *get_UP_hints_start(srid_t line_num) {
  srid_t idx = (ch_mode == BACKWARDS_CHECKING_MODE) ?
    UP_HINTS_IDX_FROM_LINE_NUM(line_num) : 1;
  return ra_get_range_start(&hints, idx);
}

/**
 * @brief Returns a pointer to one more than the last hint in the UP hints
 *        block for the given line number.
 * 
 * @param line_num The 0-indexed line number for the stored hints.
 * @return The exclusive end of the UP hints.
 */
static inline srid_t *get_UP_hints_end(srid_t line_num) {
  srid_t idx = (ch_mode == BACKWARDS_CHECKING_MODE) ?
    UP_HINTS_IDX_FROM_LINE_NUM(line_num) : 1;
  return ra_get_range_end(&hints, idx);
}

static inline srid_t *get_RAT_hints_start(srid_t line_num) {
  srid_t idx = (ch_mode == BACKWARDS_CHECKING_MODE) ?
    RAT_HINTS_IDX_FROM_LINE_NUM(line_num) : 0;
  return ra_get_range_start(&hints, idx);
}

static inline srid_t *get_RAT_hints_end(srid_t line_num) {
  srid_t idx = (ch_mode == BACKWARDS_CHECKING_MODE) ?
    RAT_HINTS_IDX_FROM_LINE_NUM(line_num) : 0;
  return ra_get_range_end(&hints, idx);
}

/**
 * @brief Returns the effective formula size, based on the checking mode,
 *        the `current_line`, and the `formula_size`. The returned value
 *        is the size of the CNF formula plus the number of checked clauses.
 * 
 * @return The effective formula size.
 */
static inline srid_t get_effective_formula_size(void) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    return CLAUSE_ID_FROM_LINE_NUM(current_line) - 1;
  } else {
    return formula_size;
  }
}

static inline srid_t get_num_RAT_clauses(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    return lines_RAT_hint_info[line_num].num_RAT_clauses;
  } else {
    return num_RAT_clauses;
  }
}

static inline srid_t get_num_reduced_clauses(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    return lines_RAT_hint_info[line_num].num_reduced_clauses;
  } else {
    return num_reduced_clauses;
  }
}

static inline void increment_num_reduced_clauses(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    lines_RAT_hint_info[line_num].num_reduced_clauses++;
  } else {
    num_reduced_clauses++;
  }
}

static inline void store_derived_deletion(srid_t clause_id) {
  FATAL_ERR_IF(ch_mode != BACKWARDS_CHECKING_MODE,
    "Can only derive deletions in backwards checking mode.");

  // Don't store derived deletions for the line with the empty clause,
  // since the empty clause's proof line will just be UP, and deletions
  // won't help speed up that check at all
  if (current_line == num_parsed_add_lines - 1) return;
  ra_insert_srid_elt(&deletions, clause_id);
}

static inline void store_user_deletion(srid_t clause_id) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    ra_insert_srid_elt(&bcu_deletions, clause_id);
  } else {
    ra_insert_srid_elt(&deletions, clause_id);
  }
}

static srid_t *get_deletions_start(srid_t line_num) {
  srid_t idx = (ch_mode == BACKWARDS_CHECKING_MODE) ?
    DEL_IDX_FROM_LINE_NUM(line_num) : 0;
  return ra_get_range_start(&deletions, idx);
}

static srid_t *get_deletions_end(srid_t line_num) {
  srid_t idx = (ch_mode == BACKWARDS_CHECKING_MODE) ?
    DEL_IDX_FROM_LINE_NUM(line_num) : 0;
  return ra_get_range_end(&deletions, idx);
}

static uint get_num_deletions(srid_t line_num) {
  return (uint) (get_deletions_end(line_num) - get_deletions_start(line_num));
}

/**
 * @brief Returns the start of the backwards-checking user (BCU) deleted
 *        clauses for a given `line_num`. Only used during backwards checking.
 * 
 * Note: it is the caller's responsibility that `ch_mode` must be set for
 * backwards checking.
 *
 * @param line_num The 0-indexed line number.
 * @return A pointer to the start of the deletions.
 */
static srid_t *get_bcu_deletions_start(srid_t line_num) {
  return ra_get_range_start(&bcu_deletions, line_num);
}

static srid_t *get_bcu_deletions_end(srid_t line_num) {
  return ra_get_range_end(&bcu_deletions, line_num);
}

/**
 * @brief Discards (i.e. erases, deletes) the stored backwards-checking
 *        user (BCU) deletions for and after the given `line_num`.
 * 
 * Whenever we are about to check a new line during backwards checking,
 * we must restore the watch pointers of the clauses deleted by the user
 * in the parsed DSR proof. This restoration also applies to clauses
 * deleted before we derive the empty clause.
 * 
 * However, if we derive the empty clause sooner than the DSR proof claims
 * we can, then any deletions after the "new" empty clause should
 * be discarded, since otherwise we will try to restore watch pointers
 * for clauses that never actually ended up being deleted. To accomplish
 * this, we clear those user deletions.
 * 
 * TODO: This problem can probably be avoided if the restoration of
 * user deletions is done after checking a line and not before checking
 * a line, but I think a single call to this function is an okay price
 * to pay to keep the restoration functionality in `prepare_dsr_line()`.
 * 
 * @param line_num The 0-indexed line number to clear deletions after.
 *                 Deletions are discarded for `line_num` as well.
 */
static void discard_bcu_deletions_after_empty_clause(srid_t line_num) {
  ra_clear_data_after_range(&bcu_deletions, line_num);
}

// Assumes only called during backwards checking.
// Returns `1` if the LUI is adjusted. Returns `0` otherwise.
static uint adjust_clause_lui(srid_t clause_id) {
  srid_t lui = clauses_lui[clause_id];

  if (IS_USER_DEL_LUI(lui)) {
    FATAL_ERR_IF(current_line > LUI_FROM_USER_DEL_LUI(lui),
      "[line %lld] Clause %lld was used in UP after being deleted on line %lld",
      current_line, TO_DIMACS_CLAUSE(clause_id), LUI_FROM_USER_DEL_LUI(lui));
  }

  if (IS_UNUSED_LUI(lui)) {
    clauses_lui[clause_id] = current_line;
    store_derived_deletion(clause_id);
    return 1;
  }

  return 0;
}

// Adds a unit propagation hint to `hints` and marks the last used id.
static inline void add_up_hint(srid_t clause_id) {
  ra_insert_srid_elt(&hints, TO_DIMACS_CLAUSE(clause_id));
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    adjust_clause_lui(clause_id);
  }
}

static void add_RAT_clause_hint(srid_t clause_id) {
  ra_insert_srid_elt(&hints, TO_RAT_HINT(clause_id));
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    lines_RAT_hint_info[current_line].num_RAT_clauses++;
  } else {
    num_RAT_clauses++;
  }
}

static inline void add_RAT_up_hint(srid_t clause_id) {
  ra_insert_srid_elt(&hints, TO_DIMACS_CLAUSE(clause_id));
}

////////////////////////////////////////////////////////////////////////////////

static inline int is_var_set_due_to_up(int var) {
  return vars_unit_indexes[var] >= 0;
}

static inline int is_lit_set_due_to_up(int lit) {
  return is_var_set_due_to_up(VAR_FROM_LIT(lit));
}

static inline int is_var_assumed_and_set_due_to_up(int var) {
  return vars_unit_indexes[var] < NO_UNIT_INDEX;
}

static inline int is_lit_assumed_and_set_due_to_up(int lit) {
  return is_var_assumed_and_set_due_to_up(VAR_FROM_LIT(lit));
}

static inline int is_var_assumed_only_for_up(int var) {
  return vars_unit_indexes[var] == NO_UNIT_INDEX;
}

static inline int is_lit_assumed_only_for_up(int lit) {
  return is_var_assumed_only_for_up(VAR_FROM_LIT(lit));
}

static inline int is_var_assumed_for_up(int var) {
  return vars_unit_indexes[var] <= NO_UNIT_INDEX;
}

static inline int is_lit_assumed_for_up(int lit) {
  return is_var_assumed_for_up(VAR_FROM_LIT(lit));
}

static inline void clear_var_unit_index(int var) {
  vars_unit_indexes[var] = NO_UNIT_INDEX;
}

static inline void clear_lit_unit_index(int lit) {
  clear_var_unit_index(VAR_FROM_LIT(lit));
}

static inline void mark_var_unit_index_as_assumed(int var) {
  vars_unit_indexes[var] |= MSB32;
}

static inline void mark_lit_unit_index_as_assumed(int lit) {
  mark_var_unit_index_as_assumed(VAR_FROM_LIT(lit));
}

static inline void clear_assumption_from_var_unit_index(int var) {
  vars_unit_indexes[var] &= (~MSB32);
}

static inline void clear_assumption_from_lit_unit_index(int lit) {
  clear_assumption_from_var_unit_index(VAR_FROM_LIT(lit));
}

static inline int get_unit_index_for_var(int var) {
  return vars_unit_indexes[var] & (~MSB32);
}

static inline int get_unit_index_for_lit(int lit) {
  return get_unit_index_for_var(VAR_FROM_LIT(lit));
}

static inline srid_t get_unit_clause_for_var(int var) {
  return unit_clauses[get_unit_index_for_var(var)];
}

static inline srid_t get_unit_clause_for_lit(int lit) {
  return get_unit_clause_for_var(VAR_FROM_LIT(lit));
}


////////////////////////////////////////////////////////////////////////////////

static void dbg_print_last_used_ids(void) {
  for (int i = 0; i < formula_size; i++) {
    if (i % 5 == 4) {
      log_raw(VL_NORMAL, "[%d] ", TO_DIMACS_CLAUSE(i));
    }
    if (IS_USER_DEL_LUI(clauses_lui[i])) {
      log_raw(VL_NORMAL, "d%d ", LUI_FROM_USER_DEL_LUI(clauses_lui[i]));
    } else if (clauses_lui[i] == -1) {
      log_raw(VL_NORMAL, "-1 ");
    } else {
      log_raw(VL_NORMAL, "%d ", CLAUSE_ID_FROM_LINE_NUM(clauses_lui[i]));
    }
  }
  log_raw(VL_NORMAL, "\n");
}

static void dbg_print_up_reasons(void) {
  for (int v = 0; v <= max_var; v++) {
    if (is_var_assumed_only_for_up(v)) {
      logc_raw("[%d]a", v + 1);
    } else if (is_var_assumed_and_set_due_to_up(v)) {
      logc_raw("[%d]a%d ", v + 1, TO_DIMACS_CLAUSE(get_unit_clause_for_var(v)));
    } else if (is_var_set_due_to_up(v)) {
      logc_raw("[%d]%d ", v + 1, TO_DIMACS_CLAUSE(get_unit_clause_for_var(v)));
    }
  }
  logc_raw("\n");
}

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Remaps clause IDs by ignored unused addition lines.
 * 
 */
static void generate_clause_id_map(void) {
  clause_id_map = xmalloc(formula_size * sizeof(srid_t));
  srid_t map_counter = num_cnf_clauses;
  for (srid_t c = num_cnf_clauses; c < formula_size; c++) {
    if (IS_USED_LUI(clauses_lui[c])) {
      clause_id_map[c] = map_counter;
      map_counter++;
    }
  }
}

static inline void resize_last_used_ids(void) {
  FATAL_ERR_IF(ch_mode != BACKWARDS_CHECKING_MODE,
    "Last used IDs are only resized during backwards checking.");
  RESIZE_MEMSET_ARR(clauses_lui,
    clauses_lui_alloc_size, formula_size, sizeof(srid_t), 0xff);
}

static inline void unassign_global_unit(int lit) {
  int var = VAR_FROM_LIT(lit);
  clear_var_unit_index(var);
  alpha[var] = 0;
}

static inline void unassign_global_unit_at_index(int index) {
  int lit = unit_literals[index];
  unassign_global_unit(lit);
}

/**
 * @brief Undoes the effects of making the literals in `unit_literals` unit,
 *        starting from `from_index` (inclusive).
 * 
 * Only undoes the effect of the units being made global.
 * The global variable `units_size` is not changed.
 * 
 * This function sets each variable's `alpha` generation to 0
 * and clears its UP index. In other words, the variable is
 * unset in the truth assignment, and no clause causes it to be unit.
 * 
 * @param from_index The index to start clearing from.
 *                   Proceeds up to `units_size` (exclusive).
 */
static void unassign_global_units(srid_t from_index) {
  for (int i = from_index; i < units_size; i++) {
    unassign_global_unit_at_index(i);
  }
}

/**
 * @brief Undoes the effects of global unit propagation due to the implied unit
 *        clause at `from_index` being unit, in preparation for its deletion
 *        from the formula.
 * 
 * When deleting an implied unit clause `C`, we need to do two things:
 * 
 *   1. Unassign unit literals dependent on `C` being unit.
 * 
 *   2. Re-run unit propagation after deleting `C`.
 * 
 * This function does (1) but does NOT do (2), i.e., it does not re-run
 * unit propagation.
 * 
 * Ideally, we would unassign only those unit clauses dependent on `C`,
 * but that analysis involves maintaining a list of dependencies. For
 * example, suppose implied unit clause `C1` depends on `C`. Then for
 * all later implied unit clauses, we need to check if that clause depends
 * on `C` OR `C1`, and this problem gets worse with each implied unit clause
 * that we unassign.
 * 
 * Thus, we do a coarse analysis: if the clause is a true unit, it is kept
 * in `unit_literals`/`unit_clauses`. Otherwise, it is unassigned by setting
 * it `alpha` timestamp to `0` and its `up_reasons` to `NO_UP_REASON`.
 * 
 * To save on time when re-running UP, we calculate and store the minimum
 * starting index for `global_up_literals_index`. In the worst case,
 * we must re-run UP from the beginning of the unit literals/clauses.
 * But since UP proceeds in rounds, then if `from_index` was derived
 * due to the `i`th round of UP, then we only need to re-run UP
 * from this `i`th round.
 * 
 * The values of `global_up_literals_index` and `units_size` are updated.
 *
 * @param from_index The 0-indexed clause ID into `unit_clauses` of the
 *                   implied unit clause that is about to get deleted.
 */
static void unassign_global_units_due_to_deletion(int from_index) {
  srid_t unit_clause = unit_clauses[from_index];
  int min_unit_index = MAX(0, from_index - 1);

  // Find the minimum index of the unit literals causing this clause to be unit.
  // We re-do UP from this minimum index (which might be > 0, saving time).
  if (min_unit_index > 0) {
    int *clause_iter = get_clause_start_unsafe(unit_clause) + 1;
    int *clause_end = get_clause_end(unit_clause);
    for (; clause_iter < clause_end; clause_iter++) {
      int lit = *clause_iter;
      int idx = get_unit_index_for_lit(lit);
      min_unit_index = MIN(min_unit_index, idx);
    }
  }

  global_up_literals_index = MIN(min_unit_index, global_up_literals_index);

  // Now keep unit literals/clauses that are true units
  int write_idx = from_index;
  for (int i = from_index; i < units_size; i++) {
    int lit = unit_literals[i];
    unit_clause = unit_clauses[i];

    // Keep the true unit, as long as it's not the one we are deleting
    if (get_clause_size(unit_clause) == 1 && i > from_index) {
      unit_literals[write_idx] = lit;
      unit_clauses[write_idx] = unit_clause;
      vars_unit_indexes[VAR_FROM_LIT(lit)] = write_idx;
      write_idx++;
    } else {
      unassign_global_unit(lit);
    }
  }

  units_size = write_idx;
}

////////////////////////////////////////////////////////////////////////////////

static void print_wps(void) {
  for (int i = 0; i <= MAX_LIT; i++) {
    srid_t *wp_list = wps[i];
    uint wp_size = wp_sizes[i];
    if (wp_size == 0) continue;
    log_raw(VL_NORMAL, "[%d] ", TO_DIMACS_LIT(i));
    for (int j = 0; j < wp_size; j++) {
      log_raw(VL_NORMAL, "%d ", TO_DIMACS_CLAUSE(wp_list[j]));
    }
  }
  log_raw(VL_NORMAL, "\n");
}

static void print_nrhs(void) {
  srid_t sum = 0;
  srid_t size = MIN(num_parsed_add_lines, (srid_t) lines_RAT_hint_info_alloc_size);
  for (srid_t i = 0; i < size; i++) {
    sum += get_num_RAT_clauses(i);
  }

  if (sum == 0) return;

  log_raw(VL_NORMAL, "Num RAT hints: ");

  for (srid_t i = 0; i < size; i++) {
    if (i % 5 == 4) {
      log_raw(VL_NORMAL, "[%lld] ", i + 1);
    }
    log_raw(VL_NORMAL, "%lld ", get_num_RAT_clauses(i));
  }
  log_raw(VL_NORMAL, "\n\n");
}

static void print_active_formula(void) {
  logc("vvvvvvvvvvv Formula below");
  srid_t c = CLAUSE_ID_FROM_LINE_NUM(current_line);
  for (srid_t cp = 0; cp <= c; cp++) {
    if (LUI_FROM_USER_DEL_LUI(clauses_lui[cp]) >= current_line) {
      dbg_print_clause(cp);
    }
  }
  logc("^^^^^^^^^^ Formula above");
}

static void print_assignment(void) {
  log_raw(VL_NORMAL, "Assignment: ");
  for (int i = 0; i <= max_var; i++) {
    int lit = POS_LIT_FROM_VAR(i);
    int nlit = NEGATE_LIT(lit);
    switch (peval_lit_under_alpha(lit)) {
      case TT:
        logc_raw("%d (%lld) ", TO_DIMACS_LIT(lit), get_unit_clause_for_lit(lit));
        break;
      case FF:
        logc_raw("%d (%lld) ", TO_DIMACS_LIT(nlit), get_unit_clause_for_lit(lit));
        break;
      default: break;
    }
  }
  logc_raw("\n");
}

static void dbg_print_unit_literals(void) {
  logc("Unit literals (total %d):", units_size);
  for (int i = 0; i < units_size; i++) {
    int lit = unit_literals[i];
    log_raw(VL_NORMAL, "c [idx %d] %d   ", i, TO_DIMACS_LIT(lit));

    if (is_lit_assumed_only_for_up(lit)) {
      log_raw(VL_NORMAL, "negated from candidate or RAT clause\n");
    } else if (is_lit_assumed_and_set_due_to_up(lit)) {
      srid_t clause = get_unit_clause_for_lit(lit);
      log_raw(VL_NORMAL, "negated and derived from clause %lld: ",
        TO_DIMACS_CLAUSE(clause));
      dbg_print_clause(clause);
    } else {
      srid_t clause = get_unit_clause_for_lit(lit);
      log_raw(VL_NORMAL, " due to clause: ");
      dbg_print_clause(clause);
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Prints the initial set of clause deletions, before a single
 *        addition line is printed. Only used for backwards checking.
 * 
 * During backwards checking, any clause that isn't used in the entire
 * proof will have an `IS_UNUSED_LUI`. This function loops through all
 * CNF formula clauses and deletes the unused ones.
 */
static void print_initial_clause_deletions(void) {
  FATAL_ERR_IF(ch_mode != BACKWARDS_CHECKING_MODE,
    "Inital clause deletions are only generated during backwards checking.");

  // Even if we print no clauses, it's okay to have an "empty" deletion line
  write_lsr_deletion_line_start(lsr_file, num_cnf_clauses);
  for (srid_t c = 0; c < num_cnf_clauses; c++) {
    if (IS_UNUSED_LUI(clauses_lui[c])) {
      write_clause_id(lsr_file, TO_DIMACS_CLAUSE(c)); 
    }
  }
  write_sr_line_end(lsr_file); 
}

// Prints the specified clause from the formula to the LSR proof file.
// The caller must ensure the clause is not deleted from the formula.
static void print_clause(srid_t clause_id) {
  int *clause = get_clause_start(clause_id);
  uint size = get_clause_size(clause_id);

  // Don't print anything if it's the empty clause
  if (size == 0) return;

  /*
   * Watch pointer management during unit propagation might have reordered
   * literals in the clause, so we grab the pivot literal from the witness
   * and then sort the remaining literals. 
   */

  // Find the pivot in the clause and swap it to the front
  int pivot = get_witness_start(LINE_NUM_FROM_CLAUSE_ID(clause_id))[0];
  for (int i = 0; i < size; i++) {
    int lit = clause[i];
    if (lit == pivot) {
      if (i != 0) {
        clause[i] = clause[0];
        clause[0] = pivot;
      }
      break;
    }
  }

  // Sort the remaining literals in the clause in increasing order of magnitude
  if (size > 1) {
    qsort(clause + 1, size - 1, sizeof(int), absintcmp);
  }

  // Now actually print the clause
  for (int i = 0; i < size; i++) {
    int lit = clause[i];
    write_lit(lsr_file, TO_DIMACS_LIT(lit));
  }
}

/** @brief Prints the current SR witness to the LSR proof file.
 * 
 *  TODO update docs. 
 */
static void print_witness(srid_t line_num) {
  int *witness_start = get_witness_start(line_num);
  int *witness_end = get_witness_end(line_num);
  int witness_size = (int) (witness_end - witness_start);

  // Don't print a witness if there isn't one (0) or if it's trivial (1)
  // TODO: This doesn't catch cases where the pivot might get mapped to TT/FF
  // in the substitution portion, so the "computed size" is different than size
  if (witness_size <= 1) return;

  /* 
   * Because witness minimization might map literals to true/false that are in
   * the "substitution portion", we do a two-pass over that part to first print
   * any true/false mapped literals, and then the non-trivial mappings.
   */

  int *mappings_start = NULL;
  int seen_pivot_divider = 0;
  int num_skipped_mapped_lits = 0;

  int *iter = witness_start;
  int pivot = *iter;
  write_lit(lsr_file, TO_DIMACS_LIT(pivot));
  iter++;

  // Pass for true-false mappings
  for (; iter < witness_end; iter++) {
    int lit = *iter;
    if (lit == WITNESS_TERM) {
      witness_end = iter;
      break;
    }

    if (!seen_pivot_divider) {
      // When we see the pivot again, the subst mappings start after it
      if (lit == pivot) {
        seen_pivot_divider = 1;
        mappings_start = iter + 1;
      } else {
        write_lit(lsr_file, TO_DIMACS_LIT(lit));
      }
    } else {
      iter++;
      int mapped_lit = *iter;
      switch (mapped_lit) {
        case SUBST_FF:
          lit = NEGATE_LIT(lit);
        case SUBST_TT: // fallthrough
          /* If we encounter the pivot at this point, it must be mapped to TT.
           * (See `find_new_pivot_for_witness()`.)
           * Since we have already printed the pivot, we must skip it here.
           */
          if (lit != pivot) {
            write_lit(lsr_file, TO_DIMACS_LIT(lit));
          }
          break;
        default: num_skipped_mapped_lits++;
      }
    }
  }

  // Don't print any substitution portion if there aren't any mapped lits
  if (num_skipped_mapped_lits == 0) return;

  // Write the pivot separator before the mapped literals section
  write_lit(lsr_file, TO_DIMACS_LIT(pivot));

  // Second pass, starting at the mappings
  for (iter = mappings_start; iter < witness_end; iter++) {
    int lit = *iter;
    iter++;
    int mapped_lit = *iter;
    switch (mapped_lit) {
      case SUBST_TT: break;
      case SUBST_FF: break;
      default:
        write_lit(lsr_file, TO_DIMACS_LIT(lit));
        write_lit(lsr_file, TO_DIMACS_LIT(mapped_lit));
    }
  }
}

/**
 * @brief Prints a clause ID hint to its re-mapped ID during backwards checking.
 * 
 * During backwards checking, we skip some addition lines, due to those clauses
 * not being needed in later proof lines. Thus, the naive mapping of proof
 * line to clause ID can be improved by re-mapping "active" clause IDs
 * downwards, starting from `num_cnf_clauses`. This mapping is stored in
 * `clause_id_map`. This function prints that re-mapping.
 * 
 * During forwards checking, `hint` is printed as-is.
 * 
 * @param hint The stored hint, under the naive mapping, in DIMACS form.
 */
static inline void print_mapped_hint(srid_t hint) {
  // During forwards checking, the map is NULL, so we write hint directly
  if (clause_id_map != NULL) {
    int is_neg_hint = 0;
    if (hint < 0) {
      is_neg_hint = 1;
      hint = -hint;
    }

    if (hint > num_cnf_clauses) {
      hint = FROM_DIMACS_CLAUSE(hint);
      hint = clause_id_map[hint];
      hint = TO_DIMACS_CLAUSE(hint);
    }

    if (is_neg_hint) {
      hint = -hint;
    }
  }

  write_clause_id(lsr_file, hint);
}

/**
 * @brief Prints the deletions that should take effect before parsing/checking
 *        the addition clause on the provided `line_num`.
 * 
 * During backwards checking, all deletions are derived and stored in
 * `deletions`. User-requested deletions are instead reflected in
 * the `clause_lui` values, and then added to `deletions` as they are
 * used in unit propagation.
 * 
 * @param line_num The 0-indexed line number of the addition clause.
 */
static void print_deletions(srid_t line_num) {
  srid_t *del_iter = get_deletions_start(line_num);
  srid_t *del_end = get_deletions_end(line_num);
  for (; del_iter < del_end; del_iter++) {
    srid_t c = *del_iter;
    print_mapped_hint(TO_DIMACS_CLAUSE(c));
  }
}

/**
 * @brief Prints a complete deletion line.
 * 
 * Used only for forwards checking.
 * 
 * @param printed_line_num The line ID to print with the line.
 */
static inline void print_deletions_with_line_id(srid_t printed_line_num) {
  if (lsr_file == NULL || get_num_deletions(printed_line_num) == 0) return;
  write_lsr_deletion_line_start(lsr_file, printed_line_num);
  print_deletions(printed_line_num);
  write_sr_line_end(lsr_file);
}

/**
 * @brief Prints first the UP hints, then the RAT hints for the given line.
 * 
 * @param line_num 
 */
static void print_hints(srid_t line_num) {
  srid_t *hints_iter = get_UP_hints_start(line_num);
  srid_t *hints_end = get_UP_hints_end(line_num);
  for (; hints_iter < hints_end; hints_iter++) {
    srid_t hint = *hints_iter; // Hints are already in DIMACS format
    print_mapped_hint(hint);
  }

  hints_iter = get_RAT_hints_start(line_num);
  hints_end = get_RAT_hints_end(line_num);
  for (; hints_iter < hints_end; hints_iter++) {
    srid_t rat_hint = *hints_iter; // Hints are already in DIMACS format
    print_mapped_hint(rat_hint);
  }
}

static void dbg_print_hints(srid_t line_num) {
  log_raw(VL_NORMAL, "[line %lld] Hints: ", TO_DIMACS_LINE(line_num));

  srid_t *hints_iter = get_UP_hints_start(line_num);
  srid_t *hints_end = get_UP_hints_end(line_num);
  for (; hints_iter < hints_end; hints_iter++) {
    srid_t hint = *hints_iter; // Hints are already in DIMACS format
    log_raw(VL_NORMAL, "%d ", hint);
  }

  hints_iter = get_RAT_hints_start(line_num);
  hints_end = get_RAT_hints_end(line_num);
  for (; hints_iter < hints_end; hints_iter++) {
    srid_t rat_hint = *hints_iter; // Hints are already in DIMACS format
    log_raw(VL_NORMAL, "%d ", rat_hint);
  }

  log_raw(VL_NORMAL, "\n");
}

/**
 * @brief Prints the stored LSR line for the given `line_num`.
 * 
 * During forwards checking, the hints structure is cleared after each line,
 * but during backwards checking, the hints are stored in "reverse order"
 * as the clauses are checked in reverse.
 * 
 * Does NOT print deletions. Print these manually through `print_deletions()`.
 * 
 * @param line_num The 0-indexed line number of the proof line.
 * @param printed_line_id The 1-indexed DIMACS ID of the proof line.
 */
static void print_lsr_line(srid_t line_num, srid_t printed_line_id) {
  if (lsr_file == NULL) return;
  write_lsr_addition_line_start(lsr_file, printed_line_id);
  print_clause(CLAUSE_ID_FROM_LINE_NUM(line_num));

  // Only print a witness if there are RAT/reduced clauses
  if (get_num_reduced_clauses(line_num) > 0) {
    print_witness(line_num);
  }

  write_lit(lsr_file, 0); // Separator between (clause + witness) and rest
  print_hints(line_num);
  write_sr_line_end(lsr_file);
}

static void print_valid_formula_if_requested(void) {
  if (valid_formula_file == NULL) return;

  if (derived_empty_clause) {
    logc("The emitted \"valid\" formula contains the empty clause.");
  }

  // Count how many non-deleted clauses there are, for the problem header
  srid_t num_present_clauses = 0;
  for (srid_t c = 0; c < formula_size; c++) {
    if (!is_clause_deleted(c)) num_present_clauses++;
  }

  // Save the value of writing to binary
  int write_binary_before = write_binary;
  write_binary = 0;

  // Write the `cnf p <num_vars> <num_clauses>` problem header
  fputc(DIMACS_PROBLEM_LINE, valid_formula_file);
  fprintf(valid_formula_file, CNF_HEADER_STR, max_var + 1, num_present_clauses);

  for (srid_t c = 0; c < formula_size; c++) {
    if (is_clause_deleted(c)) continue;
    
    int *iter = get_clause_start(c);
    int *end = get_clause_end(c);

    // Re-sort the original CNF clauses
    // Printing the LSR proof sorts all other clauses wrt pivots
    if (c < num_cnf_clauses) {
      qsort(iter, end - iter, sizeof(int), absintcmp);
    } else if (c == num_cnf_clauses) {
      fprintf(valid_formula_file,
          "c >>> Redundant clauses start below this point <<<\n");
    }

    for (; iter < end; iter++) {
      int lit = *iter;
      write_lit(valid_formula_file, TO_DIMACS_LIT(lit));
    }
    write_sr_line_end(valid_formula_file);
  }

  write_binary = write_binary_before; // Restore the old value
  fclose(valid_formula_file);
}

////////////////////////////////////////////////////////////////////////////////

// Hashing logic for clauses, used for deletions

/**
 * @brief Returns the hash of the literals in the clause.
 * 
 * The hash function is commutative, meaning that no matter how the literals
 * in the clause are ordered, the clause has the same hash value.
 * 
 * @param clause_index The clause to be hashed.
 * @return The `uint` hash of the clause's literals.
 */
static uint hash_clause(srid_t clause_index) {
  uint sum = 0, prod = 1, xor = 0;
  int *clause_iter = get_clause_start(clause_index);
  int *clause_end = get_clause_end(clause_index);

  for (; clause_iter < clause_end; clause_iter++) {
    uint lit = (uint) (*clause_iter);
    sum += lit;
    prod *= lit;
    xor ^= lit;
  }

  // Hash function borrowed from dpr-trim
  return 1023 * sum + prod ^ (31 * xor);
}

/**
 * @brief 
 * 
 * @param clause_index
 * @param[out] hp Pointer to the hash value of the clause.
 * @param[out] bp Pointer to the hash table bucket where the match lives.
 * @param[out] ep Pointer to the hash table entry where the match lives.
 * @return The clause index of a matching clause that comes before this one,
 *         or `-1` if no such clause is found.
 */
static srid_t find_hashed_clause(srid_t ci, uint *hp, ht_bucket_t **bp, ht_entry_t **ep) {
  int *clause = get_clause_start_unsafe(ci);
  uint clause_size = get_clause_size(ci);
  uint hash = hash_clause(ci);
  if (hp != NULL) *hp = hash;

  ht_bucket_t *bucket = ht_get_bucket(&clause_id_ht, hash);
  ht_entry_t *entry = NULL;
  srid_t possible_match;

  // Loop through all entries with the same hash to find a matching clause
  while ((entry = ht_get_entry_in_bucket(&clause_id_ht, bucket, hash, entry)) != NULL) {
    // Naively, we would use an `srid_t` pointer into `entry->data`,
    // but if `srid_t == llong`, then we run into alignment issues.
    // As a result, we must `memcpy` into a struct, which will be aligned.
    memcpy(&possible_match, &entry->data, sizeof(srid_t));

    // First approximation: see if the clause sizes match
    uint match_size = get_clause_size(possible_match);
    if (clause_size == match_size) {
      // Now check if all literals match.
      // Most clauses are small, so O(n^2) search is good enough.
      // Note that the literals aren't necessarily sorted due to wps.
      int *matching_clause = get_clause_start_unsafe(possible_match);
      int found_match = 1;  // We set this to 0 if a literal isn't found
      for (int i = 0; i < match_size; i++) {
        int lit = clause[i];
        int found_lit = 0;
        for (int j = 0; j < match_size; j++) {
          if (lit == matching_clause[j]) {
            found_lit = 1;
            break;
          }
        }

        if (!found_lit) {
          found_match = 0;
          break;
        }
      }

      if (found_match) {
        if (bp != NULL) *bp = bucket;
        if (ep != NULL) *ep = entry;
        return possible_match;
      }
    }
  }

  return -1;
}

/**
 * @brief Adds 1 to the clause's multiplicity counter.
 * 
 * If a clause appears more than once in the formula, then a `clause_mult_t`
 * struct is stored in the `clause_mults_ht` hash table, along with a count
 * of its multiplicity.
 * 
 * This function checks the multiplicity table, and if the clause is found,
 * its multiplicity counter is incremented. Otherwise, a new entry is added.
 */
static void inc_clause_mult(srid_t clause_index, uint hash) {
  ht_bucket_t *bucket = ht_get_bucket(&clause_mults_ht, hash);
  ht_entry_t *entry = NULL;
  clause_mult_t mult;

  while ((entry = ht_get_entry_in_bucket(&clause_mults_ht, bucket, hash, entry)) != NULL) {
    // Extract the multiplicity information from the entry
    memcpy(&mult, &entry->data, sizeof(clause_mult_t));
    if (mult.clause_id == clause_index) {
      mult.multiplicity++;
      memcpy(&entry->data, &mult, sizeof(clause_mult_t));
      return;
    }
  }

  // No matching clause was found. Add it to the multiplicity table
  mult.clause_id = clause_index;
  mult.multiplicity = 2;
  ht_insert(&clause_mults_ht, hash, &mult);
}

// Returns the number of remaining copies in the formula (after the decrease).
// Returns 0 if the clause is not found (meaning it has multiplicity of 1).
static int dec_clause_mult(srid_t clause_index, uint hash) {
  ht_bucket_t *bucket = ht_get_bucket(&clause_mults_ht, hash);
  ht_entry_t *entry = NULL;
  clause_mult_t mult;

  while ((entry = ht_get_entry_in_bucket(&clause_mults_ht, bucket, hash, entry)) != NULL) {
    memcpy(&mult, &entry->data, sizeof(clause_mult_t));
    if (mult.clause_id == clause_index) {
      mult.multiplicity--;

      // Remove the entry if we have a single copy of the clause left
      if (mult.multiplicity == 1) {
        ht_remove_entry_in_bucket(&clause_mults_ht, bucket, entry);
        return 1;
      } else {
        memcpy(&entry->data, &mult, sizeof(clause_mult_t));
        return mult.multiplicity;
      }
    }
  }

  return 0;
}

/**
 * @brief Deletes the most recently parsed clause by consulting the hash table.
 * 
 * DSR deletion lines are clauses. Because `dsr-check` permutes the literals
 * in clauses to implement watch pointers, we store clause hashes in a hash
 * table with a commutative hash function. That way, when we need to delete
 * a clause, we consult the hash table for a matching permuted clause.
 * 
 * During forwards checking, the clause is deleted from the formula and
 * the hash table. During backwards checking, the `clauses_lui`
 * is updated instead.
 * 
 * The caller must ensure that the newly parsed clause has at least two
 * literals (we don't delete the empty clause or unit clauses).
 * 
 * @return 1 if the clause was deleted, 0 if an extra copy was deleted
 *         or if the clause was not deleted due to being unit.
 */
static int delete_parsed_clause(void) {
  uint hash;
  ht_bucket_t *b;
  ht_entry_t *e;
  srid_t clause_match = find_hashed_clause(formula_size, &hash, &b, &e);

  if (clause_match == -1) {
    logc_raw("The clause requested to be deleted: ");
    dbg_print_clause(formula_size);
    log_fatal_err("[line %lld] No matching clause found for deletion.",
      TO_DIMACS_LINE(current_line));
  }

  // If we still have copies of the clause, leave the hash table alone
  if (dec_clause_mult(clause_match, hash) > 0) {
    return 0;
  }

  // Otherwise, we are deleting the last copy of this clause 

  // Forwards checking only: Do not delete (implied) units unless requested.
  int *clause_match_ptr = get_clause_start_unsafe(clause_match);
  uint clause_match_size = get_clause_size(clause_match);
  int is_a_derived_unit = is_lit_set_due_to_up(clause_match_ptr[0]) 
        && (get_unit_clause_for_lit(clause_match_ptr[0]) == clause_match);
  if (ch_mode == FORWARDS_CHECKING_MODE
      && is_a_derived_unit
      && ((ignore_unit_deletions && clause_match_size == 1)
       || (ignore_implied_unit_deletions && clause_match_size > 1))) {
    return 0;
  }

  ht_remove_entry_in_bucket(&clause_id_ht, b, e);
  store_user_deletion(clause_match);

  // How we delete the clause from the formula depends on the checking mode
  switch (ch_mode) {
    case FORWARDS_CHECKING_MODE:
      // If the clause is a(n implied) unit, unassign later units
      // We must do this before the clause is deleted from the formula
      if (is_a_derived_unit) {
        int unit_index = get_unit_index_for_lit(clause_match_ptr[0]);
        unassign_global_units_due_to_deletion(unit_index);
      }

      // Remove a non-true-unit's watch pointers
      if (clause_match_size > 1) {
        remove_wp_for_lit(clause_match_ptr[0], clause_match);
        remove_wp_for_lit(clause_match_ptr[1], clause_match);
      }

      // Now actually delete the clause from the formula
      lit_occ_delete_clause(&lit_occ, clause_match);
      delete_clause(clause_match);

      // If the clause was a(n implied) unit, we must re-run unit propagation
      if (is_a_derived_unit) {
        perform_up_for_forwards_checking(GLOBAL_GEN);
      }
      break;
    case BACKWARDS_CHECKING_MODE:
      resize_last_used_ids();
      clauses_lui[clause_match] = MARK_USER_DEL_LUI(num_parsed_add_lines);
      break;
    default: log_fatal_err("Invalid checking mode: %d", ch_mode);
  }

  return 1;
}

static inline void add_hashed_clause_to_ht(srid_t clause_index, uint hash) {
  ht_insert(&clause_id_ht, hash, &clause_index);
}

/**
 * @brief Adds a formula clause to the clause hash table.
 *        Must be called after the CNF has been parsed
 *        and after `deletions` has been initialized.
 *
 * If a formula's clause already exists in the hash table, then this function
 * deletes the clause and adds to the multiplicity of the matching clause.
 * This is to ensure that the formula's size remains the same and that the
 * formula behaves the same under the same number of deletions, but also
 * making sure there is one unique hash table entry per distinct clause.
 * 
 * @param clause_index The formula clause to be added to the hash table.
 */
static void add_formula_clause_to_ht(srid_t clause_index) {
  uint hash;
  srid_t clause_match = find_hashed_clause(clause_index, &hash, NULL, NULL);
  if (clause_match == -1) {
    add_hashed_clause_to_ht(clause_index, hash);
  } else {
    logv("[line %lld] Formula clause %lld is a duplicate of clause %lld.",
      TO_DIMACS_LINE(current_line),
      TO_DIMACS_CLAUSE(clause_index),
      TO_DIMACS_CLAUSE(clause_match));
    delete_clause(clause_index);
    inc_clause_mult(clause_match, hash);
    if (ch_mode == FORWARDS_CHECKING_MODE) {
      // Delete the duplicate in the printed LSR proof.
      // However, the user is free to delete the clause later (which we ignore),
      // since we simply subtract 1 from the multiplicity.
      store_user_deletion(clause_index);
    } else {
      // Mark the clause as unused at the first line
      clauses_lui[clause_index] = MARK_USER_DEL_LUI(0);
    }
  }
}

/**
 * @brief 
 * 
 * @return -1 if the clause is new (not in the hash table), or the clause ID
 *         of the matching clause if it is.
 */
static srid_t add_clause_to_ht_or_inc_mult(void) {
  uint hash;
  srid_t ci = formula_size - 1; // The new clause is at the end of the formula
  srid_t clause_match = find_hashed_clause(ci, &hash, NULL, NULL);

  // If the clause isn't found in the hash table, add it
  if (clause_match == -1) {
    add_hashed_clause_to_ht(ci, hash);
  } else {
    inc_clause_mult(clause_match, hash);
  }

  return clause_match;
}

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Prints or commits user deletions.
 * 
 * When a new addition line is parsed, any previous user deletions must
 * be flushed in the appropriate way, depending on the checking mode.
 * 
 * TODO: Need to store deletions if parsing whole proof.
 */
static void print_or_commit_user_deletions(void) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    ra_commit_range(&bcu_deletions);
  } else {
    // TODO: Case on parsing strategy here
    FATAL_ERR_IF(p_strategy != PS_STREAMING,
      "User deletions must be committed in streaming mode.");
    print_deletions_with_line_id(CLAUSE_ID_FROM_LINE_NUM(num_parsed_add_lines));
    ra_reset(&deletions);
  }
} 

// Parses the next DSR line. If it's a deletion line, the clause is deleted.
// Otherwise, the new candidate clause and the witness are parsed and stored.
// Returns ADDITION_LINE or DELETION_LINE for the line type.
// Errors and exits if a read error is encountered.
static int parse_dsr_line(void) {
  int line_type = read_dsr_line_start(dsr_file);
  switch (line_type) {
    case DELETION_LINE:;
      int is_tautology = parse_clause(dsr_file);

      // Only delete the clause if it isn't a tautology,
      // since we already deleted tautologies from the CNF.
      if (!is_tautology) {
        int actually_deleted_the_clause = delete_parsed_clause();
        if (actually_deleted_the_clause) {
          num_parsed_del_lines++;
        }
      }
      
      // Remove the parsed literals from the formula.
      // Note that `parse_clause()` doesn't commit the clause,
      // so `formula_size` remains unchanged.
      lits_db_size -= new_clause_size;
      break;
    case ADDITION_LINE:
      /*
       * Naively, we would flush the user deletions before parsing the
       * next addition clause. However, the addition clause might be a
       * copy of a clause already in the formula, in which case we won't
       * emit a proof line for the extra copy in the generated proof.
       * Thus, we only print/commit user deletions if we don't find a
       * clause match in the hash table.
       */
      parse_sr_clause_and_witness(dsr_file, num_parsed_add_lines);

      // Check if the new SR clause is already in the formula
      srid_t possible_match = add_clause_to_ht_or_inc_mult();
      if (possible_match != -1) {
        // Remove the witness, and remove the parsed clause from the formula.
        // `parse_sr_clause()` commits the clause, so we adjust `formula_size`.
        lits_db_size -= new_clause_size;
        formula_size -= 1;
        ra_uncommit_range(&witnesses);

        // We don't want to proof check anything, so don't return `ADD_LINE`
        line_type = DELETION_LINE;
      } else {
        print_or_commit_user_deletions();
        num_parsed_add_lines++;
      }
      break;
    default:
      log_fatal_err("Corrupted line type: %d", line_type);
  }

  num_parsed_lines++;
  return line_type;
}

/**
 * @brief Parses the entire DSR proof file. The parsing strategy must be EAGER.
 */
static void parse_entire_dsr_file(void) {
  FATAL_ERR_IF(p_strategy != PS_EAGER,
    "To parse the entire DSR file eagerly, the p_strategy must be EAGER.");

  parsed_empty_clause = 0;
  while (!parsed_empty_clause && has_another_line(dsr_file)) {
    parse_dsr_line();
    parsed_empty_clause = (new_clause_size == 0);
  }

  if (dsr_file != stdin) {
    fclose(dsr_file);
  }

  // Since we've parsed all possible clauses, we can free the hash tables
  // that were tracking clause multiplicities/duplicates.
  ht_free(&clause_id_ht);
  ht_free(&clause_mults_ht);

  if (parsed_empty_clause) {
    logc("Parsed the empty clause after %lld proof lines (%lld additions).",
      num_parsed_lines, num_parsed_add_lines);
  } else {
    logc("Parsed %lld proof lines (%lld additions), but not the empty clause.",
      num_parsed_lines, num_parsed_add_lines);
  }
}

////////////////////////////////////////////////////////////////////////////////

static void prepare_dsr_trim_data(void) {
  // Allocate an empty watch pointer array for each literal
  // Allocate some additional space, since we'll probably add new literals later
  wps_alloc_size = MAX_LIT_EXCLUSIVE * 2;
  wps = xcalloc(wps_alloc_size, sizeof(srid_t *));
  wp_alloc_sizes = xcalloc(wps_alloc_size, sizeof(uint)); 
  wp_sizes = xcalloc(wps_alloc_size, sizeof(uint));

  // Only allocate initial watch pointer space for literals in the formula 
  for (int i = 0; i <= MAX_LIT; i++) {
    wp_alloc_sizes[i] = INIT_LIT_WP_ARRAY_SIZE;
    wps[i] = xmalloc(INIT_LIT_WP_ARRAY_SIZE * sizeof(srid_t));
  }

  // Allocate empty reasons array for each variable, plus extra space
  vars_unit_indexes_alloc_size = max_var + 1;
  vars_unit_indexes = xmalloc_memset(vars_unit_indexes_alloc_size * sizeof(int), 0xff);

  // Allocate space for the unit lists. Probably won't be too large
  units_alloc_size = max_var + 1;
  unit_literals = xmalloc(units_alloc_size * sizeof(int));
  unit_clauses = xmalloc(units_alloc_size * sizeof(srid_t));

  // Allocate space for the dependency markings
  vars_dependency_markings_alloc_size = max_var + 1;
  vars_dependency_markings = xcalloc(vars_dependency_markings_alloc_size, sizeof(ullong));

  RAT_marked_vars_alloc_size = max_var + 1;
  RAT_marked_vars = xmalloc(RAT_marked_vars_alloc_size * sizeof(int));

  bmask_init(&bmask, RESIZE(num_cnf_clauses));

  // If we are backwards checking, allocate additional structures
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    // TODO: set to formula_size when resizing?
    clauses_lui_alloc_size = formula_size * 2;
    clauses_lui = xmalloc_memset(clauses_lui_alloc_size * sizeof(srid_t), 0xff);

    lines_RAT_hint_info_alloc_size = formula_size * 2;
    lines_RAT_hint_info = xcalloc(lines_RAT_hint_info_alloc_size, sizeof(line_RAT_info_t));

    unit_literals_wp_up_indexes = xcalloc(units_alloc_size, sizeof(uint));
  }

  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    ra_init(&hints,     num_cnf_clauses * 4, num_cnf_vars, sizeof(srid_t));
    ra_init(&deletions,    num_cnf_vars * 2, num_cnf_vars, sizeof(srid_t));
    ra_init(&bcu_deletions, num_cnf_clauses, num_cnf_vars, sizeof(srid_t));
  } else {
    ra_init(&hints,     num_cnf_vars * 4, 3, sizeof(srid_t));
    ra_init(&deletions, num_cnf_vars * 2, 2, sizeof(srid_t));
  }

  // Add all formula clauses to the clause hash table
  // Because this might add deletions to the formula, we must do this
  // after we have called `ra_init()` on the `deletions` data structure.
  ht_init_with_size(&clause_id_ht, sizeof(srid_t), formula_size / 2);
  ht_init(&clause_mults_ht, sizeof(clause_mult_t));
  for (srid_t i = 0; i < formula_size; i++) {
    add_formula_clause_to_ht(i);
  }

  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    parse_entire_dsr_file();
  }
}

static void resize_wps(void) {
  if (MAX_LIT >= wps_alloc_size) {
    uint old_size = wps_alloc_size;
    wps_alloc_size = RESIZE(MAX_LIT_EXCLUSIVE);
    wps = xrecalloc(wps,
      old_size * sizeof(srid_t *), wps_alloc_size * sizeof(srid_t *));
    wp_alloc_sizes = xrecalloc(wp_alloc_sizes,
      old_size * sizeof(uint), wps_alloc_size * sizeof(uint));
    wp_sizes = xrecalloc(wp_sizes,
      old_size * sizeof(uint), wps_alloc_size * sizeof(uint));
  }
}

static void resize_sr_trim_data(void) {
  // Resize arrays that depend on max_var and formula_size
  resize_wps();
  RESIZE_MEMSET_ARR(vars_unit_indexes,
    vars_unit_indexes_alloc_size, (max_var + 1), sizeof(int), 0xff);
  RECALLOC_ARR(vars_dependency_markings,
    vars_dependency_markings_alloc_size, (max_var + 1), sizeof(ullong));
}

static void resize_units(void) {
  if (units_size >= units_alloc_size) {
    int old_size = units_alloc_size;
    units_alloc_size = RESIZE(units_size);
    unit_literals = xrealloc(unit_literals, units_alloc_size * sizeof(int));
    unit_clauses = xrealloc(unit_clauses, units_alloc_size * sizeof(srid_t));

    if (ch_mode == BACKWARDS_CHECKING_MODE) {
      unit_literals_wp_up_indexes = xrecalloc(unit_literals_wp_up_indexes,
        old_size * sizeof(uint), units_alloc_size * sizeof(uint));
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Minimizes the number of RAT clauses/hint groups after checking
 *        a proof line. Only called during backwards checking.
 * 
 */
static void minimize_RAT_hints(void) {
  // These variables are declared `static` to persist across function calls
  // Only this function needs them, so we declare them here instead of globally
  static uint *skipped_RAT_indexes = NULL;
  static uint skipped_RAT_indexes_alloc_size = 0;
  static uint skipped_RAT_indexes_size = 0;

  // Iterate over the RAT hint groups and mark last used IDs
  srid_t nrhg = get_num_RAT_clauses(current_line);
  if (nrhg == 0) return;

  // Reset the skipped-indexes array, and malloc() if not yet allocated
  skipped_RAT_indexes_size = 0;
  if (skipped_RAT_indexes == NULL) {
    skipped_RAT_indexes_alloc_size = max_var;
    skipped_RAT_indexes = xmalloc(max_var * sizeof(uint));
  }

  // First pass: mark "active" clauses
  srid_t num_marked = 0;
  srid_t *hints_start = get_RAT_hints_start(current_line);
  srid_t *hints_end = get_RAT_hints_end(current_line);
  srid_t *hints_iter = hints_start;
  for (srid_t i = 0; i < nrhg; i++) {
    srid_t RAT_clause = FROM_RAT_HINT(*hints_iter);
    hints_iter++;
    srid_t RAT_lui = clauses_lui[RAT_clause];
    if (RAT_lui >= current_line) {
      // Scan through its hints and mark them as active
      srid_t hint;
      while (hints_iter < hints_end && (hint = *hints_iter) > 0) {
        hint = FROM_DIMACS_CLAUSE(hint);
        num_marked += adjust_clause_lui(hint);
        hints_iter++;
      }
    } else if (IS_UNUSED_LUI(RAT_lui)) {
      // Add unused or "current" hints to the skipped indexes list
      // Subtract 1 due to the ++ above
      INSERT_ARR_ELT_CONCAT(skipped_RAT_indexes, sizeof(uint),
        (uint) ((hints_iter - hints_start) - 1));
      SKIP_REMAINING_UP_HINTS(hints_iter, hints_end);
    } else {
      log_fatal_err("[line %lld] RAT clause %lld was deleted before UP hint.",
        TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(RAT_clause));
    }
  }

  // If we mark no new hints under RAT clauses, then we can minimize right away
  if (num_marked == 0) goto minimize_hint_groups;

  // Second pass: mark "skipped" hints
  // Keep iterating over the skipped indexes until we mark no more
  uint old_len;
  while ((old_len = skipped_RAT_indexes_size) > 0) {
    skipped_RAT_indexes_size = 0;
    num_marked = 0;

    for (uint i = 0; i < old_len; i++) {
      uint offset = skipped_RAT_indexes[i];
      srid_t *iter = hints_start + offset;
      srid_t RAT_clause = FROM_RAT_HINT(*iter);
      srid_t RAT_lui = clauses_lui[RAT_clause];

      if (IS_UNUSED_LUI(RAT_lui)) {
        // If the clause still hasn't become "active", skip it again
        // The number of skipped hints wont' increase, so we can safely add
        skipped_RAT_indexes[skipped_RAT_indexes_size] = offset;
        skipped_RAT_indexes_size++;
      } else {
        // We must have that (RAT_lui == current_line)
        // This RAT clause is now active, so mark its hints
        // Here, we might mark clauses which are not skipped (i.e. aren't RAT)
        // but which still we need to mark for deletion purposes
        iter++;
        srid_t hint;
        while (iter < hints_end && (hint = *iter) > 0) {
          hint = FROM_DIMACS_CLAUSE(hint); // Convert out of DIMACS
          iter++;
          num_marked += adjust_clause_lui(hint);
        }
      }
    }

    // If we skipped every clause we started with, we've reached fixpoint
    if (old_len == skipped_RAT_indexes_size && num_marked == 0) {
      break;
    }
  }

  // Label for third pass
  minimize_hint_groups:

  if (skipped_RAT_indexes_size == 0) return;

  // Third pass: only write down the active hints
  // The indexes left in `skipped_RAT_indexes` are the ones we need to skip
  // We intelligently move ranges of hints over with `memmove()`.
  hints_iter = hints_start;
  srid_t *write_iter = hints_start;

  uint len;
  for (uint i = 0; i < skipped_RAT_indexes_size; i++) {
    srid_t *skip_start = hints_start + skipped_RAT_indexes[i];

    // Copy hints over, only if needed
    if (skip_start != hints_iter) {
      len = (uint) (skip_start - hints_iter);
      if (write_iter != hints_iter) {
        memmove(write_iter, hints_iter, len * sizeof(srid_t));
      }
      
      write_iter += len;
    }

    hints_iter = skip_start + 1;
    SKIP_REMAINING_UP_HINTS(hints_iter, hints_end);
  }

  // Write the remaining hints
  len = (uint) (hints_end - hints_iter);
  if (write_iter != hints_iter) {
    memmove(write_iter, hints_iter, len * sizeof(srid_t));
  }
  write_iter += len;

  ullong hints_dropped = (ullong) (hints_end - write_iter);
  ra_uncommit_data_by(&hints, hints_dropped);
  lines_RAT_hint_info[current_line].num_RAT_clauses -= skipped_RAT_indexes_size;
}

/**
 * @brief Stores the unit clauses, in order, that were needed to derive
 *        (RAT) UP refutation. These clauses are stored as UP hints.
 * 
 * When checking a DSR line, potentially many rounds of RAT unit propagation
 * are done. These might use a strict subset of all unit literals derived
 * when assuming the negation of the candidate clause. When a unit literal
 * is used in a RAT UP derivation, it is marked with the timestamp of that
 * round of UP. When all RAT UP derivations are finished, only those
 * "global" unit literals used in at least one RAT UP derivation are included
 * in the "global" UP hints for this line.
 * 
 * This function stores those markings. See `mark_dependencies()`.
 * 
 * @param gen The generation value at the start of this line's proof checking.
 *            Only clauses with a dependency marking strictly greater than
 *            `gen` are added as UP hints.
 */
 static void store_active_dependencies(ullong gen) {
  for (int i = 0; i < units_size; i++) {
    int unit_lit = unit_literals[i];
    if (vars_dependency_markings[VAR_FROM_LIT(unit_lit)] > gen) {
      add_up_hint(unit_clauses[i]);
    }
  }
}

/**
 * @brief Marks the unit-propagation-dependency timestamps for each unit clause
 *        that causes the literals in `clause` to be false.
 * 
 * When storing or printing an LSR line, we want to minimize the number of
 * UP hints in the line. We calculate this minimal set of unit clauses
 * needed to derive the falsified clause by looping over the unit clauses
 * in reverse order of when they were derived, i.e., newer unit clauses
 * are processed first, and updating their "dependency markings".
 * This function updates the markings for a single clause.
 * 
 * The general strategy is as follows:
 * For every literal `l` in `clause`, we see which unit
 * clause `c` is causing `l` to be FF. If `l` was an assumed literal,
 * then we don't mark `c` (if there is such a `c` to mark). But if not,
 * then we store `gen` in `dependency_markings` for `c`.
 * 
 * This function loops over the literals in `clause` (after the `offset`,
 * which is either `0` or `1` for falsified or unit clauses, respectively)
 * and updates the `dependency_markings` for the appropriate unit clauses.
 * 
 * @param clause The clause whose literals will be used to update unit clause
 *               dependency markings.
 * @param offset The index to start the loop at. `0` for falsified clause,
 *               `1` for unit clauses. See `mark_unit_clause()`
 *               and `mark_entire_clause()`.
 * @param gen The generation value to mark the dependencies with.
 */
static void mark_clause(srid_t clause, int offset, ullong gen) {
  int *clause_iter = get_clause_start_unsafe(clause) + offset;
  int *clause_end = get_clause_end(clause);
  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    int var = VAR_FROM_LIT(lit);
    if (is_var_set_due_to_up(var)) {
      vars_dependency_markings[var] = gen;
    }
  }
}

/**
 * @brief Marks the dependency timestamps for the unit clauses causing
 *        `clause` to be unit. Used to minimize the number of UP hints.
 * 
 * @param clause The 0-indexed ID of the clause to mark.
 */
static inline void mark_unit_clause(srid_t clause, ullong gen) {
  mark_clause(clause, 1, gen);
}

/**
 * @brief Marks the dependency timestamps for the unit clauses causing
 *        `clause` to be falsified. Used to minimize the number of UP hints.
 * 
 * @param clause The 0-indexed ID of the clause to mark.
 */
static inline void mark_entire_clause(srid_t clause, ullong gen) {
  mark_clause(clause, 0, gen);
}

/**
 * @brief Marks dependencies among the derived unit clauses to minimize the
 *        number of UP hints.
 * 
 * During unit propagation, every unit literal records which clause caused it
 * to become unit. These clauses are stored in `up_reasons`.
 * 
 * Then, when UP encounters a refutation (i.e. a falsified clause), it marks
 * which unit literals/clauses are necessary to cause the refutation
 * (as UP might derive many more units than necessary). This minimized
 * set is computed by this function.
 * 
 * After the caller marks the falsified clause with `mark_entire_clause()`
 * (see `mark_up_derivation()`), this function scans backwards through
 * the unit clauses and sets each unit clause's `dependency_markings`
 * to the provided `gen`.
 * 
 * Later, when printing or storing the UP hints, only unit clauses with
 * a `dependency_markings` value strictly greater than the `alpha_generation`
 * before checking the current line are stored as UP hints.
 * 
 * The `until_index` is the (inclusive) index of the first unit clause 
 * in `unit_clauses` with which to stop marking dependencies.
 */
static void mark_dependencies(int until_index, ullong gen) {
  // We use an int here because we scan backwards until the counter is negative
  for (int i = ((int) units_size) - 1; i >= until_index; i--) {
    int lit = unit_literals[i];
    int var = VAR_FROM_LIT(lit);
    if (vars_dependency_markings[var] >= gen) {
      mark_unit_clause(unit_clauses[i], gen);
    }
  }
}

/**
 * @brief Marks clause dependencies of global units and updates their
 *        last-used indexes. Should only be called during backwards checking.
 * 
 * Called before `minimize_RAT_hints()` to address the rare case of
 * a unit clause appearing in the global UP hints that is also a reduced
 * clause under the witness. This case only occurs for true SR witnesses,
 * since * RAT/PR witnesses are simplified with `minimize_witness()` to avoid
 * this case.
 * 
 * @param gen The (inclusive) lowest timestamp for `dependency_markings`
 *            with which to mark the clause.
 */
static void mark_dependencies_and_update_lui(ullong gen) {
  for (int i = ((int) units_size) - 1; i >= 0; i--) {
    int lit = unit_literals[i];
    int var = VAR_FROM_LIT(lit);
    if (vars_dependency_markings[var] >= gen) {
      srid_t clause = unit_clauses[i];
      mark_unit_clause(clause, gen);
      adjust_clause_lui(clause);
    }
  }
}

/**
 * @brief Marks the unit clauses needed to falsify `from_clause`.
 *        The dependency markings are updated with the timestamp `gen`.
 * 
 * @param from_clause The falsified clause to mark.
 * @param gen The timestamp to mark unit clauses with. `gen` should be strictly
 *            greater than the value of `alpha_generation` before checking
 *            the current line. (i.e., `gen > old_alpha_generation`)
 */
static inline void mark_up_derivation(srid_t from_clause, ullong gen) {
  mark_entire_clause(from_clause, gen);

  // If RAT UP, then only scan until RAT unit clauses are done
  // Later, mark the UP clauses needed more "globally"
  int index = (up_state == RAT_UP) ? RAT_unit_literals_index : 0;
  mark_dependencies(index, gen);
}

/**
 * @brief Marks UP dependencies and stores UP hints, starting from the
 *        falsified clause `from_clause`.
 * 
 * @param from_clause 
 * @param gen 
 */
static void mark_and_store_up_refutation(srid_t from_clause, ullong gen) {
  mark_up_derivation(from_clause, gen + GEN_INC);
  ra_commit_range(&hints);
  store_active_dependencies(gen);
  add_up_hint(from_clause);

  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    ra_commit_range(&hints);
  } else {
    print_lsr_line(current_line, LINE_ID_FROM_LINE_NUM(current_line));
    ra_reset(&hints);
  }
}

// A wrapper for `mark_and_store_up_refutation()` for the empty clause.
static inline void mark_and_store_empty_clause_refutation(srid_t c, ullong g) {
  derived_empty_clause = 1;
  mark_and_store_up_refutation(c, g);
}

static void store_RAT_dependencies(srid_t from_clause) {
  for (int i = RAT_unit_literals_index; i < units_size; i++) {
    int lit = unit_literals[i];
    int var = VAR_FROM_LIT(lit);
    if (vars_dependency_markings[var] == alpha_generation) {
      add_RAT_up_hint(unit_clauses[i]);
    }
  }

  add_RAT_up_hint(from_clause);
}

/**
 * @brief Prints or stores the LSR line.
 * 
 * Commits the `hints` structure twice during backwards checking.
 * 
 * @param gen The generation strictly less than the `alpha_generation`
 *            values used to mark clauses in `dependency_markings`.
 */
static void print_or_store_lsr_line(ullong gen) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    mark_dependencies_and_update_lui(gen + GEN_INC);
    minimize_RAT_hints();
  } else {
    mark_dependencies(0, gen + GEN_INC);
  }

  ra_commit_range(&hints);
  store_active_dependencies(gen);
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    ra_commit_range(&hints);
  } else {
    print_lsr_line(current_line, LINE_ID_FROM_LINE_NUM(current_line));
    ra_reset(&hints);
  }
}

/**
 * @brief Prints the stored proof to the `lsr_file` after backwards checking.
 * 
 * Does nothing if the checking mode is FORWARDS, since proof lines
 * are emitted after each check.
 */
static void print_stored_lsr_proof(void) {
  if (ch_mode != BACKWARDS_CHECKING_MODE || lsr_file == NULL) return; 

  timer_record(&timer, TIMER_LOCAL);

  generate_clause_id_map();
  print_initial_clause_deletions();

  srid_t printed_line_id = num_cnf_clauses + 1;
  int is_active_deletion_line = 0;

  // For each "active" non-empty addition clause, print its LSR line
  for (srid_t line = 0; line < num_parsed_add_lines - 1; line++) {
    srid_t clause_id = CLAUSE_ID_FROM_LINE_NUM(line);
    if (IS_USED_LUI(clauses_lui[clause_id])) {
      // Terminate any active deletion lines
      if (is_active_deletion_line) {
        write_sr_line_end(lsr_file);
        is_active_deletion_line = 0;
      }

      print_lsr_line(line, printed_line_id);
      printed_line_id++;
    }

    // Only print deletions if there's a later RAT line
    // Deletions don't speed up RUP-only lines
    if (line < max_RAT_line && get_num_deletions(line) > 0) {
      if (!is_active_deletion_line) {
        is_active_deletion_line = 1;
        write_lsr_deletion_line_start(lsr_file, printed_line_id - 1);
      }

      print_deletions(line);
    }
  }

  // Before printing the empty clause, terminate any active deletion line
  if (is_active_deletion_line) {
    write_sr_line_end(lsr_file);
  }

  // Specially print the empty clause, since we don't mark it as "needed"
  print_lsr_line(num_parsed_add_lines - 1, printed_line_id);

  timer_print_elapsed(&timer, TIMER_LOCAL, "Printing the LSR proof");
}

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Minimizes the witness and checks its consistency. Must be called
 *  after assuming the negation of the candidate clause and doing UP.
 * 
 * Any witness literal l set to true that is also set to true in alpha after
 * assuming the negation of the candidate clause and doing UP can be omitted.
 * This is because any clause satisfied by l will then generate contradiction
 * with alpha (alpha satisfies it), and any clause containing -l will, when
 * its negation is assumed for RAT checking, have no effect on alpha,
 * now that it contains -l after omitting l from the witness.
 * 
 * In addition, any literal l -> m in the substitution portion, with m set to
 * either true or false in alpha, can instead be mapped to m's truth value.
 * The reason this is allowed is similar to the above: any clause containing l
 * will contain m after the substitution, and m's truth value in alpha causes
 * the same overall effect as mapping l to m's truth value directly when
 * evaluating the clause under the substitution and doing RAT checking.
 * 
 * Minimization is done by a single loop over the witness. Unnecessary literals
 * l -> T/F are removed, and any l -> m in the substitution portion with
 * m -> T/F in alpha are set to l -> T/F. If l -> m is set to l -> T/F, we 
 * then check whether l can be removed using the same logic as before.
 * Removals are handled with an increasing "write pointer" that allows the
 * rest of the substitution to be shifted to fill in the holes.
 * 
 * Before returning, the global variable `witness_size` is set appropriately.
 * 
 * Note that l -> m set to l -> T/F stays in the substitution portion.
 * Printing must handle this case with a two-pass over the substitution portion.
 * 
 * A note on design:
 * We choose to do minimization this way because otherwise, careful bookkeeping
 * would have to be performed to shuffle the direct-mapped and subst mapped
 * portions around. Alternatively, we could use two separate arrays, but that
 * is bad for locality, and the witness is not usually minimized (that much).
 * 
 * @return 1 if a new pivot must be found, 0 otherwise.
 */
static int minimize_witness(void) {
  int *witness_iter = get_witness_start(current_line);
  int *witness_end = get_witness_end(current_line);
 
  if (witness_iter + 1 >= witness_end) return 0;

  int pivot = witness_iter[0];
  witness_iter++; // Skip the pivot
  int *write_iter = witness_iter;

  int found_pivot_divider = 0;
  int must_find_new_pivot = 0;
  int iter_inc = 1;

  while (witness_iter < witness_end) {
    int lit = *witness_iter;
    if (lit == WITNESS_TERM) break;

    // If the literal is good to keep, then we write it to `write_iter`    
    int keep_lit = 1;

    if (!found_pivot_divider && lit == pivot) {
      // This lit is the separator - skip to just writing it down
      goto write_lit_at_write_iter;
    }

    // Store what the literal is mapped to under alpha and the subst witness
    peval_t lit_alpha = peval_lit_under_alpha(lit);
    peval_t lit_subst = (!found_pivot_divider) ? TT : UNASSIGNED;

    // If we are in the substitution portion, check the truth value of `m`
    if (found_pivot_divider) {
      int mapped_lit = witness_iter[1];
      switch ((lit_subst = peval_lit_under_alpha(mapped_lit))) {
        case FF: witness_iter[1] = SUBST_FF; break;
        case TT: witness_iter[1] = SUBST_TT; break;
        default: break;
      }

      /* 
       * In most cases, (l -> m) undergoes normal minimization.
       * However, we can (extremely rarely) end up in the position where
       * the pivot `p` is minimized to FF. Because we do not want to repeat
       * `p` in the TT/FF mappings to encode that it should be mapped to FF,
       * there is no way for the pivot to be both the pivot and to be mapped
       * to FF. So we need to find a new pivot.
       * 
       * We know that there must be a replacement pivot because the witness
       * cannot set the entire clause to false - otherwise the SR check would
       * fail. So there is at least one literal that is mapped to something
       * other than FF (whether that's TT or a map, that's okay). We use
       * that literal as the pivot.
       * 
       * It is more efficient to look for this literal after calling
       * `assume_subst()` in `check_dsr_line()`, so we only return that we
       * `must_find_new_pivot`, and then we call `find_new_pivot()`.
       * 
       * Note that we disallow the negation of the pivot to appear in the
       * PR section of the witness (see `sr_parser.c`). So after adjusting
       * for the correct sign, we see if the new mapping for the pivot
       * is FF. If so, we set `must_find_new_pivot` to 1.
       */
      if (VAR_FROM_LIT(lit) == VAR_FROM_LIT(pivot) && lit_subst != UNASSIGNED) {
        if ((lit_subst ^ IS_NEG_LIT(pivot)) == FF) {
          logv("[line %lld] We must find a new pivot: %d",
            TO_DIMACS_LINE(current_line), TO_DIMACS_LIT(pivot));
          must_find_new_pivot = 1;
          // We *do* keep this "redundant" literal (TODO document why later)
        }
      }
    }

    // Now compare the truth value of l in the substitution and alpha
    // TODO: Brittle negation, based on hard-coded values of peval_t.
    if (lit_alpha != UNASSIGNED) {
      if (lit_alpha == lit_subst) {
        logv("[line %lld] Redundant witness literal %d (idx %d)",
          TO_DIMACS_LINE(current_line), TO_DIMACS_LIT(lit),
          (int) (witness_iter - get_witness_start(current_line)));
        keep_lit = 0;
      }
    }

    // Overwrite bad literals as we find good literals
    write_lit_at_write_iter:;

    if (keep_lit) {
      if (write_iter != witness_iter) {
        *write_iter = lit;

        // Write down the mapped literal if we've seen the pivot separator
        if (found_pivot_divider) {
          write_iter[1] = witness_iter[1];
        }
      }
    
      write_iter += iter_inc;
    }
      
    witness_iter += iter_inc;

    // Update if we just wrote the separator
    // We need to do this after incrementing the pointers
    if (!found_pivot_divider && lit == pivot) {
      found_pivot_divider = 1;
      iter_inc = 2;
    }
  }

  // Write a new witness terminating element if we shrank the witness
  if (write_iter != witness_iter) {
    *write_iter = WITNESS_TERM;
  }

  return must_find_new_pivot;
}

/**
 * @brief Only called when the pivot maps to false under `minimize_witness()`.
 * 
 * Move the pivot to the TT/FF-mapped portion of the witness, then
 * evaluate the candidate clause against the already-assumed substitution
 * for any literal that is not mapped to FF.
 * 
 * Must be called after calling `assume_subst()`.
 * 
 * @param cc_index The clause ID for the candidate clause.
 */
static void find_new_pivot_for_witness(srid_t cc_index) {
  int *clause_iter = get_clause_start_unsafe(cc_index);
  int *clause_end = get_clause_end(cc_index);

  // Find a non-FF literal under the witness
  // Ideally, we find a TT literal, but a mapped literal will do
  int new_pivot = -1;
  int pivot_is_tt = 0;
  for (; clause_iter < clause_end && !pivot_is_tt; clause_iter++) {
    int lit = *clause_iter;
    int mapped_lit = map_lit_under_subst(lit);
    switch (mapped_lit) {
      case SUBST_FF: break;
      case SUBST_TT:
        pivot_is_tt = 1;
      default: // waterfalls from above
        new_pivot = lit;
        break;
    }
  }

  FATAL_ERR_IF(new_pivot == -1, "Cound not find a new pivot!");

  /* 
   * The pivot *must* have a (l -> TT/FF) mapping in the SR portion of the
   * witness, because otherwise it gets mapped to TT in the PR portion,
   * and we would not have ended up in this situation. Since we are replacing
   * the pivot with a new pivot, it's okay to leave this mapping in the
   * witness, as printing the line will take care of it for us.
   * 
   * We need to replace the first pivot and the separator with `new_pivot`
   * 
   * If `new_pivot` is in the PR portion, then there is no (new_pivot -> TT/FF)
   * mapping in the SR portion, due to `assume_subst()`. We swap new_pivot
   * and pivot in the PR portion, and return.
   * 
   * If `new_pivot` is in the SR portion, then either:
   *   - it is mapped to TT (modulo the sign of `new_pivot`), and so its entry
   *     needs to be erased/filled in with a later mapping-pair in the SR
   *     portion (or the WITNESS_TERM needs to be moved back 2 slots, if
   *     the mapping is at the end)
   *   
   *   - it is mapped to another literal. Here, we leave it alone, since it is
   *     allowed to re-map the pivot only.
   */
  int *witness_iter = get_witness_start(current_line);
  int *witness_end = get_witness_end(current_line);
  int pivot = witness_iter[0];
  witness_iter[0] = new_pivot;
  witness_iter++;
  
  int witness_inc = 1; // If it equals 1, then we have not seen the separator
  int encountered_new_pivot_mapping = 0;
  for (; witness_iter < witness_end; witness_iter += witness_inc) {
    int lit = *witness_iter;
    if (lit == WITNESS_TERM) break;

    if (lit == pivot && witness_inc == 1) {
      *witness_iter = new_pivot;
      witness_iter--; // The new increment will add this back
      witness_inc = 2;
      if (encountered_new_pivot_mapping) return;
    } else if (lit == new_pivot) {
      if (witness_inc == 1) {
        // Swap with the old pivot
        *witness_iter = pivot;
        encountered_new_pivot_mapping = 1;
      } else {
        // Swap the mapping with the end of the witness
        if (witness_iter + 2 < witness_end && witness_iter[2] != WITNESS_TERM) {
          int *new_pivot_ptr = witness_iter;
          
          // Scan forward until the end or until WITNESS_TERM
          do {
            witness_iter += 2;
          } while (witness_iter < witness_end && *witness_iter != WITNESS_TERM);

          // Back up two slots, and put that mapping in the new pivot's spot
          witness_iter -= 2;
          new_pivot_ptr[0] = witness_iter[0];
          new_pivot_ptr[1] = witness_iter[1];
        }

        *witness_iter = WITNESS_TERM;
        return;
      }
    }
  }
}

// Moves state from `GLOBAL_UP` -> `CANDIDATE_UP` -> `RAT_UP`.
// Sets the various indexes appropriately.
// It is a fatal error to increment the state if `up_state` is `RAT_UP`.
static void increment_state(void) {
  switch (up_state) {
    case GLOBAL_UP:
      up_state = CANDIDATE_UP;
      candidate_assumed_literals_index = units_size;
      candidate_unit_literals_index = units_size;
      break;
    case CANDIDATE_UP:
      up_state = RAT_UP;
      RAT_assumed_literals_index = units_size;
      RAT_unit_literals_index = units_size;
      break;
    case RAT_UP: log_fatal_err("Cannot increment up_state beyond RAT_UP");
    default: log_fatal_err("Corrupted up_state: %d", up_state);
  }
}

// Moves state from `RAT_UP` -> `CANDIDATE_UP` -> `GLOBAL_UP`.
// Sets the various indexes appropriately.
// It is a fatal error to decrement the state if `up_state` is `GLOBAL_UP`.
static void decrement_state(void) {
  switch (up_state) {
    case GLOBAL_UP: log_fatal_err("Cannot decrement up_state below GLOBAL_UP");
    case CANDIDATE_UP:
      up_state = GLOBAL_UP;
      units_size = candidate_assumed_literals_index;
      break;
    case RAT_UP:
      up_state = CANDIDATE_UP;
      units_size = RAT_assumed_literals_index;
      break;
    default: log_fatal_err("Corrupted up_state: %d", up_state);
  }
}

// Assumes the literal as true, and adds it to the `unit_literals` array.
// Infers the correct generation value from state.
static inline void assume_unit_literal(int lit) {
  ullong gen = (up_state == CANDIDATE_UP) ? ASSUMED_GEN : alpha_generation;
  set_lit_for_alpha(lit, gen);
  resize_units();

  unit_literals[units_size] = lit;
  units_size++;

  if (up_state == CANDIDATE_UP) {
    candidate_unit_literals_index++;
  } else if (up_state == RAT_UP) {
    RAT_unit_literals_index++;
  }
}

// Sets the literal in the clause to true, assuming it is unit in the clause.
// Then adds the literal to the `unit_literals` array.
// NOTE: When doing unit propagation, negate the literal in `unit_literals`.
static void set_unit_clause(int lit, srid_t clause, ullong gen) {
  set_lit_for_alpha(lit, gen);
  resize_units();

  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    unit_literals_wp_up_indexes[units_size] = 0;
  }

  unit_literals[units_size] = lit;
  unit_clauses[units_size] = clause;
  vars_unit_indexes[VAR_FROM_LIT(lit)] = units_size;
  units_size++;
}

// Adds a watch pointer for the lit at the specified clause ID
static void add_wp_for_lit(int lit, srid_t clause) {
  // Resize the literal-indexes arrays if lit is outside our allocated bounds
  resize_wps();

  // Now allocate more space for the `wp[lit]` array, if needed
  uint alloc_size = wp_alloc_sizes[lit];
  if (wp_sizes[lit] == alloc_size) {
    wp_alloc_sizes[lit] = MAX(INIT_LIT_WP_ARRAY_SIZE, RESIZE(alloc_size));
    wps[lit] = xrealloc(wps[lit], wp_alloc_sizes[lit] * sizeof(srid_t));
  }
  
  // TODO: Error checking, see if wp is already in the list
  /*for (uint i = 0; i < wp_sizes[lit]; i++) {
    if (wps[lit][i] == clause) {
      log_fatal_err("Clause %lld already has a watch pointer for literal %d",
        TO_DIMACS_CLAUSE(clause), TO_DIMACS_LIT(lit));
    }
  }*/

  // Finally, add the clause to the wp list
  wps[lit][wp_sizes[lit]] = clause;
  wp_sizes[lit]++;
}

static void remove_wp_for_lit(int lit, srid_t clause) {
  srid_t *wp_list = wps[lit];
  uint wp_list_size = wp_sizes[lit];

  // Find the clause in the wp list and remove it
  for (uint i = 0; i < wp_list_size; i++) {
    if (wp_list[i] == clause) {
      // Overwrite the removed clause with the last clause in the list
      wp_list[i] = wp_list[wp_list_size - 1];
      uint size = --wp_sizes[lit];

      // Downsize if the size drops below a certain threshold
      size = MAX(INIT_LIT_WP_ARRAY_SIZE, size);
      if (size < wp_alloc_sizes[lit] / 6) {
        // (But keep some padding)
        size = (size * 3) / 2;
        wp_alloc_sizes[lit] = size;
        wps[lit] = xrealloc(wps[lit], size * sizeof(srid_t));
      }

      return;
    }
  }

  if (err_verbosity_level > VL_NORMAL) {
    dbg_print_clause(clause);
  }

  log_fatal_err("[line %lld] Clause %lld not in watch pointers for literal %d",
    TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(clause), TO_DIMACS_LIT(lit));
}

// Returns the clause ID that becomes falsified, or -1 if not found.
static srid_t perform_up_for_backwards_checking(ullong gen) {
  /*

    When performing UP for backwards checking, we do a very similar thing
    to UP for forwards checking, except we skip unmarked clauses as possible
    unit clauses in favor of marked clauses (i.e., clauses that were involved
    in another UP derivation) in order to reduce the number of clauses we
    need in the formula to derive the empty clause.

    In the inner loop (j), any watch pointer with (j' < j) is either:
      - A satisfied clause, via its first watch pointer
      - A unit clause, made unit via its first watch pointer (which is then set to true)

    This is because if a clause is falsified, it generates a contradiction,
    and UP exits. If instead the first watch pointer is not satisfied, but
    the clause contains a non-falsified literal to replace the considered
    negated lit, then lit's watch pointer is removed.

    As a result, if we prefer marked clauses for UP, then circle back,
    the only clauses that "come before" will not have their truth values
    changed.

      (Lemma: when adding unit clauses/literals to be processed by UP,
        we will never have both (l) and (-l) waiting to be processed,
        since we already set the assignment.)

    As for clauses that "come after" our bookmarked spot, they will be one of:
      - A satisfied clause
      - A unit clause
      - An ignored, unmarked clause

    Repeating the UP loop on these clauses generates the following behavior:
      - Ignored (continue)
      - Ignored (since its watch pointer has been set to true, making it satisfied)
      - Actually do UP

    One solution is to "bubble up" the ignored unmarked clauses, i.e.,
    to "bubble down" the satisfied/unit clauses. One way to do this is
    to save the earliest ignored index, and then maintain the following invariant:

    | SAT | SAT | UNIT/SAT | ... | IGN | IGN | ... | new UNIT | ... |

    Then the index of the ignored clause in `wps_list[j]` increments by one,
    and the new unit/satisfied clause swaps with the earliest ignored clause:

    | SAT | SAT | UNIT/SAT | ... | new unit | IGN | ... | IGN | ... |

    This slightly changes the order of watch pointers within the list,
    which could be more expensive than simply doing the redundant thing.

    Running an experiment on packing.cnf gives about 5 billion SAT cases,
    and only 126 million UNIT cases, which makes not repeating the SAT
    cases a good thing to do, even if the swaps are expensive.

    This also means that we not only need to store the (i, j) pair of a bookmark,
    but we also need to store the (j' < j) index to swap ignored clauses with.
    (Thus, if i == i', then both j' and j need to be incremented, etc.)

      I think this means that we only have to set a bit if we ignored a clause
      during the j run for some i, save the (i, j) pair of the ignored, and
      restore it later

    Another interesting point: ignored clauses can be any type
    (SAT, UNIT, SWAP, CONTRA), we just don't know which one until we process.
    From that point, swapping can still occur, but the invariant from "before"
    is maintained, so we don't need to store anything special when processing,
    aside from setting the ignored bit to 0.
   */

  uint progressed_i = 0;
  uint bookmarked_i = UINT_MAX;
  int accepting_unused_clauses = 0;

  uint i;
  switch (up_state) {
    case GLOBAL_UP:    i = global_up_literals_index;         break;
    case CANDIDATE_UP: i = candidate_assumed_literals_index; break;
    case RAT_UP:       i = RAT_assumed_literals_index;       break;
    default: log_fatal_err("Corrupted up_state: %d", up_state);
  }

  // Reset the `wp_up_indexes`
  // TODO: Why don't we reset the whole thing?
  // I guess the thought is that during backwards checking, we've already
  // done UP on the global state, so there is nothing more to find here
  // (Especially if we uncommit true units as we move backwards through form)
  memset(unit_literals_wp_up_indexes + i, 0, (units_size - i) * sizeof(uint));

restart_up:
  for (; i < units_size; i++) {
    // Iterate through lit's watch pointers and see if any clause becomes unit
    int lit = NEGATE_LIT(unit_literals[i]);
    srid_t *wp_list = wps[lit];

    uint wp_size = wp_sizes[lit]; // Store in a local variable for efficiency
    uint j = unit_literals_wp_up_indexes[i]; // Store in a local var for eff.
    if (j == wp_size) continue;
    uint ignored_j = j;

    for (; j < wp_size; j++) {
      srid_t clause_id = wp_list[j];
      int *clause = get_clause_start(clause_id);

      // The clause is not a unit clause (yet), and its watch pointers are 
      // the first two literals in the clause (we may reorder literals here).

      // Place the other watch pointer first
      if (clause[0] == lit) {
        clause[0] = clause[1];
        clause[1] = lit;
      }

      int first_wp = clause[0];
      peval_t first_peval = peval_lit_under_alpha(first_wp);

      // If `first_wp` evals to true, then the clause is satisfied (not unit)
      if (first_peval == TT) {
        // We swap the satisfied clause back in the wp_list,
        // so that the ignored clauses get bubbled up to the end
        SWAP_WP_LIST_ELEMS(wp_list, clause_id, j, ignored_j);
        continue;
      }

      // If we haven't processed these watch pointers yet, we try to
      // replace `lit` with a non-false wp later in the clause
      if (i >= progressed_i) {
        uint clause_size = get_clause_size(clause_id);
        int found_new_wp = 0;
        for (uint k = 2; k < clause_size; k++) {
          if (peval_lit_under_alpha(clause[k]) != FF) {
            // The kth literal is non-false, so swap it with the first wp
            int new_wp = clause[k];
            clause[1] = new_wp;
            clause[k] = lit;

            // Because clauses do not have duplicate literals, we know that
            // `clause[1] != lit`, and so even if `wps` gets reallocated,
            // it won't affect `wp_list = wps[lit]`.
            add_wp_for_lit(new_wp, clause_id);

            // Instead of calling `remove_wp_for_lit()`, we swap from the back
            wp_list[j] = wp_list[wp_size - 1];
            wp_size--;
            found_new_wp = 1;
            break;
          }
        }

        if (found_new_wp) {
          j--; // We need to decrement, since we placed a new wp in `wp_list[j]`
          continue;  
        }
      }

      // We didn't find a replacement non-FF watch pointer. Is `first_wp` FF?
      if (first_peval == FF) {
        // Since all literals are false, we found a UP contradiction
        // No need to update `unit_literals_wp_up_indexes[i]`, no more UP left
        wp_sizes[lit] = wp_size; // Restore from the local variable
        return clause_id;
      } else {
        // The first literal is unassigned, so we have a unit clause/literal
        // For backwards checking, we prefer already-used clauses
        if (IS_USED_LUI(clauses_lui[clause_id])) {
          set_unit_clause(first_wp, clause_id, gen); // Add as a unit literal
          SWAP_WP_LIST_ELEMS(wp_list, clause_id, j, ignored_j);
        } else if (accepting_unused_clauses) {
          accepting_unused_clauses = 0;
          bookmarked_i = i; // Monotonically increases

          set_unit_clause(first_wp, clause_id, gen);
          SWAP_WP_LIST_ELEMS(wp_list, clause_id, j, ignored_j);

          // Now that we've marked a clause, perhaps the new unit literal
          // gives us new unit clauses that are already marked.
          // We would prefer these over more ignored, unmarked clauses
          // associated with this unit literal.
          unit_literals_wp_up_indexes[i] = ignored_j; // Save our progress
          wp_sizes[lit] = wp_size;
          i = progressed_i;
          
          goto restart_up;
        } else if (bookmarked_i == UINT_MAX) {
          // We are ignoring an unused, potentially-unit clause
          // Store the minimum wp index of any unused/skipped unit clause
          bookmarked_i = i;
        }
      }
    }

    unit_literals_wp_up_indexes[i] = ignored_j;
    wp_sizes[lit] = wp_size;
  }

  progressed_i = i;  // Lemma: (i == units_size)

  // We restart UP to process the ignored clauses, if there are any
  // On a "first pass", we always ignore clauses, so if the bookmark is set,
  // there is at least one ignored clause
  // On "return passes," the bookmark monotonically increases, and we only
  // provably have no ignored clause if we are still accepting clauses
  if (!accepting_unused_clauses && bookmarked_i != UINT_MAX) {
    // We ignored at least one clause.
    // Go back to the `bookmarked_i`
    // We restart UP at saved `unit_literals_wp_up_indexes[i]`,
    i = bookmarked_i;
    accepting_unused_clauses = 1;
    goto restart_up;
  }
  
  if (up_state == GLOBAL_UP) {
    global_up_literals_index = units_size;
  }

  return -1;
}

// Performs unit propagation. Sets the falsified clause (the contradiction) to
// up_falsified_clause. -1 if not found.
// Any literals found are set to the provided generation value.
static srid_t perform_up_for_forwards_checking(ullong gen) {
  /* 
   * The unit propagation algorithm is complicated and immersed in invariants.
   *
   * First, we assume that the unit literals in `unit_literals` have been
   * set to true in the global partial assignment `alpha`. These are the
   * literals whose negations can cause additional clauses to become unit.
   * 
   * We take each negated literal `l` and loop through its watch pointers.
   * For any clause with a pair of watch pointers, the watch pointers are
   * two previously-unset literals (under alpha) in the first two positions
   * of the clause.
   * 
   * We move the other watch pointer p to the first position and check if it is
   * set to true. If so, then we continue to the next clause. Otherwise, we
   * must search through the rest of the clause for a non-false literal. If
   * found, then we swap that literal l' with l, add l' as a watch pointer, and
   * remove l as a watch pointer.
   * 
   * Because l' is not false, then either it is true (in which case, the clause
   * does not become unit), or it is unset. Thus, we might want to check the
   * truth value of p. However, we assumed that p was unset. If, since setting 
   * unit literals, p has become false, then we will detect this in future up_queue
   * literals.
   * 
   * If we can't find a replacement non-false literal l' for l, then we check the
   * truth value of p. If p is false, then we have found a contradiction.
   * Otherwise, we have a new unit, and we continue with unit propagation.
   */

  uint i;
  switch (up_state) {
    case GLOBAL_UP:    i = global_up_literals_index;         break;
    case CANDIDATE_UP: i = candidate_assumed_literals_index; break;
    case RAT_UP:       i = RAT_assumed_literals_index;       break;
    default: log_fatal_err("Corrupted up_state: %d", up_state);
  }

  for (; i < units_size; i++) {
    int lit = NEGATE_LIT(unit_literals[i]);

    // Iterate through its watch pointers and see if the clause becomes unit
    srid_t *wp_list = wps[lit];
    uint wp_size = wp_sizes[lit]; // Store and edit this value in a variable
    for (uint j = 0; j < wp_size; j++) {
      srid_t clause_id = wp_list[j];

      int *clause = get_clause_start_unsafe(clause_id);
      uint clause_size = get_clause_size(clause_id);
      
      // Lemma: the clause is not a unit clause (yet), and its w-pointers are 
      // the first two literals in the clause (we may reorder literals here).

      // Place the other watch pointer first
      if (clause[0] == lit) {
        clause[0] = clause[1];
        clause[1] = lit;
      }

      int first_wp = clause[0];

      // If `first_wp` evals to true, then the clause is satisfied (not unit)
      peval_t first_peval = peval_lit_under_alpha(first_wp);
      if (first_peval == TT) {
        continue;
      }

      // Otherwise, scan the clause for a non-false literal
      int found_new_wp = 0;
      for (uint k = 2; k < clause_size; k++) {
        if (peval_lit_under_alpha(clause[k]) != FF) {
          // The kth literal is non-false, so swap it with the first wp
          clause[1] = clause[k];
          clause[k] = lit;

          // Because clauses do not have duplicate literals, we know that
          // `clause[1] != lit`, and so even if `wps[lit]` gets reallocated,
          // it won't affect `wp_list`.
          add_wp_for_lit(clause[1], clause_id);

          // Instead of calling remove_wp_for_lit, we can swap from the back
          wp_list[j] = wp_list[wp_size - 1];
          wp_size--;
          found_new_wp = 1;
          break;
        }
      }

      if (found_new_wp) {
        j--;       // We need to decrement, since we replaced wp_list[j]
        continue;  
      }

      // We didn't find a replacement watch pointer. Is `first_wp` false?
      if (first_peval == FF) {
        // Since all literals are false, we found a UP contradiction
        wp_sizes[lit] = wp_size; // Restore from the local variable
        return clause_id;
      } else {
        // The first literal is unassigned, so we have a unit clause/literal
        set_unit_clause(first_wp, clause_id, gen);
      }
    }

    wp_sizes[lit] = wp_size; // Restore from the local variable
  }

  if (up_state == GLOBAL_UP) {
    global_up_literals_index = units_size;
  }

  return -1;
}

/**
 * @brief Performs unit propagation. Derived unit literals are set to be
 *        true for the provided `gen` value.
 * 
 * @param gen 
 * @return The clause ID of the falsified clause implied by unit propagation,
 *         or `-1` if no such clause is found.
 */
static inline srid_t perform_up(ullong gen) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    return perform_up_for_backwards_checking(gen);
  } else {
    return perform_up_for_forwards_checking(gen);
  }
}

// Adds watch pointers / sets units and performs unit propagation.
// Skips clauses already processed (i.e. when adding a new redundant clause,
// only adds watch pointers/sets unit on that clause).
// Should be called when the global `up_state == GLOBAL_UP`.
static void add_wps_and_perform_up(srid_t clause_index, ullong gen) {
  FATAL_ERR_IF(up_state != GLOBAL_UP, "up_state not GLOBAL_UP.");

  int *clause = get_clause_start_unsafe(clause_index);
  uint clause_size = get_clause_size(clause_index);

  FATAL_ERR_IF(clause_size == 0,
    "[line %lld] Cannot add wps and UP on the empty clause, %lld",
    TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(clause_index));

  // If the clause is unit, set it to be true, do UP later
  // Otherwise, add watch pointers
  if (clause_size == 1) {
    // The clause is unit - examine its only literal
    int lit = clause[0];
    switch (peval_lit_under_alpha(lit)) {
      case FF:
        // If the literal is false, then we have a UP refutation
        mark_and_store_empty_clause_refutation(clause_index, gen);
        return;
      case TT:;
        /* If the literal is true, then the unit clause is "duplicated"
         * by another clause made unit via UP. Since we prefer true unit
         * clauses in future UP derivations, we replace the clause reason
         * for `lit` with the current clause ID, and we replace the previous
         * clause's ID in `unit_clauses`. */
        int var = VAR_FROM_LIT(lit);
        int idx = vars_unit_indexes[var];
        unit_clauses[idx] = clause_index;
        break;
      default:
        set_unit_clause(lit, clause_index, GLOBAL_GEN);
        break;
    }
  } else {
    /*
      The clause has at least two literals - add watch pointers.

      Watch pointers must be non-FF literals (when eval'ed under alpha).
      Typically, if a(n implied) unit clause `(l)` is present in the formula,
      other clauses won't contain `l` or `-l`, since in the former case,
      the clause can be removed, and in the latter case, the `-l` literal
      can be removed. But this need not be the case (perhaps the formula
      hasn't undergone pre-processing yet), and some tools, such as `sr2drat`,
      add clauses with these kinds of "useless" literals/clauses.
      So to maintain the invariant that watch pointers must be non-FF literals,
      we scan the clause for two such literals.  Along the way, we might
      discover that the clause is unit or falsified.
    */
    uint non_ff_lits = 0;
    uint unassigned_lits = 0;
    for (uint i = 0; i < clause_size && non_ff_lits < 2; i++) {
      int lit = clause[i];
      peval_t peval = peval_lit_under_alpha(lit);
      if (peval != FF) {
        // Swap the non-FF literal to be a watch pointer
        if (i != non_ff_lits) {
          clause[i] = clause[non_ff_lits];
          clause[non_ff_lits] = lit;
        }

        non_ff_lits++;
        unassigned_lits += (peval == UNASSIGNED);
      }
    }

    switch (non_ff_lits) {
      case 0:
        mark_and_store_empty_clause_refutation(clause_index, gen);
        break;
      case 1:
        // We can set this clause as a unit if it has one unassigned literal.
        // Regardless of being unit or not, add watch pointers
        if (unassigned_lits == 1) {
          set_unit_clause(clause[0], clause_index, GLOBAL_GEN);
        }
      default: // fallthrough
        add_wp_for_lit(clause[0], clause_index);
        add_wp_for_lit(clause[1], clause_index);
        break;
    }
  }

  // We don't have an immediate contradiction, so perform unit propagation
  srid_t falsified_clause = perform_up(GLOBAL_GEN);
  if (falsified_clause >= 0) {
    mark_and_store_empty_clause_refutation(falsified_clause, gen);
  }
}

/**
 * @brief Assumes the negation of the candidate redundant clause into the
 *        current truth assignment, and then performs unit propagation.
 * 
 * This function performs a similar function to `assume_negated_clause()`
 * from `global_data.c`, but with extra bookkeeping.
 * 
 * The value of `up_state` must be `GLOBAL_UP` when calling this function.
 * On return, `up_state == CANDIDATE_UP`. Call `unassume_candidate_clause()`
 * to decrement the state and undo the effects of calling this function.
 * 
 * When we assume the negation of `clause_index`, we check how each literal
 * `l` evaluates under the truth assignment `alpha`. If `l` is unassigned,
 * then we assume it as a unit literal. If `l` evaluates to true, then
 * we have a trivial unit-propagation refutation, and we can compute the
 * refutation from the unit clause causing `l` to be true.
 * 
 * The tricky case is when `l` evaluates to false. Typically, we would ignore
 * `l`, since adding `-l` to `alpha` would have no effect. However, we also
 * want to minimize the number of unit-propagation hints in the LSR proof line
 * that we generate for this clause. One method of reducing the number of hints
 * is to treat `l` as a freshly-assumed literal, rather than the final literal
 * from a chain of unit-propagation-derived unit clauses. See
 * `mark_and_store_up_refutation()` for more information on how "assumed"
 * literals reduce the number of hints.
 * 
 * Thus, when `l` evaluates to false, we mark it as an "assumed" literal.
 * See the `MARK_AS_UP_ASSUMED_VAR()` macro for more information.
 * 
 * Note that no matter the returned result, the caller must call
 * `unassume_candidate_clause()`, since some or all of the clause's literals
 * may still be assumed in `alpha`.
 * 
 * TODO: Store which literal that causes `refuting_clause` to be set
 *       in order to find the shortest possible trivial UP refutation.
 * 
 * @param clause_index The candidate clause to assume.
 * @return `-1` if a contradiction was found and the UP refutation was emitted
 *         or stored, and `0` otherwise (meaning the assumption succeeded).
 */
static int assume_candidate_clause_and_perform_up(srid_t clause_index) {
  FATAL_ERR_IF(up_state != GLOBAL_UP, "up_state not GLOBAL_UP.");
  increment_state();

  int *clause_iter = get_clause_start_unsafe(clause_index);
  int *clause_end = get_clause_end(clause_index);

  srid_t refuting_clause = -1;
  int refuting_clause_index = (int) units_size;
  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    int var = VAR_FROM_LIT(lit);
    peval_t peval = peval_lit_under_alpha(lit);
    switch (peval) {
      case TT:
        // Store which clause caused the direct UP refutation.
        // Keep looping over the clause to mark assumed variables,
        // which will help minimize the number of global UP hints we need.
        // TODO: Store the refuting clause with the shortest UP derivation
        if (get_unit_index_for_var(var) < refuting_clause_index) {
          // TODO(bug): Handle trivially tautological clauses
          refuting_clause = get_unit_clause_for_var(var);
          refuting_clause_index = get_unit_index_for_var(var);
        }
      case FF: // fallthrough
        mark_var_unit_index_as_assumed(var);
        break;
      case UNASSIGNED:
        assume_unit_literal(NEGATE_LIT(lit));
        break;
      default: log_fatal_err("Invalid peval_t value: %d", peval);
    }
  }

  // If we haven't satisfied the clause, we perform unit propagation
  if (refuting_clause == -1) {
    refuting_clause = perform_up(ASSUMED_GEN);
  }

  // If we have satisfied the clause or found a UP refutation, emit it
  if (refuting_clause != -1) {
    mark_and_store_up_refutation(refuting_clause, alpha_generation - GEN_INC);
    return -1;
  }

  return 0;
}

// Reverts changes to the data structures made during the assumption of the candidate clause.
// Must be called before adding the candidate to the formula via insert_clause().
// Decrements global state back to GLOBAL_UP.
static void unassume_candidate_clause(srid_t clause_index) {
  FATAL_ERR_IF(up_state != CANDIDATE_UP, "up_state not CANDIDATE_UP.");

  // Undo the changes we made to the data structures
  // First, unassign the UP units derived after assuming the candidate clause
  unassign_global_units(candidate_unit_literals_index);

  // Now iterate through the candidate clause itself and unassume its literals
  int *clause_iter = get_clause_start_unsafe(clause_index);
  int *clause_end = get_clause_end(clause_index);
  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    int var = VAR_FROM_LIT(lit);

    // If the literal was originally unassigned, set its gen back to 0
    if (is_var_assumed_only_for_up(var)) {
      alpha[var] = 0;
    } else {
      clear_assumption_from_var_unit_index(var);
    }
  }

  decrement_state();
}

static inline void add_RAT_marked_var(int marked_var) {
  INSERT_ARR_ELT_CONCAT(RAT_marked_vars, sizeof(int), marked_var);
}

static inline void clear_RAT_marked_vars(void) {
  for (uint i = 0; i < RAT_marked_vars_size; i++) {
    clear_assumption_from_var_unit_index(RAT_marked_vars[i]);
  }

  RAT_marked_vars_size = 0;
}

/**
 * @brief Assumes into the current truth assignment the negation of
 *        the RAT clause when mapped under the substitution.
 * 
 * This function acts similarly to `assume_negated_clause_under_subst()`
 * from `global_data.c`, but with extra bookkeeping. See its documentation
 * for motivation/implementation details.
 * 
 * The extra bookkeeping tries to minimize the number of RAT hints in
 * this clause's RAT hint group. Specifically, for any literal `l` that
 * maps to a literal `m` under the substitution such that `m` evaluates
 * to false under the current substitution, `m` is marked as "assumed."
 * When the RAT hint group is calculated, the dependency chain stops
 * at these assumed literals.
 * 
 * When we encounter one of these literals `m`, we check if `m` was
 * assumed. If it was, then we return immediately. Otherwise, we store
 * the unit clause `C` causing `m` to be false. If no trivial refutations
 * are found, then we use `C` in `mark_up_derivation()`.
 * 
 * If a nontrivial UP refutation is needed to show that the RAT clause
 * is okay, then this function calls `mark_up_derivation()`, but it does
 * NOT call `store_RAT_dependencies()`, and in fact, that function does
 * not need to be called at all, since `mark_up_derivation()` marks
 * the needed literals from the candidate clause and its UP units.
 * 
 * It is the caller's responsibility to ensure that `clause_index` is not
 * a deleted clause and is in bounds.
 * 
 * The `up_state` must be `CANDIDATE_UP` when calling this function.
 * On return, `up_state == RAT_UP`.
 * 
 * TODO: When storing `refuting_clause`, try to find the shortest trivial
 *       UP refutation possible.
 * 
 * @param clause_index The RAT clause to assume.
 * @return `SATISFIED_OR_MUL` if the clause is satisfied or has a trivial
 *         UP refutation, `0` otherwise. If `0` is returned, then the RAT
 *         clause has been assumed into the current truth assignment.
 */
static int assume_RAT_clause_under_subst(srid_t clause_index) {
  FATAL_ERR_IF(up_state != CANDIDATE_UP, "up_state not RAT_UP.");
  increment_state();
  RAT_marked_vars_size = 0;

  int *clause_ptr = get_clause_start_unsafe(clause_index);
  int *clause_end = get_clause_end(clause_index);
  srid_t refuting_clause = -1;

  for (; clause_ptr < clause_end; clause_ptr++) {
    int lit = *clause_ptr;
    int mapped_lit = map_lit_under_subst(lit);
    switch (mapped_lit) {
      case SUBST_FF: break; // Ignore the literal
      case SUBST_TT:
        log_fatal_err("[line %lld] RAT clause %lld cannot eval to SUBST_TT",
            TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(clause_index));
        break;
      default:;
        int mapped_var = VAR_FROM_LIT(mapped_lit);
        int mapped_peval = peval_lit_under_alpha(mapped_lit);
        switch (mapped_peval) {
          case FF:
            if (is_var_set_due_to_up(mapped_var)) {
              mark_var_unit_index_as_assumed(mapped_var);
              add_RAT_marked_var(mapped_var);
            }
            break;
          case TT:
            if (is_var_assumed_for_up(mapped_var)) {
              return SATISFIED_OR_MUL;
            } else if (refuting_clause == -1) {
              refuting_clause = get_unit_clause_for_var(mapped_var);
            }
            break;
          case UNASSIGNED:
            assume_unit_literal(NEGATE_LIT(mapped_lit));
            break;
          default: log_fatal_err("Corrupted peval value: %d", mapped_peval);
        }
    }
  }

  if (refuting_clause != -1) {
    mark_up_derivation(refuting_clause, alpha_generation);
    return SATISFIED_OR_MUL;
  }

  return 0;
}

// Call when global state == RAT_UP.
// Decrements state back to CANDIDATE_UP.
static void unassume_RAT_clause(srid_t clause_index) {
  FATAL_ERR_IF(up_state != RAT_UP, "up_state not RAT_UP.");

  // Clear the UP reasons for the variables set during RAT UP
  for (int i = RAT_unit_literals_index; i < units_size; i++) {
    int lit = unit_literals[i];
    clear_lit_unit_index(lit);
  }

  clear_RAT_marked_vars();
  decrement_state();
}

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Undoes the effect of adding a clause to the formula.
 *        Only called during backwards checking.
 * 
 * During backwards checking, we add all clause additions to the formula in
 * an attempt to derive the empty clause. We then work backwards by only
 * checking those clauses that were used to derive the empty clause
 * or a later clause addition.
 * 
 * Normally, adding (i.e. "committing") a redundant clause to the formula
 * causes us to perform global UP. So during backwards checking, we need
 * to undo the effect of "committing" this clause to the formula. This means
 * seeing if the clause was unit. If it was, we erase this unit and all
 * unit literals/clauses derived from this one. Since `unit_literals`
 * and `unit_clauses` are stored in order of derivation, we simply
 * loop from the back until we find this clause.
 * 
 * However, because "later" unit clauses might NOT depend on this clause,
 * we must re-run UP after removing this clause.
 * 
 * @param clause_id The 0-indexed clause ID to un-commit. In almost all cases,
 *                  this ID is `CLAUSE_ID_FROM_LINE_NUM(current_line)`.
 */
static void uncommit_clause_and_set_as_candidate(srid_t clause_id) {
  FATAL_ERR_IF(ch_mode != BACKWARDS_CHECKING_MODE,
    "uncommit_clause_and_set_as_candidate() only for backwards checking.");
  FATAL_ERR_IF(up_state != GLOBAL_UP,
    "up_state not GLOBAL_UP in uncommit_clause_and_set_as_candidate().");

  int *clause_ptr = get_clause_start_unsafe(clause_id);
  int *clause_end = get_clause_end(clause_id);

  // Ignore the empty clause
  if (clause_ptr == clause_end) return;

  // Remove the clause's watch pointers if it isn't a true unit
  if (clause_ptr + 1 != clause_end) {
    remove_wp_for_lit(clause_ptr[0], clause_id);
    remove_wp_for_lit(clause_ptr[1], clause_id);
  }

  // If this clause is unit, remove it from the set of unit clauses
  // The `unassign()` function preserves true units derived after this one
  int var = VAR_FROM_LIT(clause_ptr[0]);
  if (is_var_set_due_to_up(var) && get_unit_clause_for_var(var) == clause_id) {
    unassign_global_units_due_to_deletion(get_unit_index_for_var(var));
  }

  lit_occ_delete_clause(&lit_occ, clause_id);
}

static int can_skip_clause(srid_t clause_index) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    srid_t lui = LUI_FROM_USER_DEL_LUI(clauses_lui[clause_index]);
    return lui <= current_line;
  } else {
    return is_clause_deleted(clause_index);
  }
}

/** 
 * @brief Allocates the minimum/maximum clause ranges to check.
 *        Only called during backwards checking.
 * 
 * During forwards checking, we only check a range of clauses reduced by
 * the witness. To accomplish this, each literal tracks the first and last
 * clause it appears in. The min/max range to check is thus the smallest
 * `min` and largest `max` value among literals that would cause their
 * clause to be reduced.
 * 
 * We store this same information during backwards checking when we
 * store the initial watch pointers and perform UP to derive the empty clause.
 * 
 * This function allocates the necessary space. Indexed by line number.
 */
static void alloc_min_max_clauses_to_check(void) {
  lines_fl_clauses_to_check = xmalloc(
    num_parsed_add_lines * sizeof(fl_clause_t));
}

static void store_clause_check_range(srid_t line_num) {
  return;
  // fl_clause_t *fl = &lines_fl_clauses_to_check[line_num];
  // get_fl_clause_for_subst(line_num, &lit_occ, fl);
}

/**
 * @brief Get the min max clause to check object
 * 
 * @param[out] fl  Stores the min/max (inclusive) clauses to check.
 */
static void get_min_max_clause_to_check(fl_clause_t *fl) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    memcpy(fl, &lines_fl_clauses_to_check[current_line], sizeof(fl_clause_t));
  } else {
    get_fl_clause_for_subst(current_line, &lit_occ, fl);
  }
}

static void emit_RAT_UP_failure_error(srid_t clause_index) {
  log_err("[line %lld] No UP contradiction for RAT clause %lld.",
    TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(clause_index));

  // Print tons of information if verbosity is high enough
  if (err_verbosity_level > VL_NORMAL) {
    log_err_raw("c The current candidate clause: ");
    dbg_print_clause(CLAUSE_ID_FROM_LINE_NUM(current_line));

    log_err_raw("c The failing RAT clause: ");
    dbg_print_clause(clause_index);

    log_err_raw("c The RAT clause, under the subst: ");
    int *clause_iter = get_clause_start(clause_index);
    int *end = get_clause_end(clause_index);
    for (; clause_iter < end; clause_iter++) {
      int lit = *clause_iter;
      int mapped_lit = map_lit_under_subst(lit);
      switch (mapped_lit) {
        case SUBST_TT: log_err_raw("TT "); break;
        case SUBST_FF: log_err_raw("FF "); break;
        default: log_err_raw("%d ", TO_DIMACS_LIT(mapped_lit));
      }
    }
    log_err_raw("0\n");

    dbg_print_assignment();
    dbg_print_subst();

    // Now scan through the unit literals and list how they became unit
    if (err_verbosity_level > VL_QUIET) {
      log_err_raw("\nc The unit literals and why they are unit\n");
      log_err_raw("c Printed in order of their derivations\n");
      dbg_print_unit_literals();
    }
  } else {
    log_err_raw("c (For more information about this error, run with the `-V` option.)\n");
  }

  exit(1);
}

static void check_reduced_clause(srid_t clause_index) {
  switch (reduce_clause_under_subst(clause_index)) {
    case SATISFIED_OR_MUL:
      increment_num_reduced_clauses(current_line);
    case NOT_REDUCED: // fallthrough
      return;
    case REDUCED:
      add_RAT_clause_hint(clause_index);
      increment_num_reduced_clauses(current_line);

      // If the RAT clause is not satisfied by alpha, do UP
      if (assume_RAT_clause_under_subst(clause_index) != SATISFIED_OR_MUL) {
        srid_t falsified_clause = perform_up(alpha_generation);
        if (falsified_clause == -1) {
          emit_RAT_UP_failure_error(clause_index);
        }

        mark_up_derivation(falsified_clause, alpha_generation);
        store_RAT_dependencies(falsified_clause);
      }

      unassume_RAT_clause(clause_index);
      alpha_generation += GEN_INC; // Clear this round of RAT units from alpha
      break;
    case CONTRADICTION:
      log_fatal_err("[line %lld] Reduced clause %lld claims contradiction.",
        TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(clause_index));
    default:
      log_fatal_err("[line %lld] Clause %lld corrupted reduction value %d.",
        TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(clause_index),
        reduce_clause_under_subst(clause_index));
  }
}

static void check_reduced_clause_wrapper(size_t index) {
  usrid_t unsigned_clause = (usrid_t) index;
  srid_t clause = (srid_t) unsigned_clause;
  check_reduced_clause(clause);
}

static void collect_reduced_clauses(int lit) {
  srid_t *cl_iter = get_first_clause_containing_lit(&lit_occ, lit);
  if (cl_iter == NULL) return;
  srid_t *cl_end = get_last_clause_containing_lit(&lit_occ, lit);
  for (; cl_iter <= cl_end; cl_iter++) {
    srid_t clause = *cl_iter;
    if (can_skip_clause(clause) || bmask_is_bit_set(&bmask, clause)) continue;
    bmask_set_bit(&bmask, clause);
  }
}

static void check_dsr_line(void) {
  // We save the generation at the start of line checking so we can determine
  // which clauses are marked in the `dependency_markings` array.
  ullong old_alpha_gen = alpha_generation;
  alpha_generation += GEN_INC;
  subst_generation++;

  srid_t cc_index = CLAUSE_ID_FROM_LINE_NUM(current_line);

  // Find implied candidate unit clauses
  // If a UP refutation is found, it is stored, and we may finish the line
  if (assume_candidate_clause_and_perform_up(cc_index) == -1) {
    goto candidate_valid;
  }

  // Since we didn't derive UP contradiction, the clause should be nonempty
  FATAL_ERR_IF(new_clause_size == 0, "Didn't UP refute the empty clause.");

  // Now we turn to RAT checking - minimize and assume the witness
  max_RAT_line = MAX(max_RAT_line, current_line);
  int must_find_new_pivot = minimize_witness();
  assume_subst(current_line);
  if (must_find_new_pivot) {
    find_new_pivot_for_witness(cc_index);
  }

  if (get_witness_size(current_line) < 2) {
    num_drat_lines++;
  } else {
    num_sr_lines++;
  }

  int *witness_iter = get_witness_start(current_line);
  int *witness_end = get_witness_end(current_line);
  int pivot = witness_iter[0];
  witness_iter++; // Skip the pivot literal

  bmask_clear(&bmask);
  collect_reduced_clauses(NEGATE_LIT(pivot));

  int seen_pivot_divider = 0;
  for (; witness_iter < witness_end; witness_iter++) {
    int lit = *witness_iter;
    if (lit == WITNESS_TERM) break;
    int neg_lit = NEGATE_LIT(lit);

    if (!seen_pivot_divider) {
      if (lit == pivot) {
        seen_pivot_divider = 1;
      } else {
        collect_reduced_clauses(neg_lit);
      }
    } else {
      witness_iter++;
      collect_reduced_clauses(lit);
      collect_reduced_clauses(neg_lit);
    }
  }

  bmask_map_over_set_bits(&bmask, check_reduced_clause_wrapper);

  /*
    Now check that the candidate, mapped under the witness,
    is implied by the rest of the formula.

    Before, `dsr-trim` required the witness to satisfy the candidate clause C.
    This was enforced by requiring that the pivot literal (i.e., the first
    literal in the witness, used as a separator before the mapped portion
    of the substitution) not be re-mapped later, meaning that it was set
    to true in the final witness. Since the pivot is a member of C,
    this trivially means that the witness satisfies C.
    
    However, in the general case, we want to allow witnesses that re-map
    the pivot literal elsewhere. In the case where the witness does NOT
    satisfy C, we treat it like any other RAT clause and subject it
    to a check. The recorded hint ID is the ID of the candidate itself.
  */
  check_reduced_clause(cc_index);

  print_or_store_lsr_line(old_alpha_gen);

  // Congrats: the line checked! Undo the changes made to the data structures
candidate_valid:
  unassume_candidate_clause(cc_index);

  if (ch_mode == FORWARDS_CHECKING_MODE) {
    current_line++;
    add_wps_and_perform_up(cc_index, old_alpha_gen);
    lit_occ_add_clause(&lit_occ, cc_index);
  }
}

static void remove_wps_from_user_deleted_clauses(srid_t clause_id) {
  srid_t line = LINE_NUM_FROM_CLAUSE_ID(clause_id);
  srid_t *dels = get_bcu_deletions_start(line);
  srid_t *del_end = get_bcu_deletions_end(line);

  for (; dels < del_end; dels++) {
    srid_t del_id = *dels;
    int *del_clause = get_clause_start(del_id);
    uint clause_size = get_clause_size(del_id);

    // Ignore deletion of the clause if it is a(n implied) unit.
    // Watch pointer invariant: the true literal is the first in the clause.
    int var = VAR_FROM_LIT(del_clause[0]);
    if (is_var_set_due_to_up(var)
        && get_unit_clause_for_var(var) == del_id
        && (ignore_implied_unit_deletions
          || (ignore_unit_deletions && clause_size == 1))) {
      logv("[line %lld] Ignoring deletion of (implied) unit clause %lld.",
        TO_DIMACS_LINE(line), TO_DIMACS_CLAUSE(del_id));
      clauses_lui[del_id] = -1;
      continue;
    }

    // Remove the watch pointers for the deleted (non-true-unit) clause.
    // We restore these in `restore_wps_for_user_deleted_clauses()`.
    if (clause_size > 1) {
      remove_wp_for_lit(del_clause[0], del_id);
      remove_wp_for_lit(del_clause[1], del_id);
    }

    lit_occ_delete_clause(&lit_occ, del_id);
    soft_delete_clause(del_id);
  }
}

static void restore_wps_for_user_deleted_clauses(srid_t clause_id) {
  srid_t line = LINE_NUM_FROM_CLAUSE_ID(clause_id);
  srid_t *dels = get_bcu_deletions_start(line);
  srid_t *del_end = get_bcu_deletions_end(line);

  for (; dels < del_end; dels++) {
    srid_t del_id = *dels;

    // Only undelete clauses that were soft deleted
    if (is_clause_deleted(del_id)) {
      soft_undelete_clause(del_id);
      lit_occ_add_clause(&lit_occ, del_id);
      int *del_clause = get_clause_start_unsafe(del_id);
      uint clause_size = get_clause_size(del_id);
      if (clause_size > 1) {
        add_wp_for_lit(del_clause[0], del_id);
        add_wp_for_lit(del_clause[1], del_id);
      }
    }
  }
}

static void prepare_next_line_for_backwards_checking(void) {
  srid_t cc_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
  do {
    restore_wps_for_user_deleted_clauses(cc_id);
    current_line--;
    cc_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
    uncommit_clause_and_set_as_candidate(cc_id);
    ra_commit_range(&deletions);
  } while (IS_UNUSED_LUI(clauses_lui[cc_id]) && current_line > 0);

  // Do a fresh round of global UP after restoring wps and undoing units
  global_up_literals_index = 0;
  perform_up_for_backwards_checking(GLOBAL_GEN);

  srid_t cc_rat_hints_index = RAT_HINTS_IDX_FROM_LINE_NUM(current_line);
  ra_commit_empty_ranges_until(&hints, cc_rat_hints_index);
  new_clause_size = get_clause_size(cc_id);
}

static line_type_t prepare_next_line(void) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    prepare_next_line_for_backwards_checking();
  } else {
    num_RAT_clauses = 0;
    num_reduced_clauses = 0;
  }

  if (p_strategy == PS_EAGER) {
    // Edge case: if we are backwards checking and we made it to line 0,
    // don't check the line if we haven't used the clause somewhere else.
    srid_t candidate_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
    if (current_line == 0 && ch_mode == BACKWARDS_CHECKING_MODE \
          && IS_UNUSED_LUI(clauses_lui[candidate_id])) {
      return DELETION_LINE; // Skip checking this line
    } else {
      return ADDITION_LINE;
    }
  }
  else {
    return parse_dsr_line();
  }
}

static void prepare_lit_occ_for_cnf(void) {
  lit_occ_add_formula_until_with_clause_mappings(&lit_occ, num_cnf_clauses);
}

static void add_wps_and_up_initial_clauses(void) {
  prepare_lit_occ_for_cnf();

  srid_t c;
  for (c = 0; c < num_cnf_clauses && !derived_empty_clause; c++) {
    if (is_clause_deleted(c)) continue;
    add_wps_and_perform_up(c, 0);
  }

  if (ch_mode == FORWARDS_CHECKING_MODE) return;
  
  if (!parsed_empty_clause) {
    logc("No empty clause detected. Attempting to derive it now.");
  } else {
    logc("Empty clause detected on proof line %lld.", num_parsed_lines);
  }

  // TODO: Encapsulate better
  // TODO: No need to RESIZE from formula_size when this is the largest it'll be
  resize_sr_trim_data();
  resize_last_used_ids();
  alloc_min_max_clauses_to_check();

  // Add implied unit clauses, clause by clause
  // Stop when we finally derive the empty clause
  current_line = 0;
  srid_t end_of_formula = formula_size - parsed_empty_clause;
  for (; c < end_of_formula && !derived_empty_clause; c++) {
    // Store the min/max clause range to check, given the current formula state
    // If we end up SR-checking this clause later, we use this range
    store_clause_check_range(current_line);

    // Now process any user deletions by removing their watch pointers.
    // This function "soft deletes" the clauses from the formula,
    // which means we keep their literals while treating the clause as deleted.
    remove_wps_from_user_deleted_clauses(c);

    // Now perform UP on the "newly-added" clause
    add_wps_and_perform_up(c, 0);

    // "Commit" the new clause
    lit_occ_add_clause(&lit_occ, c);
    current_line++;
  }

  if (!derived_empty_clause) {
    log_err("Could not derive the empty clause during backwards checking.");
    log_err_raw("If the proof is instead a proof of equisatisfiability or a ");
    log_err_raw("proof of symmetry breaking, use forwards checking (-f).\n");
    exit(1);
  }

  /*
   * We need to do a bit of cleanup from the above for-loop.
   * Since `c` gets incremented before checking if we derived the empty clause,
   * we need to decrement it to correctly store the clause ID of the final
   * non-empty clause that, when added to F, implies the empty clause via UP.
   */
  c--;

  logc("The empty clause was derived after clause %lld (add'n line %lld).",
      TO_DIMACS_CLAUSE(c), TO_DIMACS_LINE(LINE_NUM_FROM_CLAUSE_ID(c)));

  // If we derived the empty clause before the last addition clause,
  // we can discard the rest of the formula
  if (c < end_of_formula - 1) {
    discard_formula_after_clause(c);

    // Because `UP_HINTS_IDX` is based on `num_parsed_add_lines`,
    // we need to manually adjust this value to be as if we parsed up
    // to `c` and then the empty clause. Since `c` is 0-indexed, we add 2
    // TODO: Base it on `formula_size` instead
    num_parsed_add_lines = LINE_NUM_FROM_CLAUSE_ID(c) + 2;
  } else if (!parsed_empty_clause) {
    /*
     * We derived the empty clause, but we didn't originally parse it.
     * Commit the empty clause to the formula (to adjust `formula_size`),
     * and "parse" the empty clause.
     */
    commit_clause();
    num_parsed_lines++;
    num_parsed_add_lines++;
  }

  /* Set the value of `current_line` to the line of the empty clause.
   * 
   * This value is extremely brittle, i.e., it depends on many different
   * data structure invariants. If these invariants or certain helper functions
   * change, then this value also needs to change.
   * 
   * Since derived deletions are stored "in reverse order," and since there
   * are no derived deletions for the empty clause, we need to ensure that
   * backwards checking proceeds directly to the clause immediately before
   * the empty clause. Since `prepare_current_line()` subtracts 1 from
   * `current_line`, we need to set `current_line` equal to the empty
   * clause, rather than the clause before it.
   */
  current_line = num_parsed_add_lines - 1;
  discard_bcu_deletions_after_empty_clause(current_line);
}

static void check_proof(void) {
  up_state = GLOBAL_UP;
  alpha_generation = GEN_INC;
  timer_record(&timer, TIMER_LOCAL);

  add_wps_and_up_initial_clauses();

  logc("Checking proof...");

  // TODO encapsulate better later
  // TODO fix with resize_sr_trim_data()
  // TODO the (+1) is a little too much?
  // TODO Go off line num and not formula size?
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    if (formula_size > lines_RAT_hint_info_alloc_size) {
      lines_RAT_hint_info = xrecalloc(lines_RAT_hint_info,
        lines_RAT_hint_info_alloc_size * sizeof(line_RAT_info_t),
        (formula_size + 1) * sizeof(line_RAT_info_t));
      lines_RAT_hint_info_alloc_size = formula_size + 1;
    }
  }

  while (has_another_dsr_line()) {
    line_type_t line_type = prepare_next_line();
    resize_sr_trim_data();
    if (line_type == ADDITION_LINE) {
      check_dsr_line(); 
    }
  }

  if (p_strategy == PS_STREAMING && dsr_file != stdin) {
    fclose(dsr_file);
  }

  timer_print_elapsed(&timer, TIMER_LOCAL, "Proof checking");
  print_proof_checking_result();

  print_stored_lsr_proof();
  print_valid_formula_if_requested();
  timer_print_elapsed(&timer, TIMER_GLOBAL, "Total runtime");
}

////////////////////////////////////////////////////////////////////////////////

int main(int argc, char **argv) {
  if (argc == 1) {
    print_short_help_msg(stdout);
    return 0;
  }

  int forward_set = 0, compress_set = 0;
  int del_units_set = 0, del_impl_units_set = 0;
  cli_opts_t cli;
  cli_init(&cli);
  
  // Emit VALID formulas to a file, upon request
  int emit_set = 0;
  char valid_formula_file_path[MAX_FILE_PATH_LEN];
  valid_formula_file_path[MAX_FILE_PATH_LEN - 1] = '\0';

  // Parse CLI arguments
  int ch;
  cli_res_t cli_res;
  while ((ch = getopt_long(argc, argv, OPT_STR, longopts, NULL)) != -1) {
    switch (ch) {
    case FORWARD_OPT:
      FATAL_ERR_IF(forward_set, "Cannot set `-f` or `--forward` twice.");
      forward_set = 1;
      p_strategy = PS_STREAMING; // TODO: Make eager possible
      ch_mode = FORWARDS_CHECKING_MODE;
      break;
    case COMPRESS_PROOF_OPT:
      FATAL_ERR_IF(compress_set, "Cannot set `-c` or `--compress` twice.");
      compress_set = 1;
      break;
    case EMIT_VALID_FORM_OPT:
      FATAL_ERR_IF(emit_set, "Cannot set `--emit-valid-formula-to` twice.");
      emit_set = 1;
      strncpy(valid_formula_file_path, argv[optind - 1], MAX_FILE_PATH_LEN - 1);
      break;
    case DEL_UNITS_OPT:
      FATAL_ERR_IF(del_units_set, "Cannot set `--delete-units` twice.");
      del_units_set = 1;
      break;
    case DEL_IMPL_UNITS_OPT:
      FATAL_ERR_IF(del_impl_units_set, "Cannot set `--delete-implied-units` twice.");
      del_impl_units_set = 1;
      break;
    default:
      cli_res = cli_handle_opt(&cli, ch, optopt, argv[optind - 1], optarg);
      switch (cli_res) {
        case CLI_UNRECOGNIZED:
          log_err("Unimplemented option: %s.", argv[optind - 1]);
          print_short_help_msg(stderr);
          return 1;
        case CLI_HELP_MESSAGE:
          print_short_help_msg(stdout);
          return 0;
        case CLI_LONG_HELP_MESSAGE:
          print_long_help_msg(stdout);
          return 0;
        case CLI_HELP_MESSAGE_TO_STDERR:
          print_short_help_msg(stderr);
          return 1;
        case CLI_SUCCESS:
          break;
        default:
          log_fatal_err("Corrupted CLI result: %d", cli_res);
      }
    }
  }

  cli_res_t pres = cli_parse_file_paths_for_dsr_trim(&cli, argv, argc, optind);
  switch (pres) {
    case CLI_HELP_MESSAGE_TO_STDERR:
      print_short_help_msg(stderr);
      return 1;
    case CLI_SUCCESS: break;
    default: log_fatal_err("Corrupted CLI result: %d", pres);
  }

  // Open the files first, to ensure we don't do work unless they exist
  logc("CNF file path: %s", cli.cnf_file_path);
  FILE *cnf_file = xfopen(cli.cnf_file_path, "r");
  
  if (cli.dsr_file_path == NULL) {
    logc("No DSR file path provided, using stdin.");
    dsr_file = stdin;
  } else {
    logc("DSR file path: %s", cli.dsr_file_path);
    dsr_file = xfopen(cli.dsr_file_path, "r");
  }

  if (cli.lsr_file_path == NULL) {
    logc("No LSR file path provided, using stdout.");
    lsr_file = stdout;
  } else {
    logc("LSR file path: %s", cli.lsr_file_path);

    // Don't open a file if we are writing to `/dev/null`
    if (strcmp(cli.lsr_file_path, "/dev/null") == 0
        || strcmp(cli.lsr_file_path, "/dev/null/") == 0) {
      lsr_file = NULL;
    } else {
      lsr_file = xfopen(cli.lsr_file_path, "w");
    }
  }

  if (p_strategy == PS_EAGER) {
    logc("Using an EAGER parsing strategy.");
  } else {
    logc("Using a STREAMING parsing strategy.");
  }

  if (ch_mode == FORWARDS_CHECKING_MODE) {
    logc("Doing FORWARDS proof checking.");
  } else {
    logc("Doing BACKWARDS proof checking.");
  }

  if (ch_mode == FORWARDS_CHECKING_MODE && p_strategy == PS_EAGER) {
    log_fatal_err("Forwards checking and eager parsing not implemented.");
  }

  if (compress_set) {
    write_binary = 1;
    logc("The emitted LSR proof will be in binary format (`-c` specified).");
  }

  if (emit_set) {
    logc("Emitting a VALID formula to: %s", valid_formula_file_path);
    valid_formula_file = xfopen(valid_formula_file_path, "w");
  }

  if (del_units_set) {
    ignore_unit_deletions = 0;
    ignore_implied_unit_deletions = 0;
    logc("Will delete true and implied units from DSR deletions.");
  }

  if (del_impl_units_set && ignore_implied_unit_deletions) {
    ignore_implied_unit_deletions = 0;
    logc("Will delete implied units from DSR deletions.");
  }

  timer_init(&timer);
  timer_record(&timer, TIMER_GLOBAL);

  timer_record(&timer, TIMER_LOCAL);
  parse_cnf(cnf_file, DELETE_TAUTOLOGIES);
  timer_print_elapsed(&timer, TIMER_LOCAL, "Parsing the CNF");

  int input_proof_is_in_binary = configure_proof_file_parsing(dsr_file);
  if (input_proof_is_in_binary) {
    logc("Detected that the DSR proof is in binary format.");
    if (write_binary == 0) {
      logc("The emitted LSR proof will also be in binary format.");
      write_binary = 1;
    }
  }

  prepare_dsr_trim_data();
  check_proof();
  return 0;
}
