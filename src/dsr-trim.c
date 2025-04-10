/**
 * @file dsr-trim.c
 * @brief Tool for labeling and trimming SR proof certificates.
 * 
 *  This tool checks deletion substitution redundancy (DSR) proofs and
 *  annotates them with unit propagation hints to form linear substitution
 *  redundancy (LSR) proofs, which can be checked by `lsr-check`.
 * 
 *  DSR proofs are (roughly) used to show that two propositional logic
 *  formulas are equisatisfiable, meaning that the original formula is
 *  satisfiable if and only if the derived formula is. DSR proofs do this
 *  by incrementally adding and deleting clauses from the formula. Added
 *  clauses must be redundant, meaning that adding them to the formula
 *  does not affect its satisfiability. (In other words, that F and
 *  (F and C) are equisatisfiable.)
 * 
 *  In most cases, DSR proofs are *unsatisfiability* proofs, meaning that
 *  the empty clause is eventually shown to be redundant. Since the empty
 *  clause is by definition unsatisfiable, this makes the original formula
 *  unsatisfiable as well.
 * 
 *  DSR proofs only contain clauses and substitution witnesses, and so
 *  `dsr-trim` must perform a kind of proof search to derive unit propagation
 *  hints. It maintains several data structures, such as a stack of unit
 *  literals/clauses and a record of which clauses were used in which UP
 *  derivations so as to minimize the number of hints.
 * 
 *  More details can be found in the paper:
 * 
 *    "Verified Substitution Redundancy Checking"
 *    Cayden Codel, Jeremy Avigad, Marijn Heule
 *    In FMCAD 2024
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-12
 */

#include <string.h>
#include <getopt.h>

#include "xio.h"
#include "xmalloc.h"
#include "global_data.h"
#include "global_parsing.h"
#include "logger.h"
#include "range_array.h"
#include "hash_table.h"
#include "cli.h"
#include "cnf_parser.h"
#include "sr_parser.h"
#include "timer.h"

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
#define INIT_LIT_WP_ARRAY_SIZE          (4)

// The initial allocation size for tracking the multiplicity of clauses.
// This allows the checker to accept multiple copies of any clause without
// actually storing multiple copies.
// See `clause_mult_t`.
#define INIT_CLAUSE_MULT_SIZE  (4)

// When setting literals "globally" under initial unit propagation, we use the
// largest possible generation value.
#define GLOBAL_GEN   (ULLONG_MAX - 1)

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

// Array containing the clause ID "reason" causing the variable to be set. Indexed by variable.
// The MSB is set during RAT assumption to let global UP clauses be marked globally. (TODO: update docs later.)
static srid_t *up_reasons = NULL;
static uint up_reasons_alloc_size = 0; // TODO: use alpha_subst_alloc_size for this?

// A list of literals, in order of when they become unit.
static int *unit_literals = NULL;

// A list of clauses, in order of when they became unit.
static srid_t *unit_clauses = NULL;
static uint units_alloc_size = 0;
static uint unit_literals_size = 0;
static uint unit_clauses_size = 0;

static uint candidate_unit_clauses_index = 0;
static uint RAT_unit_clauses_index = 0;

// Index pointing at the "unprocessed" global UP literals
static uint global_up_literals_index = 0;

static uint candidate_assumed_literals_index = 0;
static uint candidate_unit_literals_index = 0;
static uint RAT_assumed_literals_index = 0;
static uint RAT_unit_literals_index = 0;

// Generations for clauses involved in UP derivations. Indexed by clauses.
static ullong *dependency_markings = NULL;
static srid_t dependencies_alloc_size = 0;

// When assuming the RAT clause under the substitution, we record specially
// marked variables here for tautology checking. Cleared when a trivial
// UP derivation is not found, or if one is found not based on a RAT-marked var.
static int *RAT_marked_vars = NULL;
static uint RAT_marked_vars_alloc_size = 0;
static uint RAT_marked_vars_size = 0;

static FILE *dsr_file = NULL;
static FILE *lsr_file = NULL;

// The total number of addition lines parsed. Incremented by `parse_dsr_line()`.
static srid_t num_parsed_add_lines = 0;

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

// Counts the number of times a clause appears multiple times in the formula.
typedef struct clause_multiplicity {
  srid_t clause_id;
  uint multiplicity;
} clause_mult_t;

static clause_mult_t *clause_mults;
static uint clause_mults_alloc_size = 0;
static uint clause_mults_size = 0;

// Forward declare, since deletion needs it
static void remove_wp_for_lit(int lit, srid_t clause);

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

static uint *line_num_RAT_hints = NULL;
static uint line_num_RAT_hints_alloc_size = 0;
static uint num_RAT_hints = 0;

// Indexed by the 0-indexed `current_line`.
// Used only during backwards checking, and allocated by `add_initial_wps()`.
static min_max_clause_t *lines_min_max_clauses_to_check = NULL;

static timer_t timer;

////////////////////////////////////////////////////////////////////////////////

// Help messages and command line options

#define FORWARD_OPT   ('f')
#define BACKWARD_OPT  ('b')
#define OPT_STR       ("bf" BASE_CLI_OPT_STR)

// A flag set by `getopt_long()` when the user requests a longer help message.
static int long_help_msg_flag = 0;

// A flag set by `getopt_long()` when the user wants to emit a valid formula.
static int emit_valid_formula = 0;
static FILE *emit_valid_formula_file = NULL;

// The set of "long options" for CLI argument parsing. Used by `getopt_long()`.
static struct option const longopts[] = {
  { "help", no_argument, &long_help_msg_flag, 1 },
  { "dir", required_argument, NULL, DIR_OPT },
  { "name", required_argument, NULL, NAME_OPT },
  { "eager", no_argument, NULL, EAGER_OPT },
  { "streaming", no_argument, NULL, STREAMING_OPT },
  { "forward", no_argument, NULL, FORWARD_OPT },
  { "backward", no_argument, NULL, BACKWARD_OPT },
  { "emit-valid-formula-to", required_argument, &emit_valid_formula, 1 },
  { NULL, 0, NULL, 0 }  // The array of structs must be NULL/0-terminated
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
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    srid_t idx = UP_HINTS_IDX_FROM_LINE_NUM(line_num);
    return ra_get_range_start(&hints, idx);
  } else {
    return ra_get_range_start(&hints, 1);
  }
}

/**
 * @brief Returns a pointer to one more than the last hint in the UP hints
 *        block for the given line number.
 * 
 * @param line_num The 0-indexed line number for the stored hints.
 * @return The exclusive end of the UP hints.
 */
static inline srid_t *get_UP_hints_end(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    srid_t idx = UP_HINTS_IDX_FROM_LINE_NUM(line_num);
    return ra_get_range_start(&hints, idx + 1);
  } else {
    return ra_get_range_start(&hints, 2);
  }
}

static inline srid_t *get_RAT_hints_start(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    srid_t idx = RAT_HINTS_IDX_FROM_LINE_NUM(line_num);
    return ra_get_range_start(&hints, idx);
  } else {
    return ra_get_range_start(&hints, 0);
  }
}

static inline srid_t *get_RAT_hints_end(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    srid_t idx = RAT_HINTS_IDX_FROM_LINE_NUM(line_num);
    return ra_get_range_start(&hints, idx + 1);
  } else {
    return ra_get_range_start(&hints, 1);
  }
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

static inline uint get_num_RAT_hints(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    return line_num_RAT_hints[line_num];
  } else {
    return num_RAT_hints;
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
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    srid_t idx = DEL_IDX_FROM_LINE_NUM(line_num);
    return ra_get_range_start(&deletions, idx);
  } else {
    return ra_get_range_start(&deletions, 0);
  }
}

static srid_t *get_deletions_end(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    srid_t idx = DEL_IDX_FROM_LINE_NUM(line_num);
    return ra_get_range_start(&deletions, idx + 1);
  } else {
    return ra_get_range_start(&deletions, 1);
  }
}

static uint get_num_deletions(srid_t line_num) {
  return (uint) (get_deletions_end(line_num) 
    - get_deletions_start(line_num));
}

/**
 * @brief Returns the start of the backwards checking user (BCU) deleted
 *        clauses for a given `line_num`. Only used during backwards checking.
 * 
 * Note: no check is made here to ensure that the `ch_mode` is
 * backwards checking. It is the caller's responsibility.
 * 
 * @param line_num The 0-indexed line number.
 * @return A pointer to the start of the deletions.
 */
static srid_t *get_bcu_deletions_start(srid_t line_num) {
  return ra_get_range_start(&bcu_deletions, line_num);
}

static srid_t *get_bcu_deletions_end(srid_t line_num) {
  return ra_get_range_start(&bcu_deletions, line_num + 1);
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
  ra_insert_srid_elt(&hints, -TO_DIMACS_CLAUSE(clause_id));
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    line_num_RAT_hints[current_line]++;
  } else {
    num_RAT_hints++;
  }
}

static void add_RAT_up_hint(srid_t clause_id) {
  ra_insert_srid_elt(&hints, TO_DIMACS_CLAUSE(clause_id));
}

static void print_last_used_ids(void) {
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

////////////////////////////////////////////////////////////////////////////////

static void print_wps(void) {
  for (int i = 0; i <= (max_var * 2) + 1; i++) {
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
  uint sum = 0;
  uint size = MIN(num_parsed_add_lines, line_num_RAT_hints_alloc_size);
  for (int i = 0; i < size; i++) {
    sum += get_num_RAT_hints(i);
  }

  if (sum == 0) return;

  log_raw(VL_NORMAL, "Num RAT hints: ");

  for (int i = 0; i < size; i++) {
    if (i % 5 == 4) {
      log_raw(VL_NORMAL, "[%d] ", i + 1);
    }
    log_raw(VL_NORMAL, "%d ", get_num_RAT_hints(i));
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
    switch (peval_lit_under_alpha(i * 2)) {
      case TT:
        log_raw(VL_NORMAL, "%d (%lld) ", TO_DIMACS_LIT(i * 2),
        up_reasons[i]);
        break;
      case FF:
        log_raw(VL_NORMAL, "%d (%lld) ", TO_DIMACS_LIT((i * 2) + 1),
      up_reasons[i]);
        break;
      default: break;
    }
  }
  log_raw(VL_NORMAL, "\n");
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
  int *clause = get_clause_start_unsafe(clause_id);
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
 * TODO update docs
 * 
 * During forward proof checking, the current witness gets parsed into
 * the global data pointer `witness`, with corresponding size `witness_size`.
 * Before parsing a new line, this witness gets cleared by setting
 * `witness_size` to 0.
 * 
 * During backwards proof checking, the witness is stored in the `witnesses`
 * pointer. The checker must then manually set the `witness` and `witness_size`
 * data to point at the correct section of `witnesses`. While this is quite
 * manual, this ensures that
 * 
 * (1) the API for forward and backward proof checking is the same, and
 * (2) that forward proof checking can save memory by re-using `witness`.
 */
static void print_witness(srid_t line_num) {
  int *witness_start = get_witness_start(line_num);
  int *iter = witness_start;
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
        case SUBST_TT:
          write_lit(lsr_file, TO_DIMACS_LIT(lit));
          break;
        case SUBST_FF:
          write_lit(lsr_file, TO_DIMACS_LIT(NEGATE_LIT(lit)));
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
  if (get_num_deletions(printed_line_num) == 0) return;
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

  srid_t *rat_hints_iter = get_RAT_hints_start(line_num);
  srid_t *rat_hints_end = get_RAT_hints_end(line_num);
  for (; rat_hints_iter < rat_hints_end; rat_hints_iter++) {
    srid_t rat_hint = *rat_hints_iter; // Hints are already in DIMACS format
    print_mapped_hint(rat_hint);
  }
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
  write_lsr_addition_line_start(lsr_file, printed_line_id);
  print_clause(CLAUSE_ID_FROM_LINE_NUM(line_num));

  // Only print a witness if there are RAT/reduced clauses
  if (get_num_RAT_hints(line_num) > 0) {
    print_witness(line_num);
  }

  write_lit(lsr_file, 0); // Separator between (clause + witness) and rest
  print_hints(line_num);
  write_sr_line_end(lsr_file);
}

static void print_valid_formula_if_requested(void) {
  if (!derived_empty_clause && emit_valid_formula_file != NULL) {
    // Count how many non-deleted clauses there are, for the problem header
    srid_t num_present_clauses = 0;
    for (srid_t c = 0; c < formula_size; c++) {
      if (!is_clause_deleted(c)) num_present_clauses++;
    }
 
    // Save the value of writing to binary
    int write_binary_before = write_binary;
    write_binary = 0;

    // Write the `cnf p <num_vars> <num_clauses>` problem header
    fputc(DIMACS_PROBLEM_LINE, emit_valid_formula_file);
    fprintf(emit_valid_formula_file,
      CNF_HEADER_STR, max_var + 1, num_present_clauses);

    for (srid_t c = 0; c < formula_size; c++) {
      if (is_clause_deleted(c)) continue;
      
      int *iter = get_clause_start_unsafe(c);
      int *end = get_clause_end(c);

      // Re-sort the original CNF clauses
      // Printing the LSR proof sorts all other clauses wrt pivots
      if (c < num_cnf_clauses) {
        qsort(iter, end - iter, sizeof(int), absintcmp);
      } else if (c == num_cnf_clauses) {
        fprintf(emit_valid_formula_file,
            "c >>> Redundant clauses start below this point <<<\n");
      }

      for (; iter < end; iter++) {
        int lit = *iter;
        write_lit(emit_valid_formula_file, TO_DIMACS_LIT(lit));
      }
      write_sr_line_end(emit_valid_formula_file);
    }

    write_binary = write_binary_before; // Restore the old value
    fclose(emit_valid_formula_file);
  }
}

////////////////////////////////////////////////////////////////////////////////

// Hashing logic for clauses, used for deletions

// Hashes the provided clause ID.
// The hash function is commutative, meaning that no matter how the clause is
// permuted, the clause will return the same hash value.
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
  return (1023 * sum + prod ^ (31 * xor));
}

/**
 * @brief 
 * 
 * @param clause_index
 * @param[out] hp Pointer to the hash value of the clause.
 * @param[out] bp Pointer to the hash table bucket where the match lives.
 * @param[out] bi Pointer to the hash table bucket index where the match lives.
 * @return The clause index of a matching clause that comes before this one,
 *         or `-1` if no such clause is found.
 */
static srid_t find_hashed_clause(srid_t ci, uint *hp, htb_t **bp, uint *bi) {
  int *clause = get_clause_start_unsafe(ci);
  uint hash = hash_clause(ci);
  if (hp != NULL) *hp = hash;
  htb_t *bucket = ht_get_bucket(&clause_id_ht, hash);
  uint bucket_size = bucket->size;

  if (bucket_size == 0) return -1;

  // Iterate through all clauses in this bucket and try to find a match
  int *matching_clause;
  hte_t *entries = bucket->entries;
  for (int i = 0; i < bucket_size; i++) {
    srid_t possible_match = entries[i].data;

    // First approximation: see if the sizes and hashes match
    uint match_size = get_clause_size(possible_match);
    if (match_size == new_clause_size) {
      // Second approximation: see if the hashes match
      uint match_hash = hash_clause(possible_match);
      if (match_hash == hash) {
        // Most clauses are small, so O(n^2) search is good enough
        // Note that the literals aren't necessarily sorted due to wps
        matching_clause = get_clause_start(possible_match);
        int found_match = 1; // We set this to 0 if a literal isn't found
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
          if (bi != NULL) *bi = i;
          return possible_match;
        }
      }
    }
  }

  return -1;
}

static inline void add_hashed_clause_to_ht(srid_t clause_index, uint hash) {
  ht_insert(&clause_id_ht, hash, clause_index);
}

static inline void add_clause_to_ht(srid_t clause_index) {
  uint hash = hash_clause(clause_index);
  add_hashed_clause_to_ht(clause_index, hash);
}

// Adds one to the mult counter, or if one isn't there for `clause_index`,
// sets the mult to `1`. (Single occurrence clauses don't get added.)
// Essentially, the `mult` counts the additional copies of the clause.
static void inc_clause_mult(srid_t clause_index) {
  for (int i = 0; i < clause_mults_size; i++) {
    if (clause_mults[i].clause_id == clause_index) {
      clause_mults[i].multiplicity++;
      return;
    }
  }

  // Clause not found in multiplicity list - insert a new entry in the back
  RESIZE_ARR_CONCAT(clause_mults, sizeof(clause_mult_t));
  clause_mults[clause_mults_size].clause_id = clause_index;
  clause_mults[clause_mults_size].multiplicity = 1;
  clause_mults_size++;
}

// Returns the number of remaining copies (after the decrease).
// Returns 0 if the clause is not found (meaning it has multiplicity of 1).
static uint dec_clause_mult(srid_t clause_index) {
  for (int i = 0; i < clause_mults_size; i++) {
    if (clause_mults[i].clause_id == clause_index) {
      uint mult = clause_mults[i].multiplicity;
      if (mult == 1) {
        // Swap from back
        clause_mults[i] = clause_mults[clause_mults_size - 1];
        clause_mults_size--;
      } else {
        clause_mults[i].multiplicity--;
      }

      return mult;
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
 */
static void delete_parsed_clause(void) {
  htb_t *b;
  uint b_idx;
  srid_t clause_match = find_hashed_clause(formula_size, NULL, &b, &b_idx);

  if (clause_match == -1) {
    log_raw(VL_QUIET, "The clause requested to be deleted: ");
    dbg_print_clause(formula_size);
    log_fatal_err("[line %lld] No matching clause found for deletion.",
      current_line + 1);
  }

  // Check that the matching clause isn't a global unit
  // If it is, error, since we don't want to unroll and re-run UP
  for (int i = 0; i < unit_clauses_size; i++) {
    FATAL_ERR_IF(unit_clauses[i] == clause_match,
      "[line %lld] Cannot delete clause %d, as it is a global unit.",
      current_line + 1, TO_DIMACS_CLAUSE(clause_match));
  }

  // If we still have copies of the clause, leave the hash table alone
  if (dec_clause_mult(clause_match) > 0) return;

  ht_remove_at_index(b, b_idx);
  store_user_deletion(clause_match);

  // How we delete the clause from the formula depends on the checking mode
  switch (ch_mode) {
    case FORWARDS_CHECKING_MODE:;
      int *clause_match_ptr = get_clause_start_unsafe(clause_match);
      remove_wp_for_lit(clause_match_ptr[0], clause_match);
      remove_wp_for_lit(clause_match_ptr[1], clause_match);
      delete_clause(clause_match); // Deletes from the formula
      break;
    case BACKWARDS_CHECKING_MODE:
      resize_last_used_ids();
      srid_t lui = MARK_USER_DEL_LUI(num_parsed_add_lines);
      clauses_lui[clause_match] = lui;
      break;
    default: log_fatal_err("Invalid checking mode: %d", ch_mode);
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
    inc_clause_mult(clause_match);
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
    print_deletions_with_line_id(LINE_ID_FROM_LINE_NUM(num_parsed_add_lines));
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
      FATAL_ERR_IF(is_tautology || new_clause_size <= 1, 
        "[line %lld] Clause to delete was a tautology, empty, or unit.",
          num_parsed_add_lines + 1);
      delete_parsed_clause();
      
      // Remove the parsed literals from the formula
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
      srid_t possible_match = add_clause_to_ht_or_inc_mult();
      if (possible_match != -1) {
        // Remove the clause and the witness from the formula
        // `parse_sr_clause()` commits the clause, so we adjust `formula_size`
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

  return line_type;
}

/**
 * @brief Parses the entire DSR proof file. The parsing strategy must be EAGER.
 */
static void parse_entire_dsr_file(void) {
  FATAL_ERR_IF(p_strategy != PS_EAGER,
    "To parse the entire DSR file eagerly, the p_strategy must be EAGER.");

  int detected_empty_clause = 0;
  while (!detected_empty_clause && has_another_line(dsr_file)) {
    parse_dsr_line();
    detected_empty_clause = (new_clause_size == 0);
  }

  fclose(dsr_file);
  logc("Parsed %lld addition lines.", num_parsed_add_lines);

  if (!detected_empty_clause && ch_mode == BACKWARDS_CHECKING_MODE) {
    logc("No empty clause detected. Attempting to derive it now.");
  }

  if (detected_empty_clause) {
    logc("Detected the empty clause on proof line %lld.",
        num_parsed_add_lines);   
  }
}

////////////////////////////////////////////////////////////////////////////////

static void prepare_dsr_trim_data(void) {
  // Allocate an empty watch pointer array for each literal
  // Allocate some additional space, since we'll probably add new literals later
  wps_alloc_size = (max_var + 1) * 4;
  wps = xcalloc(wps_alloc_size, sizeof(srid_t *));
  wp_alloc_sizes = xcalloc(wps_alloc_size, sizeof(uint)); 
  wp_sizes = xcalloc(wps_alloc_size, sizeof(uint));

  // Only allocate initial watch pointer space for literals in the formula 
  for (int i = 0; i < (max_var + 1) * 2; i++) {
    wp_alloc_sizes[i] = INIT_LIT_WP_ARRAY_SIZE;
    wps[i] = xmalloc(INIT_LIT_WP_ARRAY_SIZE * sizeof(srid_t));
  }

  // Allocate empty reasons array for each variable, plus extra space
  up_reasons_alloc_size = (max_var + 1);
  up_reasons = xmalloc_memset(up_reasons_alloc_size * sizeof(srid_t), 0xff);

  // Allocate space for the unit lists. Probably won't be too large
  units_alloc_size = (max_var + 1);
  unit_literals = xmalloc(units_alloc_size * sizeof(int));
  unit_clauses = xmalloc(units_alloc_size * sizeof(srid_t));

  // Allocate space for the dependency markings
  dependencies_alloc_size = formula_size * 2;
  dependency_markings = xcalloc(dependencies_alloc_size, sizeof(ullong));

  RAT_marked_vars_alloc_size = (max_var + 1);
  RAT_marked_vars = xmalloc(RAT_marked_vars_alloc_size * sizeof(int));

  // Hash all formula clauses
  ht_init(&clause_id_ht, 4 * formula_size);
  for (srid_t i = 0; i < formula_size; i++) {
    add_clause_to_ht(i);
  }

  // We track multiplicities of duplicate clauses
  clause_mults_alloc_size = INIT_CLAUSE_MULT_SIZE;
  clause_mults = xmalloc(clause_mults_alloc_size * sizeof(clause_mult_t));

  // If we are backwards checking, allocate additional structures
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    // TODO: set to formula_size when resizing?
    clauses_lui_alloc_size = formula_size * 2;
    clauses_lui = xmalloc_memset(clauses_lui_alloc_size * sizeof(srid_t), 0xff);

    line_num_RAT_hints_alloc_size = formula_size * 2;
    line_num_RAT_hints = xcalloc(line_num_RAT_hints_alloc_size, sizeof(uint));

    unit_literals_wp_up_indexes = xcalloc(units_alloc_size, sizeof(int));
  }

  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    ra_init(&hints, num_cnf_clauses * 10, num_cnf_vars, sizeof(srid_t));
    ra_init(&deletions, num_cnf_vars * 10, num_cnf_vars, sizeof(srid_t));
    ra_init(&bcu_deletions, num_cnf_clauses, num_cnf_vars, sizeof(srid_t));
  } else {
    ra_init(&hints, num_cnf_vars * 10, 3, sizeof(srid_t));
    ra_init(&deletions, num_cnf_vars, 2, sizeof(srid_t));
  }

  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    parse_entire_dsr_file();
  } else {
    current_line = 0;   
  }
}

static void resize_wps(void) {
  if ((max_var + 1) * 2 >= wps_alloc_size) {
    uint old_size = wps_alloc_size;
    wps_alloc_size = RESIZE((max_var + 1) * 2);
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
  RESIZE_MEMSET_ARR(up_reasons,
    up_reasons_alloc_size, (max_var + 1), sizeof(srid_t), 0xff);
  RECALLOC_ARR(dependency_markings,
    dependencies_alloc_size, formula_size, sizeof(ullong));
}

static void resize_units(void) {
  if (unit_literals_size >= units_alloc_size) {
    int old_size = units_alloc_size;
    units_alloc_size = RESIZE(unit_literals_size);
    unit_literals = xrealloc(unit_literals, units_alloc_size * sizeof(int));
    unit_clauses = xrealloc(unit_clauses, units_alloc_size * sizeof(srid_t));

    if (ch_mode == BACKWARDS_CHECKING_MODE) {
      unit_literals_wp_up_indexes = xrecalloc(unit_literals_wp_up_indexes,
        old_size * sizeof(int), units_alloc_size * sizeof(int));
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
  uint nrh = get_num_RAT_hints(current_line);
  if (nrh == 0) return;

  skipped_RAT_indexes_size = 0;
  if (skipped_RAT_indexes == NULL) {
    skipped_RAT_indexes_alloc_size = max_var;
    skipped_RAT_indexes = xmalloc(max_var * sizeof(uint));
  }

  // First pass: mark "active" clauses
  uint num_marked = 0;
  srid_t *hints_start = get_RAT_hints_start(current_line);
  srid_t *hints_end = get_RAT_hints_end(current_line);
  srid_t *hints_iter = hints_start;
  for (uint i = 0; i < nrh; i++) {
    srid_t RAT_clause = FROM_RAT_CLAUSE(*hints_iter);
    hints_iter++;
    srid_t RAT_lui = clauses_lui[RAT_clause];
    if (RAT_lui >= current_line) {
      // Scan through its hints and mark them as active
      srid_t hint;
      while (hints_iter < hints_end && (hint = *hints_iter) > 0) {
        hint = FROM_DIMACS_CLAUSE(hint);
        hints_iter++;
        num_marked += adjust_clause_lui(hint);
      }
    } else if (IS_UNUSED_LUI(RAT_lui)) {
      // Add unused or "current" hints to the skipped indexes list
      // Subtract 1 due to the ++ above
      INSERT_ARR_ELT_CONCAT(skipped_RAT_indexes, sizeof(uint),
        (uint) ((hints_iter - hints_start) - 1));
      SKIP_REMAINING_UP_HINTS(hints_iter, hints_end);
    } else {
      log_fatal_err("[line %lld] RAT clause %lld was deleted before UP hint.",
        current_line + 1, TO_DIMACS_CLAUSE(RAT_clause));
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
      srid_t RAT_clause = FROM_RAT_CLAUSE(*iter);
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
  line_num_RAT_hints[current_line] -= skipped_RAT_indexes_size;
}

/**
 * @brief Stores the unit propagation hints for those unit clauses that
 *        had their dependency marked during UP/RAT UP derivations.
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
  for (uint i = 0; i < unit_clauses_size; i++) {
    srid_t c = unit_clauses[i];
    if (dependency_markings[c] > gen) {
      add_up_hint(c);
    }
  }
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
    minimize_RAT_hints();
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
  if (ch_mode != BACKWARDS_CHECKING_MODE) return; 

  timer_record(&timer, TIMER_LOCAL);

  generate_clause_id_map();
  print_initial_clause_deletions();

  // For each "active" addition clause, print its LSR line
  srid_t printed_line_id = num_cnf_clauses + 1;
  int is_active_deletion_line = 0;
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

// Marks the clauses causing each literal in the clause to be false.
// Ignore literals that are assumed fresh, whether in CANDIDATE or RAT.
// Literals that were globally set to unit, but are candidate assumed, are ignored.
static void mark_clause(srid_t clause, int offset) {
  int *clause_iter = get_clause_start(clause) + offset; 
  int *clause_end = get_clause_end(clause);
  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    int var = VAR_FROM_LIT(lit);
    srid_t clause_reason = up_reasons[var];
    if (clause_reason >= 0) {
      dependency_markings[clause_reason] = alpha_generation; 
    }
  }
}

/**
 * @brief Marks the dependencies for each false literal in a unit clause.
 *        Used to minimize the number of printed UP hints.
 * 
 * @param clause The 0-indexed ID of the clause to mark.
 */
static inline void mark_unit_clause(srid_t clause) {
  mark_clause(clause, 1);
}

/**
 * @brief Marks the dependencies for an entire falsified clause.
 *        Used to minimize the number of printed UP hints.
 * 
 * @param clause The 0-indexed ID of the clause to mark.
 */
static inline void mark_entire_clause(srid_t clause) {
  mark_clause(clause, 0);
}

/**
 * @brief Marks dependencies among the derived unit clauses to minimize the
 *        number of printed UP hints.
 * 
 * During unit propagation, any unit literal records which clause caused it
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
 * to the current `alpha_generation`.
 * 
 * Later, when printing or storing the UP hints, only unit clauses with
 * a `dependency_markings` value strictly greater than the `alpha_generation`
 * before checking the current line are stored as UP hints.
 */
static void mark_dependencies(void) {
  // We use an int here because we scan backwards until the counter is negative
  for (int i = unit_clauses_size - 1; i >= 0; i--) {
    srid_t clause = unit_clauses[i];
    if (dependency_markings[clause] == alpha_generation) {
      mark_unit_clause(clause);
    }
  }
}

// Backwards marks the dependencies for the UP derivation.
// Starts the marking at the clause stored in up_falsified_clause.
static inline void mark_up_derivation(srid_t from_clause) {
  mark_entire_clause(from_clause);
  mark_dependencies();
}

// TODO: Think about how to make the empty clause not be the special case
// Probably reroute the "store" to "print_or_store_line" somehow
// And then don't have a special `add_wps_and_()` call before the check line loop?
/**
 * @brief Marks UP dependencies and stores UP hints, starting from the
 *        falsified clause `from_clause`.
 * 
 * @param from_clause 
 * @param gen 
 */
static void mark_and_store_up_refutation(srid_t from_clause, ullong gen) {
  mark_up_derivation(from_clause);
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

static void store_RAT_dependencies(srid_t from_clause) {
  for (int i = RAT_unit_clauses_index; i < unit_clauses_size; i++) {
    if (dependency_markings[unit_clauses[i]] == alpha_generation) {
      add_RAT_up_hint(unit_clauses[i]);
    }
  }

  add_RAT_up_hint(from_clause);
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
 * now that it contains -l after the smaller witness.
 * 
 * In addition, any literal l -> m in the substitution portion, with m set to
 * either true or false in alpha, can instead be mapped to m's truth value.
 * The reason this is allowed is similar to the above: any clause containing l
 * will contain m after the substitution, and m's truth value in alpha causes
 * the same overall effect as mapping l to m's truth value directly when
 * evaluating the clause under the substitution and doing RAT checking.
 * 
 * A witness containing a literal l set to true that is set to false via global
 * UP before assuming the negation of the candidate, means a witness is
 * inconsistent with the formula, and will cause an error.
 * 
 * Minimization is done by a single loop over the witness. Unnecessary literals
 * l -> T/F are removed, and any l -> m in the substitution portion with
 * m -> T/F in alpha are set to l -> T/F. If l -> m is set to l -> T/F, it
 * then checks whether l can be removed using the same logic as before.
 * Removals are handled with an increasing "write pointer" that allows the
 * rest of the substitution to be shifted to fill in the holes.
 * 
 * At the end, the `witness_size` is decreased appropriately.
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
          log_msg(VL_VERBOSE, "WE MUST FIND A NEW PIVOT: %d", pivot);
          must_find_new_pivot = 1;
          // We *do* keep this "redundant" literal (TODO document why later)
        }
      }
    }

    // Now compare the truth value of l in the substitution and alpha
    // TODO: Brittle negation, based on hard-coded values of peval_t.
    if (lit_alpha != UNASSIGNED) {
      if (lit_alpha == lit_subst) {
        log_msg(VL_VERBOSE, "[line %lld] Redundant witness literal %d (idx %d)",
          current_line + 1, TO_DIMACS_LIT(lit),
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
  int *clause_iter = get_clause_start(cc_index);
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
// If incremented at `RAT_UP`, resets "back to" a RAT_UP state.
static void increment_state(void) {
  switch (up_state) {
    case GLOBAL_UP:
      up_state = CANDIDATE_UP;
      candidate_assumed_literals_index = unit_literals_size;
      candidate_unit_literals_index = unit_literals_size;
      candidate_unit_clauses_index = unit_clauses_size;
      break;
    case CANDIDATE_UP:
      up_state = RAT_UP;
      RAT_assumed_literals_index = unit_literals_size;
      RAT_unit_literals_index = unit_literals_size;
      RAT_unit_clauses_index = unit_clauses_size;
      break;
    case RAT_UP:
      unit_literals_size = RAT_assumed_literals_index;
      RAT_unit_literals_index = RAT_assumed_literals_index;
      unit_clauses_size = RAT_unit_clauses_index;
      break;
    default: log_fatal_err("Corrupted up_state: %d", up_state);
  }
}

// Moves state from `RAT_UP` -> `CANDIDATE_UP` -> `GLOBAL_UP`.
// Sets the various indexes appropriately.
static void decrement_state(void) {
  switch (up_state) {
    case GLOBAL_UP: return;
    case CANDIDATE_UP:
      up_state = GLOBAL_UP;
      unit_literals_size = candidate_assumed_literals_index;
      unit_clauses_size = candidate_unit_clauses_index;
      break;
    case RAT_UP:
      up_state = CANDIDATE_UP;
      unit_literals_size = RAT_assumed_literals_index;
      unit_clauses_size = RAT_unit_clauses_index;
      break;
    default: log_fatal_err("Corrupted up_state: %d", up_state);
  }
}

// Sets the literal to true, and adds it to the unit_literals array.
// Infers the correct generation value from state.
static inline void assume_unit_literal(int lit) {
  ullong gen = (up_state == CANDIDATE_UP) ? ASSUMED_GEN : alpha_generation;
  set_lit_for_alpha(lit, gen);
  resize_units();
  unit_literals[unit_literals_size++] = lit;

  if (up_state == CANDIDATE_UP) {
    candidate_unit_literals_index++;
  } else if (up_state == RAT_UP) {
    RAT_unit_literals_index++;
  }
}

// Sets the literal in the clause to true, assuming it is unit in the clause.
// Then adds the literal to the unit_literals array, to look for more unit clauses later.
// NOTE: When doing unit propagation, take the negation of the literal in the unit_literals array.
static void set_unit_clause(int lit, srid_t clause, ullong gen) {
  set_lit_for_alpha(lit, gen);
  up_reasons[VAR_FROM_LIT(lit)] = clause;

  // log_msg(VL_VERBOSE, "[line %lld] Setting clause %d to unit on literal %d",
  //  current_line, TO_DIMACS_CLAUSE(clause), TO_DIMACS_LIT(lit));

  FATAL_ERR_IF(clause > CLAUSE_ID_FROM_LINE_NUM(current_line),
    "Clause %lld is set to unit before its line %lld",
    TO_DIMACS_CLAUSE(clause), current_line);

  resize_units();

  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    unit_literals_wp_up_indexes[unit_literals_size] = 0;
  }

  unit_literals[unit_literals_size++] = lit;
  unit_clauses[unit_clauses_size++] = clause;
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
      // TODO: Shrink array if small enough?
      wp_list[i] = wp_list[wp_list_size - 1];
      wp_sizes[lit]--;
      return;
    }
  }

  // Fatal error: watch pointer not in the list
  log_fatal_err("Clause %lld not found in watch pointer list for literal %d",
    TO_DIMACS_CLAUSE(clause), TO_DIMACS_LIT(lit));
}

// Returns the clause ID that becomes falsified, or -1 if not found.
static srid_t perform_up_for_backwards_checking(ullong gen) {
  // When performing UP for backwards checking, we do the same thing
  // Except we skip unmarked clauses as possible units, in favor of
  // marked clauses, to reduce the number of "dependent" clauses in the formula

  /*

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
  memset(unit_literals_wp_up_indexes + i,
    0, (unit_literals_size - i) * sizeof(uint));

restart_up:
  for (; i < unit_literals_size; i++) {
    // Iterate through lit's watch pointers and see if any clause becomes unit
    int lit = NEGATE_LIT(unit_literals[i]);
    srid_t *wp_list = wps[lit];

    uint wp_size = wp_sizes[lit]; // Store in a local variable for efficiency
    uint j = unit_literals_wp_up_indexes[i]; // Store in a local var for eff.
    if (wp_size == 0 || j == wp_size) continue;
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

            // Instead of calling `remove_wp_for_lit()`, we can swap from the back
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

  progressed_i = i;  // Lemma: (i == unit_literals_size)

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
    global_up_literals_index = unit_literals_size;
  }

  return -1;
}

// Performs unit propagation. Sets the falsified clause (the contradiction) to
// up_falsified_clause. -1 if not found.
// Any literals found are set to the provided generation value.
static srid_t perform_up_for_forwards_checking(ullong gen) {
  /* The unit propagation algorithm is quite involved and immersed in invariants.
   * Buckle up, cowboys.
   *
   * First, we assume that the literals that have been found to be unit have been
   * set to true in the global partial assignment `alpha`. Those literals
   * have been added to the unit_lits array. These are the literals whose 
   * negations can cause additional clauses to become unit.
   * 
   * We take each false literal l and loop through its watch pointers. For any
   * clause with a pair of watch pointers, the watch pointers are two previously-unset 
   * literals (under alpha) in the first two positions of the clause.
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

  for (; i < unit_literals_size; i++) {
    int lit = NEGATE_LIT(unit_literals[i]);

    // Iterate through its watch pointers and see if the clause becomes unit
    srid_t *wp_list = wps[lit];
    uint wp_size = wp_sizes[lit]; // Store and edit this value in a variable
    for (uint j = 0; j < wp_size; j++) {
      srid_t clause_id = wp_list[j];
      int *clause = get_clause_start_unsafe(clause_id);
      uint clause_size = get_clause_size(clause_id);
      
      // Lemma: the clause is not a unit clause (yet), and its wpointers are 
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

          // Adding a watch pointer could potentially re-allocate the `wp_list`
          // underneath us, so we refresh the pointer
          wp_list = wps[lit];

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
    global_up_literals_index = unit_literals_size;
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

  int *clause = get_clause_start(clause_index);
  uint clause_size = get_clause_size(clause_index);

  FATAL_ERR_IF(clause_size == 0, "Cannot add wps and UP on the empty clause");

  // If the clause is unit, set it to be true, do UP later
  // Otherwise, add watch pointers
  if (clause_size == 1) {
    // The clause is unit - examine its only literal
    int lit = clause[0];
    switch (peval_lit_under_alpha(lit)) {
      case FF:
        // If the literal is false, then we have a UP refutation
        derived_empty_clause = 1;
        mark_and_store_up_refutation(clause_index, gen);
        return;
      case TT:;
        /* If the literal is true, then the unit clause is "duplicated"
          * by another clause made unit via UP. Since we prefer true unit
          * clauses in future UP derivations, we replace the clause reason
          * for `lit` with the current clause ID, and we replace the previous
          * clause's ID in `unit_clauses`. */

        // TODO: What if the previous "unit" is a duplicate unit clause
        int var = VAR_FROM_LIT(lit);
        srid_t prev_up_unit_clause = up_reasons[var];
        up_reasons[var] = clause_index;

        // Replace this clause in the `unit_clauses` structure
        // This way, UP derivations stop at this unit clause
        for (int i = 0; i < unit_clauses_size; i++) {
          if (unit_clauses[i] == prev_up_unit_clause) {
            unit_clauses[i] = clause_index;
            break;
          }
        }
        break;
      default:
        set_unit_clause(lit, clause_index, GLOBAL_GEN);
    }
  } else {
    // The clause has at least two literals - add watch pointers

    /* [Note made on 10-02-2025]
      Typically, clauses are not added with "redundant" literals, meaning
      that if a unit `l` has already been set, `-l` won't appear in the
      clause. However, some procedures (such as `sr2drat`) do not
      perform this check, and will occasionally add clauses with redundant
      literals. Thus, we must scan the clause for two valid unassigned
      literals. (Along the way, we might discover that the clause is
      unit or false!)
    */

    int first_wp;
    uint lit_counter = 0;
    for (uint i = 0; i < clause_size && lit_counter < 2; i++) {
      int lit = clause[i];
      if (peval_lit_under_alpha(lit) != FF) {
        // Maintain the invariant that the wps are the first two literals
        if (i != lit_counter) {
          clause[i] = clause[lit_counter];
          clause[lit_counter] = lit;
        }

        add_wp_for_lit(lit, clause_index);
        if (lit_counter == 0) first_wp = lit;
        lit_counter++;
      }
    }

    switch (lit_counter) {
      case 0:
        derived_empty_clause = 1;
        mark_and_store_up_refutation(clause_index, gen);
        break;
      case 1:
        remove_wp_for_lit(first_wp, clause_index);
        set_unit_clause(first_wp, clause_index, GLOBAL_GEN);
        break;
      case 2: break;
      default: log_fatal_err("Bad unassigned counter: %d", lit_counter);
    }
  }


  // We don't have an immediate contradiction, so perform unit propagation
  srid_t falsified_clause = perform_up(GLOBAL_GEN);
  if (falsified_clause >= 0) {
    derived_empty_clause = 1;
    mark_and_store_up_refutation(falsified_clause, gen);
  }
}

// A clone of of assume_negated_clause() from global_data, but with added bookkeeping. 
// Returns 0 if assumption succeeded, -1 if contradiction found and LSR line emitted.
// Must be called when global up_state == GLOBAL_UP.
// Even when -1 is returned, the candidate clause is still "assumed".
static int assume_candidate_clause_and_perform_up(srid_t clause_index) {
  FATAL_ERR_IF(up_state != GLOBAL_UP, "up_state not GLOBAL_UP.");
  increment_state();

  int satisfied_lit = -1;
  int *clause_iter = get_clause_start_unsafe(clause_index);
  int *end = get_clause_end(clause_index);

  srid_t falsified_clause = -1;
  for (; clause_iter < end; clause_iter++) {
    int lit = *clause_iter;
    int var = VAR_FROM_LIT(lit);

    // Check if the literal is satisfied by prior UP
    // If so, then we have a contradiction
    int peval = peval_lit_under_alpha(lit);
    switch (peval) {
      case FF:
        // Mark the reason for an already-satisfied literal as assumed
        // This shortens UP derivations
        up_reasons[var] |= SRID_MSB;
        break;
      case UNASSIGNED:
        // Always set (the negations of) unassigned literals to true
        // unassume_candidate_clause() will unassign these
        assume_unit_literal(NEGATE_LIT(lit));
        break;
      case TT:
        // `lit` has been derived as true in the global partial assignment
        // Thus, if we assume the negation of `lit`, we would ultimately
        // end up with a UP refutation for whatever caused `lit` to be true
        // TODO: Find the shortest literal to use here later
        if (satisfied_lit == -1) {
          satisfied_lit = lit;
          falsified_clause = up_reasons[var];
        }
        break;
      default: log_fatal_err("Invalid peval_t value: %d", peval);
    }
  }

  // If we haven't satisfied the clause, we perform unit propagation
  if (falsified_clause == -1) {
    falsified_clause = perform_up(ASSUMED_GEN);
  }

  // If we have either satisfied the clause, or found a UP derivation, emit it
  if (falsified_clause != -1) {
    mark_and_store_up_refutation(falsified_clause, alpha_generation - GEN_INC);
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
  // First, address the unit literals set during new UP
  for (int i = candidate_unit_literals_index; i < unit_literals_size; i++) {
    int lit = unit_literals[i];
    int var = VAR_FROM_LIT(lit);

    // Clear the var's reason and generation (since they were derived during candidate UP)
    up_reasons[var] = -1;
    alpha[var] = 0;
  }

  // Now iterate through the clause and undo its changes
  int *clause_iter = get_clause_start(clause_index);
  int *end = get_clause_start(clause_index + 1);
  for (; clause_iter < end; clause_iter++) {
    int lit = *clause_iter;
    int var = VAR_FROM_LIT(lit);

    if (up_reasons[var] == -1) {
      // If the literal was originally unassigned, set its gen back to 0
      alpha[var] = 0;
    } else if (up_reasons[var] < 0) {
      // The literal was assumed, but not unassigned - undo its assumption bit
      up_reasons[var] ^= SRID_MSB;
    }
  }

  decrement_state();
}

static inline void add_RAT_marked_var(int marked_var) {
  INSERT_ARR_ELT_CONCAT(RAT_marked_vars, sizeof(int), marked_var);
}

static inline void clear_RAT_marked_vars(void) {
  for (uint i = 0; i < RAT_marked_vars_size; i++) {
    up_reasons[RAT_marked_vars[i]] ^= SRID_MSB;
  }

  RAT_marked_vars_size = 0;
}

// This is clone of assume_negated_clause_under_subst(), but with extra bookkeeping.
// In particular, we add any set literals to the unit_literals array, for UP purposes.
// Returns the same values as assume_negated_clause_under_subst().
// Sets the indexes values appropriately.
// Call when global up_state == CANDIDATE_UP.
// Sets the global up_state to RAT_UP.
static int assume_RAT_clause_under_subst(srid_t clause_index) {
  FATAL_ERR_IF(up_state != CANDIDATE_UP, "up_state not RAT_UP.");
  increment_state();

  /* If we encounter false literals under alpha, we mark their reasons as assumed
   * in the typical way, but we record which have been marked as assumed only for
   * the RAT clause. This allows us to shorten/detect tautology derivations.
   * However, these markings must be cleared before returning on any code path
   * and before doing normal UP derivation, since we want to record global and
   * candidate UP dependencies accurately.
   * 
   * We might want to do this work in unassume_RAT_clause(), but then UP would
   * have to case on an additional MSB32 bit or pass the dependency index to
   * detect when an assumed variable is a "stopping variable" (global or candidate)
   * or a "non-stopping variable" (RAT). To simplify matters, we clear the
   * RAT_marked_vars array before returning on any code path here. */
  RAT_marked_vars_size = 0;

  int *clause_ptr = get_clause_start(clause_index);
  int *end = get_clause_end(clause_index);
  for (; clause_ptr < end; clause_ptr++) {
    int lit = *clause_ptr;
    int mapped_lit = map_lit_under_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT:
        clear_RAT_marked_vars();
        return SATISFIED_OR_MUL;
      case SUBST_FF: break; // Ignore the literal
      default:;
        // If the mapped literal is unassigned under `alpha`, set it
        int mapped_var = VAR_FROM_LIT(mapped_lit);
        int mapped_peval = peval_lit_under_alpha(mapped_lit);
        switch (mapped_peval) {
          case FF:
            // We can shorten tautology derivations by marking the reason as assumed.
            // However, we ignore this assumption when doing RAT UP derivations.
            // Only mark literals whose reasons are not already marked
            if (up_reasons[mapped_var] >= 0) {
              up_reasons[mapped_var] |= SRID_MSB;
              add_RAT_marked_var(mapped_var);
            }
            break;
          case TT:;
            // To satisfy the clause, we needed to have derived the truth value of
            // the mapped_lit. Mark the derivation, but do no further checking.
            int reason = up_reasons[mapped_var];
            clear_RAT_marked_vars();
            if (reason >= 0) {
              // Don't store anything in the LSR line because the derivation only
              // includes things in the global and candidate UPs.
              // The RAT check (the caller) will store the (-clause) in the line.
              // TODO????
              mark_up_derivation(reason);
            }
            return SATISFIED_OR_MUL;
          case UNASSIGNED:
            assume_unit_literal(NEGATE_LIT(mapped_lit));
            break;
          default: log_fatal_err("Corrupted peval value: %d", mapped_peval);
        }
    }
  }

  clear_RAT_marked_vars();
  return 0;
}

// Call when global state == RAT_UP.
// Decrements state back to CANDIDATE_UP.
static void unassume_RAT_clause(srid_t clause_index) {
  FATAL_ERR_IF(up_state != RAT_UP, "up_state not RAT_UP.");

  // Clear the UP reasons for the variables set during RAT UP
  for (int i = RAT_unit_literals_index; i < unit_literals_size; i++) {
    int lit = unit_literals[i];
    int var = VAR_FROM_LIT(lit);
    up_reasons[var] = -1; // Clear the reason (gen will clear via bumping)
  }

  decrement_state();
}

////////////////////////////////////////////////////////////////////////////////

static void uncommit_clause_and_set_as_candidate(void) {
  // Examine the current clause and see if it is
  //   - Empty; ignore
  //   - A unit clause: unassign its unit and all units derived from this one
  srid_t cc_id = CLAUSE_ID_FROM_LINE_NUM(current_line);

  int *clause_ptr = get_clause_start(cc_id);
  int *clause_end = get_clause_end(cc_id);
  new_clause_size = (int) (clause_end - clause_ptr);

  if (new_clause_size == 0) return;

  // Unassign the units
  int lit = clause_ptr[0];
  int var = VAR_FROM_LIT(lit);

  // The variable is unit because of this clause, undo its UP changes
  if (up_reasons[var] == cc_id) {
    // log_msg(VL_NORMAL, "c Unassigning unit literal %d\n", TO_DIMACS_LIT(lit));
    // Scan backwards for the matching unit literal
    int unit_idx;
    for (unit_idx = unit_literals_size - 1; unit_idx >= 0; unit_idx--) {
      int unit_lit = unit_literals[unit_idx];
      int unit_var = VAR_FROM_LIT(unit_lit);
      alpha[unit_var] = 0;
      up_reasons[unit_var] = -1;
      if (unit_lit == lit) {
        break;
      }
    }

    unit_idx = MAX(unit_idx, 0);
    unit_clauses_size = unit_idx;
    unit_literals_size = unit_idx;
    global_up_literals_index = unit_idx;
  }

  // Since we won't consider this clause again, remove its watch pointers
  if (new_clause_size > 1) {
    remove_wp_for_lit(lit, cc_id);
    remove_wp_for_lit(clause_ptr[1], cc_id);
  }
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
  lines_min_max_clauses_to_check = xmalloc(
    num_parsed_add_lines * sizeof(min_max_clause_t));
}

static void store_clause_check_range(srid_t line_num) {
  compute_min_max_clause_to_check(line_num);
  perform_clause_first_last_update(CLAUSE_ID_FROM_LINE_NUM(line_num)); 

  min_max_clause_t *mm = &lines_min_max_clauses_to_check[line_num];
  mm->min_clause = min_clause_to_check;
  mm->max_clause = max_clause_to_check;
  log_msg(VL_VERBOSE, "[line %lld] Storing clause range %lld to %lld",
    line_num + 1, TO_DIMACS_CLAUSE(min_clause_to_check),
    TO_DIMACS_CLAUSE(max_clause_to_check));
}

static void set_min_max_clause_to_check(void) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    min_clause_to_check =
      lines_min_max_clauses_to_check[current_line].min_clause;
    max_clause_to_check =
      lines_min_max_clauses_to_check[current_line].max_clause;
  }
}

static void emit_RAT_UP_failure_error(srid_t clause_index) {
  log_err("[line %lld] No UP contradiction for RAT clause %lld.",
    current_line + 1, TO_DIMACS_CLAUSE(clause_index));

  // Print tons of information if verbosity is high enough
  if (verbosity_level > VL_NORMAL) {
    log_raw(VL_VERBOSE, "\n//////////////////////////////////////////////\n\n");
    log_raw(VL_VERBOSE, "c The current candidate clause: ");
    dbg_print_clause(CLAUSE_ID_FROM_LINE_NUM(current_line));

    log_raw(VL_VERBOSE, "c The failing RAT clause: ");
    dbg_print_clause(clause_index);

    log_raw(VL_VERBOSE, "c The RAT clause, under the subst: ");
    int *clause_iter = get_clause_start(clause_index);
    int *end = get_clause_end(clause_index);
    for (; clause_iter < end; clause_iter++) {
      int lit = *clause_iter;
      int mapped_lit = map_lit_under_subst(lit);
      switch (mapped_lit) {
        case SUBST_TT: log_raw(VL_VERBOSE, "TT "); break;
        case SUBST_FF: log_raw(VL_VERBOSE, "FF "); break;
        default: log_raw(VL_VERBOSE, "%d ", TO_DIMACS_LIT(mapped_lit));
      }
    }
    log_raw(VL_VERBOSE, "0\n");

    log_raw(VL_VERBOSE, "\nc The active partial assignment:\n");
    dbg_print_assignment();

    log_raw(VL_VERBOSE, "\nc The active substitution:\n");
    dbg_print_subst();

    // Now scan through the unit literals and list how they became unit
    if (verbose_errors) {
      log_raw(VL_VERBOSE, "\nc The unit literals and why they are unit\n");
      log_raw(VL_VERBOSE, "c Printed in order of their derivations\n");
      for (uint i = 0; i < unit_literals_size; i++) {
        int lit = unit_literals[i];
        log_raw(VL_VERBOSE, "c Literal %d is unit due to ", TO_DIMACS_LIT(lit));

        srid_t reason = up_reasons[VAR_FROM_LIT(lit)];
        if (reason == -1) {
          log_raw(VL_VERBOSE, "being assumed in the negation of the candidate or RAT clause.\n");
        } else if (reason < 0) {
          srid_t clause = reason ^ SRID_MSB;
          log_raw(VL_VERBOSE, "clause %lld, but is currently assumed in the negation of the candidate or RAT clause: ",
            TO_DIMACS_CLAUSE(clause));
          dbg_print_clause(clause);
        } else {
          log_raw(VL_VERBOSE, "clause %lld: ", TO_DIMACS_CLAUSE(reason));
          dbg_print_clause(reason);
        }
      }
    }
  }

  exit(1);
}

static void check_RAT_clause(srid_t clause_index) {
  switch (reduce_clause_under_subst(clause_index)) {
    case NOT_REDUCED:
    case SATISFIED_OR_MUL:
      return;
    case REDUCED:
      add_RAT_clause_hint(clause_index);

      // If the RAT clause is not satisfied by alpha, do UP
      if (assume_RAT_clause_under_subst(clause_index) != SATISFIED_OR_MUL) {
        srid_t falsified_clause = perform_up(alpha_generation);
        if (falsified_clause == -1) emit_RAT_UP_failure_error(clause_index);
        mark_up_derivation(falsified_clause);
        store_RAT_dependencies(falsified_clause);
      }
      unassume_RAT_clause(clause_index);
      alpha_generation += GEN_INC; // Clear this round of RAT units from alpha
      break;
    case CONTRADICTION:
      log_fatal_err("[line %lld] Reduced clause %lld claims contradiction.",
        current_line + 1, TO_DIMACS_CLAUSE(clause_index));
    default:
      log_fatal_err("[line %lld] Clause %lld corrupted reduction value %d.",
        current_line + 1, TO_DIMACS_CLAUSE(clause_index),
        reduce_clause_under_subst(clause_index)); 
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
    log_msg(VL_VERBOSE, "[line %lld] Clause %lld was RUP, moving to next line",
      current_line + 1, TO_DIMACS_CLAUSE(cc_index));
    goto candidate_valid;
  }

  // Since we didn't derive UP contradiction, the clause should be nonempty
  FATAL_ERR_IF(new_clause_size == 0, "Didn't derive empty clause.");

  // Now we turn to RAT checking - minimize and assume the witness
  max_RAT_line = MAX(max_RAT_line, current_line);
  int must_find_new_pivot = minimize_witness();
  assume_subst(current_line);
  if (must_find_new_pivot) find_new_pivot_for_witness(cc_index);
  set_min_max_clause_to_check();

  // Now do RAT checking between min and max clauses to check (inclusive)
  log_msg(VL_VERBOSE, "[line %lld] Not RUP, checking clauses %lld to %lld", 
    current_line + 1, TO_DIMACS_CLAUSE(min_clause_to_check),
    TO_DIMACS_CLAUSE(max_clause_to_check));
  int *clause, *next_clause = get_clause_start(min_clause_to_check);
  int clause_size;
  for (srid_t i = min_clause_to_check; i <= max_clause_to_check; i++) {
    if (can_skip_clause(i)) continue;
    check_RAT_clause(i);
  }

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
    to a RAT check. The recorded hint ID is the ID of the candidate itself.
  */
  check_RAT_clause(cc_index);

  print_or_store_lsr_line(old_alpha_gen);

  // Congrats: the line checked! Undo the changes made to the data structures
candidate_valid:
  unassume_candidate_clause(cc_index);

  if (ch_mode == FORWARDS_CHECKING_MODE) {
    perform_clause_first_last_update(CLAUSE_ID_FROM_LINE_NUM(current_line));
    current_line++;
    add_wps_and_perform_up(get_effective_formula_size() - 1, old_alpha_gen);
  }
}

static void remove_wps_from_user_deleted_clauses(srid_t clause_id) {
  srid_t line = LINE_NUM_FROM_CLAUSE_ID(clause_id);
  srid_t *dels = get_bcu_deletions_start(line);
  srid_t *del_end = get_bcu_deletions_end(line);

  if (dels == del_end) return;

  for (; dels < del_end; dels++) {
    srid_t del_id = *dels;
    int *del_clause = get_clause_start(del_id);
    remove_wp_for_lit(del_clause[0], del_id);
    remove_wp_for_lit(del_clause[1], del_id);
    soft_delete_clause(del_id);
  }
}

static void restore_wps_for_user_deleted_clauses(srid_t clause_id) {
  srid_t line = LINE_NUM_FROM_CLAUSE_ID(clause_id);
  srid_t *dels = get_bcu_deletions_start(line);
  srid_t *del_end = get_bcu_deletions_end(line);

  if (dels == del_end) return;

  for (; dels < del_end; dels++) {
    srid_t del_id = *dels;
    soft_undelete_clause(del_id);
    int *del_clause = get_clause_start(del_id);
    add_wp_for_lit(del_clause[0], del_id);
    add_wp_for_lit(del_clause[1], del_id);
  }
}

static void prepare_next_line_for_backwards_checking(void) {
  srid_t cc_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
  do {
    restore_wps_for_user_deleted_clauses(cc_id);
    current_line--;
    uncommit_clause_and_set_as_candidate();
    ra_commit_range(&deletions);
    cc_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
  } while (IS_UNUSED_LUI(clauses_lui[cc_id]));

  srid_t cc_rat_hints_index = RAT_HINTS_IDX_FROM_LINE_NUM(current_line);
  ra_commit_empty_ranges_until(&hints, cc_rat_hints_index);
}

static line_type_t prepare_next_line(void) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    prepare_next_line_for_backwards_checking();
  } else {
    // For forwards checking, we clear the stored hints
    ra_reset(&hints);
    ra_reset(&deletions);
    num_RAT_hints = 0;
  }

  if (p_strategy == PS_EAGER) return ADDITION_LINE;
  else                        return parse_dsr_line();
}

static void add_wps_and_up_initial_clauses(void) {
  srid_t c;
  for (c = 0; c < num_cnf_clauses; c++) {
    add_wps_and_perform_up(c, 0);
  }

  if (ch_mode == FORWARDS_CHECKING_MODE) return;

  // TODO: Encapsulate better
  // TODO: No need to RESIZE from formula_size when this is the largest it'll be
  current_line = num_parsed_add_lines - 1; // Subtract 1 to 0-index it
  resize_sr_trim_data();
  resize_last_used_ids();
  alloc_min_max_clauses_to_check();
  uncommit_clause_and_set_as_candidate();

  current_line = 0;

  // Add implied unit clauses, clause by clause
  // Stop when we finally derive the empty clause
  for (; c < formula_size - 1 && !derived_empty_clause; c++) {
    store_clause_check_range(current_line);
    current_line++;
    remove_wps_from_user_deleted_clauses(c);
    add_wps_and_perform_up(c, 0);
  }

  FATAL_ERR_IF(!derived_empty_clause,
    "The empty clause could not be derived (even if it was in the proof?).");

  log_msg(VL_VERBOSE,
    "A UP refutation was successfully found for the empty clause.");

  remove_wps_from_user_deleted_clauses(c); // TODO: Fix this
  c--; // `c` stored one more than the ID of the clause that derived empty

  logc("Empty was supposedly derived after adding clause %lld",
    TO_DIMACS_CLAUSE(c));

  // Discard the rest of the formula, if necessary
  if (c < formula_size - 1) {
    discard_formula_after_clause(c);
    num_parsed_add_lines = current_line + 1;
  }
}

static void check_proof(void) {
  up_state = GLOBAL_UP;
  alpha_generation = GEN_INC;
  timer_record(&timer, TIMER_LOCAL);

  add_wps_and_up_initial_clauses();

  // TODO encapsulate better later
  // TODO fix with resize_sr_trim_data()
  // TODO the (+1) is a little too much?
  // TODO Go off line num and not formula size?
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    if (formula_size > line_num_RAT_hints_alloc_size) {
      line_num_RAT_hints = xrecalloc(line_num_RAT_hints,
        line_num_RAT_hints_alloc_size * sizeof(uint),
        (formula_size + 1) * sizeof(uint));
      line_num_RAT_hints_alloc_size = formula_size + 1;
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

  print_proof_checking_result();
  timer_print_elapsed(&timer, TIMER_LOCAL, "Proof checking");

  print_stored_lsr_proof();
  print_valid_formula_if_requested();
}

////////////////////////////////////////////////////////////////////////////////

int main(int argc, char **argv) {
  if (argc == 1) {
    print_short_help_msg(stdout);
    return 0;
  }

  p_strategy = PS_EAGER;
  cli_opts_t cli;
  int forward_set = 0, backward_set = 0;
  cli_init(&cli);
  
  // For emitting VALID formulas to a file, upon request
  int emit_valid_formula_opt_set = 0;
  char emit_valid_formula_file_path[MAX_FILE_PATH_LEN];
  emit_valid_formula_file_path[MAX_FILE_PATH_LEN - 1] = '\0';

  // Parse CLI arguments
  int ch;
  cli_res_t cli_res;
  while ((ch = getopt_long(argc, argv, OPT_STR, longopts, NULL)) != -1) {
    switch (ch) {
      case FORWARD_OPT:
        FATAL_ERR_IF(backward_set, "Cannot set both backward and forward checking.");
        FATAL_ERR_IF(forward_set, "Forward checking was set twice.");
        forward_set = 1;
        p_strategy = PS_STREAMING; // TODO: Make eager possible
        ch_mode = FORWARDS_CHECKING_MODE;
        break;
      case BACKWARD_OPT:
        FATAL_ERR_IF(forward_set, "Cannot set both backward and forward checking.");
        FATAL_ERR_IF(backward_set, "Backward checking was set twice.");
        backward_set = 1;
        ch_mode = BACKWARDS_CHECKING_MODE;
        break;
      case 0: // Defined long options without a corresponding short option
        if (long_help_msg_flag) {
          print_long_help_msg(stdout);
          return 0;
        } else if (emit_valid_formula) {
          FATAL_ERR_IF(emit_valid_formula_opt_set,
            "Cannot set the emit-valid-formula option twice.");
          emit_valid_formula_opt_set = 1;
          strncpy(emit_valid_formula_file_path, optarg, MAX_FILE_PATH_LEN - 1);
        } else {
          log_fatal_err("Unimplemented long option.");
        }
        break;
      default:
        cli_res = cli_handle_opt(&cli, ch, optopt, optarg);
        switch (cli_res) {
          case CLI_UNRECOGNIZED:
            log_err("Unimplemented option.");
            print_short_help_msg(stderr);
            return 1;
          case CLI_HELP_MESSAGE:
            print_short_help_msg(stderr);
            return 0;
          case CLI_SUCCESS: break;
          default: log_fatal_err("Corrupted CLI result: %d", cli_res);
        }
    }
  }

  switch (argc - optind) {
    case 0:
      FATAL_ERR_IF(!cli_is_name_opt_set(&cli), "No file prefix provided.");
      cli_concat_path_extensions(&cli, ".cnf", ".sr", ".lsr");
      break;
    case 1:
      FATAL_ERR_IF(cli_is_dir_opt_set(&cli),
        "Cannot provide a directory without a DSR file path.");

      if (cli_is_name_opt_set(&cli)) {
        cli_concat_path_extensions(&cli, ".cnf", argv[optind], ".lsr");
      } else {
        cli.cnf_file_path = argv[optind];
        cli.dsr_file_path = NULL;
        cli.lsr_file_path = NULL;
      }
      break;
    case 2:
      if (cli_is_dir_opt_set(&cli) || cli_is_name_opt_set(&cli)) {
        cli_concat_path_extensions(&cli, argv[optind], argv[optind+1], ".lsr");
      } else {
        cli.cnf_file_path = argv[optind];
        cli.dsr_file_path = argv[optind + 1];
        cli.lsr_file_path = NULL;
      }
      break;
    case 3:
      if (cli_is_dir_opt_set(&cli) || cli_is_name_opt_set(&cli)) {
        cli_concat_path_extensions(&cli,
          argv[optind], argv[optind + 1], argv[optind + 2]);
      } else {
        cli.cnf_file_path = argv[optind];
        cli.dsr_file_path = argv[optind + 1];
        cli.lsr_file_path = argv[optind + 2];
      }
      break;
    default:
      log_err("Invalid number of non-option arguments: %d.", argc - optind);
      print_short_help_msg(stderr);
      return 1;
  }

  // Open the files first, to ensure we don't do work unless they exist
  logc("CNF file path: %s", cli.cnf_file_path);
  FILE *cnf_file = xfopen(cli.cnf_file_path, "r");
  
  if (cli.dsr_file_path == NULL) {
    FATAL_ERR_IF(p_strategy == PS_EAGER,
      "Cannot use eager strategy with `stdin` as the DSR file.");
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
    lsr_file = xfopen(cli.lsr_file_path, "w");
  }

  if (emit_valid_formula_opt_set) {
    logc("Emitting a VALID formula to: %s",
      emit_valid_formula_file_path);
    emit_valid_formula_file = xfopen(emit_valid_formula_file_path, "w");
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

  timer_init(&timer);
  timer_record(&timer, TIMER_GLOBAL);

  timer_record(&timer, TIMER_LOCAL);
  parse_cnf(cnf_file);
  timer_print_elapsed(&timer, TIMER_LOCAL, "Parsing the CNF");

  prepare_dsr_trim_data();
  check_proof();

  timer_print_elapsed(&timer, TIMER_GLOBAL, "Total runtime");
  return 0;
}