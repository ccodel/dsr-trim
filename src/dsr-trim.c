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

#define INIT_LIT_WP_ARRAY_SIZE          (4)

// When setting literals "globally" under initial unit propagation, we use the
// largest possible generation value.
#define GLOBAL_GEN   (LLONG_MAX)
#define ASSUMED_GEN  (LLONG_MAX - 1)

#define MARK_USER_DELETED_LUI(x)        ((x) | SRID_MSB)
#define IS_USER_DELETED_LUI(x)          (((x) & SRID_MSB) && ((x) != -1))
#define LUI_FROM_USER_DELETED_LUI(x)    ((x) & (~SRID_MSB))
#define IS_UNUSED_LUI(x)                ((x) & SRID_MSB)

#define UP_HINTS_IDX_FROM_LINE_NUM(line_num)  \
  ((((num_parsed_add_lines - 1) - (line_num)) * 2) + 1)

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

static int candidate_unit_clauses_index = 0;
static int RAT_unit_clauses_index = 0;

// Index pointing at the "unprocessed" global UP literals
static int global_up_literals_index = 0;

static int candidate_assumed_literals_index = 0;
static int candidate_unit_literals_index = 0;
static int RAT_assumed_literals_index = 0;
static int RAT_unit_literals_index = 0;

// Generations for clauses involved in UP derivations. Indexed by clauses.
static llong *dependency_markings = NULL;
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
// static llong generation_before_line_checking = 0;
// static srid_t up_falsified_clause = -1; // Set by unit propagation, -1 if none found

// Because deletion lines in the DSR format identify a clause to be deleted,
// and not a clause ID, we use a hash table to store clause IDs, where the
// hash is a commutative function of the literals. That way, permutations of
// the clause will hash to the same thing.

// The clause ID hash table, used for checking deletions.
static ht_t clause_id_ht;

#define INIT_CLAUSE_MULT_SIZE  (4)

// Counts the number of times a clause appears multiple times in the formula.
typedef struct clause_multiplicity {
  srid_t clause_id;
  uint multiplicity;
} clause_mult_t;

static clause_mult_t *clause_mults;
static uint clause_mults_alloc_size = 0;
static uint clause_mults_size = 0;

// Forward declare (TODO: Figure out organization laterj)
static void add_wp_for_lit(int lit, srid_t clause);
static void remove_wp_for_lit(int lit, srid_t clause);

/*
 * Backwards checking:
 */

// The highest 0-indexed line ID that each clause appears in, in the proof.
// By default, initialized to -1.
// These IDs are set during backwards checking.
// First, any clause that appears in the UP refutation of the empty clause
// is marked.
static srid_t *clause_last_used_id = NULL;
static uint clause_last_used_id_alloc_size = 0;

// Stores the index into each unit literal's watch pointer list
// to reduce duplicate checks on SAT/unit clauses during backwards checking
// unit propagation.
//
// Is kept as NULL if not doing backward checking.
// See `set_unit_literal`.
static int *unit_literals_wp_up_indexes = NULL;

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

/*

Notes from 10/31:

- We assume that the clause IDs are strictly monotonically increasing,
  as a matter of data structure design. In order to accomodate for
  non-increasing clause IDs, we would need to have an actual 2D array
  for the literals, or we have an {index, size} pair for each clause.
  If we do try to keep a 1D flattened array,
  garbage collection would be more challenging, because clauses can
  "overwrite" other clauses, so there's no guarantee that we can
  re-order the clauses.
    - This is actually an extremely safe assumption, because the DSR files
      don't refer to clause IDs at all. So we can safely assume that the
      candidate clauses have IDs that are not only monotonically increasing,
      but increase by 1 each time.

- Refactor needed for how the hints are computed and stored.
  Right now the API is hard-coded for emitting proof lines as they
  are checked. But it might be faster to store the hints as they are
  computed, and then read them off into IO. (It might also be faster
  to store all the hints for *all* lines during forward checking,
  and then emit them at the end.  But this probably gives only marginal
  benefits over emitting line-by-line, and with the downside of
  storing all the hints in memory anyways.)
  In any case, redo the API to store/calculate the line/hints,
  but emit/move on otherwise.
    - Another thought: use multithreading to read the proof file
      and another to check the lines. But this introduces mutexes/
      synch problems, which the underlying IO system might take care of
      anyway (i.e., prefetching blocks, etc.)
*/


////////////////////////////////////////////////////////////////////////////////

// Help messages and command line options

#define FORWARD_OPT   ('f')
#define BACKWARD_OPT  ('b')
#define OPT_STR       ("bd:efhn:qsv")

// A flag that is set when the CLI arguments request the longer help message.
static int long_help_msg_flag = 0;

// The set of "long options" for CLI argument parsing. Used by `getopt_long()`.
static struct option const longopts[] = {
  { "help", no_argument, &long_help_msg_flag, 1 },
  { "dir", required_argument, NULL, DIR_OPT },
  { "name", required_argument, NULL, NAME_OPT },
  { "eager", no_argument, NULL, EAGER_OPT },
  { "streaming", no_argument, NULL, STREAMING_OPT },
  { "forward", no_argument, NULL, FORWARD_OPT },
  { "backward", no_argument, NULL, BACKWARD_OPT },
  { NULL, 0, NULL, 0 }  // The array of structs must be NULL/0-terminated
};

static void print_short_help_msg(FILE *f) {
  char *usage_str = "Usage: ./dsr-trim [OPTIONS] <cnf> <dsr> [lsr]\n";
  fprintf(f, "%s", usage_str);
}

static void print_long_help_msg(FILE *f) {
  char *usage_str = "Usage: ./dsr-trim [OPTIONS] <cnf> <dsr> [lsr]\n";
  fprintf(f, "%s", usage_str);
}

////////////////////////////////////////////////////////////////////////////////

// Returns 1 if there is another DSR line to be checked.
static int has_another_dsr_line(void) {
  if (p_strategy == PS_EAGER) {
    if (ch_mode == BACKWARDS_CHECKING_MODE) {
      return (current_line > 0);
    } else {
      // We parsed until we found the empty clause (if there was one)
      // So checking the last line corresponds with deriving the empty clause
      return LINE_ID_FROM_LINE_NUM(current_line) < num_parsed_add_lines;
    }
  } else {
    return !derived_empty_clause && has_another_line(dsr_file);
  }
}

static inline srid_t *get_UP_hints_start(srid_t line_num) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    srid_t idx = UP_HINTS_IDX_FROM_LINE_NUM(line_num);
    return ra_get_range_start(&hints, idx);
  } else {
    return ra_get_range_start(&hints, 1);
  }
}

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

static srid_t *get_bcu_deletions_start(srid_t line_num) {
  return ra_get_range_start(&bcu_deletions, line_num);
}

static srid_t *get_bcu_deletions_end(srid_t line_num) {
  return ra_get_range_start(&bcu_deletions, line_num + 1);
}

static inline void prepare_user_deletions(void) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    ra_commit_range(&bcu_deletions);
  } else {
    ra_reset(&deletions);
  }
}

// Assumes only called during backwards checking.
// Returns `1` if the LUI is adjusted. Returns `0` otherwise.
static inline uint adjust_clause_lui(srid_t clause_id) {
  srid_t lui = clause_last_used_id[clause_id];

  if (IS_USER_DELETED_LUI(lui)) {
    FATAL_ERR_IF(current_line > LUI_FROM_USER_DELETED_LUI(lui),
      "[line %lld] Clause %lld was used in UP after it was deleted on line %lld",
      current_line, TO_DIMACS_CLAUSE(clause_id), LUI_FROM_USER_DELETED_LUI(lui));
  }

  if (IS_UNUSED_LUI(lui)) {
    clause_last_used_id[clause_id] = current_line;
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
    if (IS_USER_DELETED_LUI(clause_last_used_id[i])) {
      log_raw(VL_NORMAL, "d%d ", LUI_FROM_USER_DELETED_LUI(clause_last_used_id[i]));
    } else if (clause_last_used_id[i] == -1) {
      log_raw(VL_NORMAL, "-1 ");
    } else {
      log_raw(VL_NORMAL, "%d ", CLAUSE_ID_FROM_LINE_NUM(clause_last_used_id[i]));
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
    if (!IS_UNUSED_LUI(clause_last_used_id[c])) {
      clause_id_map[c] = map_counter;
      map_counter++;
    }
  }
}

static inline void resize_last_used_ids(void) {
  FATAL_ERR_IF(ch_mode != BACKWARDS_CHECKING_MODE,
    "Last used IDs are only resized during backwards checking.");
  RESIZE_MEMSET_ARR(clause_last_used_id,
    clause_last_used_id_alloc_size, formula_size, sizeof(srid_t), 0xff);
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
    if (LUI_FROM_USER_DELETED_LUI(clause_last_used_id[cp]) >= current_line) {
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

/*static void verify_nrhs(uint id) {
  uint sum = 0;
  for (int i = 0; i < num_parsed_add_lines; i++) {
    if (get_num_RAT_hints(i) > 0) {
      logc("[line %lld, formula_size %lld, %lld] Bad sum with id %d", current_line, formula_size, num_parsed_add_lines, id);
      exit(1);
    }
  }
} */

/**
 * @brief Prints the initial set of clause deletions, before a single
 *        addition line is printed.
 * 
 * During backwards checking, any clause that isn't used in the entire
 * proof will have its `clause_last_used_id` set to `-1`. This function
 * loops through all CNF formula clauses and deletes the unused ones.
 */
static void print_initial_clause_deletions(void) {
  FATAL_ERR_IF(ch_mode != BACKWARDS_CHECKING_MODE,
    "Inital clause deletions are only generated during backwards checking.");

  write_lsr_deletion_line_start(lsr_file, num_cnf_clauses);
  for (srid_t c = 0; c < num_cnf_clauses; c++) {
    if (IS_UNUSED_LUI(clause_last_used_id[c])) {
      write_clause_id(lsr_file, TO_DIMACS_CLAUSE(c)); 
    }
  }
  write_sr_line_end(lsr_file); 
}

// Prints the specified clause from the formula to the LSR proof file.
// The caller must ensure the clause is not deleted from the formula.
static void print_clause(srid_t clause_id) {
  int *clause = get_clause_start_unsafe(clause_id);
  const int size = get_clause_size(clause_id);

  /*
    Since literals might have gotten reordered during watch pointer stuff,
    we need to recover the pivot from the witness (an invariant!) and then
    we sort the remaining literals 
  */

  // Make the pivot be the first literal by swapping it with the current first
  int pivot = (get_witness_start(LINE_NUM_FROM_CLAUSE_ID(clause_id)))[0];
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
  qsort(clause + 1, size - 1, sizeof(int), absintcmp);

  // Now actually print the clause
  for (int i = 0; i < size; i++) {
    const int lit = clause[i];
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
  if (witness_size <= 1) return;

  /* Because witness minimization might map literals to true/false that are in
   * the "substitution portion", we do a two-pass over that part to first print
   * the true/false mapped literals, and then the non-trivial mappings.       */

  int *mappings_start = NULL;
  int seen_pivot_divider = 0;
  int num_skipped_mapped_lits = 0;

  int tmp_pivot = *iter;
  write_lit(lsr_file, TO_DIMACS_LIT(tmp_pivot));
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
      if (lit == tmp_pivot) {
        seen_pivot_divider = 1;
        mappings_start = iter + 1;
      }

      write_lit(lsr_file, TO_DIMACS_LIT(lit));
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

  if (num_skipped_mapped_lits == 0) return;

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
 * @param hint The stored hint, under the naive mapping, in DIMACS form.
 */
static inline void print_mapped_hint(srid_t hint) {
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
 * @brief Prints deletions supplied by the user, that lie before the line.
 * 
 * @param line_num 
 * @return The number of deletions printed
 */
static int print_deletions(srid_t line_num) {
  int num_printed = 0;
  srid_t *del_iter = get_deletions_start(line_num);
  srid_t *del_end = get_deletions_end(line_num);
  for (; del_iter < del_end; del_iter++) {
    srid_t c = *del_iter;
    print_mapped_hint(TO_DIMACS_CLAUSE(c));
    num_printed++;
  }

  return num_printed;
}

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

// Prints the accumulated LSR line, according to UP and clause dependencies.
// Should be printed before incrementing the generation.
static void print_lsr_line(srid_t line_num, srid_t printed_line_id) {
  // TODO Perhaps print deletions here?

  srid_t clause_id = CLAUSE_ID_FROM_LINE_NUM(line_num);
  write_lsr_addition_line_start(lsr_file, printed_line_id);
  print_clause(clause_id);

  // If there are no RAT hint groups, then no need to print a witness
  int nrh = get_num_RAT_hints(line_num);
  if (nrh > 0) {
    print_witness(line_num);
  }

  write_lit(lsr_file, 0); // Separator between (clause + witness) and rest
  print_hints(line_num);
  write_sr_line_end(lsr_file); // Cap the end of the line with a '0'
}

static void print_lsr_deletion_line(void) {
  // TODO: THIS NEEDS TO BE REFACTORED
  return;
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
 * @param[out] hp
 * @param[out] bp
 * @param[out] bi
 * @return The clause index of a matching clause that comes before this one,
 *         or `-1` if no such clause is found.
 */
static srid_t find_hashed_clause(srid_t ci, uint *hp, htb_t **bp, uint *bi) {
  int *clause = get_clause_start_unsafe(ci);
  uint hash = hash_clause(ci);
  if (hp != NULL) *hp = hash;
  htb_t *bucket = ht_get_bucket(&clause_id_ht, hash);
  const uint bucket_size = bucket->size;

  if (bucket_size == 0) return -1;

  // Iterate through all clauses in this bucket and try to find a match
  int *matching_clause;
  hte_t *entries = bucket->entries;
  for (int i = 0; i < bucket_size; i++) {
    srid_t possible_match = entries[i].data;

    // First approximation: see if the sizes and hashes match
    const int match_size = get_clause_size(possible_match);
    if (match_size == new_clause_size) {
      // Second approximation: see if the hashes match
      uint match_hash = hash_clause(possible_match);
      if (match_hash == hash) {
        // Most clauses are small, so O(n^2) search is good enough
        // Note that the literals necessarily aren't sorted, because of wps
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

static void add_clause_to_ht(srid_t clause_index) {
  uint hash = hash_clause(clause_index);
  add_hashed_clause_to_ht(clause_index, hash);
}

// Adds one to the mult counter, or if one isn't there for `clause_index`,
// sets the mult to `1`. (Single occurrence clauses don't get added.)
// Essentially, the `mult` counts the additional copies of the clause.
static void add_clause_mult(srid_t clause_index) {
  for (int i = 0; i < clause_mults_size; i++) {
    if (clause_mults[i].clause_id == clause_index) {
      clause_mults[i].multiplicity++;
      return;
    }
  }

  // Not found - insert a new mult in the back
  RESIZE_ARR_CONCAT(clause_mults, sizeof(clause_mult_t));
  clause_mults[clause_mults_size].clause_id = clause_index;
  clause_mults[clause_mults_size].multiplicity = 1;
  clause_mults_size++;
}

// Returns the number of remaining copies (after the decrease).
// Returns 0 if the clause is not found (meaning it has multiplicity of 1).
static uint decrease_clause_mult(srid_t clause_index) {
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
 * the hash table. During backwards checking, the `clause_last_used_id`
 * is updated instead.
 * 
 * The caller must ensure that the newly parsed clause has at least two
 * literals (we don't delete the empty clause or unit clauses).
 */
static void delete_parsed_clause(void) {
  htb_t *bucket;
  uint bucket_index;
  srid_t clause_match =
    find_hashed_clause(formula_size, NULL, &bucket, &bucket_index);

  if (clause_match == -1) {
    dbg_print_clause(formula_size); // TODO remove
    FATAL_ERR_IF(clause_match == -1, "No matching clause found for deletion.");
  }

  // Check that the matching clause isn't a global unit
  // If it is, error, since we don't want to unroll and re-run UP
  for (int i = 0; i < unit_clauses_size; i++) {
    FATAL_ERR_IF(unit_clauses[i] == clause_match,
      "Cannot delete clause %d, as it is a global unit.",
      TO_DIMACS_CLAUSE(clause_match));
  }

  // If we still have copies of the clause, nothing to do with the hash table
  if (decrease_clause_mult(clause_match) != 0) return;

  ht_remove_at_index(bucket, bucket_index);
  store_user_deletion(clause_match);

  // Actual deletion in the formula differs based on the checking mode
  // TODO (and the parsing strategy)
  switch (ch_mode) {
    case FORWARDS_CHECKING_MODE:;
      logc("ALERT: Forwards checking mode deletion");
      int *clause_match_ptr = get_clause_start_unsafe(clause_match);
      remove_wp_for_lit(clause_match_ptr[0], clause_match);
      remove_wp_for_lit(clause_match_ptr[1], clause_match);
      delete_clause(clause_match);
      break;
    case BACKWARDS_CHECKING_MODE:
      resize_last_used_ids();
      srid_t lui = MARK_USER_DELETED_LUI(num_parsed_add_lines);
      clause_last_used_id[clause_match] = lui;
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

  // Check if a matching clause was found
  if (clause_match == -1) {
    add_hashed_clause_to_ht(ci, hash);
  } else {
    add_clause_mult(clause_match);
  }

  return clause_match;
}

////////////////////////////////////////////////////////////////////////////////

// Parses the next DSR line. If it's a deletion line, the clause is deleted.
// Otherwise, the new candidate clause and the witness are parsed and stored.
// Returns ADDITION_LINE or DELETION_LINE for the line type.
// Errors and exits if a read error is encountered.
static inline int parse_dsr_line(void) {
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
      print_lsr_deletion_line(); // TODO refactor with deletions
      parse_sr_clause_and_witness(dsr_file, num_parsed_add_lines);
      srid_t possible_match = add_clause_to_ht_or_inc_mult();
      if (possible_match != -1) {
        formula_size -= 1;
        lits_db_size -= new_clause_size;
        line_type = DELETION_LINE;
        ra_uncommit_range(&witnesses);
      } else {
        prepare_user_deletions();
        num_parsed_add_lines++;
      }
      break;
    default:
      log_fatal_err("Corrupted line type: %d", line_type);
  }

  return line_type;
}

static void parse_entire_dsr_file(void) {
  FATAL_ERR_IF(p_strategy != PS_EAGER,
    "To parse the entire DSR file eagerly, the p_strategy must be EAGER.");

  int detected_empty_clause = 0;
  while (has_another_line(dsr_file)) {
    parse_dsr_line();

    // Stop parsing the file if we find the empty clause
    if (new_clause_size == 0) {
      detected_empty_clause = 1;
      break;
    }
  }

  fclose(dsr_file);
  logc("Parsed %lld addition lines.", num_parsed_add_lines);

  FATAL_ERR_IF(!detected_empty_clause && ch_mode == BACKWARDS_CHECKING_MODE,
    "Cannot backwards check without the empty clause.");

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
  up_reasons = xmalloc(up_reasons_alloc_size * sizeof(srid_t));
  memset(up_reasons, 0xff, up_reasons_alloc_size * sizeof(srid_t)); // Set to -1

  // Allocate space for the unit lists. Probably won't be too large
  units_alloc_size = (max_var + 1);
  unit_literals = xmalloc(units_alloc_size * sizeof(int));
  unit_clauses = xmalloc(units_alloc_size * sizeof(srid_t));

  // Allocate space for the dependency markings
  dependencies_alloc_size = formula_size * 2;
  dependency_markings = xcalloc(dependencies_alloc_size, sizeof(llong));

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
    // TODO: use new malloc() shorthands
    // TODO: set to formula_size when resizing?
    clause_last_used_id_alloc_size = formula_size * 2;
    clause_last_used_id =
      xmalloc(clause_last_used_id_alloc_size * sizeof(srid_t));
    memset(clause_last_used_id, 0xff, clause_last_used_id_alloc_size * sizeof(srid_t));

    line_num_RAT_hints_alloc_size = formula_size * 2;
    line_num_RAT_hints = xcalloc(line_num_RAT_hints_alloc_size, sizeof(uint));

    // TODO: Correct size for this? Maybe based on num_vars instead?
    /*marked_clause_stack_alloc_size = formula_size;
    marked_clause_stack = xmalloc(marked_clause_stack_alloc_size * sizeof(srid_t));
    marked_clause_stack_size = 0; */

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
    dependencies_alloc_size, formula_size, sizeof(llong));
}

static inline void resize_units(void) {
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

// Prints those clauses that were globally set to unit during global UP and
// that were marked during UP dependency marking.
static inline void store_active_dependencies(llong gen) {
  //log_msg(VL_NORMAL, "c  Storing active deps\n");
  for (int i = 0; i < unit_clauses_size; i++) {
    srid_t c = unit_clauses[i];
    if (dependency_markings[c] > gen) {
      add_up_hint(c);
    }
  }
}

static void minimize_RAT_hints(void) {
  // Declared `static` to persist across function calls
  // Declared here to prevent a global variable
  static uint *skipped_RAT_indexes = NULL;
  static uint skipped_RAT_indexes_alloc_size = 0;
  static uint skipped_RAT_indexes_size = 0;

  // Iterate over the RAT hint groups and mark last used IDs
  int nrh = get_num_RAT_hints(current_line);
  if (nrh == 0) return;

  skipped_RAT_indexes_size = 0;
  if (skipped_RAT_indexes == NULL) {
    skipped_RAT_indexes_alloc_size = max_var;
    skipped_RAT_indexes = xmalloc(max_var * sizeof(uint));
  }

  // First pass: mark "active" clauses
  // Assume that `get_num_RAT_hints()` is correct,
  // i.e. that the iterator won't go beyond the RAT hints
  int num_marked = 0;
  srid_t *hints_start = get_RAT_hints_start(current_line);
  srid_t *hints_end = get_RAT_hints_end(current_line);
  srid_t *hints_iter = hints_start;
  for (int i = 0; i < nrh; i++) {
    srid_t RAT_clause = FROM_RAT_CLAUSE(*hints_iter);
    hints_iter++;
    srid_t RAT_lui = clause_last_used_id[RAT_clause];
    if (RAT_lui > current_line) {
      // Scan through its hints and mark them as active
      srid_t hint;
      while (hints_iter < hints_end && (hint = *hints_iter) > 0) {
        hint = FROM_DIMACS_CLAUSE(hint);
        hints_iter++;
        num_marked += adjust_clause_lui(hint);
      }
    } else if (IS_UNUSED_LUI(RAT_lui) || RAT_lui == current_line) {
      // Skip "current" hints for now
      // Subtract one due to the ++ above
      INSERT_ARR_ELT_CONCAT(skipped_RAT_indexes, sizeof(uint),
        (uint) ((hints_iter - hints_start) - 1));
      SKIP_REMAINING_UP_HINTS(hints_iter, hints_end);
    } else {
      log_fatal_err("[line %lld] RAT clause %lld was deleted before UP hint.",
        current_line, TO_DIMACS_CLAUSE(RAT_clause));
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

    for (int i = 0; i < old_len; i++) {
      uint offset = skipped_RAT_indexes[i];
      srid_t *iter = hints_start + offset;
      srid_t RAT_clause = FROM_RAT_CLAUSE(*iter);
      srid_t RAT_lui = clause_last_used_id[RAT_clause];

      if (IS_UNUSED_LUI(RAT_lui)) {
        // If the clause still hasn't become "active", skip it again
        INSERT_ARR_ELT_CONCAT(skipped_RAT_indexes, sizeof(uint), offset);
      } else if (RAT_lui == current_line) {
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
      } else {
        log_fatal_err("RAT clause has a strange marking.");
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

// Does the appropriate thing. Operates off the `current_line`.
/**
 * @brief Prints or stores the LSR line.
 * 
 * Active UP hints are stored in `hints`.
 * 
 * @param gen The generation strictly less than the `alpha_generation`
 *            values used to mark clauses in `dependency_markings`.
 */
static void print_or_store_lsr_line(llong gen) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    minimize_RAT_hints();
  }

  ra_commit_range(&hints); // TODO: store active deps for forwards too?
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    store_active_dependencies(gen);
    ra_commit_range(&hints);
  } else {
    print_lsr_line(current_line, LINE_ID_FROM_LINE_NUM(current_line));
  }
}

static void print_stored_lsr_proof(void) {
  // Only prints a stored proof during backwards checking,
  // since we emit proof lines as we go during forwards checking
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    generate_clause_id_map();
    print_initial_clause_deletions();

    // For each "active" addition clause, print its LSR line
    srid_t printed_line_id = num_cnf_clauses + 1;
    int is_active_deletion_line = 0;
    for (srid_t line = 0; line < num_parsed_add_lines - 1; line++) {
      srid_t clause_id = CLAUSE_ID_FROM_LINE_NUM(line);
      if (clause_last_used_id[clause_id] >= 0) {
        if (is_active_deletion_line) {
          write_sr_line_end(lsr_file);
          is_active_deletion_line = 0;
        }

        print_lsr_line(line, printed_line_id);
        printed_line_id++;
      }

      if (line < max_RAT_line) {
        if (get_num_deletions(line) > 0) {
          if (!is_active_deletion_line) {
            is_active_deletion_line = 1;
            write_lsr_deletion_line_start(lsr_file, printed_line_id - 1);
          }

          print_deletions(line);
        }
      }
    }

    // Specially print the empty clause, since we don't mark it as "needed"
    if (is_active_deletion_line) {
      write_sr_line_end(lsr_file);
    }

    print_lsr_line(num_parsed_add_lines - 1, printed_line_id);
  }
}

// Marks the clauses causing each literal in the clause to be false.
// Ignore literals that are assumed fresh, whether in CANDIDATE or RAT.
// Literals that were globally set to unit, but are candidate assumed, are ignored.
static inline void mark_clause(srid_t clause, int offset) {
  int *clause_iter = get_clause_start(clause) + offset; 
  int *clause_end = get_clause_start(clause + 1);
  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    int var = VAR_FROM_LIT(lit);
    srid_t clause_reason = up_reasons[var];
    if (clause_reason >= 0) {
      dependency_markings[clause_reason] = alpha_generation; 
    }
  }
}

static inline void mark_unit_clause(srid_t clause) {
  mark_clause(clause, 1);
}

static inline void mark_entire_clause(srid_t clause) {
  mark_clause(clause, 0);
}

// Start marking backwards, assuming the offending clause has already been marked.
static inline void mark_dependencies(void) {
  for (int i = unit_clauses_size - 1; i >= 0; i--) {
    srid_t clause = unit_clauses[i];
    if (dependency_markings[clause] == alpha_generation) {
      mark_unit_clause(clause);
    }
  }
}

// Backwards marks the dependencies for the UP derivation.
// Starts the marking at the clause stored in up_falsified_clause.
// NOTE: Every marked clause is stored in unit_clauses, except for up_falsified_clause,
// which is not marked.
static inline void mark_up_derivation(srid_t from_clause) {
  mark_entire_clause(from_clause);
  mark_dependencies();
}

// TODO: Think about how to make the empty clause not be the special case
// Probably reroute the "store" to "print_or_store_line" somehow
// And then don't have a special `add_wps_and_()` call before the check line loop?
static void mark_and_store_up_refutation(srid_t from_clause, llong gen) {
  mark_up_derivation(from_clause);
  ra_commit_range(&hints);
  store_active_dependencies(gen);
  add_up_hint(from_clause);
  adjust_clause_lui(from_clause);
  ra_commit_range(&hints);
}

/*

Problems:
  - we want to mark the clause_last_used_id when the clause is used for
    "the last time" when checking backwards. This usually occurs when a
    clause is used in a UP refutation or a RAT hint group. The initial set
    of "last used" clauses is set when deriving the empty clause in its
    UP refutation. When checking backwards, we uncommit the clause, meaning
    the formula_size is reduced, and the watch pointers for the clause are
    removed (if the clause has length at least 2).

  - however, when we parse the DSR proof, the user may specify that certain
    clauses should be deleted. We can mark the clause_last_used_id to that
    proof line, but then when checking later lines, we can't refer to that
    clause, and when we proceed to a line before the deletion, we have to
    restore our reference to the clause. So we need some way of knowing
    not only if a clause is deleted, but a way of restoring the watch pointers
    and "influence" of the clause when we reach its line.
      - One solution is to keep a stack of these "user deleted clauses" in an
        array in order of appearance. Then when we finish checking a line,
        to prepare for the line before, we loop over the array backwards until
        we encounter a clause that was deleted before the line we want to check
        (BEWARE OF OFF-BY-ONE ERRORS). We restore them by adding back their
        watch pointers (since we prevent users from deleting unit clauses).
        (Note if we prevent users from deleting units only, or clauses which
        become unit under the current global assignment. [although if it is
        unit under alpha, then you can just introduce the unit clause?])
          - Question: what happens if a redundant clause is satisfied by alpha?
            Double-check what I do in this scenario.
*/

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
 * @brief Minimizes the witness and checks its consistency. Call after assuming 
 *  the negation of the candidate clause and doing UP.
 * 
 * Any witness literal l set to true that is also set to true in alpha after
 * assuming the negation of the candidate clause and doing UP can be omitted.
 * This is because any clause satisfied by l will then generate contradiction
 * with alpha (alpha satisfies it), and any clause containing -l will, when
 * its negation is assumed for RAT checking, has no additional effect on alpha,
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
 */
static void minimize_witness(void) {
  int *witness_iter = get_witness_start(current_line);
  int *witness_end = get_witness_end(current_line);
  int *write_iter = NULL;
 
  if (witness_iter + 1 == witness_end) return;

  int pivot = witness_iter[0];
  int seen_pivot_divider = 0;
  witness_iter++;

  for (; witness_iter < witness_end; witness_iter++) {
    int lit = *witness_iter;
    if (lit == WITNESS_TERM) break;

    // If the literal is good to keep, then we write it to `write_iter`    
    int keep_lit = 1;

    if (!seen_pivot_divider && lit == pivot) {
      seen_pivot_divider = 1;
      witness_iter--; // Gets incremented before looping
      goto write_lit_at_write_iter;
    }

    // Store what the literal is mapped to under alpha and the subst witness
    peval_t lit_alpha = peval_lit_under_alpha(lit);
    peval_t lit_subst = (!seen_pivot_divider) ? TT : UNASSIGNED;

    // If we are in the substitution portion, check the truth value of `m`
    if (seen_pivot_divider) {
      int mapped_lit = witness_iter[1];
      switch (peval_lit_under_alpha(mapped_lit)) {
        case FF:
          // printf("c   (%d -> %d), but latter was found to be globally false\n",
          //   TO_DIMACS_LIT(lit), TO_DIMACS_LIT(mapped_lit));
          witness_iter[1] = SUBST_FF;
          lit_subst = FF;
          break;
        case TT:
          // printf("c   (%d -> %d), but latter was found to be globally true\n",
          //   TO_DIMACS_LIT(lit), TO_DIMACS_LIT(mapped_lit));
          witness_iter[1] = SUBST_TT;
          lit_subst = TT;
          break;
        default: break;
      }
    }

    // Now compare the truth value of l in the substitution and alpha
    // TODO: Brittle negation, based on hard-coded values of peval_t.
    if (lit_alpha != UNASSIGNED) {
      if (lit_alpha == lit_subst) {
        log_msg(VL_VERBOSE,
          "c Found an unnecessary literal %d at index %d in the witness\n",
          TO_DIMACS_LIT(lit),
          (int) (witness_iter - get_witness_start(current_line)));
        keep_lit = 0;
        if (write_iter == NULL) {
          // Adjust write_iter in order to start writing over this lit (pair)
          write_iter = witness_iter;
        }
      } else if (lit_alpha == -lit_subst) {
        int var = VAR_FROM_LIT(lit);
        llong gen = alpha[var];
        FATAL_ERR_IF(ABS(gen) == GLOBAL_GEN, 
          "[line %lld] Witness lit %d is set to negation of UP value.",
          current_line + 1, TO_DIMACS_LIT(lit));
      }
    }

    // Overwrite bad literals as we find good literals
  write_lit_at_write_iter:
    if (keep_lit && write_iter != NULL) {
      *write_iter = lit;
      write_iter++;
      if (seen_pivot_divider) {
        *write_iter = witness_iter[1];
        write_iter++;
      }
    }

    if (seen_pivot_divider) {
      witness_iter++;
    }
  }

  // Write a new witness terminating element if we shrank the witness
  if (write_iter != NULL) {
    *write_iter = WITNESS_TERM;
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
  llong gen = (up_state == CANDIDATE_UP) ? ASSUMED_GEN : alpha_generation;
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
static void set_unit_clause(int lit, srid_t clause, llong gen) {
  set_lit_for_alpha(lit, gen);
  up_reasons[VAR_FROM_LIT(lit)] = clause;

  // logc("[line %lld] Setting clause %d to unit on literal %d",
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

  // Now allocate more space in the wp[lit] array, if needed
  // Handles the case where both are 0 (uninitialized)
  FATAL_ERR_IF(lit < 0 || lit >= wps_alloc_size, "Invalid literal %d", lit);

  uint alloc_size = wp_alloc_sizes[lit];
  if (wp_sizes[lit] == alloc_size) {
    wp_alloc_sizes[lit] = MAX(INIT_LIT_WP_ARRAY_SIZE, RESIZE(alloc_size));
    wps[lit] = xrealloc(wps[lit], wp_alloc_sizes[lit] * sizeof(srid_t));
  }
  
  // TODO: Error checking, see if wp is already in the list
  for (uint i = 0; i < wp_sizes[lit]; i++) {
    if (wps[lit][i] == clause) {
      log_fatal_err("Clause %lld already has a watch pointer for literal %d",
        TO_DIMACS_CLAUSE(clause), TO_DIMACS_LIT(lit));
    }
  }

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
      wp_sizes[lit]--;
      return;
    }
  }

  // Fatal error: watch pointer not in the list
  // Print debug information
  print_active_formula();
  print_wps();
  log_fatal_err("Clause %lld not found in watch pointer list for literal %d",
    TO_DIMACS_CLAUSE(clause), TO_DIMACS_LIT(lit));

  // TODO: If below some threshold of size/alloc_sizes, shrink the array
}

// Returns the clause ID that becomes falsified, or -1 if not found.
static srid_t perform_up_for_backwards_checking(llong gen) {
  // When performing UP for backwards checking, we do the same thing
  // Except we skip unmarked clauses as possible units, in favor of
  // marked clauses, to reduce the number of "dependent" clauses in the formula

  // These are used to store potential new un-marked clauses while (i, j)
  // continue ahead.

  /*

    Notes:

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

  int progressed_i = -1;
  int bookmarked_i;
  int accepting_unmarked_clauses = 0;

  int i;
  switch (up_state) {
    case GLOBAL_UP:    i = global_up_literals_index;         break;
    case CANDIDATE_UP: i = candidate_assumed_literals_index; break;
    case RAT_UP:       i = RAT_assumed_literals_index;       break;
    default: log_fatal_err("Corrupted up_state: %d", up_state);
  }

  FATAL_ERR_IF(i < 0 || i > unit_literals_size, "Invalid i: %d", i);

  // Reset the `wp_up_indexes`
  // TODO: Why don't we reset the whole thing?
  // I guess the thought is that during backwards checking, we've already
  // done UP on the global state, so there is nothing more to find here
  // (Especially if we uncommit true units as we move backwards through form)
  memset(unit_literals_wp_up_indexes + i,
    0, (unit_literals_size - i) * sizeof(int));

restart_up:
  // TODO: Should we *really* restart at 0 every time???
  bookmarked_i = INT_MAX;
restart_up_without_restarting_bookmark:
  FATAL_ERR_IF(i < 0 || i > unit_literals_size, "Invalid i: %d", i);
  for (; i < unit_literals_size; i++) {
    FATAL_ERR_IF(i < 0, "negative i: %d", i);
    int lit = NEGATE_LIT(unit_literals[i]);
    FATAL_ERR_IF(lit < 0 || lit >= wps_alloc_size, "wps invalid lit: %d", lit);

    // Iterate through its watch pointers and see if the clause becomes unit
    srid_t *wp_list = wps[lit];

    int j = unit_literals_wp_up_indexes[i]; // Store in a local var for eff.
    int ignored_j = j;
    int wp_size = wp_sizes[lit]; // Store in a local variable for efficiency

    FATAL_ERR_IF(j < 0 || j > wp_size, "Invalid wp index: %d", j);

    for (; j < wp_size; j++) {
      const srid_t clause_id = wp_list[j];
      int *clause = get_clause_start(clause_id);
      const int clause_size = get_clause_size(clause_id);

      // The clause is not a unit clause (yet), and its watch pointers are 
      // the first two literals in the clause (we may reorder literals here).

      // Place the other watch pointer first
      if (clause[0] == lit) {
        clause[0] = clause[1];
        clause[1] = lit;
      }

      int first_wp = clause[0];
      const peval_t first_peval = peval_lit_under_alpha(first_wp);

      // If `first_wp` evals to true, then the clause is satisfied (not unit)
      if (first_peval == TT) {
        // We swap the satisfied clause back in the wp_list,
        // so that the ignored clauses get bubbled up to the end
        SWAP_WP_LIST_ELEMS(wp_list, clause_id, j, ignored_j);
        continue;
      }

      // Otherwise, scan the clause for a non-false literal
      int found_new_wp = 0;
      for (int k = 2; k < clause_size; k++) {
        if (peval_lit_under_alpha(clause[k]) != FF) {
          // The kth literal is non-false, so swap it with the first wp
          int new_wp = clause[k];
          clause[1] = new_wp;
          clause[k] = lit;

          // Because clauses do not have duplicate literals, we know that
          // `clause[1] != lit`, and so even if `wps[lit]` gets reallocated,
          // it won't affect `wp_list`.
          add_wp_for_lit(new_wp, clause_id);

          // Adding a watch pointer could potentially re-allocate the `wp_list`
          // underneath us, so we refresh the pointer
          if (wp_list != wps[lit]) {
            logc("Reallocation occurred underneath us!");
            wp_list = wps[lit];
          }

          // Instead of calling `remove_wp_for_lit()`, we can swap from the back
          wp_list[j] = wp_list[wp_size - 1];
          wp_size--;
          found_new_wp = 1;
          break;
        }
      }

      if (found_new_wp) {
        j--; // We need to decrement, since we replaced `wp_list[j]`
        continue;  
      }

      // We didn't find a replacement watch pointer. Is `first_wp` false?
      if (first_peval == FF) {
        // Since all literals are false, we found a UP contradiction
        wp_sizes[lit] = wp_size; // Restore from the local variable
        // No need to update `unit_literals_wp_up_indexes[i]`, since we're done
        return clause_id;
      } else {
        // The first literal is unassigned, so we have a unit clause/literal

        // For backwards checking, we prefer already-marked clauses
        // These are clauses whose last ids have been set

        // If the clause has been marked
        if (!IS_UNUSED_LUI(clause_last_used_id[clause_id])) {
          set_unit_clause(first_wp, clause_id, gen); // Add as a unit literal
          SWAP_WP_LIST_ELEMS(wp_list, clause_id, j, ignored_j);
        } else {
          bookmarked_i = MIN(i, bookmarked_i);
          if (accepting_unmarked_clauses) {
            // Add this as a unit clause, and mark it
            // Jump back to the front
            set_unit_clause(first_wp, clause_id, gen);

            accepting_unmarked_clauses = 0;

            SWAP_WP_LIST_ELEMS(wp_list, clause_id, j, ignored_j);
            unit_literals_wp_up_indexes[i] = ignored_j;
            wp_sizes[lit] = wp_size;

            // Now that we've marked a clause, perhaps the new unit literal
            // gives us new unit clauses that are already marked.
            // We would prefer these over more ignored, unmarked clauses
            // associated with this unit literal.
            i = progressed_i;

            // TODO cleanup
            goto restart_up_without_restarting_bookmark;
          }
        }
      }
    }

    FATAL_ERR_IF(ignored_j < 0 || ignored_j > wp_size,
      "Invalid ignored_j: %d", ignored_j);
    FATAL_ERR_IF(wp_size < 0, "Negative wp_size: %d", wp_size);
    unit_literals_wp_up_indexes[i] = ignored_j;
    wp_sizes[lit] = wp_size;
  }

  progressed_i = i;  // Lemma: (i == unit_literals_size)

  if (!accepting_unmarked_clauses && bookmarked_i != INT_MAX) {
    // We ignored at least one clause.
    // Go back to the bookmarked i
    // We restart UP at unit_literals_wp_up_indexes[i],
    // and the goto label resets bookmarked_i
    i = bookmarked_i;
    accepting_unmarked_clauses = 1;
    goto restart_up;
  }
  
  // TODO: Figure out if this needs to get done.  
  if (up_state == GLOBAL_UP) {
    global_up_literals_index = unit_literals_size;
  }

  return -1;
}

// Performs unit propagation. Sets the falsified clause (the contradiction) to
// up_falsified_clause. -1 if not found.
// Any literals found are set to the provided generation value.
static srid_t perform_up_for_forwards_checking(llong gen) {
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

  int i;
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
    int wp_size = wp_sizes[lit]; // Store and edit this value in a variable
    for (int j = 0; j < wp_size; j++) {
      srid_t clause_id = wp_list[j];
      int *clause = get_clause_start_unsafe(clause_id);
      const int clause_size = get_clause_size(clause_id);
      
      // Lemma: the clause is not a unit clause (yet), and its wpointers are 
      // the first two literals in the clause (we may reorder literals here).

      // Place the other watch pointer first
      if (clause[0] == lit) {
        clause[0] = clause[1];
        clause[1] = lit;
      }

      int first_wp = clause[0];

      // If `first_wp` evals to true, then the clause is satisfied (not unit)
      const peval_t first_peval = peval_lit_under_alpha(first_wp);
      if (first_peval == TT) {
        continue;
      }

      // Otherwise, scan the clause for a non-false literal
      int found_new_wp = 0;
      for (int k = 2; k < clause_size; k++) {
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

  // TODO: Figure out if this needs to get done.  
  if (up_state == GLOBAL_UP) {
    global_up_literals_index = unit_literals_size;
  }

  return -1;
}

static inline srid_t perform_up(llong gen) {
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
static void add_wps_and_perform_up(srid_t clause_index, llong gen) {
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
        // Skip the literal if we already found a satisfying literal
        if (satisfied_lit == -1) {
          log_msg(VL_NORMAL, "HELLO WORLD %d, %d",
            TO_DIMACS_LIT(lit), TO_DIMACS_CLAUSE(up_reasons[var]));
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
    mark_and_store_up_refutation(falsified_clause, alpha_generation - 1);
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
  for (int i = 0; i < RAT_marked_vars_size; i++) {
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
  int *end = get_clause_start(clause_index + 1);
  for (; clause_ptr < end; clause_ptr++) {
    int lit = *clause_ptr;
    int mapped_lit = get_lit_from_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT:
        clear_RAT_marked_vars();
        return SATISFIED_OR_MUL;
      case SUBST_FF: break; // Ignore the literal
      case SUBST_UNASSIGNED:
        mapped_lit = lit; // waterfall!
      default:;
        int mapped_var = VAR_FROM_LIT(mapped_lit);
        // Now evaluate the mapped literal under alpha. If it's unassigned, set it
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

static void soft_delete_clause(srid_t clause_id) {

}

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

  // Now check the (user) deletions and restore their watch pointers
  /*srid_t line = LINE_NUM_FROM_CLAUSE_ID(cc_id);
  srid_t *deletions = get_deletions_start(line);
  srid_t *deletions_end = get_deletions_end(line);
  for (; deletions < deletions_end; deletions++) {
    srid_t del_id = *deletions;
    logc("Restoring watch pointers for clause %lld",
      TO_DIMACS_CLAUSE(del_id));
    int *del_clause = get_clause_start(del_id);
    // Invariant: users cannot delete units, so the size is at least 2
    add_wp_for_lit(del_clause[0], del_id);
    add_wp_for_lit(del_clause[1], del_id);
  } */
}

static void commit_or_uncommit_clause(void) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    uncommit_clause_and_set_as_candidate();
  } else {
    perform_clause_first_last_update(CLAUSE_ID_FROM_LINE_NUM(current_line));
    current_line++;
  }
}

static int can_skip_clause(srid_t clause_index) {
  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    // srid_t lui = clause_last_used_id[clause_index];
    // return IS_UNUSED_LUI(clause_last_used_id[clause_index]);
    srid_t lui = LUI_FROM_USER_DELETED_LUI(clause_last_used_id[clause_index]);
    return 0 <= lui && lui <= current_line;
  } else {
    return is_clause_deleted(clause_index);
  }
}

static void check_dsr_line(void) {
  // We save the generation at the start of line checking so we can determine
  // which clauses are marked in the dependency_markings array.
  llong old_alpha_gen = alpha_generation;
  alpha_generation++;
  subst_generation++;

  srid_t cc_index = CLAUSE_ID_FROM_LINE_NUM(current_line);

  // Find implied candidate unit clauses
  // If a UP refutation is found, it is stored, and we may finish the line
  if (assume_candidate_clause_and_perform_up(cc_index) == -1) {
    goto candidate_valid;
  }

  // Since we didn't derive UP contradiction, the clause should be nonempty
  FATAL_ERR_IF(new_clause_size == 0, "Didn't derive empty clause.");

  // Now we turn to RAT checking - apply the witness
  max_RAT_line = MAX(max_RAT_line, current_line);
  minimize_witness();
  assume_subst(current_line);

  int *witness_iter = get_witness_start(current_line) + 1;
  int *witness_end = get_witness_end(current_line);

  // TODO: Off-by-one error since we may have already committed the clause?
  srid_t efs = get_effective_formula_size();
  max_clause_to_check = MIN(max_clause_to_check, efs);

  // Now do RAT checking between min and max clauses to check (inclusive)
  log_msg(VL_VERBOSE, "  [%d] Checking clauses %lld to %lld", 
    current_line + 1, min_clause_to_check + 1, max_clause_to_check + 1);
  int *clause, *next_clause = get_clause_start(min_clause_to_check);
  int clause_size;
  for (srid_t i = min_clause_to_check; i <= max_clause_to_check; i++) {
    if (can_skip_clause(i)) continue;

    // Evaluate the clause under the substitution
    switch (reduce_subst_mapped(i)) {
      case NOT_REDUCED:
      case SATISFIED_OR_MUL:
        continue;
      case REDUCED:
        add_RAT_clause_hint(i);

        // If the RAT clause is not satisfied by alpha, do UP
        if (assume_RAT_clause_under_subst(i) != SATISFIED_OR_MUL) {
          srid_t falsified_clause = perform_up(alpha_generation);
          FATAL_ERR_IF(falsified_clause == -1,
              "[line %lld] No UP contradiction for RAT clause %lld.",
              current_line + 1, TO_DIMACS_CLAUSE(i));
          mark_up_derivation(falsified_clause);
          store_RAT_dependencies(falsified_clause);
        }
        unassume_RAT_clause(i);
        alpha_generation++; // Clear this round of RAT units from alpha
        break;
      case CONTRADICTION:
        log_fatal_err("RAT contradiction: should have had UP derivation.");
      default: log_fatal_err("Corrupted reduction value.");
    }    
  }

  print_or_store_lsr_line(old_alpha_gen);

  // Congrats: the line checked! Undo the changes we made to the data structures
candidate_valid:
  unassume_candidate_clause(cc_index);

  if (ch_mode == FORWARDS_CHECKING_MODE) {
    add_wps_and_perform_up(get_effective_formula_size(), old_alpha_gen);
  }
}

static void remove_wps_from_user_deleted_clauses(srid_t clause_id) {
  srid_t line = LINE_NUM_FROM_CLAUSE_ID(clause_id);
  srid_t *dels = get_bcu_deletions_start(line);
  srid_t *del_end = get_bcu_deletions_end(line);

  if (dels == del_end) return;

  for (; dels < del_end; dels++) {
    srid_t del_id = *dels;
    //dbg_print_clause(del_id);
    int *del_clause = get_clause_start(del_id);
    remove_wp_for_lit(del_clause[0], del_id);
    remove_wp_for_lit(del_clause[1], del_id);
  }
}

static void restore_wps_for_user_deleted_clauses(srid_t clause_id) {
  srid_t line = LINE_NUM_FROM_CLAUSE_ID(clause_id);
  srid_t *dels = get_bcu_deletions_start(line);
  srid_t *del_end = get_bcu_deletions_end(line);

  if (dels == del_end) return;

  for (; dels < del_end; dels++) {
    srid_t del_id = *dels;
    int *del_clause = get_clause_start(del_id);
    add_wp_for_lit(del_clause[0], del_id);
    add_wp_for_lit(del_clause[1], del_id);
  }
}

static inline void prepare_next_line_for_backwards_checking(void) {
  srid_t cc_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
  do {
    restore_wps_for_user_deleted_clauses(cc_id);
    current_line--;
    uncommit_clause_and_set_as_candidate();
    ra_commit_range(&deletions);
    cc_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
  } while (IS_UNUSED_LUI(clause_last_used_id[cc_id]));

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
    current_line++;
  }

  if (p_strategy == PS_EAGER) return ADDITION_LINE;
  else                        return parse_dsr_line();
}

/*
static void check_proof_backwards(void) {
  up_state = GLOBAL_UP;
  alpha_generation = 1;

  // This will perform UP and store the hints in `hints`
  // TODO off by one error here
  // current_line = LINE_NUM_FROM_LINE_ID(formula_size + 1);
  // We're assuming the final clause is empty and added to the formula
 
  // This should basically have no effect
  uncommit_clause_and_set_as_candidate();
  
  // add_wps_and_perform_up(formula_size - 1, 0); // Empty clause is newest clause
  for (srid_t c = num_cnf_clauses; c < formula_size && !derived_empty_clause; c++) {
    add_wps_and_perform_up(c, 0);
  }

  FATAL_ERR_IF(!derived_empty_clause,
    "Despite being a part of the proof, the empty clause was not redundant.");

  log_msg(VL_NORMAL, "c Finished UPs on entire formula\n");

  // These should be the hints to derive the empty clause
  print_lsr_line(current_line, LINE_ID_FROM_LINE_NUM(current_line));

  // Now we need to work backwards
  while (has_another_dsr_line()) {
    // resize_sr_trim_data();
    log_msg(VL_NORMAL, "c Checking line %d\n", current_line + 1);
    check_dsr_line();
  }

  print_stored_lsr_proof();
  log_msg(VL_NORMAL, "c VERIFIED UNSAT\n");
}

static void check_and_annotate_proof(void) {
  // Perform initial unit propagation on the parsed CNF formula
  up_state = GLOBAL_UP;
  alpha_generation = 1;

  // TODO: When backwards checking, we assume that the empty clause has been
  // detected. `add_wps_and_perform_up()` is going to determine the UP
  // derivation
  add_wps_and_perform_up(formula_size, 0);
  if (derived_empty_clause) goto print_result;

  if (ch_mode == BACKWARDS_CHECKING_MODE) {
    // Basically, run through the entire proof and "add" each clause,
    // performing unit propagation, then as we move backwards,
    // un-assume or un-UP things from alpha.
  }

  // TODO: Allow for proofs that don't derive the empty clause
  // TODO: Handle deletion lines
  while (!derived_empty_clause && has_another_dsr_line()) {
    if (parse_dsr_line() == ADDITION_LINE) {
      // printf("c Parsed line %d, new clause has size %d and witness with size %d\n", 
      //   current_line + 1, new_clause_size, witness_size);
      resize_sr_trim_data(); 
      check_dsr_line();
    }
  }

print_result:
  if (p_strategy == PS_STREAMING && dsr_file != stdin) {
    fclose(dsr_file);
  }

  print_proof_checking_result();
  print_stored_lsr_proof();
}

  */

static void add_wps_and_up_initial_clauses(void) {
  srid_t c;
  for (c = 0; c < num_cnf_clauses; c++) {
    add_wps_and_perform_up(c, 0);
  }

  logc("Done UP on initial CNF clauses");

  if (ch_mode == FORWARDS_CHECKING_MODE) return;

  // TODO: Encapsulate better
  // TODO: No need to RESIZE from formula_size when this is the largest it'll be
  current_line = num_parsed_add_lines - 1; // Subtract 1 to 0-index it
  resize_sr_trim_data();
  resize_last_used_ids();
  uncommit_clause_and_set_as_candidate();

  current_line = 0;

  // Add implied unit clauses, clause by clause
  // Stop when we finally derive the empty clause
  for (; c < formula_size - 1 && !derived_empty_clause; c++) {
    logc("About to add wps for clause %lld", TO_DIMACS_CLAUSE(c));
    remove_wps_from_user_deleted_clauses(c);
    perform_clause_first_last_update(c);
    current_line++;
    add_wps_and_perform_up(c, 0);
  }

  FATAL_ERR_IF(!derived_empty_clause,
    "Despite being a part of the proof, the empty clause was not redundant.");

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
  alpha_generation = 1;

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
  print_stored_lsr_proof();
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
        } else {
          log_fatal_err("Unimplemented long option.");
        }
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
      FATAL_ERR_IF(!cli.name_provided, "No file prefix provided.");
      cli_concat_path_extensions(&cli, ".cnf", ".sr", ".lsr");
      break;
    case 1:
      FATAL_ERR_IF(cli.dir_provided,
        "Cannot provide a directory without a DSR file path.");

      if (cli.name_provided) {
        cli_concat_path_extensions(&cli, ".cnf", argv[optind], ".lsr");
      } else {
        cli.cnf_file_path = argv[optind];
        cli.dsr_file_path = NULL;
        cli.lsr_file_path = NULL;
      }
      break;
    case 2:
      if (cli.dir_provided || cli.name_provided) {
        cli_concat_path_extensions(&cli, argv[optind], argv[optind+1], ".lsr");
      } else {
        cli.cnf_file_path = argv[optind];
        cli.dsr_file_path = argv[optind + 1];
        cli.lsr_file_path = NULL;
      }
      break;
    case 3:
      if (cli.dir_provided || cli.name_provided) {
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

  parse_cnf(cnf_file);
  prepare_dsr_trim_data();
  check_proof();

  return 0;
}