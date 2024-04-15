/**
 * @file sr-trim.c
 * @brief Tool for labeling and trimming SR proof certificates.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-02-12
 */

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>
#include <unistd.h>

#include "xio.h"
#include "global_data.h"
#include "global_parsing.h"
#include "cnf_parser.h"
#include "sr_parser.h"
#include "xmalloc.h"

/*
TODOs:
  - Candidate clause minimization. When marking clauses, mark literals as well.
  - Watch pointer de-sizing. (i.e. fewer watch pointers de-size the wp array)
  - Clause deletion, via hash table.
  - Allow dsr-trim and lsr-check to verify proofs that don't derive the empty clause.
  - Detect if the empty clause was trivially derived after parsing CNF formula.
  - Rewrite PRINT_ERR_AND_EXIT macros to accept %d, etc. format strings.
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
#define INIT_CLAUSE_ID_HT_SIZE          (100000)
#define INIT_CLAUSE_ID_BUCKET_SIZE      (8)

// When setting literals "globally" under initial unit propagation, we use the
// largest possible generation value.
#define GLOBAL_GEN                (LLONG_MAX)
#define ASSUMED_GEN               (LLONG_MAX - 1)

// SR trim as a state machine, for different parts of UP.
typedef enum sr_trim_state {
  GLOBAL_UP,
  CANDIDATE_UP,
  RAT_UP,
} state_t;

static state_t state;

// 2D array of watch pointers, indexed by literals. Initialized to NULL for each literal.
static srid_t **wps = NULL;

// Allocated size of the 2D array of watch pointers.
static int wps_alloc_size = 0;

// Allocated size of watch pointer array for each literal.
// Invariant: if wps[i] == NULL, then wp_alloc_sizes[i] = 0.
static int *wp_alloc_sizes = NULL;

// Number of watch pointers under each literal.
// Invariant: if wps[i] == NULL, then wp_sizes[i] = 0.
static int *wp_sizes = NULL; // TODO: New name

// Array containing the clause ID "reason" causing the variable to be set. Indexed by variable.
static srid_t *up_reasons = NULL;
static int up_reasons_alloc_size = 0; // TODO: use alpha_subst_alloc_size for this?

// A list of literals, in order of when they become unit.
static int *unit_literals = NULL;

// A list of clauses, in order of when they became unit.
static srid_t *unit_clauses = NULL;
static int units_alloc_size = 0;
static int unit_literals_size = 0;
static int unit_clauses_size = 0;

static int candidate_unit_clauses_index = 0;
static int RAT_unit_clauses_index = 0;

// Index pointing at the "unprocessed" global UP literals
static int global_up_literals_index = 0;

// Monotonically increased index into the formula
static srid_t wp_processed_clauses = 0;

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
static int RAT_marked_vars_alloc_size = 0;
static int RAT_marked_vars_size = 0;

// Flag for noting if the witness contains a literal that once was mapped to
// another literal, but was then direct-mapped to a truth value during minimization.
// This allows for more efficient printing of the witness.
static int witness_has_direct_mapped_subst_lit = 0;

// We store the RAT derivations as they come in "printable" format.
static srid_t *lsr_line = NULL;
static int lsr_line_alloc_size = 0;
static int lsr_line_size = 0;

static FILE *sr_certificate_file = NULL;
static srid_t current_line = 0; // For printing the correct line ID
static llong generation_before_line_checking = 0;
static srid_t up_falsified_clause = -1; // Set by unit propagation, -1 if none found

static FILE *lsr_proof_file = NULL;

// Because deletion lines in the DSR format identify a clause to be deleted,
// and not a clause ID, we use a hash table to store clause IDs, where the
// hash is a commutative function of the literals. That way, permutations of
// the clause will hash to the same thing.

// The clause deletion hash table.
static srid_t **clause_id_ht = NULL;
static int clause_id_ht_alloc_size = 0;

// Stores the (logical) size of the buckets under each hash in the table.
// Not initialized to anything (check for NULL under clause_id_ht[i]).
static int *clause_id_ht_sizes = NULL;

// Stores the allocated sizes of the buckets under each hash in the table.
// Not initialized to anything (check for NULL under clause_id_ht[i]).
static int *clause_id_ht_alloc_sizes = NULL;

static void add_clause_hash(srid_t clause);

////////////////////////////////////////////////////////////////////////////////

static void print_usage(void) {
  printf("Usage: ./sr-trim <cnf> <proof> [lsr-proof] [options]\n\n");
  printf("where [options] are among the following:\n\n");
  // printf("  -i    Specify that the input proof is in the binary format.\n");
  // printf("  -b      ");
}

////////////////////////////////////////////////////////////////////////////////

static void init_sr_trim_data(void) {
  // Allocate an empty watch pointer array for each literal
  // Allocate some additional space, since we'll probably add new literals later
  wps_alloc_size = max_var * 4;
  wps = xcalloc(wps_alloc_size, sizeof(srid_t *));
  wp_alloc_sizes = xcalloc(wps_alloc_size, sizeof(int)); 
  wp_sizes = xcalloc(wps_alloc_size, sizeof(int));

  // Only allocate initial watch pointer space for literals in the formula 
  for (int i = 0; i < max_var * 2; i++) {
    wp_alloc_sizes[i] = INIT_LIT_WP_ARRAY_SIZE;
    wps[i] = xmalloc(INIT_LIT_WP_ARRAY_SIZE * sizeof(srid_t));
  }

  // Allocate empty reasons array for each variable, plus extra space
  up_reasons_alloc_size = max_var * 2;
  up_reasons = xmalloc(up_reasons_alloc_size * sizeof(srid_t));
  memset(up_reasons, 0xff, up_reasons_alloc_size * sizeof(srid_t)); // Set to -1

  // Allocate space for the unit lists. Probably won't be too large
  units_alloc_size = max_var * 2;
  unit_literals = xmalloc(units_alloc_size * sizeof(int));
  unit_clauses = xmalloc(units_alloc_size * sizeof(srid_t));

  // Allocate space for the dependency markings
  dependencies_alloc_size = formula_size * 2;
  dependency_markings = xcalloc(dependencies_alloc_size, sizeof(llong));

  RAT_marked_vars_alloc_size = max_var;
  RAT_marked_vars = xmalloc(RAT_marked_vars_alloc_size * sizeof(int));

  // Allocate space for the printable LSR line, for RAT derivations.
  lsr_line_alloc_size = formula_size;
  lsr_line = xmalloc(lsr_line_alloc_size * sizeof(srid_t));

  // Allocate space for the clause id hash table
  clause_id_ht_alloc_size = INIT_CLAUSE_ID_HT_SIZE;
  clause_id_ht = xcalloc(clause_id_ht_alloc_size, sizeof(srid_t *));
  clause_id_ht_sizes = xmalloc(clause_id_ht_alloc_size * sizeof(int));
  clause_id_ht_alloc_sizes = xmalloc(clause_id_ht_alloc_size * sizeof(int));

  // Run through all the clauses and hash them
  for (srid_t i = 0; i < formula_size; i++) {
    add_clause_hash(i);
  }

  current_line = formula_size;
}

static void resize_sr_trim_data(void) {
  // Resize arrays that depend on max_var and formula_size
  // The memset() calls don't do anything in the case of no allocation
  int old_size = up_reasons_alloc_size;
  RESIZE_ARR(up_reasons, up_reasons_alloc_size, max_var, sizeof(srid_t));
  memset(up_reasons + old_size, 0xff, (up_reasons_alloc_size - old_size) * sizeof(srid_t));

  old_size = wps_alloc_size;
  RESIZE_ARR(wps, wps_alloc_size, max_var * 2, sizeof(srid_t *));
  memset(wps + old_size, 0, (wps_alloc_size - old_size) * sizeof(srid_t *));

  srid_t old_dep_size = dependencies_alloc_size;
  RESIZE_ARR(dependency_markings, dependencies_alloc_size, formula_size, sizeof(llong));
  memset(dependency_markings + old_dep_size, 0, 
    (dependencies_alloc_size - old_dep_size) * sizeof(llong));
}

static inline void resize_units(void) {
  if (unit_literals_size >= units_alloc_size) {
    units_alloc_size = RESIZE(unit_literals_size);
    unit_literals = xrealloc(unit_literals, units_alloc_size * sizeof(int));
    unit_clauses = xrealloc(unit_clauses, units_alloc_size * sizeof(srid_t));
  }
}

////////////////////////////////////////////////////////////////////////////////

// Prints the candidate clause (the one to add to the formula) to the LSR file.
// Doesn't print anything if the empty clause has been derived.
static void print_clause(void) {
  if (!derived_empty_clause) {
    for (srid_t i = formula[formula_size]; i < lits_db_size; i++) {
      write_lit(lsr_proof_file, TO_DIMACS_LIT(lits_db[i]));
    }
  }
}

// Prints the SR witness to the LSR file.
// If the witness is empty, then nothing is printed.
static void print_witness(void) {
  if (witness_size == 0) return;

  /* Because witness minimization might map literals to true/false that are in
   * the "substitution portion", we do a two-pass over that part to first print
   * the true/false mapped literals, and then the non-trivial mappings.       */

  // If the witness doesn't have a literal mapped to true/false in the
  // substitution portion, then we can print the witness normally
  if (!witness_has_direct_mapped_subst_lit) {
    for (int i = 0; i < witness_size; i++) {
      // Add the pivot as a separator, if there's a substitution part of the witness
      if (i == subst_index) {
        write_lit(lsr_proof_file, TO_DIMACS_LIT(pivot));
      }

      write_lit(lsr_proof_file, TO_DIMACS_LIT(witness[i]));
    }
  } else {
    // We print the true/false portion first
    for (int i = 0; i < subst_index; i++) {
      write_lit(lsr_proof_file, TO_DIMACS_LIT(witness[i]));
    }

    // Now we two-pass over the substitution portion.
    // We count the number of skipped non-trivial mappings, because if it is 0,
    // then we have no substitutions and we don't print the pivot as a separator
    int skipped_mapped_lits = 0;
    for (int i = subst_index; i < witness_size; i += 2) {
      switch (witness[i + 1]) {
        case SUBST_TT:
          write_lit(lsr_proof_file, TO_DIMACS_LIT(witness[i]));
          break;
        case SUBST_FF:
          write_lit(lsr_proof_file, TO_DIMACS_LIT(NEGATE_LIT(witness[i])));
          break;
        default: skipped_mapped_lits++;
      }
    }

    // If we still have non-trivial mapped literals, print them after the pivot
    if (skipped_mapped_lits > 0) {
      write_lit(lsr_proof_file, TO_DIMACS_LIT(pivot));
      for (int i = subst_index; i < witness_size; i += 2) {
        switch (witness[i + 1]) {
          case SUBST_TT: break;
          case SUBST_FF: break;
          default: 
            write_lit(lsr_proof_file, TO_DIMACS_LIT(witness[i]));
            write_lit(lsr_proof_file, TO_DIMACS_LIT(witness[i + 1]));
        }
      }
    }
  }
}

// Prints those clauses that were globally set to unit during global UP and
// that were marked during UP dependency marking.
static inline void print_active_dependencies(void) {
  for (int i = 0; i < unit_clauses_size; i++) {
    srid_t c = unit_clauses[i];
    if (dependency_markings[c] > generation_before_line_checking) {
      write_clause_id(lsr_proof_file, c + 1); // +1 for DIMACS
    }
  }
}

// Prints the accumulated LSR line, according to UP and clause dependencies.
// Should be printed before incrementing the generation.
static void print_lsr_line(void) {
  current_line++;
  write_lsr_line_start(lsr_proof_file, current_line, 0);
  print_clause();

  // If there are no stored RAT derivations, then no need to print a witness
  if (lsr_line_size > 0) {
    print_witness();
  }

  write_lit(lsr_proof_file, 0); // Separator between (clause + witness) and rest
  print_active_dependencies();

  // If there are no RAT derivations, print the falsifying clause
  if (lsr_line_size == 0 && up_falsified_clause != -1) {
    write_clause_id(lsr_proof_file, up_falsified_clause + 1); // +1 for DIMACS
  } else {
    // Print the RAT derivations
    // In rare cases, up_falsified_clause == -1, meaning that we *did* do RAT
    // checking, but there were no RAT clauses, in which case this portion will be empty
    for (int i = 0; i < lsr_line_size; i++) {
      write_clause_id(lsr_proof_file, lsr_line[i]);
    }
  }

  write_sr_line_end(lsr_proof_file); // Cap the end of the line with a '0'
}

static inline void print_lsr_deletion_line(srid_t clause) {
  // Print the deletion line (TODO: Store later? for backwards checking)
  write_lsr_line_start(lsr_proof_file, current_line, 1);
  write_clause_id(lsr_proof_file, clause + 1);
  write_sr_line_end(lsr_proof_file);
}

static inline void clear_lsr_line(void) {
  lsr_line_size = 0;
}

// Adds the RAT clause ID, in printable format, to `lsr_line`.
static inline void add_RAT_clause_to_lsr_line(srid_t clause) {
  RESIZE_ARR(lsr_line, lsr_line_alloc_size, lsr_line_size, sizeof(int));
  lsr_line[lsr_line_size++] = -(clause + 1);
}

// Adds the clause ID, in printable format, to `lsr_line`.
static inline void add_clause_to_lsr_line(srid_t clause) {
  RESIZE_ARR(lsr_line, lsr_line_alloc_size, lsr_line_size, sizeof(int));
  lsr_line[lsr_line_size++] = (clause + 1);
}

// Marks the clauses causing each literal in the clause to be false.
// Ignore literals that are assumed fresh, whether in CANDIDATE or RAT.
// Literals that were globally set to unit, but are candidate assumed, are ignored.
static inline void mark_clause(srid_t clause, int offset) {
  int *clause_ptr = get_clause_start(clause) + offset; 
  int *clause_end = get_clause_start(clause + 1);
  for (; clause_ptr < clause_end; clause_ptr++) {
    int lit = *clause_ptr;
    int var = VAR_FROM_LIT(lit);
    srid_t reason = up_reasons[var];
    if (reason >= 0) {
      dependency_markings[reason] = alpha_generation;
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
  const llong gen = alpha_generation;
  for (int i = unit_clauses_size - 1; i >= 0; i--) {
    srid_t clause = unit_clauses[i];
    if (dependency_markings[clause] == gen) {
      mark_unit_clause(clause);
    }
  }
}

// Backwards marks the dependencies for the UP derivation.
// Starts the marking at the clause stored in up_falsified_clause.
// NOTE: Every marked clause is stored in unit_clauses, except for up_falsified_clause,
// which is not marked.
static inline void mark_up_derivation(void) {
  mark_entire_clause(up_falsified_clause);
  mark_dependencies();
}

static void store_RAT_dependencies() {
  for (int i = RAT_unit_clauses_index; i < unit_clauses_size; i++) {
    if (dependency_markings[unit_clauses[i]] == alpha_generation) {
      add_clause_to_lsr_line(unit_clauses[i]);
    }
  }

  add_clause_to_lsr_line(up_falsified_clause);
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
 * At the end, `subst_index` and `witness_size` are decreased appropriately.
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
  witness_has_direct_mapped_subst_lit = 0;
  int write_index = -1;
  int skipped_tf_lits = 0, skipped_lits = 0;

  for (int i = 0; i < witness_size; i++) {
    int lit = witness[i];
    int var = VAR_FROM_LIT(lit);
    int keep_lit = 1;
    const int in_tf_mapped = (i < subst_index) ? 1 : 0;
    peval_t lit_alpha = peval_lit_under_alpha(lit);
    peval_t lit_subst = (in_tf_mapped) ? TT : UNASSIGNED;

    // We track whether a literal in the substitution portion becomes true/false
    // If we end up keeping that lit (i.e. keep_lit == 1), then we set a global
    // flag `witness_has_direct_mapped_subst_lit`, which will cause different
    // printing code to be run when printing the witness.
    int subst_is_direct_mapped = 0;

    // If we are in the substitution portion, check the truth value of m
    if (!in_tf_mapped) {
      int mapped_lit = witness[i + 1];
      switch (peval_lit_under_alpha(mapped_lit)) {
        case FF:
          // printf("c   (%d -> %d), but latter was found to be globally false\n",
          //   TO_DIMACS_LIT(lit), TO_DIMACS_LIT(mapped_lit));
          witness[i + 1] = SUBST_FF;
          lit_subst = FF;
          subst_is_direct_mapped = 1;
          break;
        case TT:
          // printf("c   (%d -> %d), but latter was found to be globally true\n",
          //   TO_DIMACS_LIT(lit), TO_DIMACS_LIT(mapped_lit));
          witness[i + 1] = SUBST_TT;
          lit_subst = TT;
          subst_is_direct_mapped = 1;
          break;
        default: break;
      }
    }

    // Now compare the truth value of l in the substitution and alpha
    // TODO: Brittle negation, based on hard-coded values of peval_t.
    if (lit_alpha != UNASSIGNED) {
      if (lit_alpha == lit_subst) {
        // printf("c    Found an unnecessary literal %d at index %d\n", TO_DIMACS_LIT(lit), i);
        keep_lit = 0;
        subst_is_direct_mapped = 0;
        skipped_tf_lits += (in_tf_mapped) ? 1 : 0;
        skipped_lits += (in_tf_mapped) ? 1 : 2;
        if (write_index == -1) {
          write_index = i;
        }
      } else if (lit_alpha == -lit_subst) {
        llong gen = alpha[var];
        PRINT_ERR_AND_EXIT_IF(ABS(gen) == GLOBAL_GEN, 
          "Witness lit is set to negation of UP value.");
      }
    }

    if (keep_lit && write_index != -1) {
      witness[write_index++] = lit;
      if (!in_tf_mapped) {
        witness[write_index++] = witness[i + 1];
      }
    }

    witness_has_direct_mapped_subst_lit |= subst_is_direct_mapped;
    i += (in_tf_mapped) ? 0 : 1;
  }

  // Adjust witness size and subst_index based on the number of removed lits
  subst_index -= skipped_tf_lits;
  witness_size -= skipped_lits;
}

// Moves state from GLOBAL_UP -> CANDIDATE_UP -> RAT_UP.
// Sets the various indexes appropriately.
// If incremented at RAT_UP, resets "back to" a RAT_UP state.
static void increment_state(void) {
  switch (state) {
    case GLOBAL_UP:
      state = CANDIDATE_UP;
      candidate_assumed_literals_index = unit_literals_size;
      candidate_unit_literals_index = unit_literals_size;
      candidate_unit_clauses_index = unit_clauses_size;
      break;
    case CANDIDATE_UP:
      state = RAT_UP;
      RAT_assumed_literals_index = unit_literals_size;
      RAT_unit_literals_index = unit_literals_size;
      RAT_unit_clauses_index = unit_clauses_size;
      break;
    case RAT_UP:
      unit_literals_size = RAT_assumed_literals_index;
      RAT_unit_literals_index = RAT_assumed_literals_index;
      unit_clauses_size = RAT_unit_clauses_index;
      break;
    default: PRINT_ERR_AND_EXIT("Corrupted state.");
  }
}

// Moves state from RAT_UP -> CANDIDATE_UP -> GLOBAL_UP.
// Sets the various indexes appropriately.
static void decrement_state(void) {
  switch (state) {
    case GLOBAL_UP: return;
    case CANDIDATE_UP:
      state = GLOBAL_UP;
      unit_literals_size = candidate_assumed_literals_index;
      unit_clauses_size = candidate_unit_clauses_index;
      break;
    case RAT_UP:
      state = CANDIDATE_UP;
      unit_literals_size = RAT_assumed_literals_index;
      unit_clauses_size = RAT_unit_clauses_index;
      break;
    default: PRINT_ERR_AND_EXIT("Corrupted state.");
  }
}

// Sets the literal to true, and adds it to the unit_literals array.
// Infers the correct generation value from state.
static inline void assume_unit_literal(int lit) {
  llong gen = (state == CANDIDATE_UP) ? ASSUMED_GEN : alpha_generation;
  set_lit_for_alpha(lit, gen);
  resize_units();
  unit_literals[unit_literals_size++] = lit;

  // TODO: While incrementing is slower than setting it when we're done,
  // there's less chance for bugs. Make it be a setting later.
  if (state == CANDIDATE_UP) {
    candidate_unit_literals_index++;
  } else if (state == RAT_UP) {
    RAT_unit_literals_index++;
  }
}

// Sets the literal in the clause to true, assuming it's unit in the clause.
// Then adds the literal to the unit_literals array, to look for more unit clauses later.
// NOTE: When doing unit propagation, take the negation of the literal in the unit_literals array.
static void set_unit_clause(int lit, srid_t clause, llong gen) {
  set_lit_for_alpha(lit, gen);
  up_reasons[VAR_FROM_LIT(lit)] = clause;

  resize_units();
  unit_literals[unit_literals_size++] = lit;
  unit_clauses[unit_clauses_size++] = clause;
}

// Adds a watch pointer for the lit at the specified clause ID
static void add_wp_for_lit(int lit, srid_t clause) {
  // Resize the literal-indexes arrays if lit is outside our allocated bounds
  if (max_var * 2 >= wps_alloc_size) {
    int old_size = wps_alloc_size;
    wps_alloc_size = RESIZE(max_var * 2);
    wps = xrealloc(wps, wps_alloc_size * sizeof(srid_t *));
    wp_alloc_sizes = xrealloc(wp_alloc_sizes, wps_alloc_size * sizeof(int));
    wp_sizes = xrealloc(wp_sizes, wps_alloc_size * sizeof(int));

    // Set to NULL the new spaces in wps
    int added_size = wps_alloc_size - old_size;
    memset(wps + old_size, 0, added_size * sizeof(srid_t *));
    memset(wp_alloc_sizes + old_size, 0, added_size * sizeof(int));
    memset(wp_sizes + old_size, 0, added_size * sizeof(int));
  }

  // Now allocate more space in the wp[lit] array, if needed
  // Handles the case where both are 0 (uninitialized)
  if (wp_sizes[lit] == wp_alloc_sizes[lit]) {
    wp_alloc_sizes[lit] = MAX(INIT_LIT_WP_ARRAY_SIZE, RESIZE(wp_alloc_sizes[lit]));
    wps[lit] = xrealloc(wps[lit], wp_alloc_sizes[lit] * sizeof(srid_t));
  }

  // Finally, add the clause to the wp list
  wps[lit][wp_sizes[lit]] = clause;
  wp_sizes[lit]++;
}

static void remove_wp_for_lit(int lit, srid_t clause) {
  srid_t *wp_list = wps[lit];
  int wp_list_size = wp_sizes[lit];

  // Find the clause in the wp list and remove it
  for (int i = 0; i < wp_list_size; i++) {
    if (wp_list[i] == clause) {
      // Overwrite the removed clause with the last clause in the list
      wp_list[i] = wp_list[wp_list_size - 1];
      wp_sizes[lit]--;
      return;
    }
  }

  // TODO: If below some threshold of size/alloc_sizes, shrink the array
}

// Performs unit propagation. Sets the falsified clause (the contradiction) to
// up_falsified_clause. -1 if not found.
// Any literals found are set to the provided generation value.
static void perform_up(llong gen) {
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
  switch (state) {
    case GLOBAL_UP:    i = global_up_literals_index;         break;
    case CANDIDATE_UP: i = candidate_assumed_literals_index; break;
    case RAT_UP:       i = RAT_assumed_literals_index;       break;
    default: PRINT_ERR_AND_EXIT("Corrupted state.");
  }

  // TODO: Better way of doing this, since the size may increase as we do UP?
  // TODO: When doing backwards checking, use clauses that are already marked
  up_falsified_clause = -1;
  for (; i < unit_literals_size; i++) {
    int lit = NEGATE_LIT(unit_literals[i]);

    // Iterate through its watch pointers and see if the clause becomes unit
    srid_t *wp_list = wps[lit];
    for (int j = 0; j < wp_sizes[lit]; j++) {
      srid_t clause_id = wp_list[j];
      int *clause = get_clause_start(clause_id);
      const int clause_size = get_clause_size(clause_id);
      
      // Lemma: the clause is not a unit clause (yet), and its watch pointers are 
      // the first two literals in the clause (we may reorder literals here).

      // Place the other watch pointer first
      if (clause[0] == lit) {
        clause[0] = clause[1];
        clause[1] = lit;
      }

      int first_wp = clause[0];

      // If the first watch pointer is true, then the clause is satisfied (not unit)
      if (peval_lit_under_alpha(first_wp) == TT) {
        continue;
      }

      // Otherwise, scan the clause for a non-false literal
      int found_new_wp = 0;
      for (int k = 2; k < clause_size; k++) {
        if (peval_lit_under_alpha(clause[k]) != FF) {
          clause[1] = clause[k];
          clause[k] = lit;
          add_wp_for_lit(clause[1], clause_id);
          // Instead of calling remove_wp_for_lit, we can more intelligently swap
          wp_list[j] = wp_list[wp_sizes[lit] - 1];
          wp_sizes[lit]--;
          found_new_wp = 1;
          break;
        }
      }

      if (found_new_wp) {
        j--;       // We need to decrement, since we replaced wp_list[j]
        continue;  
      }

      // We didn't find a replacement watch pointer. Is the first watch pointer false?
      if (peval_lit_under_alpha(first_wp) == FF) {
        // printf("c       [%ld, UP] Found contradiction in clause %d\n", current_line + 1, clause_id + 1);
        up_falsified_clause = clause_id;
        return;
      } else {
        set_unit_clause(first_wp, clause_id, gen); // Add as a unit literal
      }
    }
  }
  
  if (state == GLOBAL_UP) {
    global_up_literals_index = unit_literals_size;
  }
}

// Adds watch pointers / sets units and performs unit propagation.
// Skips clauses already processed (i.e. when adding a new redundant clause,
// only adds watch pointers/sets unit on that clause).
// Should be called when the global state == GLOBAL_UP.
static void add_wps_and_perform_up() {
  PRINT_ERR_AND_EXIT_IF(state != GLOBAL_UP, "state not GLOBAL_UP.");

  int *clause, *next_clause = get_clause_start(wp_processed_clauses);
  int clause_size;

  // Beyond the initial setup, this loop only runs once
  // Make more efficient later?
  for (; wp_processed_clauses < formula_size; wp_processed_clauses++) {
    clause = next_clause;
    next_clause = get_clause_start(wp_processed_clauses + 1);
    clause_size = next_clause - clause;

    // If the clause is unit, set it to be true, do UP later. Otherwise, add watch pointers
    if (clause_size == 1) {
      // The clause is unit - examine its only literal
      int lit = *clause;

      // Check if it is falsified - if so, then we have a UP derivation
      if (peval_lit_under_alpha(lit) == FF) {
        derived_empty_clause = 1;
        up_falsified_clause = wp_processed_clauses;
        mark_up_derivation();
        print_lsr_line();
        return;
      } else {
        // Set its one literal globally to true, and add its negation to the UP queue
        set_unit_clause(lit, wp_processed_clauses, GLOBAL_GEN);
      }
    } else {
      // The clause has at least two literals - make them the watch pointers
      add_wp_for_lit(clause[0], wp_processed_clauses);
      add_wp_for_lit(clause[1], wp_processed_clauses);
    }
  }

  // We don't have an immediate contradiction, so perform unit propagation
  perform_up(GLOBAL_GEN);
  if (up_falsified_clause >= 0) {
    derived_empty_clause = 1;
    mark_up_derivation();
    print_lsr_line();
  }
}

// A clone of of assume_negated_clause() from global_data, but with added bookkeeping. 
// Returns 0 if assumption succeeded, -1 if contradiction found and LSR line emitted.
// Must be called when global state == GLOBAL_UP.
// Even when -1 is returned, the candidate clause is still "assumed".
static int assume_candidate_clause_and_perform_up(void) {
  PRINT_ERR_AND_EXIT_IF(state != GLOBAL_UP, "state not GLOBAL_UP.");
  increment_state();

  // TODO: Find "shortest" UP derivation later
  int satisfied_lit = -1;
  up_falsified_clause = -1; // Clear any previous UP falsifying clause

  for (srid_t i = formula[formula_size]; i < lits_db_size; i++) {
    int lit = lits_db[i];
    int var = VAR_FROM_LIT(lit);

    // Check if the literal is satisfied by prior UP
    // If so, then we have a contradiction
    switch (peval_lit_under_alpha(lit)) {
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
          satisfied_lit = lit;
          up_falsified_clause = up_reasons[var];
        }
        break;
      default: PRINT_ERR_AND_EXIT("Invalid peval_t value.");
    }
  }

  // If we haven't satisfied the clause, we perform unit propagation
  if (up_falsified_clause == -1) {
    perform_up(ASSUMED_GEN);
  }

  // If we have either satisfied the clause, or found a UP derivation, emit it
  if (up_falsified_clause != -1) {
    mark_up_derivation();
    print_lsr_line();
    return -1;
  }

  return 0;
}

// Reverts changes to the data structures made during the assumption of the candidate clause.
// Must be called before adding the candidate to the formula via insert_clause().
// Decrements global state back to GLOBAL_UP.
static void unassume_candidate_clause(void) {
  PRINT_ERR_AND_EXIT_IF(state != CANDIDATE_UP, "state not CANDIDATE_UP.");

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
  for (srid_t i = formula[formula_size]; i < lits_db_size; i++) {
    int lit = lits_db[i];
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
  RESIZE_ARR(RAT_marked_vars, RAT_marked_vars_alloc_size, 
    RAT_marked_vars_size, sizeof(int));
  RAT_marked_vars[RAT_marked_vars_size++] = marked_var;
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
// Call when global state == CANDIDATE_UP.
// Sets the global state to RAT_UP.
static int assume_RAT_clause_under_subst(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(state != CANDIDATE_UP, "state not RAT_UP.");
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
        switch (peval_lit_under_alpha(mapped_lit)) {
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
              up_falsified_clause = reason;
              mark_up_derivation();
            }
            return SATISFIED_OR_MUL;
          case UNASSIGNED:
            assume_unit_literal(NEGATE_LIT(mapped_lit));
            break;
          default: PRINT_ERR_AND_EXIT("Corrupted peval value.");
        }
    }
  }

  clear_RAT_marked_vars();
  return 0;
}

// Call when global state == RAT_UP.
// Decrements state back to CANDIDATE_UP.
static void unassume_RAT_clause(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(state != RAT_UP, "state not RAT_UP.");

  // Clear the UP reasons for the variables set during RAT UP
  for (int i = RAT_unit_literals_index; i < unit_literals_size; i++) {
    int lit = unit_literals[i];
    int var = VAR_FROM_LIT(lit);
    up_reasons[var] = -1; // Clear the reason (gen will clear via bumping)
  }

  decrement_state();
}

////////////////////////////////////////////////////////////////////////////////

// Hashes the provided clause ID.
// The hash function is commutative, meaning that no matter how the clause is
// permuted, the clause will return the same hash value.
// (Could be computed as the literals are parsed and stored, but because only
// dsr-trim hashes clauses, this is better from an encapsulation perspective.)
static unsigned int hash_clause(srid_t clause) {
  unsigned int sum = 0, prod = 1, xor = 0;
  int *clause_ptr, *clause_end;

  // Slightly API-breaking, but since we don't compute these as we parse the
  // clauses, and we store almost-clauses in the formula, we need to know
  // if the clause we are hashing is the newest one or not.
  clause_ptr = get_clause_start(clause);
  if (clause == formula_size) {
    clause_end = lits_db + lits_db_size;
  } else {
    clause_end = get_clause_start(clause + 1);
  }

  for (; clause_ptr < clause_end; clause_ptr++) {
    int lit = *clause_ptr;
    sum += lit;
    prod *= lit;
    xor ^= lit;
  }

  // Hash function borrowed from dpr-trim
  return (1023 * sum + prod ^ (31 * xor)) % clause_id_ht_alloc_size;
}

static void add_clause_hash(srid_t clause) {
  // For now, we don't resize the hash table. TODO: implement resizing.
  // TODO: Implement de-sizing when clauses get deleted.
  unsigned int hash = hash_clause(clause);

  // Allocate a hash table bucket, if it doesn't exist yet
  if (clause_id_ht[hash] == NULL) {
    clause_id_ht[hash] = xmalloc(INIT_CLAUSE_ID_BUCKET_SIZE * sizeof(srid_t));
    clause_id_ht_sizes[hash] = 0;
    clause_id_ht_alloc_sizes[hash] = INIT_CLAUSE_ID_BUCKET_SIZE;
  }

  // Resize the bucket if we've run out of space 
  if (clause_id_ht_sizes[hash] >= clause_id_ht_alloc_sizes[hash]) {
    clause_id_ht_alloc_sizes[hash] = RESIZE(clause_id_ht_sizes[hash]);
    clause_id_ht[hash] = xrealloc(clause_id_ht[hash], 
      clause_id_ht_alloc_sizes[hash] * sizeof(srid_t));
  }

  // Add the clause to the bucket
  clause_id_ht[hash][clause_id_ht_sizes[hash]++] = clause;
}

// Finds and deletes a matching clause (i.e., a permutation of the new clause).
// The deletion is reflected in the hash table and in `lits_db`/`formula`.
// Errors and exits if no matching clause exists.
// Assumes that the clause is not unit (i.e., it has at least two literals).
static void get_and_remove_clause_hash(void) {
  // TODO: Implement de-sizing
  unsigned int hash = hash_clause(formula_size);
  const int *clause_ptr = get_clause_start(formula_size);

  // Now iterate through all clauses in the bucket to find a matching clause
  const srid_t *bucket = clause_id_ht[hash];
  const int bucket_size = clause_id_ht_sizes[hash];
  for (int i = 0; i < bucket_size; i++) {
    srid_t candidate_match = bucket[i];

    // Only check for matching literals if the sizes match
    if (get_clause_size(candidate_match) == new_clause_size) {
      // Most clauses are small (<= 20 lits), so O(n^2) search is good enough
      int *candidate_start = get_clause_start(candidate_match);
      int *candidate_end = get_clause_start(candidate_match + 1);
      int found_match = 1;
      for (int *ptr = candidate_start; ptr < candidate_end; ptr++) {
        int new_lit = *ptr;
        int found_lit = 0;
        for (int j = 0; j < new_clause_size; j++) {
          if (new_lit == clause_ptr[j]) {
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
        // Check if the clause is a global unit clause
        // If it is, error, since we don't want to handle re-running UP
        for (int j = 0; j < unit_clauses_size; j++) {
          if (unit_clauses[j] == candidate_match) {
            PRINT_ERR_AND_EXIT("Deleted clause is a global unit.");
          }
        }

        // The matching clause wasn't unit, so we delete it and its hash
        if (bucket_size > 1) {
          clause_id_ht[hash][i] = bucket[(bucket_size - 1)];
        }
        
        clause_id_ht_sizes[hash]--;

        // Remove the watch pointers for the matching clause
        // Our invariant is that the first two literals are watch pointers
        // Do this before deleting the clause from the formula, because
        // otherwise the garbage collector can move the literals underneath
        remove_wp_for_lit(candidate_start[0], candidate_match);
        remove_wp_for_lit(candidate_start[1], candidate_match);

        // Delete the identified matching clause from the formula
        delete_clause(candidate_match);

        // Remove the literals for the parsed deletion clause in lits_db
        lits_db_size -= new_clause_size;

        print_lsr_deletion_line(candidate_match);
        return;
      }
    }
  }

  PRINT_ERR_AND_EXIT("No matching clause found for deletion.");
}

////////////////////////////////////////////////////////////////////////////////

// Parses the next DSR line. If it's a deletion line, the clause is deleted.
// Otherwise, the new candidate clause and the witness are parsed and stored.
// Returns ADDITION_LINE or DELETION_LINE for the line type.
// Errors and exits if a read error is encountered.
static inline int parse_dsr_line(void) {
  int line_type = read_dsr_line_start(sr_certificate_file);
  switch (line_type) {
    case DELETION_LINE:;
      int is_tautology = parse_clause(sr_certificate_file);
      PRINT_ERR_AND_EXIT_IF(is_tautology || new_clause_size <= 1, 
        "Clause to delete was a tautology, was empty, or was a unit.");
      get_and_remove_clause_hash();
      break;
    case ADDITION_LINE:
      parse_sr_clause_and_witness(sr_certificate_file);
      break;
    default:
      PRINT_ERR_AND_EXIT("Corrupted line type.");
  }

  return line_type;
}

static void check_sr_line(void) {
  // We save the generation at the start of line checking so we can determine
  // which clauses are marked in the dependency_markings array.
  generation_before_line_checking = alpha_generation;
  alpha_generation++;
  subst_generation++;
  clear_lsr_line();

  // TODO: Replace -1/0 with enum/#define
  if (assume_candidate_clause_and_perform_up() == -1) {
    // printf("c Found UP derivation with candidate clause, skipping RAT check\n");
    goto candidate_valid;
  }

  // Since we didn't derive UP contradiction, the clause should be nonempty
  PRINT_ERR_AND_EXIT_IF(new_clause_size == 0, "Didn't derive empty clause.");

  // Assumes the witness into the substitution data structure.
  minimize_witness();
  assume_subst();

  // Now do RAT checking between min and max clauses to check (inclusive)
  // printf("c   [%d] Checking clauses %d to %d\n", 
  //   current_line + 1, min_clause_to_check + 1, max_clause_to_check + 1);
  int *clause, *next_clause = get_clause_start(min_clause_to_check);
  int clause_size;
  for (srid_t i = min_clause_to_check; i <= max_clause_to_check; i++) {
    if (is_clause_deleted(i)) continue;

    // Evaluate the clause under the substitution
    switch (reduce_subst_mapped(i)) {
      case NOT_REDUCED:
      case SATISFIED_OR_MUL:
        continue;
      case REDUCED:
        add_RAT_clause_to_lsr_line(i);

        // If the RAT clause is not satisfied, do unit propagation
        if (assume_RAT_clause_under_subst(i) != SATISFIED_OR_MUL) {
          perform_up(alpha_generation);
          PRINT_ERR_AND_EXIT_IF(up_falsified_clause == -1, "No RAT UP contradiction.");
          mark_up_derivation();
          store_RAT_dependencies();
        }

        // Undo the changes we made by (potentially partially) assuming the RAT clause
        unassume_RAT_clause(i);
        alpha_generation++;
        break;
      case CONTRADICTION:
        PRINT_ERR_AND_EXIT("RAT contradiction: should have had UP derivation.");
      default: PRINT_ERR_AND_EXIT("Corrupted reduction value.");
    }    
  }

  // TODO: For backwards checking, don't print here, but store it instead
  print_lsr_line();

  // Congrats - the line checked out! Undo the changes we made to the data structures
candidate_valid:
  unassume_candidate_clause();
  add_clause_hash(formula_size);
  insert_clause_first_last_update(); // Officially add the clause to the formula
  add_wps_and_perform_up();
}

static void process_sr_certificate(void) {
  derived_empty_clause = 0;
  alpha_generation = 1;

  state = GLOBAL_UP;
  add_wps_and_perform_up();

  // TODO: Allow for proofs that don't derive the empty clause
  // TODO: Handle deletion lines
  while (!derived_empty_clause && has_another_line(sr_certificate_file)) {
    if (parse_dsr_line() == ADDITION_LINE) {
      // printf("c Parsed line %d, new clause has size %d and witness with size %d\n", 
      //   current_line + 1, new_clause_size, witness_size);
      resize_sr_trim_data(); 
      check_sr_line();
    }
  }

  fclose(sr_certificate_file);
  if (lsr_proof_file != stdout) {
    fclose(lsr_proof_file);
  }

  if (derived_empty_clause) {
    printf("s VERIFIED UNSAT\n");
  } else {
    printf("s VALID\n");
  }
}

int main(int argc, char **argv) {
  if (argc < 3) {
    print_usage();
    return 0;
  }

  extern char *optarg;
  char opt;
  //while ((opt = getopt(argc, argv, 
  //        "dhvqQza:A:c:C:f:g:G:l:m:o:r:s:t:T:w:")) != -1) {

  //}

  // Open all the necessary files at the start, to ensure that we don't do
  // work unless the files exist. Also might stop race conditions.
  FILE *cnf_file = xfopen(argv[1], "r");
  sr_certificate_file = xfopen(argv[2], "r");
  lsr_proof_file = (argc == 3) ? stdout : xfopen(argv[3], "w");

  parse_cnf(cnf_file);
  init_sr_trim_data();

  printf("c Formula has ");
  printf(SRID_FORMAT_STR, formula_size);
  printf(" clauses and %d variables.\n", max_var);

  process_sr_certificate();
  return 0;
}