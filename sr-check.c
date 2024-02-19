/**
 * @file sr-check.c
 * @brief A substitution redundancy checker, based on lpr-check.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-01-23
 */

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>
#include <math.h>

#include "xio.h"
#include "global_data.h"
#include "xmalloc.h"
#include "cnf_parser.h"

#define RESIZE_AND_SET_ARRAY(arr, alloc_size, size, data_size, filler)  do {   \
    if (size >= alloc_size) {                                                  \
      int old_alloc_size_abcdefg = alloc_size;                                 \
      alloc_size = RESIZE(size);                                               \
      arr = xrealloc(arr, alloc_size * data_size);                             \
      memset(arr + old_alloc_size_abcdefg, filler,                             \
        (alloc_size - old_alloc_size_abcdefg) * data_size);                    \
    }                                                                          \
  } while (0)

#define DELETION_LINE     10
#define ADDITION_LINE     20
      
////////////////////////////////////////////////////////////////////////////////

static int max_line_id = 0; // Max line identifier checked/parsed.

/** Place to store SR lines. */
static int *witness = NULL;
static int witness_size = 0;
static int witness_alloc_size = 0;

// The clause ID tokens from the SR file. Not 0-indexed, negatives mark RAT hints.
static int *hints = NULL;
static int hints_size = 0;
static int hints_alloc_size = 0;

// Metadata about the SR proof line
static int num_RAT_hints = 0;

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
static int min_clause_to_check = 0;
static int max_clause_to_check = 0;
static int subst_pair_incomplete = 0;

static int new_clause_size = 0;
static int pivot = 0;
static int derived_empty_clause = 0;

// Witnesses in SR can have both literals set to true/false, as in LRAT/LPR,
// or they can set variables to other literals. The point at which the witness
// switches from LPR to substitution is updated when an SR proof line is parsed.
static int subst_index = 0;

static FILE *sr_file = NULL;

////////////////////////////////////////////////////////////////////////////////

void print_usage(void) {
  printf("c Usage: ./sr-check <cnf-file> <sr-file>\n");
}

// Initializes check-specific data structures. Call after parsing the CNF file.
void init_sr_data(void) {
  witness_alloc_size = max_var * 2;
  witness_size = 0;
  witness = xmalloc(witness_alloc_size * sizeof(int));

  hints_alloc_size = formula_size * 10;
  hints_size = 0;
  hints = xmalloc(hints_alloc_size * sizeof(int));
}

static void set_min_and_max_clause_to_check(int lit) {
  update_first_last_clause(lit);
  if (lits_first_clause[lit] != -1) {
    min_clause_to_check = MIN(min_clause_to_check, lits_first_clause[lit]); 
    max_clause_to_check = MAX(max_clause_to_check, lits_last_clause[lit]);
  }
}

static void insert_witness_lit(int lit) {
  // Resize if inserting the literal would exceed the allocated size
  RESIZE_ARR(witness, witness_alloc_size, witness_size, sizeof(int));
  witness[witness_size] = lit;
  witness_size++;

  // If we are reading in UP literals, or the first half of a subst mapping
  if (subst_index == INT_MAX) {
    // Since a UP literal is set to true in the witness, clauses with the
    // negation of the literal get reduced, so must be checked
    int neg_lit = NEGATE_LIT(lit);
    set_min_and_max_clause_to_check(neg_lit);
  } else if (subst_pair_incomplete) {
    // If a mapping, we need to check both lit and its negation
    int neg_lit = NEGATE_LIT(lit);
    set_min_and_max_clause_to_check(lit);
    set_min_and_max_clause_to_check(neg_lit);
  }
}

/** Inserts a clause ID hint into the hints array.
 *  Unlike for the literals, we leave the clause IDs as-is, no remapping
 *  That way, we can still tell where the RAT hints start
 */
static void insert_hint(int clause_id) {
  RESIZE_ARR(hints, hints_alloc_size, hints_size, sizeof(int));
  // Check that the clause_id is in range
  int id = ABS(clause_id) - 1;
  PRINT_ERR_AND_EXIT_IF(id > formula_size || is_clause_deleted(id),
    "Clause ID in the SR proof line is out of bounds or is deleted.");
  hints[hints_size] = clause_id;
  hints_size++;
  if (clause_id < 0) {
    num_RAT_hints++;
  }
}

// Computes the reduction of the clause under the partial assignment.
// Returns SATISFIED_OR_MUL, or CONTRADICTION, or the unit lit.
static int reduce(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(is_clause_deleted(clause_index),
    "Trying to unit propagate on a deleted clause.");

  int unit_lit = -1;
  int *start = get_clause_start(clause_index);
  int *end = get_clause_start(clause_index + 1);
  for (; start < end; start++) {
    int lit = *start;
    switch (peval_lit_under_alpha(lit)) {
      case UNASSIGNED:
        if (unit_lit == -1) {
          unit_lit = lit;
        } else {
          return SATISFIED_OR_MUL;
        }
        break;
      case FF: break;
      case TT: return SATISFIED_OR_MUL;
      default: PRINT_ERR_AND_EXIT("Corrupted alpha evaluation.");
    }
  }

  return (unit_lit == -1) ? CONTRADICTION : unit_lit;
}

// Evaluate the clause under the substitution. SATISFIED_OR_MUL is satisfied only.
static int reduce_subst_mapped(int clause_index) {
  PRINT_ERR_AND_EXIT_IF(is_clause_deleted(clause_index),
    "Trying to unit propagate on a deleted clause.");

  int id_mapped_lits = 0, falsified_lits = 0;
  int *start = get_clause_start(clause_index);
  int *end = get_clause_start(clause_index + 1);
  int size = end - start;

  for (; start < end; start++) {
    int lit = *start;
    int mapped_lit = get_lit_from_subst(lit);
    switch (mapped_lit) {
      case SUBST_TT: return SATISFIED_OR_MUL;
      case SUBST_FF: falsified_lits++; break;
      case SUBST_UNASSIGNED: mapped_lit = lit;
      default:
        if (mapped_lit == lit) {
          id_mapped_lits++;
        }

        // Check for tautology
        // TODO: Alternatively, write a set_lit_for_taut operation that
        // returns whether tautology happens. In most cases, tautology doesn't
        // happen, so the fast path should be simple checking
        switch (peval_lit_under_taut(mapped_lit)) {
          case UNASSIGNED: // Not encountered mapped_lit or negation before
            set_lit_for_taut(mapped_lit, current_generation);
            break;
          case FF: return SATISFIED_OR_MUL; // Negation encountered before
          case TT: break; // Encountered mapped_lit before, so ignore
          default: PRINT_ERR_AND_EXIT("Corrupted tautology evaluation.");
        }
    }
  }

  if (falsified_lits == size) {
    return CONTRADICTION;
  } else if (id_mapped_lits == size) {
    return NOT_REDUCED;
  } else {
    return REDUCED;
  }
}

// Perform unit propagation starting from a hint index. Stops if end or negative hint.
// Returns CONTRADICTION if false derived, or 0 otherwise. Updates hint index
static int unit_propagate(int *hint_ptr, long gen) {
  int up_clause, up_res, hint_index = *hint_ptr;
  while (hint_index < hints_size && (up_clause = hints[hint_index]) > 0) {
    // Perform unit propagation against alpha on up_clause
    // Subtract one from the identifier because it's 1-indexed in the proof line
    up_res = reduce(up_clause - 1);
    switch (up_res) {
      case CONTRADICTION: // The line checks out, and we can add the clause
        // Scan the hint_index forward until a negative hint is found
        do {
          hint_index++;
        } while (hints[hint_index] > 0 && hint_index < hints_size);
        *hint_ptr = hint_index;
        return CONTRADICTION;
      case SATISFIED_OR_MUL: // Unit propagation shouldn't give us either
        PRINT_ERR_AND_EXIT("Found satisfied clause in UP part of hint.");
      default: // We have unit on a literal - add to alpha
        set_lit_for_alpha(up_res, gen);
    }

    hint_index++;
  }

  *hint_ptr = hint_index;
  return 0;
}

////////////////////////////////////////////////////////////////////////////////

// Parses the next SR line. Returns either DELETION_LINE or ADDITION_LINE.
// If deletion line, the deletions are handled already.
static int parse_line(void) {
  int line_id, token, res;
  witness_size = hints_size = num_RAT_hints = new_clause_size = 0;
  min_clause_to_check = INT_MAX;
  max_clause_to_check = 0;
  subst_pair_incomplete = 0;
  subst_index = INT_MAX;

  READ_NUMERICAL_TOKEN(res, sr_file, &line_id); // Grab line id. Should be positive

  // Now we test for a deletion line
  res = fscanf(sr_file, "d %d", &token);
  if (res == 1) {
    // We have a deletion line, as there was a match in fscanf()
    // Check that the line id is (non-strictly) monotonically increasing
    PRINT_ERR_AND_EXIT_IF(line_id < max_line_id, "Deletion line id decreases.");
    max_line_id = line_id;   // Lemma: line_id >= max_line_id

    // Now loop on tokens until a zero is read, deleting clauses along the way
    while (token != 0) {
      PRINT_ERR_AND_EXIT_IF(token < 0, "Deletion line has negative clause ID.");
      delete_clause(token - 1);
      READ_NUMERICAL_TOKEN(res, sr_file, &token);
    }

    return DELETION_LINE; // A deletion line is always valid, so there's nothing more to check
  }

  // Since we don't have a deletion line, we have an addition line
  // Check that the line id is strictly monotonically increasing
  PRINT_ERR_AND_EXIT_IF(line_id <= max_line_id, "Addition line id doesn't increase.");
  max_line_id = line_id;  // Lemma: line_id > max_line_id

  // In case a line is "skipped", cap off empty clauses until formula size catches up
  while (formula_size < max_line_id - 1) {
    insert_clause();
    delete_clause(formula_size - 1);
  }

  /* Now consume the rest of the line. The literals for the candidate clause are
     stored in the lits_db array. We can add eagerly add the literals in the 
     clause because if the clause is redundant, we'd add it to the formula 
     anyway, and if the clause doesn't check, then we stop the proof.
     Store the witness and hints in the appropriate arrays, too.  */
  int lit, clause, num_times_found_pivot = 0;
  int zeros_left = 2;  // Two zeroes are expected in a well-formed SR proof line
  while (zeros_left > 0) {
    READ_NUMERICAL_TOKEN(res, sr_file, &token);

    if (token == 0) {
      zeros_left--;
      continue;
    }

    // Lemma: token != 0. What part of the line are we at?
    switch (zeros_left) {
      case 2: // We're reading in the clause/witness - but which part?
        lit = FROM_DIMACS_LIT(token);
        if (num_times_found_pivot == 0) {
          pivot = lit; // First lit in a nonempty candidate clause is the pivot
          num_times_found_pivot++;
        } else if (lit == pivot) {
          num_times_found_pivot++;
        }

        // The pivot demarcates different areas of the clause + witness part
        switch (num_times_found_pivot) {
          case 1: // We're reading in the clause
            insert_lit_no_first_last_update(lit);
            new_clause_size++;
            break;
          case 3: // We're reading in the substitution part of the witness (waterfall!)
            subst_index = (subst_index == INT_MAX) ? witness_size : subst_index;
            subst_pair_incomplete = !subst_pair_incomplete;
          case 2: // We're reading in the LPR part of the witness
            insert_witness_lit(lit);
            break;
          default: PRINT_ERR_AND_EXIT("Seen pivot more than 3 times.");
        }

        break;
      case 1: // We're reading in the UP/RAT hints 
        insert_hint(token); break;
      case 0: break;
      default: PRINT_ERR_AND_EXIT("Corrupted zeros_left value.");
    }
  }

  if (subst_pair_incomplete) {
    PRINT_ERR_AND_EXIT("Missing second half of subst mapping pair.");
  }

  // printf("c Checking addition line %d, expecting %d RAT hints among %d hints for gen %ld\n", 
    //line_id, num_RAT_hints, hints_size, current_generation);
  return ADDITION_LINE;
}

static void check_line(void) {
  // Now that the line is parsed, set up the negation of the candidate clause
  // We set each variable's value to current_generation + num_RAT_hints
  current_generation++;
  long negated_clause_gen = current_generation + num_RAT_hints;

  // Set the negated literals of the candidate clause to be true
  assume_negated_clause(formula_size, negated_clause_gen);

  // Now take the UP hints (if any) to extend alpha
  int hint_index = 0;
  if (unit_propagate(&hint_index, negated_clause_gen) == CONTRADICTION) {
    goto finish_line;
  }

  // printf("c   Done unit propagating, hint_index = %d\n", hint_index);

  // Lemma: hint_index >= 0 and past the UP hints

  // Double-check that the proposed clause is not the empty clause
  // (The empty clause cannot have a witness, and must have contradiction through UP)
  PRINT_ERR_AND_EXIT_IF(new_clause_size == 0, "UP didn't derive contradiction for empty clause.");
  // Lemma: new_clause_size > 0

  // Add the witness, if it exists. It not, set it to the pivot (first lit in new clause)
  set_mapping_for_subst(pivot, SUBST_TT, negated_clause_gen);

  // TODO: Update the first/last for pivot?
  min_clause_to_check = MIN(min_clause_to_check, lits_first_clause[pivot]);
  max_clause_to_check = MAX(max_clause_to_check, lits_last_clause[pivot]);
  for (int i = 1; i < witness_size; i++) {
    if (i < subst_index) {
      set_mapping_for_subst(witness[i], SUBST_TT, negated_clause_gen);
    } else {
      set_mapping_for_subst(witness[i], witness[i + 1], negated_clause_gen);
      i++;
    }
  }

  // Now for each clause, check that it is either
  //   - Satisfied, or not reduced, by the witness
  //   - A RAT clause, whose hints derive contradiction
  // We assume that the RAT hints are sorted in order
  // printf("c   [%d] Checking clauses %d to %d\n", max_line_id, min_clause_to_check, max_clause_to_check);
  int hint = ABS(hints[hint_index]) - 1;
  for (int i = min_clause_to_check; i <= max_clause_to_check; i++) {
    if (is_clause_deleted(i)) {
      continue; // Skip deleted clauses, nothing to prove
    }

    // printf("c     [%d] checking clause %d (hi %d [%d])\n", max_line_id, i + 1, hint_index, hint + 1);

    // Check if the clause is the next RAT hint
    // (Assume no RAT hint is omitted, and the RAT hints are ordered by clause ID)
    // Lemma: (hint_index < hints_size) -> (hints[hint_index] < 0)
    if (hint_index < hints_size && i == hint) {
      // printf("c    [%d] hint_index %d, %d, is RAT\n", max_line_id, hint_index, hint + 1);
      // Assume the negation of the RAT clause and perform unit propagation
      // We expect CONTRADICTION. If not, error
      int neg_res = assume_negated_clause_under_subst(i, current_generation);

      // TODO: Cayden ask Marijn question
      // Apparently, RAT clauses can have no RAT hints, and so must be immediately satisfied
      if (neg_res == SATISFIED_OR_MUL) {
        // Scan the hint_index forward until the hint is once again negative
        do {
          hint_index++;
        } while (hints[hint_index] > 0 && hint_index < hints_size);
        hint = ABS(hints[hint_index]) - 1;
        continue;
      }
      
      hint_index++;
      if (unit_propagate(&hint_index, current_generation) != CONTRADICTION) {
        PRINT_ERR_AND_EXIT("RAT clause UP didn't derive contradiction.");
      }
      hint = ABS(hints[hint_index]) - 1;
    } else {
      // Check that the clause is satisfied or not reduced by the witness
      switch (reduce_subst_mapped(i)) {
        case NOT_REDUCED:
        case SATISFIED_OR_MUL:
          continue;
        case REDUCED: 
          printf("c [%d] Reduced clause %d has not RAT hint\n", max_line_id, i + 1);
          PRINT_ERR_AND_EXIT("Reduced clause has no RAT hint.");
        case CONTRADICTION: PRINT_ERR_AND_EXIT("Contradiction derived in non-RAT clause.");
        default: PRINT_ERR_AND_EXIT("Corrupted clause reduction.");
      }
    }
  }

finish_line:
  current_generation = negated_clause_gen;
  if (new_clause_size == 0) {
    derived_empty_clause = 1;
  } else {
    insert_clause_first_last_update();
  }
}

static void check_proof(char *filename) {
  sr_file = xfopen(filename, "r");

  do {
    switch (parse_line()) {
      case DELETION_LINE: continue;
      case ADDITION_LINE: check_line(); break;
      default: PRINT_ERR_AND_EXIT("Corrupted line type.");
    }
  } while (!derived_empty_clause);

  fclose(sr_file);
  printf("s VERIFIED UNSAT\n");
}

int main(int argc, char *argv[]) {
  if (argc != 3) {
    print_usage();
    PRINT_ERR_AND_EXIT("Incorrect number of arguments.");
  }

  parse_cnf(argv[1]);
  init_sr_data();

  printf("c CNF formula claims to have %d clauses and %d variables.\n", formula_size, max_var);

  check_proof(argv[2]);
  return 0;
}