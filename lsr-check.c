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
#include "sr_parser.h"

#define DELETION_LINE     (10)
#define ADDITION_LINE     (20)

////////////////////////////////////////////////////////////////////////////////

static int max_line_id = 0; // Max line identifier checked/parsed.

// The clause ID tokens from the SR file. Not 0-indexed, negatives mark RAT hints.
static int *hints = NULL;
static int hints_size = 0;
static int hints_alloc_size = 0;

// Metadata about the SR proof line
static int num_RAT_hints = 0;

static FILE *sr_file = NULL;

////////////////////////////////////////////////////////////////////////////////

static void print_usage(void) {
  printf("c Usage: ./sr-check <cnf-file> <sr-file>\n");
}

// Initializes check-specific data structures. Call after parsing the CNF file.
static void init_sr_check_data(void) {
  hints_alloc_size = formula_size * 10;
  hints_size = 0;
  hints = xmalloc(hints_alloc_size * sizeof(int));
}

/** Inserts a clause ID hint into the hints array.
 *  Unlike for the literals, we leave the clause IDs as-is, no remapping.
 *  That way, we can still tell where the RAT hints start.
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
        // printf("[%d] Found satisfied clause %d in UP part of hint (index %d)\n",
        //  max_line_id, up_clause, hint_index);
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
  subst_index = INT_MAX;

  READ_NUMERICAL_TOKEN(res, sr_file, &line_id); // First token is the line id

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

  // Read in the clause and witness portions of the SR proof line
  parse_sr_clause_and_witness(sr_file);

  // Now consume the rest of the line. The hints are stored in the hints array,
  // keeping the clause IDs as-is so we can tell where the RAT hints start.
  READ_NUMERICAL_TOKEN(res, sr_file, &token);
  while (token != 0) {
    insert_hint(token);
    READ_NUMERICAL_TOKEN(res, sr_file, &token);
  }

  return ADDITION_LINE;
}

static void check_line(void) {
  // Now that the line is parsed, set up the negation of the candidate clause
  // We set each variable's value to alpha_generation + num_RAT_hints
  alpha_generation++;
  subst_generation++;
  long negated_clause_gen = alpha_generation + num_RAT_hints;

  // Set the negated literals of the candidate clause to be true
  assume_negated_clause(formula_size, negated_clause_gen);

  // Now take the UP hints (if any) to extend alpha
  int hint_index = 0;
  if (unit_propagate(&hint_index, negated_clause_gen) == CONTRADICTION) {
    goto finish_line;
  }

  // Lemma: hint_index >= 0 and past the UP hints
  // Lemma: hint_index >= hints_size OR hints[hint_index] < 0

  // Double-check that the proposed clause is not the empty clause
  // (The empty clause cannot have a witness, and must have contradiction through UP)
  PRINT_ERR_AND_EXIT_IF(new_clause_size == 0, "UP didn't derive contradiction for empty clause.");
  // Lemma: new_clause_size > 0

  assume_subst();
  PRINT_ERR_AND_EXIT_IF(min_clause_to_check < 0 || max_clause_to_check > formula_size
    || min_clause_to_check > max_clause_to_check,
      "Clause range to check is inconsistent.");

  // Now for each clause, check that it is either
  //   - Satisfied or not reduced by the witness
  //   - A RAT clause, whose hints derive contradiction
  int rat_hint_start_index = hint_index;
  int matching_hint_index;
  for (int i = min_clause_to_check; i <= max_clause_to_check; i++) {
    if (is_clause_deleted(i)) {
      continue; // Skip deleted clauses, nothing to prove
    }

    // Check how the clause behaves under the substitution
    // TODO: Cache the computed reduction under subst into an array, which resizes to max_clause_size?
    switch (reduce_subst_mapped(i)) {
      case NOT_REDUCED:
      case SATISFIED_OR_MUL:
        continue;
      case REDUCED:
        // Find the reduced clause's hint
        // Invariant: hint_index points at the "next negative hint," if the hints are sorted
        // If the hints are sorted, check that the next one is valid
        if (hint_index < hints_size && -(hints[hint_index] + 1) == i) {
          matching_hint_index = hint_index;
        } else {
          // Scan through all the RAT hints for a negative one matching this clause
          matching_hint_index = -1;
          for (int h = rat_hint_start_index; h < hints_size; h++) {
            if (-(hints[h] + 1) == i) {
              matching_hint_index = h;
              hint_index = MAX(hint_index, h);
              break;
            }
          }

          PRINT_ERR_AND_EXIT_IF(matching_hint_index == -1, "RAT clause has no RAT hint.");
        }

        // We successfully found a matching RAT hint
        // Assume the negation of the RAT clause and perform unit propagation
        int neg_res = assume_negated_clause_under_subst(i, alpha_generation);

        // RAT clauses can have no RAT hints, and so must be immediately satisfied.
        // This occurs if the candidate unit propagations set a literal, satisfying the RAT clause.
        // Notably, this is different than the witness satisfying the clause.
        // If the RAT clause is satisfied by our prior UPs, then we scan to the next RAT hint.
        if (neg_res == SATISFIED_OR_MUL) {
          // Scan the matching_hint_index forward until the hint is once again negative
          do {
            matching_hint_index++;
          } while (hints[matching_hint_index] > 0 && matching_hint_index < hints_size);
          hint_index = MAX(hint_index, matching_hint_index);
          continue;
        }

        matching_hint_index++;
        // Now perform unit propagation. We expect CONTRADICTION. If not, error
        if (unit_propagate(&matching_hint_index, alpha_generation) != CONTRADICTION) {
          PRINT_ERR_AND_EXIT("RAT clause UP didn't derive contradiction.");
        }

        // Once we have succeeded on UP, set the hint_index forward
        // If the hints are sorted, this moves the hint_index along one grouping
        hint_index = MAX(hint_index, matching_hint_index);
        alpha_generation++;
        break;
      case CONTRADICTION:
        PRINT_ERR_AND_EXIT("RAT contradiction: should have had UP derivation.");
      default: PRINT_ERR_AND_EXIT("Corrupted clause reduction.");
      }
  }

finish_line:
  alpha_generation = negated_clause_gen;
  if (new_clause_size == 0) {
    derived_empty_clause = 1;
  } else {
    insert_clause_first_last_update();
  }
}

static void check_proof() {
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

  // Open all the necessary files at the start, to ensure that we don't do
  // work unless the files exist. Also might stop race conditions.
  FILE *cnf_file = xfopen(argv[1], "r");
  sr_file = xfopen(argv[2], "r");

  parse_cnf(cnf_file);
  init_sr_check_data();

  printf("c Formula has %d clauses and %d variables.\n", formula_size, max_var);

  check_proof();
  return 0;
}