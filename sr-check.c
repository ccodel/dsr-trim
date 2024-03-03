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
static int derived_empty_clause = 0;

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

  // Lemma: hint_index >= 0 and past the UP hints

  // Double-check that the proposed clause is not the empty clause
  // (The empty clause cannot have a witness, and must have contradiction through UP)
  PRINT_ERR_AND_EXIT_IF(new_clause_size == 0, "UP didn't derive contradiction for empty clause.");
  // Lemma: new_clause_size > 0

  assume_subst(negated_clause_gen);

  // Now for each clause, check that it is either
  //   - Satisfied, or not reduced, by the witness
  //   - A RAT clause, whose hints derive contradiction
  // We assume that the RAT hints are sorted in order
  int hint = ABS(hints[hint_index]) - 1;
  for (int i = min_clause_to_check; i <= max_clause_to_check; i++) {
    if (is_clause_deleted(i)) {
      continue; // Skip deleted clauses, nothing to prove
    }

    // Check if the clause is the next RAT hint
    // (Assume no RAT hint is omitted, and the RAT hints are ordered by clause ID)
    // Lemma: (hint_index < hints_size) -> (hints[hint_index] < 0)
    if (hint_index < hints_size && i == hint) {
      // Assume the negation of the RAT clause and perform unit propagation
      int neg_res = assume_negated_clause_under_subst(i, current_generation);

      // RAT clauses can have no RAT hints, and so must be immediately satisfied.
      // This occurs if the candidate unit propagations set a literal, satisfying the RAT clause.
      // Notably, this is different than the witness satisfying the clause.
      // If the RAT clause is satisfied by our prior UPs, then we scan to the next RAT hint.
      if (neg_res == SATISFIED_OR_MUL) {
        // Scan the hint_index forward until the hint is once again negative
        do {
          hint_index++;
        } while (hints[hint_index] > 0 && hint_index < hints_size);
        hint = ABS(hints[hint_index]) - 1;
        continue;
      }
      
      hint_index++;
      // Now perform unit propagation. We expect CONTRADICTION. If not, error
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
        case REDUCED:       PRINT_ERR_AND_EXIT("Reduced clause has no RAT hint.");
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
  init_sr_check_data();

  printf("c CNF formula claims to have %d clauses and %d variables.\n", formula_size, max_var);

  check_proof(argv[2]);
  return 0;
}