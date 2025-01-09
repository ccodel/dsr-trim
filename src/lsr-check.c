/**
 * @file sr-check.c
 * @brief A linear substitution redundancy checker, based on lpr-check.
 * 
 *  This tool checks linear substitution redundancy (LSR) proofs produced
 *  by the `dsr-trim` tool. LSR proofs are (roughly) used to show that two 
 *  propositional logic formulas are equisatisfiable, meaning that the
 *  original formula is satisfiable if and only if the derived formula is.
 *  LSR proofs do this by incrementally adding new clauses to the formula.
 *  The proof checker must determine that these clauses are redundant, meaning
 *  that adding them to the formula does not affect satisfiability.
 *  (In other words, that F and (F and C) are equisatisfiable.)
 * 
 *  In most cases, LSR proofs are *unsatisfiability* proofs, meaning that
 *  the empty clause is eventually shown to be redundant. Since the empty
 *  clause is by definition unsatisfiable, this makes the original formula
 *  unsatisfiable as well.
 * 
 *  (LSR proofs may also include deletion lines, so a proof that does not
 *  show unsatisfiability may not show true equisatisfiability, since
 *  deleting a clause may make the formula satisfiable.)
 * 
 *  LSR proofs may be checked in linear time (with respect to the size of
 *  the proof and the formula) due to the presence of unit propagation (UP)
 *  hints, which indicate the next step in performing UP. These hints are
 *  added to DSR proofs by `dsr-trim`.
 * 
 *  All LRAT and LPR proofs are automatically LSR proofs, so `lsr-check`
 *  provides a superset of the functionality of similar checkers, such as
 *  `lrat-check`, `lpr-check`, and `cake_lpr`.
 * 
 *  At a high-level, `lsr-check` works as follows.
 * 
 *  After parsing a CNF formula, `lsr-check` checks LSR addition and deletion
 *  lines until either the empty clause is derived or until there are no
 *  more lines to check.
 * 
 *  Each addition line has the following form:
 * 
 *   <id> [clause] [witness] 0 [UP hints] [RAT hints] 0
 * 
 *  where:
 * 
 *  <id> is a 1-indexed line identifier. `lsr-check` requires these IDs to
 *  monotonically increase (although some other proof checkers allow
 *  the IDs to specify *any* deleted or non-existent clause)).
 *  Any unit propagation (UP) hints refer to the clause by this ID.
 * 
 *  [clause] is a list of literals in the candidate redundant clause.
 *  This clause may be empty. If so, then no witness or RAT hints can 
 *  be provided.
 * 
 *  [witness] is a substitution witness mapping literals to either 
 *  true or false; or from variables to other literals.
 * 
 *  [UP hints] and [RAT hints] are groups of clause IDs that guide
 *  unit propagation. Each group of RAT hints start with the negative
 *  clause ID of the RAT clause to check.
 * 
 *  Deletion lines specify the clause IDs of the clauses to delete from
 *  the formula. This has the effect of making it easier and more efficient
 *  to show redundancy.
 * 
 *  `lsr-check` contains two parsing strategies: eager and streaming.
 *  When eagerly parsing, the entire proof is read into memory before
 *  proof checking begins. Otherwise, the proof is streamed (perhaps from
 *  `stdin`), and the proof is checked as it is read. THis is helpful for
 *  very large proofs that cannot be written to disk.
 *
 *  More details can be found in `dsr-trim`, or in the paper:
 * 
 *    "Verified Substitution Redundancy Checking"
 *    Cayden Codel, Jeremy Avigad, Marijn Heule
 *    In FMCAD 2024
 *  
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2024-01-23
 */

#include <string.h>
#include <getopt.h>

#include "xio.h"
#include "logger.h"
#include "global_data.h"
#include "global_parsing.h"
#include "range_array.h"
#include "xmalloc.h"
#include "cnf_parser.h"
#include "sr_parser.h"

/*
 * Each LSR proof line starts with a line iD. This ID (almost always) starts
 * at one more than the number of CNF clauses. These IDs are 1-indexed, so
 * we must subtract 1 when referring to the formula data structure.
 * 
 * However, we 0-index these line IDs when referring to witnesses, hints,
 * and deletions, and we start them at 0. These macros do the conversions
 * we need, with the convention that the `line_num` is 0-indexed, while
 * the `line_id` is essentially `num_cnf_clauses`-indexed.
 */

#define LINE_ID_FROM_LINE_NUM(line_num)   ((line_num) + num_cnf_clauses + 1)
#define CLAUSE_ID_FROM_LINE_NUM(line_num) ((line_num) + num_cnf_clauses)
#define LINE_NUM_FROM_LINE_ID(line_id)    ((line_id) - (num_cnf_clauses + 1))

////////////////////////////////////////////////////////////////////////////////

// Max line identifier checked/parsed. Is 1-indexed and in DIMACS form.
static srid_t max_line_id = 0;

// The current line number being checked. This is 0-indexed and starts at 0.
static srid_t current_line_num = 0;

// The unit propagation hints. When the parsing strategy is `PS_EAGER`,
// the hints are indexed by line number. Otherwise, they are at index 0.
static range_array_t hints;

// When the parsing strategy is `PS_STREAMING`, this tractks the number of
// RAT hint groups for the parsed line. Otherwise, it is ignored.
static uint num_RAT_hints = 0;

// When the parsing strategy is `PS_EAGER`, this stores the number of RAT
// hint groups for each line. If we are STREAMING, this is ignored.
static uint *line_num_RAT_hints = NULL;
static uint line_num_RAT_hints_alloc_size = 0;

// The clause IDs to delete, indexed by line number.
// Only used when the parsing strategy is `PS_EAGER`. Otherwise, deletions
// are handled when they are parsed.
static range_array_t deletions;

// The active LSR proof file. Assigned in `main()`. Can be `stdin`.
static FILE *lsr_file = NULL;

////////////////////////////////////////////////////////////////////////////////

// Help messages and command line options

#define HELP_MSG_OPT            ('h')
#define QUIET_MODE_OPT          ('q')
#define VERBOSE_MODE_OPT        ('v')
#define DIR_OPT                 ('d')
#define NAME_OPT                ('n')
#define EAGER_OPT               ('e')
#define STREAMING_OPT           ('s')
#define OPT_STR                 ("d:ehn:qsv")

// A flag that is set when the CLI arguments request the longer help message.
static int long_help_msg_flag = 0;

// The set of "long options" for CLI argument parsing. Used by `getopt_long()`.
static struct option longopts[] = {
  { "help", no_argument, &long_help_msg_flag, 1 },
  { "dir", required_argument, NULL, DIR_OPT },
  { "name", required_argument, NULL, NAME_OPT },
  { "eager", no_argument, NULL, EAGER_OPT },
  { "streaming", no_argument, NULL, STREAMING_OPT },
  { NULL, 0, NULL, 0 }  // The array of structs must be NULL/0-terminated
};

static void print_short_help_msg(FILE *f) {
  char *usage_str = "Usage: ./lsr-check [OPTIONS] <cnf> [lsr]\n"
  "\n"
  "  <cnf>     CNF file path.\n"
  "  [lsr]     Optional LSR proof file path. If omitted, `stdin` is used.\n"
  "\n"
  "where [OPTIONS] may take any of the following:\n"
  "\n"
  "  -h        Prints this help message.\n"
  "  --help    Prints a longer help message.\n"
  "\n"
  "  -q        Quiet mode.\n"
  "  -v        Verbose mode.\n"
  "\n"
  "  --dir=<dir>  | -d dir   The common directory for the CNF and LSR files.\n"
  "  --eager      | -e       Parse the entire LSR file before proof checking.\n"
  "  --streaming  | -s       Stream the LSR proof. (Used by default.)\n"
  "\n";

  fprintf(f, "%s", usage_str);
}

static void print_long_help_msg(FILE *f) {
  char *usage_str = "Usage: ./lsr-check [OPTIONS] <cnf> [lsr]\n"
  "\n"
  "where\n"
  "\n"
  "  <cnf>     Required file path to the CNF file.\n"
  "  [lsr]     Optional file path to the LSR proof file. If no path is given,\n"
  "            the proof is read from `stdin` (and `--eager` cannot be used).\n"
  "\n"
  "and where [OPTIONS] may take any of the following:\n"
  "\n"
  "  -h        Prints a short help message. (No proof checking.)\n"
  "  --help    Prints this (longer) help message. (No proof checking.)\n"
  "\n"
  "  -q        Quiet mode. Only reports the final result.\n"
  "  -v        Verbose mode. Prints additional statistics and information\n"
  "            All comment lines are prefixed with \"c \".\n"
  "\n"
  "  --dir=<dir>  | -d <dir>   Specifies the common directory to use for the\n"
  "                            CNF and LSR files. <dir> is prefixed to the\n"
  "                            CNF and LSR file paths provided.\n"
  "  \n"
  "  --eager      | -e         Eagerly parse the LSR file, meaning the entire\n"
  "                            LSR file is parsed before any proof checking\n"
  "                            is performed. This option may only be used\n"
  "                            when an LSR file path is provided. Cannot be \n"
  "                            used at the same time as `--streaming`.\n"
  "\n"
  "  --streaming  | -s         Stream the LSR proof, meaning that parsing\n"
  "                            and proof checking are interleaved, which is\n"
  "                            useful when proofs are very large or being\n"
  "                            generated online by a SAT solver.\n"
  "                            When streaming is used, the LSR file may\n"
  "                            come from `stdin`. Cannot be used at the\n"
  "                            same time as `--eager`.\n"
  "                            Streaming is the default option.\n"
  "\n";

  fprintf(f, "%s", usage_str);
}

////////////////////////////////////////////////////////////////////////////////

/**
 * @brief Returns the number of RAT hint groups for the current line.
 * 
 * When the parsing strategy is `PS_EAGER`, we store this data in a
 * line-indexed array. Otherwise, we use `num_RAT_hints`.
 */
static inline uint get_num_RAT_hints(void) {
  if (p_strategy == PS_EAGER) {
    return line_num_RAT_hints[current_line_num];
  } else {
    return num_RAT_hints;
  }
}

/**
 * @brief Returns a pointer to the start of the UP hints for the current line.
 * 
 * The pointer will point to the start of *all* the hints, including any
 * global UP hints.
 */
static inline srid_t *get_hints_start(void) {
  if (p_strategy == PS_EAGER) {
    return ra_get_range_start(&hints, current_line_num);
  } else {
    return ra_get_range_start(&hints, 0);
  }
}

/**
 * @brief Returns a pointer to the end of the UP hints for the current line.
 * 
 * The `unit_propagate()` function uses pointer iterators, so we need a
 * pointer to the end of the hints, not merely a size.
 */
static inline srid_t *get_hints_end(void) {
  if (p_strategy == PS_EAGER) {
    return ra_get_range_start(&hints, current_line_num + 1);
  } else {
    return ra_get_range_start(&hints, 1);
  }
}

/**
 * @brief Prepares the data structure that stores UP hints to receive hints
 *        for the next addition line.
 * 
 * The caller must set `current_line_num` to the line being parsed before
 * calling this function.
 */
static void prepare_hints(void) {
  if (p_strategy == PS_EAGER) {
    ra_commit_empty_ranges_until(&hints, current_line_num);
  } else {
    ra_reset(&hints);
    num_RAT_hints = 0;
  }
}

/**
 * @brief Prepares the data structure that stores deletions to receive the
 *        next deletion line.
 * 
 * In the spirit of accepting non-standard input, `lsr-check` allows LSR
 * deletion "lines" to span multiple actual deletion lines, so the caller
 * should ensure that `prepare_deletions()` is not called before parsing
 * the next *deletion* line, but the next *batch* of deletion lines.
 */
static void prepare_deletions(void) {
  if (p_strategy == PS_EAGER) {
    ra_commit_range(&deletions);
  }
}

/** 
 * @brief Inserts a clause ID hint into the hints data structure.
 * 
 * When we insert the ID, we keep it 1-indexed, so we can still tell
 * where the RAT hint groups begin. (Negative IDs indicate the start
 * of a new hint group.)
 * 
 * @param clause_id The 1-indexed clause ID (in DIMACS form).
 */
static void insert_hint(srid_t clause_id) {
  // Check that the clause_id is in range
  srid_t id = ABS(clause_id) - 1;
  PRINT_ERR_AND_EXIT_IF(id > LINE_ID_FROM_LINE_NUM(current_line_num) 
    || is_clause_deleted(id),
    "Clause ID in the SR proof line is out of bounds or is deleted.");

  ra_insert_srid_elt(&hints, clause_id);

  // If the clause starts a new RAT hint group, increment the
  // number of RAT hint groups according to our parsing strategy
  if (clause_id < 0) {
    if (p_strategy == PS_EAGER) {
      RECALLOC_ARR(line_num_RAT_hints, line_num_RAT_hints_alloc_size, 
        current_line_num, sizeof(uint));
      line_num_RAT_hints[current_line_num]++;
    } else {
      num_RAT_hints++;
    }
  }
}

// Parses the next SR line. Returns either DELETION_LINE or ADDITION_LINE.
// If deletion line, the deletions are handled already.
static int parse_lsr_line(void) {
  srid_t line_id, clause_id;

  int line_type = read_lsr_line_start(lsr_file, &line_id);
  current_line_num = LINE_NUM_FROM_LINE_ID(line_id);
  current_line_num = MAX(-1, current_line_num);
  switch (line_type) {
    case DELETION_LINE:
      // Ensure that the line ID is (non-strictly) monotonically increasing
      PRINT_ERR_AND_EXIT_IF(line_id < max_line_id, "Deletion line ID decreases.");
      max_line_id = line_id;
      srid_t deletion_line_num = MAX(0, current_line_num + 1);

      if (p_strategy == PS_EAGER) {
        ra_commit_empty_ranges_until(&deletions, deletion_line_num);
      }

      // Now loop on clause ID tokens until a zero is read
      while ((clause_id = read_clause_id(lsr_file)) != 0) {
        clause_id--;
        PRINT_ERR_AND_EXIT_IF(clause_id < 0, "Deletion line has negative clause ID.");
        if (p_strategy == PS_EAGER) {
          ra_insert_srid_elt(&deletions, clause_id);
        } else {
          delete_clause(clause_id);
        }
      }

      break;
    case ADDITION_LINE:
      // Check that the line id is strictly monotonically increasing
      PRINT_ERR_AND_EXIT_IF(line_id <= max_line_id, "Addition line id doesn't increase.");
      max_line_id = line_id;

      // In case a line is "skipped", cap off empty clauses until formula size catches up
      while (formula_size < max_line_id - 1) {
        commit_clause();
        delete_clause(formula_size - 1);
      }

      parse_sr_clause_and_witness(lsr_file, current_line_num);
      commit_clause(); 

      // Parse the UP hints, keeping the clause IDs as-is so we can tell
      // where the RAT hint groups start (i.e. with negative clause IDs)
      int counter = 0;
      prepare_hints();
      prepare_deletions();
      while ((clause_id = read_clause_id(lsr_file)) != 0) {
        counter++;
        insert_hint(clause_id);
      }

      ra_commit_range(&hints);
      break;
    default: PRINT_ERR_AND_EXIT("Invalid line type.");
  }

  return line_type;
}

static void parse_entire_lsr_file(void) {
  PRINT_ERR_AND_EXIT_IF(p_strategy != PS_EAGER,
    "To parse the entire LSR file eagerly, the p_strategy must be EAGER.");

  

  int detected_empty_clause = 0;
  while (has_another_line(lsr_file)) {
    parse_lsr_line();
    
    // Stop parsing the file if we found the empty clause
    if (new_clause_size == 0) {
      detected_empty_clause = 1;
      break;
    }
  }
  
  fclose(lsr_file);

  // Just in case, commit the hints and deletions
  ra_commit_range(&hints);
  ra_commit_range(&deletions);
  
  if (detected_empty_clause) {
    log_msg(VL_NORMAL, "c Detected the empty clause.\n");
  }

  log_msg(VL_NORMAL, "c Parsed %d proof lines.\n", current_line_num + 1);
}

/**
 * @brief Allocates memory for LSR-specific data structures. If the parsing
 *        strategy in EAGER, this function also parses the entire file.
 * 
 * If the file is parsed, the `current_line_num` is set back to 0.
 */
static void prepare_sr_check_data(void) {
  switch (p_strategy) {
    case PS_EAGER:
      // In eager mode, we parse the entire LSR proof file first.
      // We store the hints and witnesses in range arrays
      ra_init(&hints, num_cnf_clauses * 10, num_cnf_vars, sizeof(srid_t));
      line_num_RAT_hints_alloc_size = num_cnf_clauses;
      line_num_RAT_hints = xcalloc(line_num_RAT_hints_alloc_size, sizeof(uint));
      ra_init(&deletions, num_cnf_clauses * 10, num_cnf_vars, sizeof(srid_t));
      parse_entire_lsr_file();
      current_line_num = 0;
      break;
    case PS_STREAMING:
      ra_init(&hints, num_cnf_vars * 10, 2, sizeof(srid_t));
      break;
    default: PRINT_ERR_AND_EXIT("Unknown parsing strategy.");
  }
}

static int has_another_lsr_line(void) {
  if (p_strategy == PS_EAGER) {
    return LINE_ID_FROM_LINE_NUM(current_line_num) <= max_line_id;
  } else {
    return has_another_line(lsr_file);
  }
}

static int prepare_next_line(void) {
  switch (p_strategy) {
    case PS_EAGER:;
      // Process deletions until we have an addition line
      srid_t clause_id = CLAUSE_ID_FROM_LINE_NUM(current_line_num);
      current_line_num--; // Handle deletions from the current line first
      do { 
        current_line_num++;
        int deletions_size = ra_get_range_size(&deletions, current_line_num);
        if (deletions_size > 0) {
          srid_t *del_iter = 
            (srid_t *) ra_get_range_start(&deletions, current_line_num);
          srid_t *del_end = del_iter + deletions_size;
          for (; del_iter < del_end; del_iter++) {
            delete_clause(*del_iter);
          }
        }

        clause_id = CLAUSE_ID_FROM_LINE_NUM(current_line_num);
      } while (is_clause_deleted(clause_id));
      new_clause_size = get_clause_size(clause_id);
      return ADDITION_LINE;
    case PS_STREAMING: return parse_lsr_line();
    default: PRINT_ERR_AND_EXIT("Unknown parsing strategy.");
  }
}

// Computes the reduction of the clause under the partial assignment.
// Returns SATISFIED_OR_MUL, or CONTRADICTION, or the unit lit.
static int reduce(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(is_clause_deleted(clause_index),
    "Trying to unit propagate on a deleted clause.");

  int unit_lit = CONTRADICTION;
  int *start = get_clause_start(clause_index);
  int *end = get_clause_start(clause_index + 1);
  for (; start < end; start++) {
    int lit = *start;
    switch (peval_lit_under_alpha(lit)) {
      case UNASSIGNED:
        if (unit_lit == CONTRADICTION) {
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

  return unit_lit;
}

// Perform unit propagation starting from a hint index. Stops if end or negative hint.
// Returns CONTRADICTION if false derived, or 0 otherwise. Updates hint index
static int unit_propagate(srid_t **hint_ptr, srid_t *hints_end, llong gen) {
  int up_res;
  srid_t up_clause;
  srid_t *hints_iter = *hint_ptr;
  while (hints_iter < hints_end && (up_clause = *hints_iter) > 0) {
    // Perform unit propagation against alpha on up_clause
    // Subtract one from the identifier because it's 1-indexed in the proof line
    up_res = reduce(up_clause - 1);
    switch (up_res) {
      case CONTRADICTION: // The line checks out, and we can add the clause
        // Scan the hint_index forward until a negative hint is found
        do {
          hints_iter++;
        } while (*hints_iter > 0 && hints_iter < hints_end);
        *hint_ptr = hints_iter;
        return CONTRADICTION;
      case SATISFIED_OR_MUL: // Unit propagation shouldn't give us either
        PRINT_ERR_AND_EXIT("Found satisfied clause in UP part of hint.");
      default: // We have unit on a literal - add to alpha
        set_lit_for_alpha(up_res, gen);
    }

    hints_iter++;
  }

  *hint_ptr = hints_iter;
  return 0;
}

/**
 * @brief Marks the current candidate clause as checked for the SR property.
 * 
 * The current candidate clause is indicated by the `current_line_num` variable.
 * 
 * When the parsing strategy is `PS_EAGER`, the clauses are in the formula
 * already, but we need to update the first/last information for the literals.
 */
static void mark_clause_as_checked(void) {
  perform_clause_first_last_update(CLAUSE_ID_FROM_LINE_NUM(current_line_num));
  if (p_strategy == PS_EAGER) {
    current_line_num++;
  }
}

////////////////////////////////////////////////////////////////////////////////

static void check_line(void) {
  // Clear the previous partial assignment and substitution
  alpha_generation++;
  subst_generation++;

  // Make the negated literals of the candidate clause persist for all RAT hints
  llong negated_clause_gen = alpha_generation + get_num_RAT_hints();
  srid_t candidate_clause_id = CLAUSE_ID_FROM_LINE_NUM(current_line_num);
  assume_negated_clause(candidate_clause_id, negated_clause_gen);

  // Now take the UP hints (if any) to extend alpha
  srid_t *hints_iter = get_hints_start();
  srid_t *hints_end = get_hints_end();
  if (unit_propagate(&hints_iter, hints_end, negated_clause_gen) == CONTRADICTION) {
    goto finish_line;
  }

  // If there are RAT hints, `hints_iter` now points to the first RAT hint

  // Double-check that the proposed clause is not the empty clause
  // (The empty clause cannot have a witness, and must have a UP contradiction)
  PRINT_ERR_AND_EXIT_IF(new_clause_size == 0,
    "UP didn't derive contradiction for empty clause.");
  assume_subst(current_line_num);

  // TODO: Prove that the candidate clause is implied by the witness

  log_msg(VL_VERBOSE, "c [line %d] Checking clauses %d to %d\n", 
      LINE_ID_FROM_LINE_NUM(current_line_num),
      min_clause_to_check + 1, max_clause_to_check + 1);

  // Now for each clause, check that it is either
  //   - Satisfied or not reduced by the witness
  //   - A RAT clause, whose hints derive contradiction
  srid_t *rat_hints_start = hints_iter;
  srid_t *up_iter;
  for (srid_t i = min_clause_to_check; i <= max_clause_to_check; i++) {
    if (is_clause_deleted(i)) {
      continue; // Skip deleted clauses, nothing to prove
    }

    // Check how the clause behaves under the substitution
    // TODO: Cache the computed reduction under subst in an array?
    switch (reduce_subst_mapped(i)) {
      case NOT_REDUCED:
      case SATISFIED_OR_MUL:
        continue;
      case REDUCED:
        /* 
         * Now find the reduced clause's RAT hint group.
         * In most cases, the RAT hint groups should be sorted by increasing
         * absolute value of the RAT clause's ID, so `hints_iter` should point
         * to the right group. But if the RAT hint group doesn't start with
         * the expected clause ID, we must scan through all RAT hints to find
         * a matching hint.
         */

        if (hints_iter < hints_end && -((*hints_iter) + 1) == i) {
          up_iter = hints_iter;
        } else {
          // Scan through all the RAT hints for a negative one matching this clause
          for (up_iter = rat_hints_start; up_iter < hints_end; up_iter++) {
            if (-((*up_iter) + 1) == i) {
              hints_iter = MAX(hints_iter, up_iter);
              break;
            }
          }

          PRINT_ERR_AND_EXIT_IF(up_iter == hints_end, "RAT clause has no RAT hint.");
        }

        // We successfully found a matching RAT hint
        // Assume the negation of the RAT clause and perform unit propagation
        int neg_res = assume_negated_clause_under_subst(i, alpha_generation);

        /* 
         * It is possible for a RAT clause to have no UP derivation. This occurs
         * when the clause is immediately satisfied by alpha (when extended
         * by the UP after assuming the negation of the candidate clause).
         * Notably, this is different than the witness satisfying the clause.
         * If the RAT clause is satisfied by alpha, we skip its UP hints, if any.
         */
        if (neg_res == SATISFIED_OR_MUL) {
          do {
            up_iter++;
          } while (*up_iter > 0 && up_iter < hints_end);
        } else {
          up_iter++; // Move to the first UP hint
          // We expect a UP contradiction. If not, the proof is invalid
          if (unit_propagate(&up_iter, hints_end, alpha_generation) != CONTRADICTION) {
            PRINT_ERR_AND_EXIT("RAT clause UP didn't derive contradiction.");
          }
        }

        hints_iter = MAX(hints_iter, up_iter);
        alpha_generation++; // Clear negated RAT clause in `alpha`
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
    mark_clause_as_checked();
  }
}

static void check_proof(void) {
  log_msg(VL_NORMAL, "c Checking proof...\n");

  while (!derived_empty_clause && has_another_lsr_line()) {
    int line_type = prepare_next_line();
    if (line_type == ADDITION_LINE) {
      check_line();
    }
  }

  if (p_strategy == PS_STREAMING) {
    fclose(lsr_file);
  }

  if (derived_empty_clause == 0) {
    log_msg(VL_QUIET, "s VALID\n");
    log_msg(VL_NORMAL, "c A valid proof, without an empty clause.\n.");
  } else {
    log_msg(VL_QUIET, "s VERIFIED UNSAT\n");
  }
}

int main(int argc, char *argv[]) {
  if (argc == 1) {
    print_short_help_msg(stdout);
    return 0;
  }

  p_strategy = PS_STREAMING;
  int eager_strategy_set = 0;
  int streaming_strategy_set = 0;
  int verbose_mode_set = 0;
  int quiet_mode_set = 0;
  int dir_provided = 0;
  int name_provided = 0;
  char cnf_file_path_buf[MAX_FILE_PATH_LEN];
  char lsr_file_path_buf[MAX_FILE_PATH_LEN];
  char *cnf_file_path = NULL;
  char *lsr_file_path = NULL;
  size_t dir_len = 0;

  // Parse CLI arguments
  int ch;
  while ((ch = getopt_long(argc, argv, OPT_STR, longopts, NULL)) != -1) {
    switch (ch) {
      case HELP_MSG_OPT:
        print_short_help_msg(stdout);
        return 0;
      case QUIET_MODE_OPT:
        verbosity_level = VL_QUIET;
        quiet_mode_set = 1;
        break;
      case VERBOSE_MODE_OPT:
        verbosity_level = VL_VERBOSE;
        verbose_mode_set = 1;
        break;
      case EAGER_OPT:
        p_strategy = PS_EAGER;
        eager_strategy_set = 1;
        break;
      case STREAMING_OPT:
        p_strategy = PS_STREAMING;
        streaming_strategy_set = 1;
        break;
      case DIR_OPT:
        dir_provided = 1;
        PRINT_ERR_AND_EXIT_IF(name_provided, 
          "Cannot provide both a directory and a name.");

        dir_len = strlcpy(cnf_file_path_buf, optarg, MAX_FILE_PATH_LEN);
        PRINT_ERR_AND_EXIT_IF(dir_len >= MAX_FILE_PATH_LEN,
          "CNF file path too long.");
        PRINT_ERR_AND_EXIT_IF(dir_len == 0, "Empty directory provided");
        cnf_file_path = ((char *) cnf_file_path_buf) + dir_len;

        dir_len = strlcpy(lsr_file_path_buf, optarg, MAX_FILE_PATH_LEN);
        lsr_file_path = ((char *) lsr_file_path_buf) + dir_len;

        if (cnf_file_path[-1] != '/') {
          memcpy(cnf_file_path++, "/", 2);
          memcpy(lsr_file_path++, "/", 2);
          dir_len++;
        }
        break;
      case NAME_OPT:
        name_provided = 1;
        PRINT_ERR_AND_EXIT_IF(dir_provided, 
          "Cannot provide both a directory and a name.");

        dir_len = strlcpy(cnf_file_path_buf, optarg, MAX_FILE_PATH_LEN);
        PRINT_ERR_AND_EXIT_IF(dir_len >= MAX_FILE_PATH_LEN,
          "CNF file path too long.");
        cnf_file_path = ((char *) cnf_file_path_buf) + dir_len;

        dir_len = strlcpy(lsr_file_path_buf, optarg, MAX_FILE_PATH_LEN);
        lsr_file_path = ((char *) lsr_file_path_buf) + dir_len;
        break;
      case '?': // Unknown option used
        fprintf(stderr, "Unknown option provided.\n");
        print_short_help_msg(stderr);
        return 1;
      case ':': // Missing option argument where one was required
        fprintf(stderr, "Missing argument for option.\n");
        print_short_help_msg(stderr);
        return 1;
      case 0: // Long options without a short option
        if (long_help_msg_flag) {
          print_long_help_msg(stdout);
          return 0;
        }
        break;
      default:
        print_short_help_msg(stderr);
        return 1;
    }
  }

  PRINT_ERR_AND_EXIT_IF(quiet_mode_set && verbose_mode_set,
    "Cannot set both quiet and verbose modes.");
  PRINT_ERR_AND_EXIT_IF(eager_strategy_set && streaming_strategy_set,
    "Cannot set both eager and streaming strategies.");

  // `getopt_long()` sets `optind` to the index of the next non-option argument
  // It also shuffles the non-option arguments to the end
  // Check the number of file path args
  switch (argc - optind) {
    case 0:
      PRINT_ERR_AND_EXIT_IF(!name_provided, "No CNF file path provided.");
      memcpy(cnf_file_path, ".cnf", 5);
      cnf_file_path = cnf_file_path_buf;

      memcpy(lsr_file_path, ".lsr", 5);
      lsr_file_path = lsr_file_path_buf;
      break;
    case 1:
      PRINT_ERR_AND_EXIT_IF(dir_provided,
        "Cannot provide a directory without an LSR file path.");

      if (name_provided) {
        // Assume a ".cnf" file extension
        memcpy(cnf_file_path, ".cnf", 5);
        cnf_file_path = cnf_file_path_buf;

        // Copy over the provided proof file extension
        // TODO: Check out of bounds here?
        strlcpy(lsr_file_path, argv[optind], MAX_FILE_PATH_LEN - dir_len);
        lsr_file_path = lsr_file_path_buf;
      } else {
        // The CNF file is provided as a normal file path
        cnf_file_path = argv[optind];
      }
      break;
    case 2:
      if (dir_provided || name_provided) {
        // Concatenate the file paths or file extensions with the prefix
        size_t len = strlcpy(cnf_file_path, argv[optind], MAX_FILE_PATH_LEN - dir_len);
        PRINT_ERR_AND_EXIT_IF(len + dir_len >= MAX_FILE_PATH_LEN, "CNF file path too long.");
        cnf_file_path = cnf_file_path_buf;

        len = strlcpy(lsr_file_path, argv[optind + 1], MAX_FILE_PATH_LEN - dir_len);
        PRINT_ERR_AND_EXIT_IF(len + dir_len >= MAX_FILE_PATH_LEN, "LSR file path too long.");
        lsr_file_path = lsr_file_path_buf;
      } else {
        cnf_file_path = argv[optind];
        lsr_file_path = argv[optind + 1];
      }
      break;
    default:
      fprintf(stderr, "Error: Invalid number of non-option arguments provided.\n");
      print_short_help_msg(stderr);
      return 1;
  }

  // Open the files first, to ensure we don't do work unless they exist
  FILE *cnf_file = xfopen(cnf_file_path, "r");
  if (lsr_file_path == NULL) {
    PRINT_ERR_AND_EXIT_IF(p_strategy == PS_EAGER,
      "Cannot use eager strategy with `stdin` as the LSR file.");
    lsr_file = stdin;
  } else {
    lsr_file = xfopen(lsr_file_path, "r");
  }

  log_msg(VL_NORMAL, "c CNF file path: %s\n", cnf_file_path);
  if (lsr_file == stdin) {
    log_msg(VL_NORMAL, "c No LSR file path provided, using stdin.\n");
  } else {
    log_msg(VL_NORMAL, "c LSR file path: %s\n", lsr_file_path);
  }

  if (p_strategy == PS_EAGER) {
    log_msg(VL_NORMAL, "c Using an EAGER parsing strategy.\n");
  } else {
    log_msg(VL_NORMAL, "c Using a STREAMING parsing strategy.\n");
  }

  parse_cnf(cnf_file);
  log_msg(VL_NORMAL, "c The CNF formula has %lld clauses and %d variables.\n",
    ((llong) formula_size), max_var);

  prepare_sr_check_data();
  check_proof();

  return 0;
}