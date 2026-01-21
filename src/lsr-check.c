/**
 * @file lsr-check.c
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
 *  When a chain of additions is shown to be redundant, then the two formulas
 *  are equisatisfiable.
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
 *  unit propagation. Each group of RAT hints starts with the negative
 *  clause ID of the RAT clause to check.
 * 
 *  Deletion lines specify the clause IDs of the clauses to delete from
 *  the formula. This has the effect of making it easier and more efficient
 *  to show redundancy.
 * 
 *  `lsr-check` contains two parsing strategies: eager and streaming.
 *  When eagerly parsing, the entire proof is read into memory before
 *  proof checking begins. Otherwise, the proof is streamed (potentially from
 *  `stdin`), and the proof is checked as it is read. This can be used 
 *  to check very large proofs that cannot be written to disk.
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
#include "xmalloc.h"
#include "logger.h"
#include "global_data.h"
#include "global_parsing.h"
#include "range_array.h"
#include "cli.h"
#include "cnf_parser.h"
#include "timer.h"
#include "lsr-check/lsr_data.h"
#include "lsr-check/lsr_err.h"

////////////////////////////////////////////////////////////////////////////////

// Help messages and command line options

// The option string used by `getopt_long()`.
// Specifies the (short) command line options and whether they take arguments.
#define OPT_STR  BASE_CLI_OPT_STR

// The set of "long options" for CLI argument parsing. Used by `getopt_long()`.
static struct option const longopts[] = {
  BASE_LONG_OPTS_ARRAY
};

// Prints a shorter help message to the provided `FILE` stream.
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
  "  --dir=<dir>  | -d <d>   Common directory for CNF and LSR files.\n"
  "  --name=<n>   | -n <n>   Common file path for CNF and LSR files.\n"
  "  --eager      | -e       Parse the entire proof before proof checking.\n"
  "\n";
  
  fprintf(f, "%s", usage_str);
}

// Prints a longer help message to the provided `FILE` stream.
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
  "  --dir=<d>   | -d <dir>    Specify a common directory to use for the\n"
  "                            CNF and LSR files. <dir> is prefixed to the\n"
  "                            CNF and LSR file paths provided.\n"
  "\n"
  "  --name=<n>  | -n <name>   Specify a common file path root for the CNF\n"
  "                            and LSR files. If this is used, then\n"
  "                            `stdin` cannot be used as the source\n"
  "                            of the proof file. When no arguments\n"
  "                            are provided, then \".cnf\" and \".lsr\"\n"
  "                            are used as the default file extensions.\n"
  "                            Providing one argument replaces the\n"
  "                            proof file's extension. Both replaces both.\n"
  "\n"
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
 * @brief Computes the reduction of the clause under the current assignment.
 * 
 * This function is the engine of unit propagation. The UP hints should
 * specify clauses that become unit, or evaluate to false, under the
 * current partial assignment. If they are unit, then 
 * 
 * @return `SATISFIED_OR_MUL`, `CONTRADICTION`, or the unit literal.
 */
static int reduce(srid_t clause_index) {
  FATAL_ERR_IF(is_clause_deleted(clause_index),
    "[line %lld (id %lld)] Trying to unit propagate on a deleted clause %lld.",
    TO_DIMACS_CLAUSE(current_line), LINE_ID_FROM_LINE_NUM(current_line),
    TO_DIMACS_CLAUSE(clause_index));

  int unit_lit = CONTRADICTION;
  int *clause_iter = get_clause_start_unsafe(clause_index);
  int *clause_end = get_clause_end(clause_index);
  for (; clause_iter < clause_end; clause_iter++) {
    int lit = *clause_iter;
    int peval_lit = peval_lit_under_alpha(lit);
    switch (peval_lit) {
      case UNASSIGNED:
        if (unit_lit == CONTRADICTION) {
          unit_lit = lit;
        } else {
          return SATISFIED_OR_MUL;
        }
        break;
      case FF: break;
      case TT: return SATISFIED_OR_MUL;
      default: log_fatal_err("Corrupted alpha evaluation: %d.", peval_lit);
    }
  }

  return unit_lit;
}

/**
 * @brief Performs unit propagation by using the hints pointed to by `hint_ptr`.
 *        Expects a clause to evaluate to false before `hints_end` is reached.
 *        Extensions to the current assignment have their generation set to
 *        to the provided generation `gen.
 * 
 * See `peval_lit_under_alpha()` and `global_data.c` for more information
 * about how the partial assignment interacts with generation values.
 * 
 * When the function returns, `hint_ptr` is set to the end of the current
 * hint group (i.e., either the end of all the hints `hints_end`, or it
 * points to the negative clause ID starting the next hint group).
 * 
 * @param hint_ptr A pointer to the hint iterator. Updated on return.
 * @param hints_end A pointer to the end of all the RAT hints. (Exclusive)
 * @param gen The generation value to set partial assignment extensions to.
 * 
 * @return `CONTRADICTION` if a clause evaluates to false, and 0 otherwise.
 */
static int unit_prop(srid_t **hint_ptr, srid_t *hints_end, ullong gen) {
  int up_res;
  srid_t up_clause;
  srid_t *hints_iter = *hint_ptr;
  while (hints_iter < hints_end && (up_clause = *hints_iter) > 0) {
    hints_iter++;
    up_clause = FROM_DIMACS_CLAUSE(up_clause);
    // Perform unit propagation against alpha on `up_clause`
    up_res = reduce(up_clause);
    switch (up_res) {
      case CONTRADICTION: // The line checks out, and we can add the clause
        // Scan the hint_index forward until a negative hint is found
        SKIP_REMAINING_UP_HINTS(hints_iter, hints_end);
        *hint_ptr = hints_iter;
        return CONTRADICTION;
      case SATISFIED_OR_MUL: // Unit propagation shouldn't give us either
        lsr_err_satisfied_clause_hint(up_clause);
      default: // We have unit on a literal - extend alpha
        set_lit_for_alpha(up_res, gen);
    }
  }

  *hint_ptr = hints_iter;
  return 0;
}

// Returns `1` if the expected number of RAT clauses was checked, 0 otherwise.
static int check_only_hints(srid_t *hints_iter, srid_t *hints_end, int pivot) {
  log_msg(VL_VERBOSE, "[line %lld | id %lld] Checking only the RAT hints",
    get_line_id_for_line_num(current_line),
    LINE_ID_FROM_LINE_NUM(current_line));

  srid_t goal_occs = get_lit_occurrences(&lit_occ, NEGATE_LIT(pivot));
  srid_t occs = 0;
  srid_t max_clause = -1; // Assume increasing hint groups
  while (hints_iter < hints_end) {
    srid_t c = FROM_RAT_HINT(*hints_iter);
    FATAL_ERR_IF(c <= max_clause, "Not increasing IDs");
    max_clause = c;

    switch (reduce_clause_under_pivot(c, pivot)) {
      case NOT_REDUCED:
      case SATISFIED_OR_MUL:
        log_fatal_err("[line %lld | id %lld] "
          "Purported RAT clause %lld is not RAT",
          get_line_id_for_line_num(current_line),
          LINE_ID_FROM_LINE_NUM(current_line),
          TO_DIMACS_CLAUSE(c));
      case REDUCED:;
        occs++;
        hints_iter++;
        int neg_res = assume_negated_clause_under_subst(c, alpha_generation);
        if (neg_res == SATISFIED_OR_MUL) {
          SKIP_REMAINING_UP_HINTS(hints_iter, hints_end);
        } else {
          if (unit_prop(&hints_iter, hints_end, alpha_generation)
              != CONTRADICTION) {
            lsr_err_no_up_contradiction(c, *(hints_iter - 1));
          }
        }

        alpha_generation += GEN_INC;
        break;
      case CONTRADICTION:
        log_fatal_err("[line %lld | id %lld] "
          "Reduced clause %lld claims contradiction.",
          get_line_id_for_line_num(current_line),
          LINE_ID_FROM_LINE_NUM(current_line),
          TO_DIMACS_CLAUSE(c));
      default: 
        log_fatal_err("[line %lld | id %lld] "
          "Clause %lld corrupted reduction value %d.",
          get_line_id_for_line_num(current_line),
          LINE_ID_FROM_LINE_NUM(current_line),
          TO_DIMACS_CLAUSE(c),
          reduce_clause_under_pivot(c, pivot)); 
    }
  }

  return (occs == goal_occs);
}

static void check_SR_clause(srid_t i, srid_t **iter_ptr,
                             srid_t *hints_start, srid_t *hints_end) {
  srid_t *hints_iter = *iter_ptr;
  srid_t *up_iter;

  // Check how the clause behaves under the substitution
  switch (reduce_clause_under_subst(i)) {
    case NOT_REDUCED:
    case SATISFIED_OR_MUL:
      return;
    case REDUCED:
      /* 
       * Now find the reduced clause's RAT hint group.
       * In most cases, the RAT hint groups are sorted by increasing
       * magnitude of the RAT clause's ID, so `hints_iter` should point
       * to the correct group. But if the RAT hint group doesn't start with
       * the expected clause ID, we must scan through all RAT hints to find
       * a matching hint.
       */
      if (hints_iter < hints_end && FROM_RAT_HINT(*hints_iter) == i) {
        up_iter = hints_iter;
      } else {
        // Scan all the RAT hints for a negative ID matching this clause
        for (up_iter = hints_start; up_iter < hints_end; up_iter++) {
          if (FROM_RAT_HINT(*up_iter) == i) {
            hints_iter = MAX(hints_iter, up_iter);
            break;
          }
        }

        if (up_iter == hints_end) {
          lsr_err_no_rat_hint_group(i);
        }
      }

      // We successfully found a matching RAT hint
      // Assume the negation of the RAT clause and perform unit propagation
      up_iter++;

      /* 
       * It is possible for a RAT clause to have no UP derivation. This occurs
       * when the clause is immediately satisfied by alpha (when extended
       * by the UP after assuming the negation of the candidate clause).
       * Notably, this is different than the witness satisfying the clause.
       * If alpha satisfies the RAT clause, then we skip its UP hints, if any.
       */
      int neg_res = assume_negated_clause_under_subst(i, alpha_generation);
      if (neg_res == SATISFIED_OR_MUL) {
        SKIP_REMAINING_UP_HINTS(up_iter, hints_end);
      } else {
        if (unit_prop(&up_iter, hints_end, alpha_generation) != CONTRADICTION) {
          lsr_err_no_up_contradiction(i, *(up_iter - 1));
        }
      }

      hints_iter = MAX(hints_iter, up_iter);
      alpha_generation += GEN_INC; // Clear the RAT UP units
      break;
    case CONTRADICTION:
      log_fatal_err("[line %lld] Reduced clause %lld claims contradiction.",
        TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(i));
    default:
      log_fatal_err("[line %lld] Clause %lld corrupted reduction value %d.",
        TO_DIMACS_LINE(current_line), TO_DIMACS_CLAUSE(i),
        reduce_clause_under_subst(i)); 
  }

  *iter_ptr = hints_iter;
}

/**
 * @brief Checks the current LSR addition line for the SR property, using
 *        the parsed substitution witness and unit propagation hints.
 * 
 * We want to show the following:
 * 
 *   (F /\ !C)  |-  (F /\ C)|w
 * 
 * First, we implicitly add the negation of the candidate clause to the formula.
 * Because all CNF clauses are disjunctions, the negation of the clause is
 * an AND of unit literals. Thus, all literals are negated and set in the
 * partial assignment `alpha`. See `assume_negated_clause()`.
 * 
 * Then, we add implied units to `alpha`. This is the optional first group
 * of hints. If no UP contradiction is found, then then check the entire
 * formula for entailment under witness reduction.
 */
static void check_line(void) {
  // Clear the previous partial assignment and substitution
  alpha_generation += GEN_INC;
  subst_generation++;

  // Make the negated literals of the candidate clause persist for all RAT hints
  ullong cc_gen = alpha_generation + (GEN_INC * get_num_RAT_hints());
  srid_t candidate_clause_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
  int pivot = assume_negated_clause(candidate_clause_id, cc_gen);

  srid_t *hints_iter = get_hints_start();
  srid_t *hints_end = get_hints_end();

  // Now take non-RAT UP hints (if any) to extend alpha
  if (unit_prop(&hints_iter, hints_end, cc_gen) == CONTRADICTION) {
    goto finish_line;
  }

  // If there are RAT hints, `hints_iter` now points to the first RAT hint

  // Double-check that the proposed clause is not the empty clause
  // (The empty clause cannot have a witness, and must have a UP contradiction)
  FATAL_ERR_IF(new_clause_size == 0,
    "[line %lld | id %lld] No UP contradiction for the empty clause.",
      get_line_id_for_line_num(current_line),
      LINE_ID_FROM_LINE_NUM(current_line));

  // If the witness is a single literal, then we may check only the RAT clauses
  if (get_witness_size(current_line) <= 1) {
    if (check_only_hints(hints_iter, hints_end, pivot)) {
      goto finish_line;
    }

    // If the check fails, we do it the old-fashioned way.
    // This *should* result in an error on some RAT clause without a hint group
  }
  
  fl_clause_t check_range;
  assume_subst(current_line);
  get_fl_clause_for_subst(current_line, &lit_occ, &check_range);

  logv("[line %lld | id %lld] Checking clauses %lld to %lld", 
      get_line_id_for_line_num(current_line),
      LINE_ID_FROM_LINE_NUM(current_line),
      TO_DIMACS_CLAUSE(check_range.first_clause),
      TO_DIMACS_CLAUSE(check_range.last_clause));

  // Now for each (not-deleted) clause, check that it is either
  //   - Satisfied or not reduced by the witness
  //   - A reduced clause, whose hints derive contradiction
  srid_t *hints_start = hints_iter;
  srid_t *up_iter;
  for (srid_t i = check_range.first_clause; i <= check_range.last_clause; i++) {
    if (is_clause_deleted(i)) continue;
    check_SR_clause(i, &hints_iter, hints_start, hints_end);
  }

  // We also check the candidate clause, since the witness might not satisfy it
  check_SR_clause(candidate_clause_id, &hints_iter, hints_start, hints_end);

finish_line:
  alpha_generation = cc_gen; // Clear all unit propagations for this line
  if (new_clause_size == 0) {
    derived_empty_clause = 1;
  } else {
    mark_clause_as_checked(candidate_clause_id);
  }
}

/**
 * @brief Checks the LSR proof. Prints the result to `stdout`.
 * 
 * If the parsing strategy is `PS_STREAMING`, then parsing is interleaved with
 * proof checking until the proof is done or until the empty clause is derived.
 */
static void check_proof(void) {
  logc("Checking proof...");
  timer_record(&timer, TIMER_LOCAL);

  while (!derived_empty_clause && has_another_lsr_line()) {
    line_type_t line_type = prepare_next_lsr_line();
    if (line_type == ADDITION_LINE) {
      check_line();
    }
  }

  if (p_strategy == PS_STREAMING && lsr_file != stdin) {
    fclose(lsr_file);
  }

  if (p_strategy == PS_EAGER) {
    timer_print_elapsed(&timer, TIMER_LOCAL, "Proof checking");
  } else {
    timer_print_elapsed(&timer, TIMER_LOCAL, "Proof checking (and parsing)");
  }

  timer_print_elapsed(&timer, TIMER_GLOBAL, "Total runtime");
  print_proof_checking_result();
}

////////////////////////////////////////////////////////////////////////////////

int main(int argc, char *argv[]) {
  if (argc == 1) {
    print_short_help_msg(stdout);
    return 0;
  }

  p_strategy = PS_STREAMING;
  cli_opts_t cli;
  cli_init(&cli);

  // Parse CLI arguments
  int ch;
  cli_res_t cli_res;
  while ((ch = getopt_long(argc, argv, OPT_STR, longopts, NULL)) != -1) {
    switch (ch) {
      case 0: // Defined long options without a corresponding short option
        log_fatal_err("Unimplemented long option.");
        break;
      default:
        cli_res = cli_handle_opt(&cli, ch, optopt, argv[optind - 1], optarg);
        switch (cli_res) {
          case CLI_UNRECOGNIZED:
            log_err("Unimplemented option: %s", argv[optind - 1]);
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
          case CLI_SUCCESS: break;
          default: log_fatal_err("Corrupted CLI result.");
        }
    }
  }

  // `getopt_long()` sets `optind` to the index of the first non-option argument
  // It also shuffles all of the non-option arguments to the end of `argv`
  // Thus, we expect the CNF and LSR file paths to be at the end now
  cli_res_t pres = cli_parse_file_paths_for_lsr_check(&cli, argv, argc, optind);
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

  if (cli.lsr_file_path == NULL) {
    logc("No LSR file path provided, using stdin.");
    lsr_file = stdin;
  } else {
    logc("LSR file path: %s", cli.lsr_file_path);
    lsr_file = xfopen(cli.lsr_file_path, "r");
  }

  if (p_strategy == PS_EAGER) {
    logc("Using an EAGER parsing strategy.");
  } else {
    logc("Using a STREAMING parsing strategy.");
  }

  timer_init(&timer);
  timer_record(&timer, TIMER_GLOBAL);

  timer_record(&timer, TIMER_LOCAL);
  parse_cnf(cnf_file, KEEP_TAUTOLOGIES);
  timer_print_elapsed(&timer, TIMER_LOCAL, "Parsing the CNF");

  int input_proof_is_in_binary = configure_proof_file_parsing(lsr_file);
  if (input_proof_is_in_binary) {
    logc("Detected that the LSR proof is in binary format.");
  }

  prepare_lsr_check_data();
  check_proof();
  return 0;
}
