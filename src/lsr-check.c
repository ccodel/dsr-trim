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
#include "xmalloc.h"
#include "logger.h"
#include "global_data.h"
#include "global_parsing.h"
#include "range_array.h"
#include "cli.h"
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

/** @brief The clause IDs to delete, indexed by line number.
 * 
 * This is only used when the parsing strategy is `PS_EAGER`. Otherwise,
 * deletions are handled as they are parsed, and `deletions` is unused.
 * 
 * Note that deletion lines are processed *after* addition lines with the
 * same ID, and the proof may start with a deletion line with an ID smaller
 * than the first addition line's. Thus, we index into `deletions` by adding
 * 1 to the `current_line_num`.
 */
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

// Prints the shorter help message to the provided `FILE` stream.
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

// Prints the longer help message to the provided `FILE` stream.
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
 * `line_num`-indexed array. Otherwise, we use `num_RAT_hints`.
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
 * the next *deletion* line, but rather the next *batch* of deletion lines.
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

// Parses the next LSR line. Returns either DELETION_LINE or ADDITION_LINE.
// If deletion line, the deletions are handled already.
/**
 * @brief Parses the next LSR line and stores/processes the data according
 *        to the current parsing strategy. Returns either `DELETION_LINE`
 *        or `ADDITION_LINE`.
 * 
 * If the parsing strategy is `PS_EAGER`, we store the candidate redundant
 * clauses in the CNF `lits_db` database, the hints in `hints`, any
 * substitution witness in `witnesses`, and * deletion lines in `deletions`.
 * 
 * If the parsing strategy is `PS_STREAMING`, we store the clause like normal,
 * but we reset `hints` and `witnesses` to clear the previous line's data.
 * This way, we reduce our memory overhead and benefit from caching.
 */
static int parse_lsr_line(void) {
  srid_t line_id, clause_id;

  int line_type = read_lsr_line_start(lsr_file, &line_id);
  current_line_num = LINE_NUM_FROM_LINE_ID(line_id); // Convert out of DIMACS
  current_line_num = MAX(-1, current_line_num);
  switch (line_type) {
    case DELETION_LINE:
      // Ensure that the line ID is (non-strictly) monotonically increasing
      PRINT_ERR_AND_EXIT_IF(line_id < max_line_id, "Deletion line ID decreases.");
      max_line_id = line_id;

      // We "1-index" deletion lines to account for a starting deletion line
      srid_t deletion_line_num = MAX(0, current_line_num + 1);

      // Cap off empty deletion lines until we reach the current line
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

      // Create deleted (empty) clauses until the formula size catches up
      while (formula_size < max_line_id - 1) {
        commit_clause();
        delete_clause(formula_size - 1);
      }

      parse_sr_clause_and_witness(lsr_file, current_line_num);
      commit_clause(); // Officially add the clause to the formula

      // Since deletion lines come after addition lines, prepare deletions here
      prepare_deletions();

      // Parse the UP hints, keeping the clause IDs as-is so we can tell
      // where the RAT hint groups start (i.e. with negative clause IDs)
      prepare_hints();
      while ((clause_id = read_clause_id(lsr_file)) != 0) {
        insert_hint(clause_id);
      }

      ra_commit_range(&hints);
      break;
    default: PRINT_ERR_AND_EXIT("Invalid line type.");
  }

  return line_type;
}

/**
 * @brief Parses the entire LSR file and stores the data accordingly.
 * 
 * Call only if the parsing strategy is `PS_EAGER`.
 * 
 * Upon return, the `lsr_file` is closed, and `current_line_num` is set to
 * the final line number parsed. Callers may want to set this variable back
 * to 0 before starting proof checking.
 */
static void parse_entire_lsr_file(void) {
  PRINT_ERR_AND_EXIT_IF(p_strategy != PS_EAGER,
    "To parse the entire LSR file eagerly, the p_strategy must be EAGER.");

  int detected_empty_clause = 0;
  while (has_another_line(lsr_file)) {
    parse_lsr_line();
    
    // Stop parsing the file if we find the empty clause
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
 * Upon return, the `current_line_num` is set to 0.
 */
static void prepare_lsr_check_data(void) {
  if (p_strategy == PS_EAGER) {
    ra_init(&hints, num_cnf_clauses * 10, num_cnf_vars, sizeof(srid_t));
    ra_init(&deletions, num_cnf_clauses * 10, num_cnf_vars, sizeof(srid_t));
    line_num_RAT_hints_alloc_size = num_cnf_clauses;
    line_num_RAT_hints = xcalloc(line_num_RAT_hints_alloc_size, sizeof(uint));
    parse_entire_lsr_file();
    current_line_num = 0;
  } else {
    ra_init(&hints, num_cnf_vars * 10, 2, sizeof(srid_t));
  }
}

/**
 * @brief Returns 1 if another LSR line exists to be checked or parsed.
 * 
 * When the parsing strategy is `PS_EAGER`, the `current_line_num` is compared
 * against the maximum line ID encountered during parsing. This function
 * assumes that the caller increments `current_line_num` after an addition
 * line is successfully checked.
 * 
 * When the parsing strategy is `PS_STREAMING`, the `lsr_file` stream is
 * read from until a new line of input is detected.
 */
static int has_another_lsr_line(void) {
  if (p_strategy == PS_EAGER) {
    return LINE_ID_FROM_LINE_NUM(current_line_num) <= max_line_id;
  } else {
    return has_another_line(lsr_file);
  }
}

/**
 * @brief Prepares data structures and values to parse or check the next line.
 * 
 * When the parsing strategy is `PS_EAGER`, stored deletion lines are processed
 * (and clauses are deleted from the formula) until an addition line is
 * found. On return, the `current_line_num` is set to the next addition line
 * to check. If the line is an addition, then `new_clause_size` is set to the
 * size of the next candidate clause.
 * 
 * When the parsing strategy is `PS_STREAMING`, a new LSR line is parsed.
 * 
 * @return The line type (`ADDITION_LINE` or `DELETION_LINE`).
 */
static int prepare_next_line(void) {
  if (p_strategy == PS_EAGER) {
    // Process deletions until we have an addition line
    // Note that deletions are "1-indexed", so we process the deletions
    // for the line we just checked first, before incrementing the line number
    srid_t clause_id = CLAUSE_ID_FROM_LINE_NUM(current_line_num);
    do { 
      int deletions_size = ra_get_range_size(&deletions, current_line_num);
      if (deletions_size > 0) {
        srid_t *del_iter = 
          (srid_t *) ra_get_range_start(&deletions, current_line_num);
        srid_t *del_end = del_iter + deletions_size;
        for (; del_iter < del_end; del_iter++) {
          delete_clause(*del_iter);
        }
      }

      current_line_num++;
      clause_id = CLAUSE_ID_FROM_LINE_NUM(current_line_num);
    } while (is_clause_deleted(clause_id));
    new_clause_size = get_clause_size(clause_id);
    return ADDITION_LINE;
  } else {
    return parse_lsr_line();
  }
}

/**
 * @brief Computes the reduction of the clause under the current assignment.
 * 
 * This function is the engine of unit propagation. The UP hints should
 * specify clauses that become unit, or evaluate to false, under the
 * current partial assignment. If they are unit, then 
 * 
 * @returns `SATISFIED_OR_MUL`, `CONTRADICTION`, or the unit literal.
 */
static int reduce(srid_t clause_index) {
  PRINT_ERR_AND_EXIT_IF(is_clause_deleted(clause_index),
    "Trying to unit propagate on a deleted clause.");

  int unit_lit = CONTRADICTION;
  int *start = get_clause_start_unsafe(clause_index);
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
      default: // We have unit on a literal - extend alpha
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
  alpha_generation++;
  subst_generation++;

  // Make the negated literals of the candidate clause persist for all RAT hints
  llong cc_gen = alpha_generation + get_num_RAT_hints();
  srid_t candidate_clause_id = CLAUSE_ID_FROM_LINE_NUM(current_line_num);
  assume_negated_clause(candidate_clause_id, cc_gen);

  srid_t *hints_iter = get_hints_start();
  srid_t *hints_end = get_hints_end();

  // Now take non-RAT UP hints (if any) to extend alpha
  if (unit_propagate(&hints_iter, hints_end, cc_gen) == CONTRADICTION) {
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
          // Scan all the RAT hints for a negative ID matching this clause
          for (up_iter = rat_hints_start; up_iter < hints_end; up_iter++) {
            if (-((*up_iter) + 1) == i) {
              hints_iter = MAX(hints_iter, up_iter);
              break;
            }
          }

          PRINT_ERR_AND_EXIT_IF(up_iter == hints_end,
            "RAT clause has no corresponding RAT hint group.");
        }

        // We successfully found a matching RAT hint
        // Assume the negation of the RAT clause and perform unit propagation
        int neg_res = assume_negated_clause_under_subst(i, alpha_generation);

        /* 
         * It is possible for a RAT clause to have no UP derivation. This occurs
         * when the clause is immediately satisfied by alpha (when extended
         * by the UP after assuming the negation of the candidate clause).
         * Notably, this is different than the witness satisfying the clause.
         * If alpha satisfies the RAT clause, then we skip its UP hints, if any
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
        alpha_generation++; // Clear the negated RAT clause and UP extensions
        break;
      case CONTRADICTION:
        PRINT_ERR_AND_EXIT("RAT contradiction: should have had UP derivation.");
      default: PRINT_ERR_AND_EXIT("Corrupted clause reduction.");
    }
  }

finish_line:
  alpha_generation = cc_gen; // Clear all unit propagations we did
  if (new_clause_size == 0) {
    derived_empty_clause = 1;
  } else {
    mark_clause_as_checked();
  }
}

/**
 * @brief Checks the LSR proof.
 * 
 * If the parsing strategy is `PS_STREAMING`, then parsing is interleaved with
 * proof checking until the proof is done or until the empty clause is derived.
 */
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

  if (derived_empty_clause) {
    log_msg(VL_QUIET, "s VERIFIED UNSAT\n");
  } else {
    log_msg(VL_QUIET, "s VALID\n");
    log_msg(VL_NORMAL, "c A valid proof, without an empty clause.\n.");
  }
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
        if (long_help_msg_flag) {
          print_long_help_msg(stdout);
          return 0;
        } else {
          PRINT_ERR_AND_EXIT("Unimplemented long option.");
        }
      default:
        cli_res = cli_handle_opt(&cli, ch, optopt, optarg);
        switch (cli_res) {
          case CLI_UNRECOGNIZED:
            fprintf(stderr, "Error: Unimplemented option.\n");
          case CLI_HELP_MESSAGE:
            print_short_help_msg(stderr);
            return 1;
          case CLI_SUCCESS: break;
          default: PRINT_ERR_AND_EXIT("Corrupted CLI result.");
        }
    }
  }

  // `getopt_long()` sets `optind` to the index of the first non-option argument
  // It also shuffles all of the non-option arguments to the end of `argv`
  // Thus, we expect the CNF and LSR file paths to be at the end now
  //   (modulo some behavior changes due to `-n` and `-d` flags)
  switch (argc - optind) {
    case 0:
      PRINT_ERR_AND_EXIT_IF(!cli.name_provided, "No file prefix provided.");
      cli_concat_path_extensions(&cli, ".cnf", ".dsr", ".lsr");
      break;
    case 1:
      PRINT_ERR_AND_EXIT_IF(cli.dir_provided,
        "Cannot provide a directory without an LSR file path.");

      if (cli.name_provided) {
        cli_concat_path_extensions(&cli, ".cnf", "", argv[optind]);
      } else {
        // The CNF file is provided as a normal file path
        cli.cnf_file_path = argv[optind];
        cli.lsr_file_path = NULL;
      }
      break;
    case 2:
      if (cli.dir_provided || cli.name_provided) {
        cli_concat_path_extensions(&cli, argv[optind], "", argv[optind + 1]);
      } else {
        cli.cnf_file_path = argv[optind];
        cli.lsr_file_path = argv[optind + 1];
      }
      break;
    default:
      fprintf(stderr, "Error: Invalid number of non-option arguments.\n");
      print_short_help_msg(stderr);
      return 1;
  }

  // Open the files first, to ensure we don't do work unless they exist
  FILE *cnf_file = xfopen(cli.cnf_file_path, "r");
  if (cli.lsr_file_path == NULL) {
    PRINT_ERR_AND_EXIT_IF(p_strategy == PS_EAGER,
      "Cannot use eager strategy with `stdin` as the LSR file.");
    lsr_file = stdin;
  } else {
    lsr_file = xfopen(cli.lsr_file_path, "r");
  }

  log_msg(VL_NORMAL, "c CNF file path: %s\n", cli.cnf_file_path);
  if (lsr_file == stdin) {
    log_msg(VL_NORMAL, "c No LSR file path provided, using stdin.\n");
  } else {
    log_msg(VL_NORMAL, "c LSR file path: %s\n", cli.lsr_file_path);
  }

  if (p_strategy == PS_EAGER) {
    log_msg(VL_NORMAL, "c Using an EAGER parsing strategy.\n");
  } else {
    log_msg(VL_NORMAL, "c Using a STREAMING parsing strategy.\n");
  }

  parse_cnf(cnf_file);
  log_msg(VL_NORMAL, "c The CNF formula has %lld clauses and %d variables.\n",
    ((llong) formula_size), max_var);

  prepare_lsr_check_data();
  check_proof();

  return 0;
}