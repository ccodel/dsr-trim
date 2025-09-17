/**
 * @file lsr_data.c
 * @brief Data structures used by `lsr-check`.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-04-16
 */

#include "lsr_data.h"
#include "../xmalloc.h"
#include "../global_data.h"
#include "../global_parsing.h"
#include "../sr_parser.h"
#include "../logger.h"

srid_t max_line_id = 0;
srid_t current_line = 0;

range_array_t hints;
uint num_RAT_hints = 0;
uint *line_num_RAT_hints = NULL;
uint line_num_RAT_hints_alloc_size = 0;

srid_t *line_ids = NULL;
uint line_ids_alloc_size = 0;

range_array_t deletions;
uint *lits_occurrences = NULL;

FILE *lsr_file = NULL;
sr_timer_t timer;

static srid_t num_parsed_lines = 0;

////////////////////////////////////////////////////////////////////////////////

srid_t get_line_id_for_clause(srid_t clause_id) {
  return line_ids[LINE_NUM_FROM_CLAUSE_ID(clause_id)];
}

srid_t get_line_id_for_line_num(srid_t line_num) {
  return line_ids[line_num];
}

static void store_line_num(srid_t line_num) {
  RESIZE_ARR(line_ids, line_ids_alloc_size,
    current_line, sizeof(srid_t));
  line_ids[current_line] = line_num;
}

/**
 * @brief Returns the number of RAT hint groups for the current line.
 * 
 * When the parsing strategy is `PS_EAGER`, we store this data in a
 * `line_num`-indexed array. Otherwise, we use `num_RAT_hints`.
 */
uint get_num_RAT_hints(void) {
  if (p_strategy == PS_EAGER) {
    return line_num_RAT_hints[current_line];
  } else {
    return num_RAT_hints;
  }
}

/**
 * @brief Prepares the data structure that stores UP hints to receive hints
 *        for the next addition line.
 * 
 * The caller must set `current_line` to the line being parsed before
 * calling this function.
 */
static void prepare_hints_for_next_addition_line(void) {
  if (p_strategy == PS_EAGER) {
    ra_commit_empty_ranges_until(&hints, current_line);
    RECALLOC_ARR(line_num_RAT_hints, line_num_RAT_hints_alloc_size, 
      current_line, sizeof(uint));
    
  } else {
    ra_reset(&hints);
    num_RAT_hints = 0;
  }
}

/**
 * @brief Adds one to the occurrence counter for each literal in the clause.
 * 
 * If the witness is ever omitted/just the pivot (i.e., a DRAT witness),
 * then only the hint groups included in the line need to be checked.
 * But to ensure that we didn't miss any RAT hint groups, we count the
 * number of times we encounter each relevant literal. If the counts
 * agree at the end, then the line was good.
 * 
 * When a clause gets added to the formula, its literals need to have their
 * occurrence counts incremented. This function does that.
 * 
 * @param clause_index The clause ID.
 */
static void add_occurrences_for_clause(srid_t clause_index) {
  int *start = get_clause_start_unsafe(clause_index);
  int *end = get_clause_end(clause_index);
  while (start < end) {
    int lit = *start;
    lits_occurrences[lit]++;
    start++;
  }
}

/**
 * @brief Subtracts one from the occurrences for each literal in the clause.
 * 
 * When a clause is deleted or otherwise removed from the formula, we need
 * to decrease the occurrence count for each literal in the clause.
 * 
 * Call this function before actually deleting the clause.
 * 
 * @param clause_index The clause ID.
 */
static void remove_occurrences_for_clause(srid_t clause_index) {
  int *start = get_clause_start_unsafe(clause_index);
  int *end = get_clause_end(clause_index);
  while (start < end) {
    int lit = *start;
    lits_occurrences[lit]--;
    start++;
  }
}

/**
 * @brief Marks the given candidate clause as being successfully redundant.
 *        Also increments the `current_line`.
 * 
 * When the parsing strategy is `PS_EAGER`, the clauses are in the formula
 * already, but we need to update the first/last information for the literals
 * and the occurrences for the literals in the clause.
 */
void mark_clause_as_checked(srid_t clause_id) {
  perform_clause_first_last_update(clause_id);
  add_occurrences_for_clause(clause_id);
  current_line++;
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
static void prepare_deletions_for_next_deletion_line(void) {
  if (p_strategy == PS_EAGER) {
    ra_commit_range(&deletions);
  }
}

static inline void actually_delete_clause(srid_t clause_id) {
  remove_occurrences_for_clause(clause_id);
  delete_clause(clause_id);
}

/**
 * @brief Processes a clause ID during parsing for deletion.
 * 
 * During streaming, we delete clauses as we go. When eagerly parsing,
 * we store the clause IDs for later.
 * 
 * @param clause_id The clause to be deleted, in 1-indexed (DIMACS) form.
 */
void process_deletion(srid_t clause_id) {
  FATAL_ERR_IF(clause_id < 0, "Deletion ID %lld was negative.", clause_id);
  clause_id = FROM_DIMACS_CLAUSE(clause_id);
  if (p_strategy == PS_EAGER) {
    ra_insert_srid_elt(&deletions, clause_id);
  } else {
    actually_delete_clause(clause_id);
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
  srid_t id = CLAUSE_ABS(clause_id);
  id = FROM_DIMACS_CLAUSE(id);
  srid_t current_line_id = LINE_ID_FROM_LINE_NUM(current_line);
  FATAL_ERR_IF(id > current_line_id || is_clause_deleted(id),
    "[line %lld | id %lld] Clause %lld is out of bounds or is deleted.",
    num_parsed_lines, current_line_id, TO_DIMACS_CLAUSE(id));

  ra_insert_srid_elt(&hints, clause_id);

  // If the clause starts a new RAT hint group, increment the
  // number of RAT hint groups according to our parsing strategy
  if (clause_id < 0) {
    if (p_strategy == PS_EAGER) {
      line_num_RAT_hints[current_line]++;
    } else {
      num_RAT_hints++;
    }
  }
}

/**
 * @brief Allocates memory for LSR-specific data structures. If the parsing
 *        strategy is `EAGER`, this function also parses the entire file.
 * 
 * Upon return, the `current_line` is set to 0.
 */
void prepare_lsr_check_data(void) {
  line_ids_alloc_size = num_cnf_clauses;
  line_ids = xcalloc(line_ids_alloc_size, sizeof(srid_t));

  // Count the number of times each literal appears in the original CNF
  lits_occurrences = xcalloc((max_var + 1) * 2, sizeof(uint));
  for (srid_t c = 0; c < formula_size; c++) {
    add_occurrences_for_clause(c);
  }

  if (p_strategy == PS_EAGER) {
    ra_init(&hints, num_cnf_clauses * 10, num_cnf_vars, sizeof(srid_t));
    ra_init(&deletions, num_cnf_clauses * 10, num_cnf_vars, sizeof(srid_t));

    line_num_RAT_hints_alloc_size = num_cnf_clauses;
    line_num_RAT_hints = xcalloc(line_num_RAT_hints_alloc_size, sizeof(uint)); 

    parse_entire_lsr_file();
  } else {
    ra_init(&hints, num_cnf_vars * 10, 2, sizeof(srid_t));
    max_line_id = num_cnf_clauses;
    // No deletions, since we process them as we go
  }

  current_line = 0;
}

/**
 * @brief Returns 1 if another LSR line exists to be checked or parsed.
 * 
 * When the parsing strategy is `PS_EAGER`, the `current_line` is compared
 * against the maximum line ID encountered during parsing. This function
 * assumes that the caller increments `current_line` after an addition
 * line is successfully checked.
 * 
 * When the parsing strategy is `PS_STREAMING`, the `lsr_file` stream is
 * read from until a new line of input is detected.
 */
int has_another_lsr_line(void) {
  if (p_strategy == PS_EAGER) {
    return LINE_ID_FROM_LINE_NUM(current_line) <= max_line_id;
  } else {
    return has_another_line(lsr_file);
  }
}

static inline void delete_stored_clauses(void) {
  srid_t *del_iter = get_deletions_start();
  srid_t *del_end = get_deletions_end();
  for (; del_iter < del_end; del_iter++) {
    actually_delete_clause(*del_iter);
  }
}

/**
 * @brief Prepares data structures and values to parse or check the next line.
 * 
 * When the parsing strategy is `PS_EAGER`, stored deletion lines are processed
 * (and clauses are deleted from the formula) until an addition line is
 * found. On return, the `current_line` is set to the next addition line
 * to check. If the line is an addition, then `new_clause_size` is set to the
 * size of the next candidate clause.
 * 
 * When the parsing strategy is `PS_STREAMING`, a new LSR line is parsed.
 * 
 * @return The line type (`ADDITION_LINE` or `DELETION_LINE`).
 */
line_type_t prepare_next_lsr_line(void) {
  if (p_strategy == PS_EAGER) {
    // Process deletions until we have an addition line
    // Deletions are 1-indexed, but for any ID, deletions follow addition lines
    // So we first handle the deletion based the new `current_line`
    // (from `mark_clause_as_checked()`), but due to the 1-indexing,
    // this actually handles the deletions following the previous line
    srid_t clause_id;
    current_line--;
    do {
      current_line++;
      delete_stored_clauses();
      clause_id = CLAUSE_ID_FROM_LINE_NUM(current_line);
    } while (is_clause_deleted(clause_id));
    new_clause_size = get_clause_size(clause_id);
    return ADDITION_LINE;
  } else {
    return parse_lsr_line();
  }
}

/**
 * @brief Parses the next LSR line and stores/processes the data according
 *        to the current parsing strategy. Returns either `DELETION_LINE`
 *        or `ADDITION_LINE`.
 * 
 * If the parsing strategy is `PS_EAGER`, we store the candidate redundant
 * clauses in the CNF `lits_db` database, the hints in `hints`, any
 * substitution witness in `witnesses`, and deletion lines in `deletions`.
 * 
 * If the parsing strategy is `PS_STREAMING`, we store the clause like normal,
 * but we reset `hints` and `witnesses` to clear the previous line's data.
 * This way, we reduce our memory overhead and benefit from caching.
 */
line_type_t parse_lsr_line(void) {
  num_parsed_lines++;
  srid_t line_id, clause_id;
  line_type_t line_type = read_lsr_line_start(lsr_file, &line_id);
  current_line = LINE_NUM_FROM_LINE_ID(line_id); // Convert out of DIMACS
  switch (line_type) {
    case DELETION_LINE:
      // Ensure that the line ID is (non-strictly) monotonically increasing
      FATAL_ERR_IF(line_id < max_line_id,
        "Deletion line ID (%lld) decreases.", line_id);
      max_line_id = line_id;

      // We "1-index" deletion lines to account for a starting deletion line
      srid_t deletion_line_num = MAX(0, current_line + 1);

      // Cap off empty deletion lines until we reach the current line
      if (p_strategy == PS_EAGER) {
        ra_commit_empty_ranges_until(&deletions, deletion_line_num);
      }

      // The deletion line ends when we encounter a 0
      while ((clause_id = read_clause_id(lsr_file)) != 0) {
        process_deletion(clause_id); 
      }

      break;
    case ADDITION_LINE:
      // Check that the line id is strictly monotonically increasing
      FATAL_ERR_IF(line_id <= max_line_id,
        "Addition line ID (%lld) doesn't increase.", line_id);
      max_line_id = line_id;
      store_line_num(num_parsed_lines);

      // Create deleted (empty) clauses until the formula size catches up
      while (formula_size < max_line_id - 1) {
        commit_clause();
        delete_clause(formula_size - 1);
      }

      parse_sr_clause_and_witness(lsr_file, current_line);
      prepare_deletions_for_next_deletion_line();

      // Parse the UP hints, keeping the clause IDs as-is so we can tell
      // where the RAT hint groups start (i.e. with negative clause IDs)
      prepare_hints_for_next_addition_line();
      while ((clause_id = read_clause_id(lsr_file)) != 0) {
        insert_hint(clause_id);
      }

      ra_commit_range(&hints);
      break;
    default: log_fatal_err("Invalid line type: %d", line_type);
  }

  return line_type;
}

/**
 * @brief Parses the entire LSR file and stores the data accordingly.
 * 
 * Call only if the parsing strategy is `PS_EAGER`.
 * 
 * Upon return, the `lsr_file` is closed, and `current_line` is set to
 * the final line number parsed. Callers may want to set this variable back
 * to 0 before starting proof checking.
 */
void parse_entire_lsr_file(void) {
  FATAL_ERR_IF(p_strategy != PS_EAGER,
    "To parse the entire LSR file eagerly, the p_strategy must be EAGER.");

  timer_record(&timer, TIMER_LOCAL);

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
    logc("Detected the empty clause on line %lld.", current_line + 1);
  }

  logc("Parsed %lld proof lines.", current_line + 1);
  timer_print_elapsed(&timer, TIMER_LOCAL, "Parsing the LSR proof");
}
