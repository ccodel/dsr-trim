/**
 * @file lsr_data.h
 * @brief Data structures used by `lsr-check`.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-04-16
 */

#ifndef _LSR_CHECK_DATA_H_
#define _LSR_CHECK_DATA_H_

#include "../global_types.h"
#include "../global_data.h"
#include "../lit_occ.h"
#include "../range_array.h"
#include "../timer.h"
#include <stdio.h>

#ifndef SKIP_REMAINING_UP_HINTS
#define SKIP_REMAINING_UP_HINTS(iter, end) do {                                \
  while ((iter) < (end) && *(iter) > 0) { (iter)++; }                          \
} while (0)
#endif

// Max line identifier checked/parsed. Is 1-indexed and in DIMACS form.
extern srid_t max_line_id;

// The current line number being checked. This is 0-indexed and starts at 0.
extern srid_t current_line;

// The unit propagation hints. When the parsing strategy is `PS_EAGER`,
// the hints are indexed by line number. Otherwise, they are at index 0.
extern range_array_t hints;

// When the parsing strategy is `PS_STREAMING`, this tracks the number of
// RAT hint groups for the parsed line. Otherwise, it is ignored.
extern uint num_RAT_hints;

// When the parsing strategy is `PS_EAGER`, this stores the number of RAT
// hint groups for each line. If we are STREAMING, this is ignored.
extern uint *line_num_RAT_hints;
extern uint line_num_RAT_hints_alloc_size;

// Indexed by `current_line`. Stores the addition clause's line ID and
// line number during parsing. For example, if `510 3 -2 0` occurs on
// the 5th line of the file, then the structure stores `{ 510, 5 }`.
extern srid_t *line_ids;
extern uint line_ids_alloc_size;

/** @brief The clause IDs to delete, indexed by line number.
* 
* This is only used when the parsing strategy is `PS_EAGER`. Otherwise,
* deletions are handled as they are parsed, and `deletions` is unused.
* 
* Note that deletion lines are processed *after* addition lines with the
* same ID, and the proof may start with a deletion line with an ID smaller
* than the first addition line's. Thus, we index into `deletions` by adding
* 1 to the `current_line`.
*/
extern range_array_t deletions;

// The active LSR proof file. Assigned in `main()`. Can be `stdin`.
extern FILE *lsr_file;

// Timer used to time various parts of the runtime.
// Initialized in the `main()` function and not `prepare_lsr_check_data()`.
extern sr_timer_t timer;

// Counts the number of times and the clauses that literals appear in.
extern lit_occ_t lit_occ;

////////////////////////////////////////////////////////////////////////////////

srid_t get_line_id_for_clause(srid_t clause_id);
srid_t get_line_id_for_line_num(srid_t line_num);

uint get_num_RAT_hints(void);

/**
 * @brief Returns a pointer to the start of the UP hints for the current line.
 * 
 * The pointer will point to the start of *all* the hints, including any
 * global UP hints.
 */
#define get_hints_start()    ((srid_t *) \
    ra_get_range_start(&hints, (p_strategy == PS_EAGER) ? current_line : 0))

/**
 * @brief Returns a pointer to the end of the UP hints for the current line.
 * 
 * The `unit_propagate()` function uses pointer iterators, so we need a
 * pointer to the end of the hints, not merely a size.
 */
#define get_hints_end()    ((srid_t *) \
    ra_get_range_end(&hints, (p_strategy == PS_EAGER) ? current_line : 0))

void mark_clause_as_checked(srid_t clause_id);

// Returns a pointer to the start of the current line's deletions, if any.
// If there are no deletions, then this function equals `get_deletions_end()`.
// Implemented as a macro.
#define get_deletions_start()  \
    ((srid_t *) ra_get_range_start(&deletions, current_line))

// Returns a pointer to the end of the current line's deletions, if any.
// Implemented as a macro.
#define get_deletions_end()    \
    ((srid_t *) ra_get_range_end(&deletions, current_line))

void dbg_print_lsr_hints(void);
void prepare_lsr_check_data(void);
int has_another_lsr_line(void);
line_type_t prepare_next_lsr_line(void);

line_type_t parse_lsr_line(void);
void parse_entire_lsr_file(void);

#endif /* _LSR_CHECK_DATA_H_ */