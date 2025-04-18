/**
 * @file lsr_err.h
 * @brief Verbose error messages for `lsr-check`.
 * 
 * @author Cayden Codel (ccodel@andrew.cmu.edu)
 * @date 2025-04-16
 */

#ifndef _LSR_CHECK_ERR_H_
#define _LSR_CHECK_ERR_H_

#include "../global_types.h"

void lsr_err_no_rat_hint_group(srid_t clause_id);
void lsr_err_no_up_contradiction(srid_t clause_id, srid_t contra_hint);

#endif /* _LSR_CHECK_ERR_H_ */