#ifndef _SEQUENCE_H
#define _SEQUENCE_H

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "gc.h"

typedef uint64_t SNAKEVAL;

uint64_t get_length(SNAKEVAL val) asm("len");
uint64_t concat(SNAKEVAL val1, SNAKEVAL val2, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("?concat");
uint64_t charAt(SNAKEVAL str_val, SNAKEVAL idx_val, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("?charAt");
uint64_t intToChar(SNAKEVAL num, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("chr");
uint64_t charToInt(SNAKEVAL chr) asm("ord");
uint64_t slice(SNAKEVAL seq_val, SNAKEVAL start_idx_val, bool start_default, SNAKEVAL end_idx_val, bool end_default, SNAKEVAL step_val, bool step_default, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("?slice");
uint64_t numToString(SNAKEVAL val, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("numToString");

#endif
