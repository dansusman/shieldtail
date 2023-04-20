#ifndef _SEQUENCE_H
#define _SEQUENCE_H

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

typedef uint64_t SNAKEVAL;

uint64_t get_length(SNAKEVAL val) asm ("len");
uint64_t concat(SNAKEVAL val1, SNAKEVAL val2, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("?concat");
uint64_t charAt(SNAKEVAL str_val, SNAKEVAL idx_val, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm ("?charAt");
uint64_t intToChar(SNAKEVAL num, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm ("chr");
uint64_t charToInt(SNAKEVAL chr) asm ("ord");

#endif
