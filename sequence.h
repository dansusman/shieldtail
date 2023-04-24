#ifndef _SEQUENCE_H
#define _SEQUENCE_H

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include "gc.h"

typedef uint64_t SNAKEVAL;

/*
    Returns the length of the given string or tuple.
    Guards against SNAKEVALs that aren't heap sequences (tuple/string) by
    erroring with ERR_LENGTH_NOT_SEQ.

    Assembly alias: `len'

    Arguments:
        val: the tuple or string for which we compute the length

    Returns:
        The length of the input val
*/
uint64_t get_length(SNAKEVAL val) asm("len");

/*
    Concatenates the two given tuples/strings together and copies the result to the heap.

    Errors with ERR_CONCAT_NOT_SAME if the given heap sequences are not both strings or both tuples.
    We only ever call this runtime function after checking that `val1' and `val2' are both valid
    heap sequences (either a tuple or a string).

    Arguments:
        val1: the first string/tuple (to be concatted to)
        val2: the second string/tuple (to be added on the end)
        alloc_ptr: the location at which to begin allocating the new string/tuple (R15)
        cur_frame: the base pointer to the beginning of the current frame (RBP)
        cur_stack_top: the base pointer of the topmost stack frame (RSP)

    Returns:
        The new top of the heap, at which to continue allocations
*/
uint64_t concat(SNAKEVAL val1, SNAKEVAL val2, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("?concat");

/*
    Finds the character at the given index within the given string.

    Errors with ERR_GET_HIGH_INDEX or ERR_GET_LOW_INDEX if the provided index
    is outside the bounds of the string.

    We only call this runtime function after checking that `str_val' is a valid
    heap sequence and `idx_val' is a valid integer.

    Arguments:
        str_val: the first string/tuple (to be concatted to)
        idx_val: the second string/tuple (to be added on the end)
        alloc_ptr: the location at which to begin allocating the new string/tuple (R15)
        cur_frame: the base pointer to the beginning of the current frame (RBP)
        cur_stack_top: the base pointer of the topmost stack frame (RSP)

    Returns:
        The new top of the heap, at which to continue allocations
*/
uint64_t charAt(SNAKEVAL str_val, SNAKEVAL idx_val, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("?charAt");

/*
    Converts the given SNAKEVAL to its corresponding ASCII character, if it exists.

    Errors with ERR_CHR_NOT_NUM if `num' is not a valid ASCII code number.

    Assembly alias: `chr'

    Arguments:
        num: the number to convert to a character
        alloc_ptr: the location at which to begin allocating the new string/tuple (R15)
        cur_frame: the base pointer to the beginning of the current frame (RBP)
        cur_stack_top: the base pointer of the topmost stack frame (RSP)

    Returns:
        The new top of the heap, at which to continue allocations
*/
uint64_t intToChar(SNAKEVAL num, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("chr");

/*
    Converts the given SNAKEVAL to its corresponding ASCII character code, if it exists.

    Errors with ERR_ORD_NOT_CHAR if `chr' is not a valid ASCII character.

    Assembly alias: `chr'

    Arguments:
        chr: the character to convert to a ASCII code number

    Returns:
        The ASCII code of the given character
*/
uint64_t charToInt(SNAKEVAL chr) asm("ord");

/*
    Creates a new string/tuple with contents of the given `seq_val' from the given
    start index (inclusive) through the given end index (exclusive), using steps
    of a given size. Provides boolean flags for using standard start index, end index, and/or step.

    We only call this after checking that the given heap sequence is a valid tuple/string and
    `start_idx_val', `end_idx_val', and `step_val' are valid numbers.

    Errors with ERR_SLICE_NOT_NUM if `step_val' is 0.

    Arguments:
        seq_val: the heap sequence (tuple/string) to slice
        start_idx_val: the index at which to start slicing (inclusive)
        start_default: true if no start_idx was explicitly provided, false otherwise
        end_idx_val: the index at which to end slicing (exclusive)
        end_default: true if no end_idx was explicitly provided, false otherwise
        step_val: the step for each iteration in the slicing (e.g. 2 = skip every other)
        step_default: true if no step was explicitly provided, false otherwise
        alloc_ptr: the location at which to begin allocating the new string/tuple (R15)
        cur_frame: the base pointer to the beginning of the current frame (RBP)
        cur_stack_top: the base pointer of the topmost stack frame (RSP)

    Returns:
        The new top of the heap, at which to continue allocations
*/
uint64_t slice(SNAKEVAL seq_val, SNAKEVAL start_idx_val, bool start_default, SNAKEVAL end_idx_val, bool end_default, SNAKEVAL step_val, bool step_default, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("?slice");

/*
    Converts the given number to a valid SNAKEVAL string.

    Errors with ERR_NUM_TO_STRING_NOT_NUM if `num' is not a valid number.

    Assembly alias: `numToString'

    Arguments:
        val: the number to convert to a string
        alloc_ptr: the location at which to begin allocating the new string/tuple (R15)
        cur_frame: the base pointer to the beginning of the current frame (RBP)
        cur_stack_top: the base pointer of the topmost stack frame (RSP)

    Returns:
        The new top of the heap, at which to continue allocations
*/
uint64_t numToString(SNAKEVAL val, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("numToString");

/*
    Converts the given string to its corresponding boolean, nil, or number.

    Errors with ERR_FROM_STR_NOT_STR if `str_val' isn't a valid string. Errors with ERR_FROM_STR_INVALID
    if the length of the given string is larger than the biggest possible number in our language.

    Assembly alias: `fromString'

    Arguments:
        str_val: the string to convert to a boolean, nil, or number

    Returns:
        BOOL_TRUE       if `str_val' is "true"
        BOOL_FALSE      if `str_val' is "false"
        NIL             if `str_val' is "nil"
        a number        if `str_val' is "<some number>"
*/
uint64_t fromString(SNAKEVAL str_val) asm("fromString");

#endif
