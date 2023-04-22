#include "sequence.h"

extern uint64_t NUM_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t FORWARDING_TAG_MASK;
extern uint64_t SEQ_HEAP_TAG_MASK;
extern uint64_t NUM_TAG;
extern uint64_t CLOSURE_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t FORWARDING_TAG;
extern uint64_t STRING_HEAP_TAG;
extern uint64_t NIL;

extern uint64_t ERR_COMP_NOT_NUM;
extern uint64_t ERR_ARITH_NOT_NUM;
extern uint64_t ERR_LOGIC_NOT_BOOL;
extern uint64_t ERR_IF_NOT_BOOL;
extern uint64_t ERR_OVERFLOW;
extern uint64_t ERR_GET_NOT_TUPLE;
extern uint64_t ERR_GET_LOW_INDEX;
extern uint64_t ERR_GET_HIGH_INDEX;
extern uint64_t ERR_NIL_DEREF;
extern uint64_t ERR_OUT_OF_MEMORY;
extern uint64_t ERR_SET_NOT_TUPLE;
extern uint64_t ERR_SET_LOW_INDEX;
extern uint64_t ERR_SET_HIGH_INDEX;
extern uint64_t ERR_CALL_NOT_CLOSURE;
extern uint64_t ERR_CALL_ARITY_ERR;
extern uint64_t ERR_GET_NOT_NUM;
extern uint64_t ERR_SET_NOT_NUM;
extern uint64_t ERR_TUPLE_DESTRUCTURE_MISMATCH;
extern uint64_t ERR_CONCAT_NOT_SEQ;
extern uint64_t ERR_CONCAT_NOT_SAME;
extern uint64_t ERR_LENGTH_NOT_SEQ;
extern uint64_t ERR_ORD_NOT_CHAR;
extern uint64_t ERR_CHR_NOT_NUM;
extern uint64_t ERR_SLICE_NOT_SEQ;
extern uint64_t ERR_SLICE_NOT_NUM;

extern uint64_t *HEAP_END asm("?HEAP_END");

uint64_t *try_gc(uint64_t *alloc_ptr, uint64_t bytes_needed, uint64_t *cur_frame, uint64_t *cur_stack_top) asm("?try_gc");
void error() asm("?error");

SNAKEVAL get_length(SNAKEVAL val)
{
  bool is_seq = (val & TUPLE_TAG_MASK) == TUPLE_TAG;
  if (!is_seq)
  {
    error(ERR_LENGTH_NOT_SEQ, val);
  }

  uint64_t *seq = (uint64_t *)(val - TUPLE_TAG);
  bool is_string = (seq[0] & SEQ_HEAP_TAG_MASK) == STRING_HEAP_TAG;
  return seq[0] - (is_string ? STRING_HEAP_TAG : 0);
}

uint64_t concat(SNAKEVAL val1, SNAKEVAL val2, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top)
{
  uint64_t *seq1 = (uint64_t *)(val1 - TUPLE_TAG);
  uint64_t *seq2 = (uint64_t *)(val2 - TUPLE_TAG);
  // if one is a string and one is a tuple
  if ((seq1[0] & SEQ_HEAP_TAG_MASK) != (seq2[0] & SEQ_HEAP_TAG_MASK))
  {
    error(ERR_CONCAT_NOT_SAME, val1);
  }

  bool is_string = (seq1[0] & SEQ_HEAP_TAG_MASK) == STRING_HEAP_TAG;
  uint64_t size1;
  uint64_t size2;

  if (is_string)
  {
    // take off the tag, we just want the machine size
    size1 = (seq1[0] - STRING_HEAP_TAG) / 2;
    size2 = (seq2[0] - STRING_HEAP_TAG) / 2;
  }
  else
  {
    size1 = seq1[0] / 2;
    size2 = seq2[0] / 2;
  }

  // sum of the sizes, plus 1 word for size and maybe 1 for padding
  uint64_t summed_size = size1 + size2;
  uint64_t total_machine_size = (is_string ? letters_to_words(summed_size) : (summed_size)) + 1;
  total_machine_size += total_machine_size % 2 == 0 ? 0 : 1;

  uint64_t *new_heap = alloc_ptr;

  // do GC and get a new heap pointer if needed
  if (HEAP_END - alloc_ptr < total_machine_size)
  {
    new_heap = try_gc(alloc_ptr, total_machine_size, cur_frame, cur_stack_top);
  }

  // store the new combined size
  new_heap[0] = (size1 + size2) * 2 + (is_string ? STRING_HEAP_TAG : 0);

  if (is_string)
  {
    char *seq1_char = (char *)seq1;
    char *seq2_char = (char *)seq2;
    char *new_str = (char *)new_heap;
    // copy in all of the elements from the first heap sequence
    for (int i = 8; i < size1 + 8; i++)
    {
      // strings store multiple chars in one word so we need to account for different heap addresses
      new_str[i] = seq1_char[i];
    }
    // copy in all of the elements from the second heap sequence
    for (int i = 8; i < size2 + 8; i++)
    {
      new_str[i + size1] = seq2_char[i];
    }
  }
  else
  {
    // copy in all of the elements from the first heap sequence
    for (int i = 0; i < size1; i++)
    {
      new_heap[i + 1] = seq1[i + 1];
    }

    // copy in all of the elements from the second heap sequence
    for (int i = 0; i < size2; i++)
    {
      new_heap[i + size1 + 1] = seq2[i + 1];
    }
  }

  // return what the heap pointer should be after this allocation
  return new_heap + total_machine_size;
}

uint64_t charAt(SNAKEVAL str_val, SNAKEVAL idx_val, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top)
{
  char *str = (char *)(str_val - TUPLE_TAG);
  uint64_t machine_idx = idx_val / 2;
  uint64_t length = (str[0] - STRING_HEAP_TAG) / 2;

  if (machine_idx < 0)
  {
    error(ERR_GET_LOW_INDEX, idx_val);
  }
  else if (machine_idx >= length)
  {
    error(ERR_GET_HIGH_INDEX, idx_val);
  }
  else
  {
    uint64_t *new_heap = alloc_ptr;

    uint64_t total_machine_size = 2;

    // do GC and get a new heap pointer if needed
    if (HEAP_END - alloc_ptr < total_machine_size)
    {
      new_heap = try_gc(alloc_ptr, total_machine_size, cur_frame, cur_stack_top);
    }

    // store the new string with size 1 (to tagged snake val)
    new_heap[0] = 1 * 2 + 1;
    new_heap[1] = str[machine_idx + 8];

    // return what the heap pointer should be after this allocation
    return new_heap + total_machine_size;
  }
}

uint64_t intToChar(SNAKEVAL num, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top)
{
  if ((num & NUM_TAG_MASK) != NUM_TAG || num / 2 > 255 || num < 0)
  {
    error(ERR_CHR_NOT_NUM, num);
  }

  uint64_t *new_heap = alloc_ptr;

  uint64_t total_machine_size = 2;

  // do GC and get a new heap pointer if needed
  if (HEAP_END - alloc_ptr < total_machine_size)
  {
    new_heap = try_gc(alloc_ptr, total_machine_size, cur_frame, cur_stack_top);
  }

  // store the new string with size 1 (to tagged snake val)
  new_heap[0] = 1 * 2 + 1;
  new_heap[1] = (char)(num / 2);

  // return what the heap pointer should be after this allocation
  return new_heap + total_machine_size;
}

uint64_t charToInt(SNAKEVAL chr_val)
{
  bool is_seq = (chr_val & TUPLE_TAG_MASK) == TUPLE_TAG;
  if (!is_seq)
  {
    error(ERR_ORD_NOT_CHAR, chr_val);
  }

  uint64_t *chr = (uint64_t *)(chr_val - TUPLE_TAG);
  bool is_string = (chr[0] & SEQ_HEAP_TAG_MASK) == STRING_HEAP_TAG;

  if (!is_string)
  {
    error(ERR_ORD_NOT_CHAR, chr_val);
  }

  uint64_t length = (chr[0] - STRING_HEAP_TAG) / 2;
  if (length != 1)
  {
    error(ERR_ORD_NOT_CHAR, chr_val);
  }

  return chr[1] * 2;
}

uint64_t slice(SNAKEVAL seq_val, SNAKEVAL start_idx_val, SNAKEVAL end_idx_val, SNAKEVAL step_val, uint64_t *alloc_ptr, uint64_t *cur_frame, uint64_t *cur_stack_top)
{
  uint64_t *seq = (uint64_t *)(seq_val - TUPLE_TAG);
  bool is_string = (seq[0] & SEQ_HEAP_TAG_MASK) == STRING_HEAP_TAG;
  uint64_t size;

  if (step_val == 0)
  {
    error(ERR_SLICE_NOT_NUM, step_val);
  }

  if (is_string)
  {
    // take off the tag, we just want the machine size
    size = (seq[0] - STRING_HEAP_TAG) / 2;
  }
  else
  {
    size = seq[0] / 2;
  }

  uint64_t start_idx = start_idx_val / 2;
  uint64_t end_idx = end_idx_val / 2;
  uint64_t step = step_val / 2;
  uint64_t buffer[size];
  int length_of_result;

  // we don't know exactly how large our newly allocated heap sequence should be
  // so do the assignment into a buffer and count how big our thing is
  // then we'll copy that buffer to the correct heap location later
  if (is_string)
  {
    length_of_result = 0;
    char *str = (char *)&seq[1];
    char *new_str = (char *)buffer;
    // copy in all of the elements from the first heap sequence
    for (int i = start_idx; ((int32_t)step) > 0 ? i < (int32_t)end_idx : i > (int32_t)end_idx; i += step)
    {
      // strings store multiple chars in one word so we need to account for different heap addresses
      if (i < size && i >= 0)
      {
        new_str[length_of_result] = str[i];
        length_of_result++;
      }
    }
  }
  else
  {
    uint64_t *tup = &seq[1];
    length_of_result = 0;
    // copy in all of the elements from the first heap sequence
    for (int i = start_idx; ((int32_t)step) > 0 ? i < (int32_t)end_idx : i > (int32_t)end_idx; i += step)
    {
      // strings store multiple chars in one word so we need to account for different heap addresses
      if (i < size && i >= 0)
      {
        buffer[length_of_result] = tup[i];
        length_of_result++;
      }
    }
  }

  uint64_t total_machine_size = 1 + (is_string ? letters_to_words(length_of_result) : length_of_result);
  total_machine_size += total_machine_size % 2 == 0 ? 0 : 1;

  uint64_t *new_heap = alloc_ptr;

  // do GC and get a new heap pointer if needed
  if (HEAP_END - alloc_ptr < total_machine_size)
  {
    new_heap = try_gc(alloc_ptr, total_machine_size, cur_frame, cur_stack_top);
  }

  // store the new combined size
  new_heap[0] = (length_of_result * 2) + (is_string ? STRING_HEAP_TAG : 0);

  memcpy(&new_heap[1], buffer, total_machine_size * 8);
  // return what the heap pointer should be after this allocation
  return new_heap + total_machine_size;
}
