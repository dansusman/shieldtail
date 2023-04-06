#include <gc.h>

typedef uint64_t SNAKEVAL;

#define OUT stdout
#ifdef DEBUG
#define DEBUG_PRINT(...) fprintf(OUT, __VA_ARGS__)
#else
#define DEBUG_PRINT(...) \
  do                     \
  {                      \
  } while (0)
#endif

void printHelp(FILE *out, SNAKEVAL val);
extern uint64_t NUM_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t FORWARDING_TAG_MASK;
extern uint64_t CLOSURE_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t FORWARDING_TAG;
extern uint64_t NIL;
extern uint64_t tupleCounter;
extern uint64_t *STACK_BOTTOM;
extern uint64_t *FROM_S;
extern uint64_t *FROM_E;
extern uint64_t *TO_S;
extern uint64_t *TO_E;

void naive_print_heap(uint64_t *heap, uint64_t *heap_end)
{
  DEBUG_PRINT("In naive_print_heap from %p to %p\n", heap, heap_end);
  for (uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1)
  {
    DEBUG_PRINT("  %ld/%p: %p (%ld)\n", i, (heap + i), (uint64_t *)(*(heap + i)), *(heap + i));
  }
}

void smarter_print_heap_section(uint64_t *heap, uint64_t *heap_end)
{
  for (uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1)
  {
    DEBUG_PRINT("  %ld/%p: %p (", i, (heap + i), (uint64_t *)(*(heap + i)));
    printHelp(OUT, *(heap + i));
    DEBUG_PRINT(")\n");
  }
}

void smarter_print_heap(uint64_t *from_start, uint64_t *from_end, uint64_t *to_start, uint64_t *to_end)
{
#ifdef DEBUG

  // Print out the entire heap (both semispaces), and
  // try to print values readably when possible
  DEBUG_PRINT("In smarter_print_heap from %p to %p\n", from_start, to_end);
  DEBUG_PRINT("From section (from %p to %p):\n", from_start, from_end);
  smarter_print_heap_section(from_start, from_end);

  DEBUG_PRINT("To section (from %p to %p):\n", to_start, to_end);
  smarter_print_heap_section(to_start, to_end);
  DEBUG_PRINT("\n");
#endif
}

bool valIsClosure(uint64_t val)
{
  return (val & CLOSURE_TAG_MASK) == CLOSURE_TAG;
}

bool valIsTuple(uint64_t val)
{
  return (val & TUPLE_TAG_MASK) == TUPLE_TAG;
}

bool valIsForwarding(uint64_t val)
{
  return (val & FORWARDING_TAG_MASK) == FORWARDING_TAG;
}

// Performs the GC copying logic for Closure values
uint64_t copyClosure(uint64_t *closure_addr, uint64_t *heap_top)
{
  DEBUG_PRINT("Copying closure\n");
  SNAKEVAL closure = *closure_addr;
  uint64_t *closure_ptr = (uint64_t *)(closure - CLOSURE_TAG);

  if (valIsForwarding(*closure_ptr))
  {
    uint64_t *forward_ptr = (uint64_t *)(*closure_ptr - FORWARDING_TAG);
    DEBUG_PRINT("Found forwarding pointer %018llx\n", (uint64_t)forward_ptr);
    uint64_t retagged_ptr = (uint64_t)forward_ptr + CLOSURE_TAG;
    *closure_addr = retagged_ptr;
    return heap_top;
  }

  uint64_t num_free_vars = closure_ptr[2];
  uint64_t closure_length = 3 + num_free_vars;
  uint64_t padded_closure_length = closure_length + (closure_length % 2);

  for (int i = 0; i < padded_closure_length; i++)
  {
    DEBUG_PRINT("Copying value at closure[%d] ", i);
    DEBUG_PRINT(printHelp(OUT, closure_ptr[i]));
    DEBUG_PRINT(" from %p to %p\n", closure_ptr + i, heap_top + i);
    heap_top[i] = closure_ptr[i];
  }

  closure_addr = heap_top;
  uint64_t f_ptr = (uint64_t)heap_top;
  f_ptr += FORWARDING_TAG;
  *closure_ptr = f_ptr;
  DEBUG_PRINT("making forwarding pointer at %p\n", *closure_ptr);

  uint64_t *new_heap_top = heap_top + padded_closure_length;
  for (int i = 3; i < closure_length; i++)
  {
    new_heap_top = copy_if_needed(&closure_addr[i], new_heap_top);
  }

  return new_heap_top;
}

// Performs the GC copying logic for Tuple values
uint64_t copyTuple(uint64_t *tuple_addr, uint64_t *heap_top)
{
  DEBUG_PRINT("Copying tuple\n");
  SNAKEVAL tuple = *tuple_addr;
  uint64_t *tuple_ptr = (uint64_t *)(tuple - TUPLE_TAG);

  if (valIsForwarding(*tuple_ptr))
  {
    uint64_t *forward_ptr = (uint64_t *)(*tuple_ptr - FORWARDING_TAG);
    DEBUG_PRINT("Found forwarding pointer %018llx\n", (uint64_t)forward_ptr);
    uint64_t retagged_ptr = (uint64_t)forward_ptr + TUPLE_TAG;
    *tuple_addr = retagged_ptr;
    return heap_top;
  }

  uint64_t arity = tuple_ptr[0] / 2;
  uint64_t tuple_length = 1 + arity;
  uint64_t padded_tuple_length = tuple_length + (tuple_length % 2);

  for (int i = 0; i < padded_tuple_length; i++)
  {
    DEBUG_PRINT("Copying value at tuple[%d] (raw, not index) ", i);
    DEBUG_PRINT(printHelp(OUT, tuple_ptr[i]));
    DEBUG_PRINT(" from %p to %p\n", tuple_ptr + i, heap_top + i);
    heap_top[i] = tuple_ptr[i];
  }

  tuple_addr = heap_top;
  uint64_t f_ptr = (uint64_t)heap_top;
  f_ptr += FORWARDING_TAG;
  *tuple_ptr = f_ptr;
  DEBUG_PRINT("making forwarding pointer at %p\n", tuple_ptr);

  uint64_t *new_heap_top = heap_top + padded_tuple_length;
  for (int i = 1; i < tuple_length; i++)
  {
    new_heap_top = copy_if_needed(&tuple_addr[i], new_heap_top);
  }

  return new_heap_top;
}

/*
  Copies a Racer value from the given address to the new heap,
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Racer value, which contains a Racer value,
                     i.e. a tagged word.
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location
    with a forwarding pointer to its new location
 */
uint64_t *copy_if_needed(uint64_t *garter_val_addr, uint64_t *heap_top)
{
  uint64_t garter_val = *garter_val_addr;

  if (garter_val == NIL)
  {
    return heap_top;
  }

  if (valIsClosure(garter_val))
  {
    uint64_t *new_heap_top = copyClosure(garter_val_addr, heap_top);
    if (new_heap_top != heap_top)
    {
      uint64_t closure_ptr = ((uint64_t)heap_top) + CLOSURE_TAG;
      *garter_val_addr = closure_ptr;
    }
    return new_heap_top;
  }
  else if (valIsTuple(garter_val))
  {
    uint64_t *new_heap_top = copyTuple(garter_val_addr, heap_top);
    if (new_heap_top != heap_top)
    {
      uint64_t tuple_ptr = ((uint64_t)heap_top) + TUPLE_TAG;
      *garter_val_addr = tuple_ptr;
    }
    return new_heap_top;
  }
  else
  {
    DEBUG_PRINT("Skipping copying a non-heap value: ");
#ifdef DEBUG
    printHelp(OUT, garter_val);
#endif
    DEBUG_PRINT("\n");

    return heap_top;
  }
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Racer frame
    top_frame: the base pointer of the topmost Racer stack frame
    top_stack: the current stack pointer of the topmost Racer stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
uint64_t *gc(uint64_t *bottom_frame, uint64_t *top_frame, uint64_t *top_stack, uint64_t *from_start, uint64_t *from_end, uint64_t *to_start)
{

  DEBUG_PRINT("Collecting garbage\n");
  uint64_t *old_top_frame = top_frame;
  uint64_t *old_to_start = to_start;

  do
  {
    DEBUG_PRINT("starting GC on new stack frame\n");
    DEBUG_PRINT("Top stack: %p, top frame: %p\n", top_stack, top_frame);

    for (uint64_t *cur_word = top_stack + 1; cur_word < top_frame; cur_word++)
    {
      DEBUG_PRINT("copying value at %p: ", cur_word);
#ifdef DEBUG
      printHelp(OUT, *cur_word);
#endif
      DEBUG_PRINT("\n");
      to_start = copy_if_needed(cur_word, to_start);
      DEBUG_PRINT("done copying\n");
      smarter_print_heap(from_start, from_end, old_to_start, to_start);
      // smarter_print_heap(from_start, from_end, old_to_start, to_start);
    }
    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack frame,
     * [top_frame + 8] is the return address, and
     * [top_frame + 16] is therefore the next frame's stack-top
     */
    top_stack = top_frame + 2;
    old_top_frame = top_frame;
    top_frame = (uint64_t *)(*top_frame);
  } while (old_top_frame <= bottom_frame); // Use the old stack frame to decide if there's more GC'ing to do

  // after copying and GC'ing all the stack frames, return the new allocation starting point
  return to_start;
}
