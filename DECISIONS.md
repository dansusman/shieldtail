-   We chose not to support chars as an immediate. Instead, they are just strings of length 1. This choice impacted the following things:
    -- Character only functions (e.g. <TBD>) need an additional check for length 1 strings
    -- <TBD>

-   Strings are CExprs because while they don't contain <expr> parts, they require further computation to be ready; namely, create the string, place it on the heap, return the heap pointer.
    -- it feels a bit odd because strings are constants, but they're more complex than our other immediates, so this feels right

-   Strings are immutatable, following Python's conventions.
    -- concatenation makes a copy of the original strings, smashing them together

-   Highlight bit pattern details (LSB of arity for xyz reasons)

-   We support string at index access with the syntax "hello"[1] -> "e" because we're treating strings and tuples similarly in many ways, and we thought it'd be grating to have an alternative syntax for getting the character at a given index
