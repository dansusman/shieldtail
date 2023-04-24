# Strings

-   [x] Strings/Chars in lexer.mll and parser.mly
        -- multi-line strings?
-   [x] EString, ImmString
-   [x] Allocation
-   [x] GC: need to sweep strings (copy/paste tuple case again?)
-   [x] Char doesn't need a whole word
-   [x] get at index for strings
-   [x] Concatenation
        -- str1 ^ str2
-   [x] charToInt, intToChar | chr, ord
-   [x] String equality
-   [x] slicing
-   [x] Build out a string library
    -   [x] toString
    -   [x] split
    -   [x] comparison (but not defined as primops)
    -   [x] isPrefix
-   [x] escape sequence printing
-   [x] test a bunch of random special characters via ascii code and direct usage

## Compilation

-   [x] Readdress the tagging pattern
    -   use the LSB of arity to delineate
-   [x] Create and store strings on heap (return the heap_reg, ofc)
-   [x] Tuple indexing and other existing things must not accept strings
-   [x] Tag error checks for prim ops
        -- concatenation needs to check for string tag for left and right

# Implement the functionality to demo

-   [x] Caesar cipher (input, string get at index, len, ord, chr, concat)
-   [x] reverse a string [::-1] (input, slicing)
-   [x] Pig Latin (input, slicing, len, concat, split)
-   [x] Sort a list of strings (input, comparison, split)

# Testing

-   [ ] Make sure existing prim ops do/don't allow strings appropriately

# Presentation

-   [x] write substantial documentation - D
-   [x] Write down where each string operation in STRINGS.md lives within input/ dir - D
-   [ ] Write some agenda notes
-   [ ] Highlight important design decisions (see DECISIONS.md) - D
-   [ ] Well-defined and Heavily Detailed README - D then J
        -- usage examples
        -- supported language features
        -- high-level description
        -- snake puns (maybe a snake starting with S?)
-   [ ] write lots of integration tests - J
-   [ ] revive test.ml - D
-   [ ] revive existing integration tests - J

# Other Ideas

-   [x] Support strings as input
