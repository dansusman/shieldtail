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
-   [ ] split/slicing?
-   [ ] toString
-   [ ] Build out a string library
-   [ ] String >, <, etc.?
-   [ ] support strings as input?
        -- write down any input() decisions/make examples to show old stuff still works
-   [ ] write substantial documentation
-   [ ] test a bunch of random special characters via ascii code and direct usage

## Compilation

-   [x] Readdress the tagging pattern
    -   use the LSB of arity to delineate
-   [x] Create and store strings on heap (return the heap_reg, ofc)
-   [x] Tuple indexing and other existing things must not accept strings
-   [ ] Tag error checks for prim ops
        -- concatenation needs to check for string tag for left and right

# Implement the functionality to demo

-   [x] Caesar cipher (input, string get at index, len, ord, chr, concat)
-   [ ] Pig Latin (input, slicing, len, concat, split)
-   [ ] Sort a list of strings (input, comparison, split)
-   [ ] reverse a string [::-1] (input, slicing)

# Dicts

-   [ ] Add parsing/lexing support
-   [ ] Desugar appropriately
-   [ ] Handle duplicate keys
-   [ ] Make interesting test cases
-   [ ] Be creative if we feel like it

# Presentation

-   [ ] Build a slide deck
-   [ ] Divide and Conquer
-   [ ] Practice a little
-   [ ] Highlight important design decisions (see DECISIONS.md)
-   [ ] Well-defined and Heavily Detailed README
        -- usage examples
        -- supported language features
        -- high-level description
        -- snake puns (maybe a snake starting with S?)

# Other Ideas

-   [ ] Support strings as input
-   [ ] Decouple tuple and string logic?
-   [ ] Support Comments (syntax: "~", "`", "--", ",", etc.)
-   [ ] f strings? (if it's just a desugaring or
        something comparably simple)
-   [ ] StringBuilders?
