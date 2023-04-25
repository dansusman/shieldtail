# Shield-Tailed Snake

(Strings Tuples)

## Overview

-   Features we implemented
    -   ASCII set support
    -   Including escape characters: \n, \r, \t, \b, \", \\, \{arbitrary ASCII code}
    -   Characters are strings of length 1
    -   String compression (one byte per char)
    -   Representation of strings on the heap
    -   Tuple-string correlation
    -   GC for strings
    -   String (and mostly also tuple) functions
        -   In C runtime
            -   concatenation
            -   equals
            -   numToString
            -   slicing (with fancy python syntax)
            -   fromString
            -   input for strings (only)
            -   chr, ord (conversion between 1-strings and numbers)
            -   len
        -   In our language:
            -   comparison
            -   toString (of any type)
            -   split
            -   toLowercase, toUppercase, isLowercase, isUppercase, isAlpha, isNumeric, isAlphanumeric
            -   equalsIgnoreCase
            -   conversion between tuples and strings
            -   indexOf
            -   contains
            -   isPrefix
            -   sort
    -   not dicts

## Walkthrough

-   sequence.h/c
-   GC (small change)
-   input, print
-   Go through each compiler phase
    -   Lexing
    -   Parsing
    -   Well-formedness
    -   Desugaring (trivial)
    -   Add native lambdas (trivial)
    -   Rename (trivial)
    -   ANF'ing (trivial)
    -   Free vars (trivial)
    -   Stack/reg allocation (trivial)
    -   Compilation
