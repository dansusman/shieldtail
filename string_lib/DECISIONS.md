# String Library Design Decisions

-   Characters are simply strings of length 1. This matches Python's behavior, and simplifies the design of our language. This choice impacts us in the following ways:

    -   `ord` must check for strings of length 1, since we expect a single character here (runtime error if things go wrong)
    -   Strings, tuples, and 1-strings play very nicely with one another

-   Strings are ANF'd into CExprs because, while they don't contain <expr> parts, they require further computation to be ready; namely, create the string, place it on the heap, return the heap pointer.

    -   it feels a bit odd because strings are constants, but they're definitely more complex than our other immediates, and we definitely want them to be lettable

-   Strings are immutatable, following Python's conventions.

    -   concatenation makes a copy of the original strings, smashing them together
    -   slicing returns a copy of the original

-   Strings are represented as heap sequences (like tuples), where the first word is the length in characters + 1

    -   this gives us a tagging convention unique to strings (the ones bit of "arity" is 1 if it's a string, 0 if it's a tuple)
    -   tuples and strings can interact with each other in a bunch of nice ways
        -   e.g. conversion between tuples and strings, slicing for tuples and strings, concat strings, concat tuples, etc.
        -   lots of our string changes in this project apply to tuples as well
    -   we introduced new runtime errors to ensure we are operating on strings when we want strings and tuples when we want tuples
    -   GC, printing, and equality for tuples and strings required only minor changes to existing code

-   We support string at index access with the syntax "hello"[1] -> "e" because we're treating strings and tuples similarly in many ways, and we thought it'd be grating to have an alternative syntax for getting the character at a given index

-   We don't support a syntax like "hello"[1] := "q" because strings are immutable.
-   [Our library](./) is broken into multiple files because otherwise there is a Stack Overflow error in the OCaml runner. We discovered the stack can't handle all of our string functions and examples being in one file, so we broke the library up into logically alike and/or mutually dependent pieces.

[Go back](../README.md)
