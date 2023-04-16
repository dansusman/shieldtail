-   We chose not to support chars as an immediate. Instead, they are just strings of length 1. This choice impacted the following things:
    -- Character only functions (e.g. <TBD>) need an additional check for length 1 strings
    -- <TBD>

-   Strings are immutatable, following Python's conventions.
    -- concatenation makes a copy of the original strings, smashing them together
