# SHIeld-Tailed Snake - Strings beHavIng somEwhat Like Tuples, and trAnsLatIon bEtween Dem

(it's shit)

## Compiler for a Dynamically Typed, Expression Based, Garbage Collected Language, written in ML

This repository holds the source code and test files for the SHIT snake language, a final project for CS4410 at Northeastern University. Written by Jamin Eisenberg and Daniel Susman.

## Features

-   Strings and Comments
    -   See [Our String Library](./strings/) for details
-   Tuples (untyped)
-   First-class, recursive lambdas
-   I/O (`input()`, `print(val)`)
-   Cheney's semi-space garbage collection
-   x84_64 target architecture
-   Register Allocation via Graph Coloring
-   Sequencing
-   Nil values

## Example Program

```
def isPrefix(str, prefix):
    if len(prefix) > len(str): false
    else: if len(prefix) == 0: true
    else: equal(str[0], prefix[0]) && isPrefix(str[1:], prefix[1:])

def splitHelp(str, delim, acc):
    if len(str) == 0: (acc, )
    else:
        let fs = str[0], rst = str[1:] in
        if isPrefix(delim, fs):
            (acc,) ^ splitHelp(str[len(delim):], delim, "")
        else: splitHelp(rst, delim, acc ^ fs)

def split(str, delim):
    if len(str) == 0: (str,)
    else: splitHelp(str, delim, "")
    def pigLatinHelp(s):
        if len(s) == 0: ""
        else: s[0][1:] ^ s[0][0] ^ "ay " ^ pigLatinHelp(s[1:])

def pigLatin(s):
    if len(s) == 0: s
    else:
        let words = split(s, " ") in
        pigLatinHelp(words)

pigLatin("pig latin is the best way to communicate");
```

## Usage

To build our project and run unit/integration tests,

```bash
    $ make test && ./test
```

To run a specific test file,

```bash
    $ make test
    $ ./output/do_pass/<file_name>.run
```

To view intermediate representations and state of the world through the various compilation phases,

```bash
    $ ./main -t input/do_pass/<file_name>.shit
```

## Compiler Design Decisions

For string specific design decisions, please read [DECISIONS.md](./strings/DECISIONS.md).

### Disclaimer

This language is experimental/educational. We don't recommend you use it in production.
