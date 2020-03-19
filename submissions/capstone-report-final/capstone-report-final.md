[TOC]
# Learning Support for Writing Proofs in Coq

# Abstract

# Context 
## Introduction 
## Functional programming (FP)
## Proving
## The Coq proof assistant
## YSC3236: Functional Programming & Proving (FPP)
## GNU Emacs Editor
## Proof General

# Motivation
## Building muscle memory
## Common beginner mistakes 
### Abuse of tactics 
### Misuse of tactics 
### Not utilizing unfold lemmas

# Solution
## Providing learning support with a program checker
The program checker thus supports learning by providing three core features corresponding to the three common mistakes described:
1. Warns user of instances where unpermitted tactics are used.
2. Warns user of instances of incorrect arity in terms supplied to “rewrite” and “exact” tactics.
3. (TBC) Warns user of missing unfold lemmas when appropriate, and verifies the form of existing unfold lemmas.

## Usage
To apply the program checker to your proof script, simply execute the following Emacs command while in Proof General, with the editor focused on the buffer containing the script:
```
 M-x jeremy-parse-buffer
```

If the script is syntactically correct, then the checker will evaluate the script and display any relevant warnings, for example:   
```
WARNING: In term (add_comm n):
 Term (add_comm) with arity 2 incorrectly applied to 1 terms (n).
```
Or, if there are no warnings: 
```
No warnings.
```
## Possible errors
Note: your proof script should be *self-contained* and *syntactically correct*. 

- Self-contained: The arity checker only checks terms that are defined in the same file, and modules that have been registered (i.e. `Nat`). To avoid generating false positives (i.e. missing warnings), by design you cannot send only a selection of the script (TBC).

- Syntactically correct: To confirm this, the checker will first send the entire buffer to Proof General's coqtop for evaluation. As long as Coq accepts it, the checker will accept it.

If there are Coq syntax errors, the minibuffer will display:
```
Processing buffer...done
Coq error raised. Please correct and try again.
```
The checker will then terminate without evaluating the script. The Coq errors will be in the response buffer, as usual. 

If `Parser error: Unrecognized tokens found.` is displayed, then the checker contains unsupported syntax, or there is a bug in the checker. See "Appendix/Supported syntax" for more details. 

To extend the supported syntax or modify checker behaviour, see "Design and implementation/Extensibility".
## Examples 
## Setup 

# Design and implementation 
## Parsing input to generate a syntax tree
The code referenced in this section can be found in `jeremy-parser/parser.py` unless otherwise specified. 

In order to check the program for mistakes, we parse the input into a syntax tree that can be conveniently evaluated.

First, we preprocess the input string to remove any extraneous tabs, spaces, etc in order to simplify the matching logic later on (`preprocess` function in `jeremy-parser/parser.py`).

The tree will be composed of `Node` objects:
```python
class Node:
    def __init__(self, label, val=None, children=None):
        # We label every node by its 'type', for evaluation purposes.
        self.label = label
        # The node's actual value (e.g. the identifier of a term) is not needed for evaluation, but is used for logging and displaying warning messages.
        self.val = val
        # Each node has a list of children, or subcomponents.
        self.children = children or []
```
- `construct_node`
  - The main parser function `construct_node` returns a recursively constructed syntax tree. It assumes the input has already been matched on a syntax rule `rule`, and `s` is the remaining substring to be evaluated for the node's subcomponents. 
  - First, it constructs an appropriately labeled `Node`. 
  - It performs a lookup in the `grammar.GRAMMAR` map to obtain the expected children of `rule`.  
  - It then calls `construct_children`, and assigns the result to the current node.

- `construct_children` 
  - Attempts to match the beginning of `s` using each rule in the list `expected`. 
  - For each rule, it performs a lookup in the `grammar.GRAMMAR` map to obtain the corresponding regex pattern (see 'Design and implementation/BNF-like grammar abstraction').
  - On a match, it consumes the matched substring, recursively generating a subtree using that substring, before constructing the siblings of that subtree by recursing on  the remaining string `s[match.end():]` with the same `expected` rules.

```python
# Edited for brevity (removed logging messages).
def construct_node(s: str, rule) -> Node:
    def construct_children(s: str, expected) -> List[Node]:
        if not s:
            return []
        for item in expected:
            pattern, _ = grammar.GRAMMAR[item]
            match = re.match(pattern, s)
            if match:
                if item == LABEL_TERM:
                    child = construct_term(s)
                    return [child]
                try:
                    child = construct_node(match.group(1), item)
                    children = [child] + construct_children(
                        s[match.end():],
                        expected
                    )
                    return children
                except Exception as e:
                    if str(e) != "No match":
                        raise e
        raise Exception("No match")
    _, expected = grammar.GRAMMAR[rule]
    node = Node(rule, s)
    if expected == []:
        return node
    children = construct_children(s, expected)
    node.children = children
    return node

```


## BNF-like grammar abstraction 
The code referenced in this section can be found in `jeremy-parser/grammar.py` unless otherwise specified. 

## Arity checker
The code referenced in this section can be found in `jeremy-parser/parser.py` unless otherwise specified. 

## Test suite
The code referenced in this section can be found in `jeremy-parser/tests.py` unless otherwise specified. 

## Extensibility

# Discussion 
## Time complexity
## Alternative approaches 
### Parsing techniques
### Modifying Coqtop source code
### Using a parser generator
### Implementing a Coq plugin 
## Reflections 

# Acknowledgements
# References
# Appendix
## Supported syntax