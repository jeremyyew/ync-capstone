[TOC]
# Learning Support for Writing Proofs in Coq

# Abstract

# Context 
## Introduction 
## Functional programming (FP)
## Proving
## The Coq proof assistant
## YSC3236: Functional Programming & Proving (FPP)
## The GNU Emacs text editor
## Proof General

# Motivation
## Building muscle memory
## Common beginner mistakes 
### Abuse of tactics 
### Misuse of tactics 
### Not utilizing unfold lemmas

# Solution
## `proofreader`: providing learning support by parsing student submissions
I implement a parser which provides learning support by checking student submissions. It has three core features corresponding to the three common mistakes described:
1. (TBC) Warns user of instances where unpermitted tactics are used.
2. Warns user of instances of incorrect arity in terms supplied to “rewrite” and “exact” tactics.
3. (TBC) Warns user of missing unfold lemmas when appropriate, and verifies the form of existing unfold lemmas.

## Usage
To apply the parser to your proof script, simply execute the following Emacs command while in Proof General, with the editor focused on the buffer containing the script:
```
 M-x jeremy-parse-buffer
```

If the script is syntactically correct, then the parser will evaluate the script and display any relevant warnings, for example:   
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

- Self-contained: The parser only checks the arity of terms that have been defined in the input file, as well as modules that have been pre-registered (i.e. `Nat`). To avoid generating false positives (i.e. missing warnings), by design you cannot send only a selection of the script (TBC).

- Syntactically correct: To confirm this, the parser will first send the entire buffer to Proof General's coqtop for evaluation. As long as Coq accepts it, the parser will accept it.

If there are Coq syntax errors, the minibuffer will display:
```
Processing buffer...done
Coq error raised. Please correct and try again.
```
The parser will then terminate without evaluating the script. The Coq errors will be in the response buffer, as usual. 

If `Parser error: Unrecognized tokens found.` is displayed, then the script contains unsupported syntax, or there is a bug in the parser. See "Appendix/Supported syntax" for more details. 

To extend the supported syntax or modify the parser behaviour, see "Design and implementation/Extensibility".
## Examples 
## Setup 

# Design and implementation 
## Parsing input to generate a syntax tree
The code referenced in this section can be found in `jeremy-parser/parser.py` unless otherwise specified. 

In order to check the program, we parse the input string into a syntax tree that can be conveniently evaluated.

### Constructing syntax tree nodes
First, we preprocess the input string to remove any extraneous tabs, spaces, etc in order to simplify the matching logic later on (`preprocess` function in `jeremy-parser/parser.py`).

We define a `Node` object:
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

The recursive function `construct_node` and its helper `construct_children` then consumes the input string by matching regex patterns on the beginning of input substring, while recursively constructing a syntax tree composed of `Node` objects.

- `construct_node`
  - The main parser function `construct_node` returns a syntax tree. It assumes the input has already been matched on a syntax rule `rule`, and `s` is the remaining substring to be evaluated for the node's subcomponents. 
  - First, it constructs an appropriately labeled `Node`. 
  - It performs a lookup in the `grammar.GRAMMAR` map to obtain the expected children of `rule`.  
  - It then calls `construct_children`, and assigns the result to the current node.

  - `construct_children` 
    - Attempts to match the beginning of `s` using each rule in the list `expected`. 
    - For each rule, it performs a lookup in the `grammar.GRAMMAR` map to obtain the corresponding regex pattern (see 'Design and implementation/BNF-like grammar abstraction').
    - On a match, it consumes the matched substring, recursively generating a subtree using that substring, before constructing the siblings of that subtree by recursing on  the remaining string `s[match.end():]` with the same `expected` rules.

```python
# Edited for brevity
def construct_node(s: str, rule) -> Node:
    def construct_children(s: str, expected) -> List[Node]:
        if not s:
            return []
        for item in expected:
            pattern, _ = grammar.GRAMMAR[item]
            match = re.match(pattern, s)
            if match:
                # if item == LABEL_TERM:
                #     child = construct_term(s) 
                #     return [child]
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

### Constructing terms and subterms
The above functions are generic enough to construct most syntactical units in our sublanguage. However, in order to validate the arity of terms supplied to the `rewrite` and `exact` tactics, we need to parse a term into its subterms, which are grouped in nested parenthesis. Regular expressions are not expressive enough to capture nested patterns. Here is an example substring: 
```
exact (my_lemma_1 (my_lemma_2 n1) n2).
exact (my_lemma_3 n3).
``` 
Suppose we have constructed the first `exact` node, and now we need to capture the parent term `(my_lemma_1 (my_lemma_2 n1) n2)`, before trying to capture its children `my_lemma_1`, `(my_lemma_2 n1)` and `n2`.
- A lazy match on opening and closing parenthesis, such as `\(.?\)`, would capture:
  -  `(my_lemma_1 (my_lemma_2 n1)`. 
- On the other hand, a greedy match like `\(.+\)` would capture everything until the last parenthesis in the substring:
  - `(my_lemma_1 (my_lemma_2 n1) n2).exact (my_lemma_3 n3).`

Even if we use some strategy to exclude literals to avoid greedy matches across separate tactics, consider this example: 
```
exact (my_lemma_1 (my_lemma_2 n1) (my_lemma_3 n2)).
```
Suppose we have captured the entire parent term as well as the first subterm `my_lemma_1`, and now we need to capture the second subterm `(my_lemma_2 n1)`, from the substring `(my_lemma_2 n1) (my_lemma_3 n2)`. However, a greedy match would give us the entire substring
- `(my_lemma_2 n1) (my_lemma_3 n2)`

Hence the generic `construct_node` cannot construct this subtree. Thankfully, this is a familiar problem of counting parenthesis, implemented iterative-style here: 
```python
def get_next_subterm(s) -> str:
    k = 0
    term = ""
    remaining = ""
    for i, c in enumerate(s):
        if c == " " and k == 0:
            remaining = s[i+1:]
            break
        elif c == '(':
            k += 1
        elif c == ')':
            k -= 1
        term += c
    if k != 0:
        raise Exception("Invalid parentheses.")
    return term, remaining
```
Then we just need a specialized `construct_term` function, which mirrors `construct_node` except for two key differences:
  - the helper function `construct_subterms` simply looks for the next subterm instead of matching iteratively on a list of expected rules
  - we terminate a recursion when the current term has no subterms (there are no spaces, so it is a single term), instead of iterating over a terminal node's empty list of expected tokens. 
  
```python
def construct_term(term: str) -> Node:
    def construct_subterms(s: str) -> List[Node]:
        if s == "":
            return []
        subterm, remaining = get_next_subterm(s)
        child = construct_term(subterm)
        children = [child] + construct_subterms(remaining)
        return children
    if term and term[0] == "(" and term[-1] == ")":
        term = term[1:-1]
    node = Node(LABEL_TERM, term)
    if re.fullmatch(r"[^\s]+", term):
        return node
    node.children = construct_subterms(term)
    return node
```
And now we only need to delegate the construction of term subtrees to `construct_term` by uncommenting the following lines in `construct_node`:
```
for item in expected:
    pattern, _ = grammar.GRAMMAR[item]
    match = re.match(pattern, s)
    if match:
        # if item == LABEL_TERM:
        #     child = construct_term(s) 
        #     return [child]
```
(Note: Consider refactoring so that `construct_node` implements `construct_term`, since `get_next_term` has the same output as a regexp.)

## A note on BNF grammar notation

## BNF-like grammar module
The code referenced in this section can be found in `jeremy-parser/grammar.py` unless otherwise specified. 

The `grammar` module provides the `GRAMMAR` variable, which is a map of grammar rules intended to emulate the logic of a BNF grammar notation. 

Each key-value pair maps a grammar rule name to a tuple containing a regexp patterns and the children it should (or could) contain:
- `RULE: (PATTERN, [RULE...RULE])`
  - `PATTERN`: A regexp pattern that the parser will try to match the beginning of the current string with. If successful, then the current string contains this syntactical construct, provided the parser can recursively consume the substring contained in the capture group using the children's rules.
  - `[RULE...RULE]`: A list of child rules that the parser will attempt to recursively match, in order, on the captured substring. If empty, this rule is a terminal/leaf node, i.e. a rule that is not defined in terms of other rules. 

Here is a truncated version of the actual `GRAMMAR` map. Note the indentation does not correspond to actual nesting of data, but is intended to visual reflect the nested definitions.

```python
GRAMMAR = {
    LABEL_DOCUMENT:
        (None,
         [LABEL_REQUIRE_IMPORT,
          LABEL_PROOF,
          LABEL_ASSERTION,
          ...]),

        LABEL_REQUIRE_IMPORT:
            (r"Require Import (.+?)\.",
             []),

        LABEL_PROOF:
            (r"Proof\.(.*?)(?:Qed|Admitted|Abort)\.",
             [LABEL_INTRO,
              LABEL_REWRITE,
              ...]),

            LABEL_INTRO:
                (r"intro\s?(.*?){}".format(REGEXP_TACTIC_END),
                 []),

            LABEL_REWRITE:
                (r"{}\s?((?:->|<-)?\s?\(?.+?\)?){}(?={}|$)".format(KW_REWRITE,
                                                                   REGEXP_TACTIC_END,
                                                                   TACTIC_KEYWORDS),
                 [LABEL_REWRITE_ARROW, LABEL_TERM]),

                LABEL_REWRITE_ARROW:
                    (r"(->|<-)\s?",
                     []),
                LABEL_TERM:
                    (r"(.+)",
                        []),

        LABEL_ASSERTION:
            ("(" + ASSERTION_KEYWORDS + r" .+?)\.",
             [LABEL_ASSERTION_KEYWORD,
              LABEL_ASSERTION_IDENT,
              LABEL_FORALL,
              LABEL_ASSERTION_TERM]),

            LABEL_ASSERTION_KEYWORD:
                ("(" + ASSERTION_KEYWORDS + ")",
                 []),

            LABEL_ASSERTION_IDENT:
                (r"\s*([^\s]+?)\s*:\s*",
                 []),

            LABEL_FORALL:
                (r"forall \(?(.+?)\)?,\s*",
                 [LABEL_BINDER, LABEL_TYPE]),

                LABEL_BINDER:
                    (r"([^:\s]+)\s*",
                     []),

                LABEL_TYPE:
                    (r":\s*(.+)",
                     []),

            LABEL_ASSERTION_TERM:
                (r"(.+)",
                 []),

    LABEL_COMMENT:
        # Note: Will not parse nested comments properly!
        (r"\s?(\(\*.+?\*\))\s?",
         #  r"(?:\s?\(\*.+?\*\)\s?)"
         [])
    ...
}
```

To explain an example in detail: 
```
LABEL_PROOF:
    (r"Proof\.(.*?)(?:Qed|Admitted|Abort)\.",
        [LABEL_INTRO,
        LABEL_REWRITE,
        ...]),
```

Here, the `LABEL_PROOF` rule states that *"a proof is a lazily matched substring beginning with the keyword 'Proof' plus a period, and ends with either 'Qed', 'Admitted', or 'Abort', plus a period. Furthermore, the inner string (in parenthesis) must consist of any number of child components matching the rules `intro`, `rewrite`, etc"*.  

Observe: 
- Rules are identified by constants, which are given by `LABEL`-prefixed names.
- `LABEL_DOCUMENT` is the root node, so it has no prerequisite matching pattern. Thus the first value is `None`.
- For readability and code reuse, we inject constants into a regexp via the string method `format` (string interpolation/templating would be even more readable, but cannot be used together with Python's `r` regexp syntax highlighting.)

The `grammar` module is an abstraction over the branching logic that the constructor function follows as it recursively constructs the syntax tree, allowing new rules to be defined simply by adding a key-value pair, without modifying the constructor function. Without the abstraction, we would have one logical branch (with repeated branches for multiple references) for each rule, or one function definition for each rule, which would create significant code duplication.

Having generated a syntax tree, we are now in a position to traverse it in order to provide our above-mentioned features. 

## Feature 1: (TBC) Recognizing unpermitted tactics

## Feature 2: Checking arity
The code referenced in this section can be found in `jeremy-parser/parser.py` unless otherwise specified. 

We now have a syntax tree which we can traverse to find errors. 

(To be refactored into two functions. Arity check should return only warning data to be formatted separately).

```python

def check_arity(t, arity_db):
    warnings = []
    warnings_output = []

    def check_subterms(subterms, parent_term):
        if not subterms:
            return
        first_term = subterms[0]
        if first_term.val in arity_db:
            arity_expected = arity_db[first_term.val]
            arity = len(subterms) - 1
            args = [term.val for term in subterms[1:]]
            arg_strings = ",".join([f"({arg})" for arg in args])
            if arity != arity_expected:
                warning_str = utils.warning_format(
                    parent_term.val, first_term.val,
                    arity_expected, arity, arg_strings)
                warnings_output.append(warning_str)
                logger.info(warning_str)

        if not first_term.children and first_term.val not in arity_db:
            logger.info(
                f"In {parent_term.val},direct term {first_term.val} not seen or registered.")

        assert((not first_term.children or len(subterms) == 1))

        check_subterms(first_term.children, parent_term)
        for subterm in subterms[1:]:
            if not subterm.children:
                check_subterms([subterm], parent_term)
            else:
                check_subterms(subterm.children, parent_term)

    def collect_arity(assertion):
        ident = assertion.children[1]
        forall = assertion.children[2]
        binders = [c for c in forall.children if c.label == LABEL_BINDER]
        arity = len(binders)
        arity_db[ident.val] = arity
        logger.info(f"New term {ident.val} arity added in db: {arity_db}.")

    def traverse(t):
        logger.info(f"TRAVERSING {t.label}")
        if t.label in [LABEL_DOCUMENT, LABEL_PROOF]:
            for child in t.children:
                traverse(child)
        elif t.label in [LABEL_EXACT, LABEL_REWRITE]:
            if t.children[0].label == LABEL_REWRITE_ARROW:
                t.children = t.children[1:]
            check_subterms(t.children, t.children[0])
        elif t.label == LABEL_ASSERTION:
            collect_arity(t)
    traverse(t)
    return warnings, "\n".join(warnings_output)
```
Since the tree traversal is left-to-right, and assertions must be declared before they are referenced, we could collect arity signatures and check arity at the same time, in a single traversal instead of two traversals. This was the approach in an earlier implementation. However, I decided that two separate functions makes for more readable and maintanable code, with no change to big-O time complexity, and a negligible cost in actual performance. 
## (TBC) Feature 3: Identify missing unfold lemmas, and verify existing ones

## Extending the parser
## Unit tests
The code referenced in this section can be found in `jeremy-parser/tests.py` unless otherwise specified. 
## Acceptance tests

# Discussion 
## Time complexity
### Regular expression matching in `construct_node`
Regular expressions can be computationally expensive - for example, they might grow exponentially in complexity when catastrophic backtracking occurs. However:
- All the regex patterns in the `grammar` module use lazy quantifiers, thus avoiding backtracking. 
- Almost all matches are performed on Coq sentences or fragments of sentences, which are very short substrings. 
- Since we only accept input that is syntactically validated by `coqtop`, the input is predictable.  
- We try to arrange expected rules in order of frequency of occurence, so we reach a match sooner rather than later, similar to regex alternation optimization. This reduces the number of match attempts on each substring, which would be a constant factor anyway. 

Therefore we can reasonably assume total `O(N)` time (where `N` is the length of the input string) and `O(1)` space complexity for regex matching.

Note that counting parentheses in `get_next_subterm` incurs `O(N)` time complexity as well. 

### Traversing the syntax tree in `check_arity`
Since the syntax tree consists almost entirely of subtrees that need to be evaluated, the depth-first traversal incurs a `O(N)` time complexity, where `N` is the number of nodes, which is a constant fraction of the length of the input string. Since the iterative-style collection of warnings does not incur call-stack memory, the space complexity is `O(1)`. 

### String slicing
In Python, strings are immutable, hence all instances of string slicing (e.g. `s[match.end():]` in `construct_node` and `s[i+1:]` in `construct_term`) will create a new copy of the string, which involves `O(N)` time complexity, where `N` is the length of the sliced substring. 

This is sometimes a concern for processing long strings. In this case, the expected depth of `TERM` subtrees for actual student submissions is 2-4 levels (highly nested terms would be highly unreadable, and also quite difficult to construct deliberately in simple proofs), so we would only copy the entire substring a few times. Thus, we can assume a worst-case constant multiple of substring length, i.e. `O(kN)`.

Furthermore, string slicing is only used on term substrings, which are expected to be short. 

## Performance 
- Run on long proof.
## Limitations of the `grammar` module
- Does not express specific subcomponents of a unit, since the parser function expects to process only one captured substring. 
  - Instead, we always expect the captured substring to potentially contain any quantity of any type of child rule in any sequence.
    - In other words, we assume 0...n quantity for each possible child rule; we can't express specific `k`-quantity of any particular child syntactical unit. 
    - Furthermore, a captured substring can contain any sequence of all included child syntactical unit, i.e. we cannot express homogenous lists of only one type (or a subgroup) of children. 
  - It doesn't matter, though. 
  - If we needed to express this, we could simply have the parser function expect $n$ number of capture groups, and then each rule list could be a list of lists of rules, with each group of expected children corresponding to each capture group, in order.
- Does not express alternate patterns for one rule. A single regex pattern defines the acceptable structure for each rule.
  - Under the current system, if needed, we would construct a distinct rule for each alternate pattern and associated group of expected children, even though logically they may be the same syntactical unit.
  - It doesn't matter, though.
  - If we needed to express this, we could define a rule as a list of pattern/rule list pairs, with each pair representing an additional matching option. 
## Alternative approaches 
### Parsing techniques
- bottom up vs top down
### Modifying Coqtop source code
- install another version of coqtop 
- huge codebase
### Using a parser generator
- 
### Implementing a Coq plugin 
## Reflections 

# Acknowledgements
# References
# Appendix
## Supported syntax
# Questions for Prof Danvy
- If my regex does not contain greedy quantifiers, does that mean the regex engine in theory never backtracks?
- My parser allows for backtracking, but so far I have not encountered any backtracking scenarios.
  - Do you think there would be any cases where backtracking is ever needed? 
  - If not, is the correct term 'unambiguous` or is there another term for languages that do not require backtracking? 