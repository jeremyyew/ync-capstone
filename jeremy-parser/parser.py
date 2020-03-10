from terminals import *
import re
from typing import List, Dict
import logging
import sys
sys.setrecursionlimit(1000)

LOG = logging.debug
logging.basicConfig(filename='parser.log', level=logging.DEBUG)

# TODO:
# 1. Define assertion and collect arity signatures.
# 2. Only collect for those that have been proven.
# 2. Define  rewrite.
# 3. Define intros, check, compute, induction, assert, destruct, reflexivity, unfold, apply.
# 3. Emacs command to call program.
# 4. Send back warning messages and display them.
# 5. Line number would be nice.
# 6. Fold-unfold lemmas?


class Node:
    def __init__(self, label, val=None, children=None):
        self.label = label
        self.val = val
        self.children = children or []


def preprocess(s: str) -> str:
    # Remove tab, FF, CR, LF.
    s = re.sub(r"\t|\f|\r|\n", "", s)
    s = re.sub(r"\.\s+", ".", s)
    return s

# RULE: PATTERN, [RULE...RULE]
# PATTERN: A regexp pattern applied to the current string to check if it can return a match for this rule.
# List of RULE: Try matching each child rule (in order) on the contents of the current pattern's captured group. If empty, rule is a terminal and there are no children.


# binder       ::=  name
#               ( name … name : term )
#               ( name [: term] := term )
#               ' pattern
GRAMMAR = {
    LABEL_DOCUMENT:
        (None,
         [LABEL_PROOF,
          LABEL_ASSERTION]),

        LABEL_PROOF:
            (r"Proof\.(.*?)Qed\.",
             [LABEL_INTRO,
              LABEL_EXACT]),

            LABEL_INTRO:
                (r"intro (.+?)\.",
                 []),

            LABEL_EXACT:
                (r"exact (\(.+?\))\.",  # We disambiguate the module separator period from sentence period by matching on parenthesis, it is required. This is a bug for Check, since Coq will accept Check <term> without parenthesis.
                 [LABEL_TERM]),

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
                 [])
}


def get_next_subterm(s: str) -> str:
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


def construct_term(term: str) -> Node:
    def construct_subterms(s: str) -> List[Node]:
        if s == "":
            return []
        subterm, remaining = get_next_subterm(s)
        child = construct_term(subterm)
        LOG(f"Constructing other children of {s} with \"{remaining}\"...")
        children = [child] + construct_subterms(remaining)
        return children
    LOG(f"Constructing node TERM:{term}...")
    if term and term[0] == "(" and term[-1] == ")":
        term = term[1:-1]
    node = Node(LABEL_TERM, term)
    if re.fullmatch(r"[^\s]+", term):
        LOG("TERMINAL")
        return node
    node.children = construct_subterms(term)
    return node


def construct_node(s: str, rule) -> Node:
    def construct_children(s: str, expected) -> List[Node]:
        if not s:
            return []
        LOG(f"\n\nWith node {rule}, at:\n\"{s}\"\n")
        LOG("Attemping matches, expecting: [" + ", ".join(expected) + "]")
        for item in expected:
            pattern, _ = GRAMMAR[item]
            match = re.match(pattern, s)
            if match:
                LOG(f"Matched: {item} on \"{match.group(0)}\".")
                if item == LABEL_TERM:
                    child = construct_term(s)
                    return [child]
                try:
                    pattern, _ = GRAMMAR[item]
                    child = construct_node(match.group(1), item)
                    LOG(
                        f"Constructing other children of {rule} on \"{s[match.end():]}\"...")
                    children = [child] + construct_children(
                        s[match.end():],
                        expected
                    )
                    return children
                except Exception as e:
                    if str(e) != "No match":
                        raise e
                    LOG(
                        f"""Failed constructing node {item} or children.
                        Backtracking from {rule}...""")
        raise Exception("No match")
    LOG(f"Constructing node {rule}...")
    _, expected = GRAMMAR[rule]
    node = Node(rule, s)
    if expected == []:
        return node
    children = construct_children(s, expected)
    node.children = children
    return node


errors = {}


def log_warning(parent, first_term, arity_expected, arity, arg_strings):
    LOG(
        f"WARNING: In term ({parent}):\n Term ({first_term}) with arity {arity_expected} incorrectly applied to {arity} terms {arg_strings}.\n")


def log_correct(parent, first_term, arity_expected, arity, arg_strings):
    LOG(
        f"In term ({parent}):\n Term ({first_term}) with arity {arity_expected} correctly applied to {arity} terms {arg_strings}.\n")


def check_arity(t, arity_db, parent=None):
    warnings = []

    def check_arity_helper(t, arity_db, parent=None):
        def check_arity_terms(terms, parent):
            if terms == []:
                return
            first_term = terms[0].val
            if first_term not in arity_db:
                return
            arity_expected = arity_db[first_term]
            arity = len(terms) - 1
            args = [term.val for term in terms[1:]]
            arg_strings = ",".join([f"({arg})" for arg in args])
            if arity == arity_expected:
                pass
                # log_correct(parent, first_term,
                #             arity_expected, arity, arg_strings)
            else:
                warnings.append((parent, first_term,
                                 arity_expected, arity, arg_strings))
                log_warning(parent, first_term,
                            arity_expected, arity, arg_strings)
            for term in terms[1:]:
                check_arity_helper(term, arity_db, parent)
        if t.label == LABEL_TERM:
            # Refactor to only check at first level.
            check_arity_terms([t], parent or t.val)
            check_arity_terms(t.children, t.val)
        else:
            for child in t.children:
                check_arity_helper(child, arity_db, parent)
    check_arity_helper(t, arity_db, parent)
    return warnings
