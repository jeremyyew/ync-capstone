from terminals import *
import re
import utils
from typing import List, Dict
import logging
import sys
import arity_db
sys.setrecursionlimit(1000)

LOG = logging.debug
logging.basicConfig(filename='parser-backtrack.log', level=logging.DEBUG)


class Node:
    def __init__(self, label, val=None, children=None):
        self.label = label
        self.val = val
        self.children = children or []


def preprocess(s: str) -> str:
    # Remove tab, FF, CR, LF.
    s = re.sub("\t|\f|\r|\n", "", s)
    return s


GRAMMAR = {
    # RULE: PATTERN, [RULE...RULE]
    # PATTERN: A regexp pattern applied to the current string to check if it can return a match for this rule.
    # List of RULE: Try matching each child rule (in order) on the contents of the current pattern's captured group. If empty, rule is a terminal and there are no children.
    LABEL_DOCUMENT: (None,
                     [LABEL_PROOF, LABEL_ASSERTION]),

    LABEL_PROOF: (r"Proof\.(.+?)Qed\.",
                  [LABEL_INTRO, LABEL_EXACT]),

    LABEL_ASSERTION: (r"(Lemma .+?)\.",
                      []),

    LABEL_INTRO: (r"intro (.+?)\.",
                  []),

    LABEL_EXACT: (r"exact (\(.+?\))\.",  # We disambiguate the module separator period from sentence period by matching on parenthesis, it is required. This is a bug for Check, since Coq will accept Check <term> without parenthesis.
                  [LABEL_TERM]),
    LABEL_TERM: (r"(.+)", []),
}

# Will need a constructor for non-collection nodes, e.g. tactics are made of fixed number of lements.

# (lemma_b_2 (lemma_a_1 a1) (lemma_b_2 b1 b2))
# lemma_b_2 (lemma_a_1 a1) (lemma_b_2 b1 b2)


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
    # try again but search for next period with substring starting index i + 1
    # create node, make recursive call.


coq_test = """Lemma truism:
    forall P: nat -> Prop,
    (exists n: nat,
    P n) ->
    exists n: nat,
    P n.
Proof.
intros P H_P.
Qed.
Restart.
intros P[n H_Pn].
"""

coq_test1 = """
Lemma A.
Proof.
intro n1.
intro n2.
intro n3.
exact (lemma_a_1).
exact (lemma_a_1 a1 a2).
exact (lemma_b_2).
exact (lemma_b_2 b1).
exact (lemma_b_2 b1 b2 b3).
exact (lemma_b_2 (lemma_a_1)).
exact (lemma_b_2 b1 (lemma_a_1)).

exact (lemma_a_1 a1).
exact (lemma_b_2 b1 b2).
exact (lemma_b_2 (lemma_a_1 a1) (lemma_b_2 b1 b2)).
Qed.
Lemma B.
"""

coq_test2 = """
Lemma A.
Proof.
exact (lemma_b_2 (lemma_a_1 a1) (lemma_b_2 b1 b2)).
Qed.
"""
s = preprocess(coq_test2)
root = construct_node(s, LABEL_DOCUMENT)
utils.pretty(root)

ARITY = {
    "lemma_a_1": 1,
    "lemma_b_2": 2,
}


def check_arity(t) -> bool:
    if t.label == LABEL_TERM and t.children:
        first_term = t.children[0].val
        arity_expected = ARITY[first_term]
        arity = len(t.children) - 1
        arg_strings = ",".join([f"({c.val})" for c in t.children[1:]])
        if arity == arity_expected:
            print(
                f"Term ({first_term}) with arity {arity_expected} correctly applied to {arity} terms {arg_strings}.")
        else:
            print(
                f"WARNING: Term ({first_term}) with arity {arity_expected} incorrectly applied to {arity} terms {arg_strings}.")
    for child in t.children:
        check_arity(child)


check_arity(root)
