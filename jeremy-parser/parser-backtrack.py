from terminals import *
import re
import utils
from typing import List, Dict
import logging
import sys
sys.setrecursionlimit(20)

LOG = logging.debug


class Node:
    def __init__(self, label, val=None, children=None):
        self.label = label
        self.val = val
        self.children = children or []


def preprocess(s: str) -> str:
    # Remove tab, FF, CR, LF.
    s = re.sub("\t|\f|\r|\n", "", s)
    return s


def is_terminal(label):
    _, items = GRAMMAR[label]
    return items == ()


def extract_val(s, pattern) -> (str, str):
    # refactor this by extracting value from the regex match capture group
    return s, s


PATTERN_PROOF = r"Proof\..+?Qed\."
PATTERN_ASSERTION = r"Lemma [^\.]+?\."

EMPTY = "EMPTY"

GRAMMAR = {
    # RULE: PATTERN, (ITEM...ITEM)
    # PATTERN == None: no pattern to apply.
    # ITEMS == (): rule is terminal.
    LABEL_DOCUMENT: (None, (LABEL_PROOF, LABEL_ASSERTION)),
    LABEL_PROOF: (PATTERN_PROOF, ()),
    LABEL_ASSERTION: (PATTERN_ASSERTION, ())
}

# Will need a constructor for non-collection nodes, e.g. tactics are made of fixed number of lements.


def construct_node(s: str, label) -> Node:
    def construct_children(s: str, expected) -> List[Node]:
        if not s:
            return []
        LOG(f"\nWith node {label}, at:\n\"{s}\"\n")
        for item in expected:
            pattern, _ = GRAMMAR[item]
            LOG(f"Trying to match {item}...")
            match = re.match(pattern, s)
            if match:
                LOG(f"Matched: {item} on \"{match.group(0)}\".")
                try:
                    child = construct_node(s[match.start():match.end()], item)
                    LOG(f"Constructing other children of {label}...")
                    children = [child] + construct_children(
                        s[match.end():],
                        expected
                    )
                    return children
                except Exception as e:
                    LOG(
                        f"""Failed constructing node {item} or children .
                        Backtracking from {label}...""")
                    if str(e) != "No match":
                        raise e
        raise Exception("No match")
    LOG(f"Constructing node {label}...")
    pattern, expected = GRAMMAR[label]
    val, s = extract_val(s, pattern)
    if is_terminal(label):
        LOG("is terminal")
        return Node(label, val)
    children = construct_children(s, expected)
    node = Node(label, val)
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

coq_test_period = """
Lemma A.
Proof.
intro n2.
rewrite -> (Nat.add_comm n 0).
intro n3.
Qed.
"""
s = preprocess(coq_test_period)
root = construct_node(s, LABEL_DOCUMENT)
utils.pretty(root)
