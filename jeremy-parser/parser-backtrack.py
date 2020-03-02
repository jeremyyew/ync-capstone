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
    matches = GRAMMAR[label]
    return len(matches) == 1 and matches[0] == PATTERNS[label]


def extract_val(s, label) -> (str, str):
    # refactor this by extracting value from the regex match capture group
    if label == LABEL_PROOF:
        # remove label
        pass
    return s, s


GRAMMAR = {
    LABEL_DOCUMENT: (LABEL_PROOF, LABEL_ASSERTION, EMPTY),
    LABEL_PROOF: (PATTERN_PROOF,),
    LABEL_ASSERTION: (PATTERN_ASSERTION,)
}


def construct_node(s: str, label) -> Node:

    def construct_children(s: str, expected) -> List[Node]:
        if not s:
            return []
        LOG(f"\nWith node {label}, at:\n\"{s}\"\n")
        for e in expected:
            if e == EMPTY:
                continue
            LOG(f"Trying to match {e}...")
            match = re.match(PATTERNS[e], s)
            if match:
                LOG(f"Matched: {e} on \"{match.group(0)}\".")
                try:
                    child = construct_node(s[match.start():match.end()], e)
                    LOG(f"Constructing other children of {label}...")
                    children = [child] + construct_children(
                        s[match.end():],
                        expected
                    )
                    return children
                except Exception as e:
                    LOG(
                        f"""Failed constructing node {e} or children .
                        Backtracking from {label}...""")
                    if str(e) != "No match":
                        raise e
        raise Exception("No match")
    LOG(f"Constructing node {label}...")
    val, s = extract_val(s, label)
    if is_terminal(label):
        LOG("is terminal")
        return Node(label, val)
    expected = GRAMMAR[LABEL_DOCUMENT]
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
