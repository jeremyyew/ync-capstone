from terminals import *
import re
import utils
from typing import List, Dict
import logging
import sys
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

    LABEL_EXACT: (r"exact (\(.+\)).",  # We disambiguate the module separator period from sentence period by matching on parenthesis, it is required. This is a bug for Check, since Coq will accept Check <term> without parenthesis.
                  [LABEL_TERM_WITH_ARGS]),
    LABEL_TERM: (r"([^\s]+)\s?",
                 [LABEL_TERM_WITH_ARGS,
                  LABEL_IDENT]),
    LABEL_TERM_WITH_ARGS: (r"\((.+)\)\s?",
                           [LABEL_TERM_WITH_ARGS, LABEL_TERM]),
    LABEL_IDENT: (r"\(?(.+)\)?",
                  [])
}

# Will need a constructor for non-collection nodes, e.g. tactics are made of fixed number of lements.


# def validate_terms() -> bool:


def construct_node(s: str, rule) -> Node:
    def construct_children(s: str, expected) -> List[Node]:
        if not s:
            return []
        LOG(f"\n\nWith node {rule}, at:\n\"{s}\"\n")
        LOG("Attemping matches, expecting: [" + ", ".join(expected) + "]")
        for item in expected:
            pattern, _ = GRAMMAR[item]
            # if item in (LABEL_INTRO, LABEL_EXACT):
            #     for match in re.finditer("\.", s):
            #         match.start()
            match = re.match(pattern, s)
            if match:
                LOG(f"Matched: {item} on \"{match.group(0)}\".")
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

coq_test_period = """
Lemma A.
Proof.
intro n1.
intro n2.
intro n3.
exact (Nat.lemma1 (Nat.lemma2 (Nat.lemma3 arg3_1) arg2_2) arg1_3).
Qed.
Lemma B.
"""
s = preprocess(coq_test_period)
root = construct_node(s, LABEL_DOCUMENT)
utils.pretty(root)

# print(re.match(r"exact \((.+?)\)\.", "exact (Nat.add_comm 0 n).").group(1))
# ms = re.finditer(r"\.", "12.34.5678.")
# for m in ms:
#     print(m.start(0))
