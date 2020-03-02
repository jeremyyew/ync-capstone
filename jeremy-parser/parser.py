import re
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

# https://vallentin.dev/2016/11/29/pretty-print-tree
LABEL_DOCUMENT = "DOCUMENT"
LABEL_PROOF = "PROOF"
LABEL_SENTENCE = "SENTENCE"
LABEL_KW_PROOF = "PROOF_KEYWORD"
LABEL_KW_QED = "QED_KEYWORD"

KW_PROOF = "Proof"
KW_QED = "Qed"


def pretty(node, _prefix="", _last=True):
    print(_prefix,  "|- " if _last else "|- ", node.label,
          ":", (f"\n   {_prefix}\"{node.val}\"" if node.val else ""), "\n", sep="")
    _prefix += "      "
    child_count = len(node.children)
    for i, child in enumerate(node.children):
        _last = i == (child_count - 1)
        pretty(child, _prefix, _last)


def lexer(s):
    # Remove tab, FF, CR, LF.
    s = re.sub("\t|\f|\r|\n", "", s)
    # Split by period to get sentences. Need to disambiguate from module separator.
    sentences = s.split(".")[:-1]
    # Strip whitespace from each sentence, and split each sentence by whitespace to get tokens in each sentence.
    # tokenized = [t.strip().split() for t in sentences]
    tokenized = [t.strip() for t in sentences]
    return tokenized


class Node:
    def __init__(self, label, val=None, children=None):
        self.label = label
        self.val = val
        self.children = children or []


def construct_tree(tokens) -> Node:
    t = Node(LABEL_DOCUMENT)
    while tokens:
        if tokens[0] == KW_PROOF:
            proof_node, tokens = construct_proof_node(tokens)
            t.children.append(proof_node)
        else:
            # pretty_labels(t)
            t.children.append(Node(LABEL_SENTENCE, tokens[0]))
            tokens = tokens[1:]
    return t


def construct_proof_node(tokens) -> (Node, list):
    # print("\nconstructing proof node\n")
    t = Node(LABEL_PROOF, children=[Node(LABEL_KW_PROOF, tokens[0])])
    tokens = tokens[1:]
    while tokens:
        if tokens[0] == KW_QED:
            t.children.append(Node(LABEL_KW_QED, tokens[0]))
            tokens = tokens[1:]
            break
        else:
            t.children.append(Node(LABEL_SENTENCE, tokens[0]))
            tokens = tokens[1:]
    # print("\nreturning proof node\n")
    return t, tokens


tokens = lexer(coq_test)
root = construct_tree(tokens)
pretty(root)
