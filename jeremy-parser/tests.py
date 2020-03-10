import pickle
import unittest
import deepdiff
from terminals import LABEL_DOCUMENT
from parser import preprocess, construct_node, check_arity
import utils


coq_test = """
Lemma A_1: forall n:nat, n = n.
Proof.
intro P H_P.
Qed.
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
Proof.
intro n1.
intro n2.
intro n3.
exact (lemma_b_2 (lemma_a_1 a1) (lemma_b_2 b1 b2)).
Qed.
"""

coq_test_arity1 = """
Proof.
    exact (lemma_b_2 (lemma_a_1)).
Qed.
"""


class TestParser(unittest.TestCase):
    def parser_helper(self, name, code):
        s = preprocess(code)
        t = construct_node(s, LABEL_DOCUMENT)

        try:
            with open(f'pickled_trees/{name}', 'rb') as f:
                pickled = pickle.load(f)
        except FileNotFoundError:
            pickle.dump(t, open(f'pickled_trees/{name}', 'wb'))
            with open(f'pickled_trees/{name}', 'rb') as f:
                pickled = pickle.load(f)

        diff = deepdiff.DeepDiff(t, pickled)
        try:
            self.assertEqual(diff, {})
        except AssertionError:
            print(
                f"\n*********\nPARSER OUTPUT FOR TESTCASE: {name}\n*********\n")
            utils.pretty(t)
            print(
                f"\n*********\nEXPECTED FOR TESTCASE: {name}\n*********\n")
            utils.pretty(pickled)

    def arity_helper(self, name, code, arity_db):
        s = preprocess(code)
        t = construct_node(s, LABEL_DOCUMENT)
        warnings = check_arity(t, arity_db, None)
        self.assertEqual(warnings,
                         [('lemma_b_2 (lemma_a_1)',
                           'lemma_b_2', 2, 1, '(lemma_a_1)'),
                          ('lemma_b_2 (lemma_a_1)',
                           'lemma_a_1', 1, 0, '')])

    def test_parser(self):
        self.parser_helper("coq_test2", coq_test2)

    def test_arity(self):
        arity_db = {
            "lemma_a_1": 1,
            "lemma_b_2": 2,
        }
        self.arity_helper("coq_test_arity1", coq_test_arity1, arity_db)


class TestParityCheck(unittest.TestCase):
    def test_arity(self):
        pass


unittest.main()

# Fixpoint left_balanced (t : binary_tree) : bool :=
#   match t with
#   | Leaf =>
#     true
#   | Node t1 n t2 =>
#     match t2 with
#     | Leaf =>
#       left_balanced t1
#     | Node _ _ _ =>
#       false
#     end
#   end.

# Lemma unfold_left_balanced_Leaf :
#   left_balanced Leaf = true.
# Proof.
#   unfold_tactic left_balanced.
# Qed.

# Lemma unfold_left_balanced_Node :
#   forall (t1 : binary_tree)
#          (n : nat)
#          (t2 : binary_tree),
#     left_balanced (Node t1 n t2) = match t2 with
#                                    | Leaf =>
#                                      left_balanced t1
#                                    | Node _ _ _ =>
#                                      false
#                                    end.
# Proof.
#   unfold_tactic left_balanced.
# Qed.
