import pickle
import unittest
import deepdiff
from terminals import LABEL_DOCUMENT
from parser import preprocess, construct_node, check_arity, logger
import utils


class TestParser(unittest.TestCase):
    def parser_helper(self, name, code):
        s = preprocess(code)
        t = construct_node(s, LABEL_DOCUMENT)

        try:
            with open(f'pickled/{name}', 'rb') as f:
                pickled = pickle.load(f)
        except FileNotFoundError:
            with open(f'pickled/{name}', 'wb') as f:
                pickle.dump(t, f)
            with open(f'pickled/{name}', 'rb') as f:
                pickled = pickle.load(f)

        diff = deepdiff.DeepDiff(t, pickled)
        try:
            self.assertEqual(diff, {})
            utils.pretty(t)
        except AssertionError:
            print(
                f"\n*********\nPARSER OUTPUT FOR TESTCASE: {name}\n*********\n")
            utils.pretty(t)
            print(
                f"\n*********\nEXPECTED FOR TESTCASE: {name}\n*********\n")
            utils.pretty(pickled)

    def test_assertion1(self):
        assertion1 = """
        Lemma A_1 :
        forall a b : nat,
        a + b = a + b.
        Lemma A_1 :
        forall a b : nat,
        a + b = a + b.
        Lemma A_1 :
        forall a b : nat,
        a + b = a + b.
        """
        self.parser_helper("assertion1", assertion1)

    def test_term1(self):
        term1 = """Proof.
        intro n1.
        intro n2.
        intro n3.
        exact (lemma_b_2 (lemma_a_1 a1) (lemma_b_2 b1 b2)).
        Qed.
        """
        self.parser_helper("term1", term1)


class TestParityCheck(unittest.TestCase):
    def arity_helper(self, code, arity_db, expected_warnings):
        s = preprocess(code)
        t = construct_node(s, LABEL_DOCUMENT)
        warnings = check_arity(t, arity_db, None)
        self.assertEqual(warnings,
                         expected_warnings)

    def test_arity_pos(self):
        arity_db = {
            "lemma_a_1": 1,
            "lemma_a_2": 2,
            "lemma_a_3": 3,
        }
        test = """Proof.
        exact (lemma_a_1 n1).
        exact (lemma_a_2 n1 n2).
        exact (lemma_a_3 n1 n2 n3).
        exact (lemma_a_3 (lemma_a_2 n1 n2) (lemma_a_1 n1) n3).
        Qed.
        """
        expected_warnings = []
        self.arity_helper(test,
                          arity_db, expected_warnings)

    def test_arity_neg(self):
        arity_db = {
            "lemma_a_1": 1,
            "lemma_a_2": 2,
        }
        test = """Proof.
        exact (lemma_a_1).
        exact (lemma_a_1 n1 n2).
        exact (lemma_a_2).
        exact (lemma_a_2 n1).
        exact (lemma_a_2 n1 n2 n3).
        exact (lemma_a_2 (lemma_a_1)).
        exact (lemma_a_2 (lemma_a_1 n1 n2) n3 n4).
        Qed.
        """
        # parent, first_term, arity_expected, arity, arg_strings
        expected_warnings = [
            ('lemma_a_1', 'lemma_a_1', 1, 0, ''),
            ('lemma_a_1 n1 n2', 'lemma_a_1', 1, 2, '(n1),(n2)'),
            ('lemma_a_2', 'lemma_a_2', 2, 0, ''),
            ('lemma_a_2 n1', 'lemma_a_2', 2, 1, '(n1)'),
            ('lemma_a_2 n1 n2 n3', 'lemma_a_2', 2, 3, '(n1),(n2),(n3)'),
            ('lemma_a_2 (lemma_a_1)', 'lemma_a_2', 2, 1, '(lemma_a_1)'),
            ('lemma_a_2 (lemma_a_1)', 'lemma_a_1', 1, 0, ''),
            ('lemma_a_2 (lemma_a_1 n1 n2) n3 n4', 'lemma_a_2',
             2, 3, '(lemma_a_1 n1 n2),(n3),(n4)'),
            ('lemma_a_1 n1 n2', 'lemma_a_1', 1, 2, '(n1),(n2)')]
        self.arity_helper(test,
                          arity_db, expected_warnings)


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
