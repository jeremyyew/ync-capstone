import pickle
import unittest
import deepdiff
from terminals import *
from parser import preprocess, construct_node, check_arity, logger
import utils


class TestParser(unittest.TestCase):
    def parser_helper(self, name, code):
        s = preprocess(code)
        logger.info(f"\n*********\nCONSTRUCTING TREE OF {name}:\n*********\n")
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
            logger.info(f"\n*********\nTREE OF {name}:\n*********\n")
            logger.info("\n"+utils.pretty2str(t))
        except AssertionError as e:
            logger.info(
                f"\n*********\nPARSER OUTPUT FOR TESTCASE: {name}\n*********\n")
            logger.info("\n"+utils.pretty2str(t))
            logger.info(
                f"\n*********\nEXPECTED FOR TESTCASE: {name}\n*********\n")
            logger.info("\n"+utils.pretty2str(pickled))
            raise e

    def unpermitted_tactic_helper(self, name, code, expected_tactic, expected_remaining):
        s = preprocess(code)
        try:
            logger.info(
                f"\n*********\nCONSTRUCTING TREE OF {name}:\n*********\n")
            t = construct_node(s, LABEL_DOCUMENT)
        except UnmatchedTactic as e:
            if e.tactic != expected_tactic or \
                    e.remaining != expected_remaining:
                print(f"\ntactic captured:{e.tactic}")
                print(f"\nremaining string:{e.remaining}")
                raise e

    def test_require_import1(self):
        require_import1 = """
        Require Import Arith.
        Require Import Arith Bool.
        """
        self.parser_helper("require_import1", require_import1)

    def test_assertion1(self):
        assertion1 = """
        Lemma A_1 : forall a b : nat,
        a + b = a + b. Proof. Admitted.
        Lemma A_2 : forall (a b : nat),
        a + b = a + b. Proof. Admitted.
        Lemma A_3 : forall a b:nat,
        a + b = a + b. Proof. Admitted.
        Lemma A_4 : forall (a b:nat),
        a + b = a + b. Proof. Admitted.
        Lemma A_5 : forall a b,
        a + b = a + b. Proof. Admitted.
        """
        self.parser_helper("assertion1", assertion1)

    def test_term1(self):
        term1 = """
        Proof.
        exact (lemma_a_2 (lemma_a_1 n1 n2) n3 n4).
        exact (lemma_b_2 (lemma_a_1 a1) (lemma_b_2 b1 b2)).
        Qed.
        """
        self.parser_helper("term1", term1)

    def test_proof1(self):
        proof1 = """
        Proof. Qed.
        Proof. Admitted.
        Proof. Abort.
        Proof. intro n. Qed.
        Proof. intro n. Admitted.
        Proof. intro n. Abort.
        """
        self.parser_helper("proof1", proof1)

    def test_restart1(self):
        restart1 = """
        Proof. intro n. Restart. Qed.
        Proof. Restart. intro n. Qed.
        Proof. Restart. Restart. Qed.
        """
        self.parser_helper("restart1", restart1)

    def test_intro1(self):
        intro1 = """
        Proof.
        intro.
        intro n1.
        Qed.
        """
        self.parser_helper("intro1", intro1)

    def test_intros1(self):
        intros1 = """
        Proof.
        intros.
        intros n1.
        intros n1 n2.
        Qed.
        """
        self.parser_helper("intros1", intros1)

    def test_exact1(self):
        exact1 = """
        Proof.
        exact lemma_a_1.
        exact Nat.add_comm.
        exact (Nat.add_comm).
        exact (Nat.add_comm n1).
        exact (Nat.add_comm n1 n2).
        exact (lemma_a_2 (lemma_a_1 n1) n2).
        exact (Nat.add_comm (lemma_a_1 n1) n2).
        Qed.
        """
        self.parser_helper("exact1", exact1)

    def test_rewrite1(self):
        rewrite1 = """
        Proof.
        rewrite->lemma_a_1.
        rewrite<-lemma_a_1.
        rewrite-> lemma_a_1.
        rewrite<- lemma_a_1.
        rewrite ->lemma_a_1.
        rewrite <-lemma_a_1.
        rewrite -> lemma_a_1.
        rewrite <- lemma_a_1.
        rewrite -> (Nat.add_comm (lemma_a_1 n1) n2).
        rewrite lemma_a_1.
        rewrite Nat.add_comm.
        rewrite (Nat.add_comm).
        rewrite (Nat.add_comm n1).
        rewrite (Nat.add_comm n1 n2).
        rewrite (lemma_a_2 (lemma_a_1 n1) n2).
        rewrite (Nat.add_comm (lemma_a_1 n1) n2).
        Qed.
        """
        self.parser_helper("rewrite1", rewrite1)

    def test_reflexivity1(self):
        reflexivity1 = """
        Proof.
        reflexivity.
        intro n.reflexivity.
        exact lemma_a_1.reflexivity.
        exact Nat.add_comm.reflexivity.
        exact (lemma_a_1).reflexivity.
        exact (Nat.add_comm).reflexivity.
        exact (Nat.add_comm n1).reflexivity.
        reflexivity.
        Qed.
        """
        self.parser_helper("reflexivity1", reflexivity1)

    def test_comment1(self):
        comment1 = """
        Require Import Arith.(*hello*)(*hello*)
        Proof.(*hello*)
        reflexivity.(*hello*)
        intro n.(*hello*)
        exact lemma_a_1.(*hello*)
        exact Nat.add_comm.(*hello*)
        exact (lemma_a_1).    (*hello*)
        exact (Nat.add_comm).  (*hello*)
        exact (Nat.add_comm n1).         (*hello*)
        Qed.(*hello*)
        (*hello*)
        """
        self.parser_helper("comment1", comment1)

    def test_check1(self):
        check1 = """
        Proof.
        Check lemma_a_1.
        Check Nat.add_comm.
        Check (lemma_a_1).
        Check (Nat.add_comm).
        Check(Nat.add_comm).
        Check(lemma_a_1).
        intro n.
        Check (Nat.add_comm (lemma_a_1 n1) n2).Check(Nat.add_comm (lemma_a_1 n1) n2).
        Qed.
        Check lemma_a_1.
        Check Nat.add_comm.
        Check (lemma_a_1).
        Check (Nat.add_comm).
        Check(Nat.add_comm).
        Check(lemma_a_1).
        Check (Nat.add_comm (lemma_a_1 n1) n2).Check(Nat.add_comm (lemma_a_1 n1) n2).
        """
        self.parser_helper("check1", check1)

    def test_compute1(self):
        compute1 = """
        Proof.
        Compute lemma_a_1.
        Compute Nat.add_comm.
        Compute (lemma_a_1).
        Compute (Nat.add_comm).
        Compute(Nat.add_comm).
        Compute(lemma_a_1).
        intro n.
        Compute (Nat.add_comm (lemma_a_1 n1) n2).Compute(Nat.add_comm (lemma_a_1 n1) n2).
        Qed.
        Compute lemma_a_1.
        Compute Nat.add_comm.
        Compute (lemma_a_1).
        Compute (Nat.add_comm).
        Compute(Nat.add_comm).
        Compute(lemma_a_1).
        Compute (Nat.add_comm (lemma_a_1 n1) n2).Check(Nat.add_comm (lemma_a_1 n1) n2).
        """
        self.parser_helper("compute1", compute1)

    def test_unpermitted_tactic1(self):
        code = """
            Proof.
            trivial.
            reflexivity. 
            exact (lemma_a n1).
            Qed.
            """
        self.unpermitted_tactic_helper("unpermitted1",
                                       code,
                                       "trivial",
                                       "trivial.reflexivity.exact (lemma_a n1).")

    def test_unpermitted_tactic2(self):
        code = """
            Proof.
            auto.
            Qed.
            """
        self.unpermitted_tactic_helper("unpermitted2",
                                       code,
                                       "auto",
                                       "auto.")


class TestParityCheck(unittest.TestCase):
    def arity_helper(self, name, code, arity, expected_warnings):
        s = preprocess(code)
        logger.info(f"\n*********\nCONSTRUCTING TREE OF {name}:\n*********\n")
        t = construct_node(s, LABEL_DOCUMENT)
        logger.info(f"\n*********\nTREE OF {name}:\n*********\n")
        logger.info("\n"+utils.pretty2str(t))
        warnings, _ = check_arity(t, arity)
        logger.info(
            f"Parity check warnings: {warnings}")
        self.assertEqual(warnings, expected_warnings)

    def test_aritypos(self):
        expected_warnings = []
        arity1 = {
            "lemma_a_1": 1,
            "lemma_a_2": 2,
            "lemma_a_3": 3,
            "Nat.add_comm": 2
        }
        aritypos1 = """
        Proof.
        exact (Nat.add_comm n1 n2).
        exact (lemma_a_1 n1).
        exact (lemma_a_2 n1 n2).
        exact (lemma_a_3 n1 n2 n3).
        exact (lemma_a_3 (lemma_a_2 n1 n2) (lemma_a_1 n1) n3).
        Qed.
        """
        arity2 = {"Nat.add_comm": 2}
        aritypos2 = """
        Lemma lemma_a_1: forall (n1: nat), n1 = n1. Proof. Admitted.
        Lemma lemma_a_2: forall (n1 n2 : nat), n1 + n2 = n1 + n2. Proof. Admitted.
        Lemma lemma_a_3: forall (n1 n2 n3 : nat), n1 + n2 + n3 = n1 + n2 + n3. Proof. Admitted.
        Proof.
        exact (Nat.add_comm n1 n2).
        exact (lemma_a_1 n1).
        exact (lemma_a_2 n1 n2).
        exact (lemma_a_3 n1 n2 n3).
        exact (lemma_a_3 (lemma_a_2 n1 n2) (lemma_a_1 n1) n3).
        Qed.
        """
        self.arity_helper("aritypos1", aritypos1, arity1, expected_warnings)
        self.arity_helper("aritypos2", aritypos2, arity2, expected_warnings)

    def test_arityneg12(self):
        # parent_term.val, first_term.val,  arity_expected, arity, args
        expected_warnings = [
            ['Nat.add_comm',
                'Nat.add_comm', 2, 0, []],
            ['Nat.add_comm',
                'Nat.add_comm', 2, 0, []],
            ['Nat.add_comm n1',
                'Nat.add_comm', 2, 1, ['n1']],
            ['lemma_a_1',
                'lemma_a_1', 1, 0, []],
            ['lemma_a_1',
                'lemma_a_1', 1, 0, []],
            ['lemma_a_1 n1 n2',
                'lemma_a_1', 1, 2, ['n1', 'n2']],
            ['lemma_a_2',
                'lemma_a_2', 2, 0, []],
            ['lemma_a_2 n1',
                'lemma_a_2', 2, 1, ['n1']],
            ['lemma_a_2 n1 n2 n3',
                'lemma_a_2', 2, 3, ['n1', 'n2', 'n3']],
            ['lemma_a_2 (lemma_a_1)',
                'lemma_a_2', 2, 1, ['lemma_a_1']],
            ['lemma_a_2 (lemma_a_1)',
                'lemma_a_1', 1, 0, []],
            ['lemma_a_2 (lemma_a_1 n1 n2) n3 n4',
                'lemma_a_2', 2, 3, ['lemma_a_1 n1 n2', 'n3', 'n4']],
            ['lemma_a_2 (lemma_a_1 n1 n2) n3 n4',
                'lemma_a_1', 1, 2, ['n1', 'n2']]]
        arity1 = {
            "lemma_a_1": 1,
            "lemma_a_2": 2,
            "Nat.add_comm": 2
        }
        arityneg1 = """
        Proof.
        exact Nat.add_comm.
        exact (Nat.add_comm).
        exact (Nat.add_comm n1).
        exact lemma_a_1.
        exact (lemma_a_1).
        exact (lemma_a_1 n1 n2).
        exact (lemma_a_2).
        exact (lemma_a_2 n1).
        exact (lemma_a_2 n1 n2 n3).
        exact (lemma_a_2 (lemma_a_1)).
        exact (lemma_a_2 (lemma_a_1 n1 n2) n3 n4).
        Qed.
        """
        # parent_term.val, first_term.val, arity_expected, arity, arg_strings
        arity2 = {"Nat.add_comm": 2}
        arityneg2 = """
        Lemma lemma_a_1: forall (n1: nat), n1 = n1. Proof. Admitted.
        Lemma lemma_a_2: forall (n1 n2 : nat), n1 + n2 = n1 + n2. Proof. Admitted.
        Proof.
        exact Nat.add_comm.
        exact (Nat.add_comm).
        exact (Nat.add_comm n1).
        exact lemma_a_1.
        exact (lemma_a_1).
        exact (lemma_a_1 n1 n2).
        exact (lemma_a_2).
        exact (lemma_a_2 n1).
        exact (lemma_a_2 n1 n2 n3).
        exact (lemma_a_2 (lemma_a_1)).
        exact (lemma_a_2 (lemma_a_1 n1 n2) n3 n4).
        Qed.
        """
        self.arity_helper("arityneg1", arityneg1, arity1, expected_warnings)
        self.arity_helper("arityneg2", arityneg2, arity2, expected_warnings)

    def test_arityneg3(self):
        # parent_term.val, first_term.val,  arity_expected, arity, args
        expected_warnings = [
            ['Nat.add_comm',
                'Nat.add_comm', 2, 0, []],
            ['Nat.add_comm',
                'Nat.add_comm', 2, 0, []],
            ['Nat.add_comm',
                'Nat.add_comm', 2, 0, []],
            ['Nat.add_comm',
                'Nat.add_comm', 2, 0, []],
            ['Nat.add_comm (Nat.add_comm)',
                'Nat.add_comm', 2, 1, ['Nat.add_comm']],
            ['Nat.add_comm (Nat.add_comm)',
                'Nat.add_comm', 2, 0, []]]
        arity3 = {
            "Nat.add_comm": 2
        }
        arityneg3 = """
        Proof.
        exact Nat.add_comm.
        exact (Nat.add_comm).
        rewrite <- Nat.add_comm.
        rewrite <- (Nat.add_comm).
        rewrite <- (Nat.add_comm (Nat.add_comm)).
        Qed.
        """
        # parent_term.val, first_term.val, arity_expected, arity, arg_strings
        self.arity_helper("arityneg3", arityneg3, arity3, expected_warnings)


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
