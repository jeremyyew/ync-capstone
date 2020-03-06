

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
