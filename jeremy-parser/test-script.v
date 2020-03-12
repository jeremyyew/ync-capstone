Lemma lemma_a_1: forall (n1 n2: nat), n1 +n2 = n1 +n2.
Proof.
Admitted.
Lemma lemma_a_2: forall (n1 n2: nat), n1 + n2= n1 + n2.
Proof.
  intro n1.
  exact (lemma_a_1 n1).
Qed.
