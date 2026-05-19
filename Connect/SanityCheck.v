Lemma test: forall P Q R,
  (Q -> R) -> (P -> Q -> R).
Proof. auto. Qed.

Lemma test2: forall P1 P2 Q,
  (P1 -> P2) -> ((P2 -> Q) -> (P1 -> Q)).
Proof. auto. Qed.
