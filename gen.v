
(* lemmas which shouldn't be necessary at all! *)

Lemma or_false: forall P : Prop, iff (or P False) P. Proof. tauto. Qed.
Lemma false_or: forall P : Prop, iff (or False P) P. Proof. tauto. Qed.
Lemma and_true: forall P : Prop, iff (and P True) P. Proof. tauto. Qed.
Lemma true_and: forall P : Prop, iff (and True P) P. Proof. tauto. Qed.

