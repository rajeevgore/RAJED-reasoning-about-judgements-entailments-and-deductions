Add LoadPath "../general".
Require Import Arith Init.Wf.
Definition strong_induction_wf := well_founded_induction lt_wf.

Theorem strong_induction :  forall P : nat -> Prop,
    P 0 -> (forall n : nat, (forall m, m <= n -> P m) -> P (S n)) ->
    forall n : nat, P n.
Proof.
  intros P H0 H1 n. induction n using strong_induction_wf.
  destruct n. assumption.
  apply H1.  intros m Hm. apply H. unfold lt.
  apply le_n_S.  assumption.
Qed.
