Require Import List List_lemmas.

(* Contains lemmas for swapped plus definitions and lemmas for swapped_spec and swapped_gen, all used for contraction. *)

Lemma swapped_comm : forall {T} (A B : list T),
    swapped A B ->
    swapped B A.
Proof.
  intros T A B H.
  inversion H. subst.
  eapply swapped_I'.
Qed.

(* Sequences of swaps of length n+1. *)
Inductive swapped_spec {T} : nat -> list T -> list T -> Prop :=
  swapped_spec_I X Y : swapped X Y -> swapped_spec 0 X Y
| swapped_spec_step n A B C :
    swapped_spec n A B -> swapped B C -> swapped_spec (S n) A C.

Lemma swapped_spec_refl : forall {T} n (A : list T),
    swapped_spec n A A.
Proof.
  induction n; intros. econstructor. apply swapped_same.
  econstructor. apply IHn.
  apply swapped_same.
Qed. 

Lemma swapped_app_L : forall {T} n (l A B : list T),
    swapped_spec n A B ->
    swapped_spec n (l ++ A) (l ++ B).
Proof.
  induction n; intros until 0; intros Hswap.
  constructor. apply swapped_L. inversion Hswap. auto.
  inversion Hswap. subst.
  econstructor. eapply IHn. exact H0.
  apply swapped_L. assumption.
Qed.

Lemma swapped_spec_trans : forall {T} n1 n2 (l1 l2 l3 : list T),
    swapped_spec n1 l1 l2 ->
    swapped_spec n2 l2 l3 ->
    exists m, swapped_spec m l1 l3.
Proof.
  induction n2; intros until 0; intros H1 H2.
  inversion H2. subst. exists (S n1).
  econstructor. apply H1. apply H.
  inversion H2. subst.
  eapply IHn2 in H1. destruct H1 as [m H1].
  exists (S m). econstructor.
  apply H1. apply H3. apply H0.
Qed.

Lemma swapped_spec_trans_exact : forall {T} n1 n2 (l1 l2 l3 : list T),
    swapped_spec n1 l1 l2 ->
    swapped_spec n2 l2 l3 ->
    swapped_spec (S (n1 + n2)) l1 l3.
Proof.
  induction n2; intros until 0; intros H1 H2.
  inversion H2. subst. rewrite PeanoNat.Nat.add_0_r. 
  econstructor. apply H1. apply H.
  inversion H2. subst.
  eapply IHn2 in H1. simpl.  econstructor.
  rewrite <- PeanoNat.Nat.add_succ_comm.
  apply H1. apply H3. assumption.
Qed.

Lemma swapped_spec_comm : forall {T} n (A B : list T),
    swapped_spec n A B ->
    swapped_spec n B A.
Proof.
  induction n; intros until 0; intros H.
  constructor. inversion H. subst.
  eapply swapped_comm. assumption.
  inversion H. subst.
  eapply swapped_comm in H2.
  eapply swapped_spec_I in H2.
  apply IHn in H1. 
  pose proof (swapped_spec_trans_exact _ _ _ _ _ H2 H1) as H3.
  apply H3.
Qed.

Lemma swapped_spec_conv : forall {T} n m (A B : list T),
  n = m ->
  swapped_spec n A B ->
  swapped_spec m A B.
Proof.  intros. subst. auto. Qed.

Lemma swapped_app_mid_L : forall {T} n (A B C D E : list T),
    swapped_spec n (A ++ B ++ C ++ D) E ->
    swapped_spec (S n) (A ++ C ++ B ++ D) E.
Proof.
  intros until 0; intros Hswap.
  assert (S n = S (0 + n)) as Hass.
  reflexivity.
  eapply swapped_spec_conv. symmetry. apply Hass.
  eapply swapped_spec_trans_exact.
  constructor. apply swapped_I'.
  apply Hswap.
Qed.

Lemma swapped_app_mid_R : forall {T} n (A B C D E : list T),
    swapped_spec n E (A ++ B ++ C ++ D) ->
    swapped_spec (S n) E (A ++ C ++ B ++ D).
Proof.
  intros until 0; intros H.
  eapply swapped_spec_comm in H.
  eapply swapped_spec_comm.
  eapply swapped_app_mid_L.
  apply H.
Qed.

Lemma swapped_spec_front_mid : forall {T} n (A B C D : list T),
    swapped_spec n B (C ++ D) ->
    exists m, swapped_spec m (A ++ B) (C ++ A ++ D).
Proof.
  intros T n A B C D Hswap.
  eapply swapped_app_L in Hswap.
  eapply swapped_spec_trans. exact Hswap.
  rewrite <- app_nil_l.
  eapply swapped_app_mid_R.
  apply swapped_spec_refl.
  Unshelve. apply 0.
Qed.

Lemma swapped__n_mid : forall {T} m (l Γ1 Γ2 Γ1' Γ2' : list T),
    swapped_spec m (Γ1 ++ Γ2) (Γ1' ++ Γ2') ->
    exists n, swapped_spec n (Γ1 ++ l ++ Γ2) (Γ1' ++ l ++ Γ2').
Proof.
  intros until 0.
  intros H. eapply swapped_app_L in H.
  rewrite <- app_nil_l in H.
  rewrite <- app_nil_l in H at 1.
  apply swapped_app_mid_L in H.
  eapply swapped_app_mid_R in H.
  exists (S (S m)). exact H.
Qed.

(* Sequences of swaps, length implicit. *)
Inductive swapped_gen {T} Γ Δ  :=
  swapped_gen_I : (exists n, @swapped_spec T n Γ Δ) -> swapped_gen Γ Δ.

Lemma swapped_gen_front_mid : forall {T} (A B C D : list T),
    swapped_gen B (C ++ D) ->
    swapped_gen (A ++ B) (C ++ A ++ D).
Proof.
  intros T A B C D Hswap. inversion Hswap as [Hs].
  destruct Hs as [n Hs].
  constructor.
  eapply swapped_spec_front_mid. exact Hs.
Qed.

Lemma swapped_spec_opp : forall {T} n (A B C : list T),
    swapped_spec n B C ->
    swapped A B ->
    swapped_spec (S n) A C.
Proof.
  intros until 0; intros H1 H2.
  eapply swapped_spec_I in H2.
  eapply swapped_spec_trans_exact in H1.
  2 : eapply H2. auto.
Qed.

Lemma swapped__gen : forall {T} (A B : list T),
  swapped A B -> swapped_gen A B.
Proof.
  intros T A B H. constructor.
  exists 0. constructor. exact H.
Qed.

Lemma swapped_gen_app_L : forall {T} (l A B : list T),
    swapped_gen A B ->
    swapped_gen (l ++ A) (l ++ B).
Proof.
  intros T l A B H. inversion H as [H2].
  destruct H2 as [n H2]. constructor.
  eapply swapped_app_L in H2. exists n. exact H2.
Qed.

Lemma swapped_gen_refl : forall {T} (A : list T),
    swapped_gen A A.
Proof.
  intros T A. constructor.
  exists 0. apply swapped_spec_refl.
Qed.  