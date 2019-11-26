Require Import List.

Import ListNotations.
Set Implicit Arguments.

(* Contains lemmas for swapped plus definitions and lemmas for swapped_spec and swapped_gen, all used for contraction. *)


Inductive swappedP T: list T -> list T -> Prop :=
  | swappedP_I : forall (X Y A B C D : list T), X = (A ++ B ++ C ++ D) -> 
    Y = (A ++ C ++ B ++ D) -> swappedP X Y.

Lemma swappedP_I': forall T (A B C D : list T),
  swappedP (A ++ B ++ C ++ D) (A ++ C ++ B ++ D).
Proof.  intros.  eapply swappedP_I ; reflexivity. Qed.
   
Lemma swappedP_same: forall T X, swappedP X (X : list T).
Proof.  intros.  apply (swappedP_I [] [] [] X) ; simpl ; reflexivity. Qed.

Lemma swappedP_L: forall T X Y Z,
  swappedP X (Y : list T) -> swappedP (Z ++ X) (Z ++ Y).
Proof.  intros. destruct H. subst. 
  rewrite !(app_assoc Z). apply swappedP_I'. Qed.

Lemma swappedP_R: forall T X Y Z,
  swappedP X (Y : list T) -> swappedP (X ++ Z) (Y ++ Z).
Proof.  intros. destruct H. subst. rewrite <- !app_assoc. apply swappedP_I'. Qed.

Lemma swappedP_cons: forall T (x : T) Y Z,
  swappedP Y Z -> swappedP (x :: Y) (x :: Z).
Proof.
  intros. destruct H. subst.
  repeat rewrite app_comm_cons.
  apply swappedP_I'.
Qed.

Lemma swappedP_simple: forall T U V X Y,
  U = X ++ Y -> V = Y ++ X -> swappedP U (V : list T).
Proof.  intros. subst. 
  apply (swappedP_I [] X Y []) ; simpl ; rewrite app_nil_r ; reflexivity. Qed.

Lemma swappedP_simple': forall T X Y, swappedP (X ++ Y : list T) (Y ++ X).
Proof.  intros. eapply swappedP_simple ; reflexivity. Qed. 

Lemma swappedP_simpleL: forall T X Y Z,
  Y = Z -> swappedP (X ++ Y) (Z ++ X : list T).
Proof.  intros. subst. apply swappedP_simple'. Qed.

Lemma swappedP_simpleR: forall T X Y Z,
  Y = Z -> swappedP (Y ++ X) (X ++ Z : list T).
Proof.  intros. subst. apply swappedP_simple'. Qed.

Lemma swappedP_comm : forall {T} (A B : list T),
    swappedP A B ->
    swappedP B A.
Proof.
  intros T A B H.
  inversion H. subst.
  eapply swappedP_I'.
Qed.

(* Sequences of swaps of length n+1. *)
Inductive swappedP_spec {T} : nat -> list T -> list T -> Prop :=
  swappedP_spec_I X Y : swappedP X Y -> swappedP_spec 0 X Y
| swappedP_spec_step n A B C :
    swappedP_spec n A B -> swappedP B C -> swappedP_spec (S n) A C.

Lemma swappedP_spec_refl : forall {T} n (A : list T),
    swappedP_spec n A A.
Proof.
  induction n; intros. econstructor. apply swappedP_same.
  econstructor. apply IHn.
  apply swappedP_same.
Qed. 

Lemma swappedP_app_L : forall {T} n (l A B : list T),
    swappedP_spec n A B ->
    swappedP_spec n (l ++ A) (l ++ B).
Proof.
  induction n; intros until 0; intros Hswap.
  constructor. apply swappedP_L. inversion Hswap. auto.
  inversion Hswap. subst.
  econstructor. eapply IHn. exact H0.
  apply swappedP_L. assumption.
Qed.

Lemma swappedP_spec_trans : forall {T} n1 n2 (l1 l2 l3 : list T),
    swappedP_spec n1 l1 l2 ->
    swappedP_spec n2 l2 l3 ->
    exists m, swappedP_spec m l1 l3.
Proof.
  induction n2; intros until 0; intros H1 H2.
  inversion H2. subst. exists (S n1).
  econstructor. apply H1. apply H.
  inversion H2. subst.
  eapply IHn2 in H1. destruct H1 as [m H1].
  exists (S m). econstructor.
  apply H1. apply H3. apply H0.
Qed.

Lemma swappedP_spec_trans_exact : forall {T} n1 n2 (l1 l2 l3 : list T),
    swappedP_spec n1 l1 l2 ->
    swappedP_spec n2 l2 l3 ->
    swappedP_spec (S (n1 + n2)) l1 l3.
Proof.
  induction n2; intros until 0; intros H1 H2.
  inversion H2. subst. rewrite PeanoNat.Nat.add_0_r. 
  econstructor. apply H1. apply H.
  inversion H2. subst.
  eapply IHn2 in H1. simpl.  econstructor.
  rewrite <- PeanoNat.Nat.add_succ_comm.
  apply H1. apply H3. assumption.
Qed.

Lemma swappedP_spec_comm : forall {T} n (A B : list T),
    swappedP_spec n A B ->
    swappedP_spec n B A.
Proof.
  induction n; intros until 0; intros H.
  constructor. inversion H. subst.
  eapply swappedP_comm. assumption.
  inversion H. subst.
  eapply swappedP_comm in H2.
  eapply swappedP_spec_I in H2.
  apply IHn in H1. 
  pose proof (@swappedP_spec_trans_exact T _ _ _ _ _ H2 H1) as H3.
  apply H3.
Qed.

Lemma swappedP_spec_conv : forall {T} n m (A B : list T),
  n = m ->
  swappedP_spec n A B ->
  swappedP_spec m A B.
Proof.  intros. subst. auto. Qed.

Lemma swappedP_app_mid_L : forall {T} n (A B C D E : list T),
    swappedP_spec n (A ++ B ++ C ++ D) E ->
    swappedP_spec (S n) (A ++ C ++ B ++ D) E.
Proof.
  intros until 0; intros Hswap.
  assert (S n = S (0 + n)) as Hass.
  reflexivity.
  eapply swappedP_spec_conv. symmetry. apply Hass.
  eapply swappedP_spec_trans_exact.
  constructor. apply swappedP_I'.
  apply Hswap.
Qed.

Lemma swappedP_app_mid_R : forall {T} n (A B C D E : list T),
    swappedP_spec n E (A ++ B ++ C ++ D) ->
    swappedP_spec (S n) E (A ++ C ++ B ++ D).
Proof.
  intros until 0; intros H.
  eapply swappedP_spec_comm in H.
  eapply swappedP_spec_comm.
  eapply swappedP_app_mid_L.
  apply H.
Qed.

Lemma swappedP_spec_front_mid : forall {T} n (A B C D : list T),
    swappedP_spec n B (C ++ D) ->
    exists m, swappedP_spec m (A ++ B) (C ++ A ++ D).
Proof.
  intros T n A B C D Hswap.
  eapply swappedP_app_L in Hswap.
  eapply swappedP_spec_trans. exact Hswap.
  rewrite <- app_nil_l.
  eapply swappedP_app_mid_R.
  apply swappedP_spec_refl.
  Unshelve. apply 0.
Qed.

Lemma swappedP__n_mid : forall {T} m (l Γ1 Γ2 Γ1' Γ2' : list T),
    swappedP_spec m (Γ1 ++ Γ2) (Γ1' ++ Γ2') ->
    exists n, swappedP_spec n (Γ1 ++ l ++ Γ2) (Γ1' ++ l ++ Γ2').
Proof.
  intros until 0.
  intros H. eapply swappedP_app_L in H.
  rewrite <- app_nil_l in H.
  rewrite <- app_nil_l in H at 1.
  apply swappedP_app_mid_L in H.
  eapply swappedP_app_mid_R in H.
  exists (S (S m)). exact H.
Qed.

(* Sequences of swaps, length implicit. *)
Inductive swappedP_gen {T} Γ Δ  :=
  swappedP_gen_I : (exists n, @swappedP_spec T n Γ Δ) -> swappedP_gen Γ Δ.

Lemma swappedP_gen_front_mid : forall {T} (A B C D : list T),
    swappedP_gen B (C ++ D) ->
    swappedP_gen (A ++ B) (C ++ A ++ D).
Proof.
  intros T A B C D Hswap. inversion Hswap as [Hs].
  destruct Hs as [n Hs].
  constructor.
  eapply swappedP_spec_front_mid. exact Hs.
Qed.

Lemma swappedP_spec_opp : forall {T} n (A B C : list T),
    swappedP_spec n B C ->
    swappedP A B ->
    swappedP_spec (S n) A C.
Proof.
  intros until 0; intros H1 H2.
  eapply swappedP_spec_I in H2.
  eapply swappedP_spec_trans_exact in H1.
  2 : eapply H2. auto.
Qed.

Lemma swappedP__gen : forall {T} (A B : list T),
  swappedP A B -> swappedP_gen A B.
Proof.
  intros T A B H. constructor.
  exists 0. constructor. exact H.
Qed.

Lemma swappedP_gen_app_L : forall {T} (l A B : list T),
    swappedP_gen A B ->
    swappedP_gen (l ++ A) (l ++ B).
Proof.
  intros T l A B H. inversion H as [H2].
  destruct H2 as [n H2]. constructor.
  eapply swappedP_app_L in H2. exists n. exact H2.
Qed.

Lemma swappedP_gen_refl : forall {T} (A : list T),
    swappedP_gen A A.
Proof.
  intros T A. constructor.
  exists 0. apply swappedP_spec_refl.
Qed.  