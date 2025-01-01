Require Import String.
Require Import List ListDec ListSet SetoidList Decidable.
Import ListNotations.
Require Import ListSetNotations.
Require Import Bool.
Require Import Permutation.
Require Import Arith.
Require Import Wellfounded.
Require Import Datatypes.
Require Import ssrbool.

Require Import Recdef.
Require Import Lia.
Require Import Ring.
From AAC_tactics Require Import AAC.

Require Import Tactics.
Require Import EqDec.

Definition comp {A B C : Type} (g : B -> C) (f : A -> B) : A -> C := fun x => g (f x).
(*Notation "g ∘ f" := (compose g f).*)



Set Implicit Arguments.

Open Scope type_scope.

Definition wf_nat_ind {A : Type} (size : A -> nat) :=
  well_founded_induction_type (wf_inverse_image _ _ _ size Nat.lt_wf_0).


Section list_biind.
  Variables A B : Type.
  Variable P : list A -> list B -> Type.
  Hypothesis BC : P [] [].
  Hypothesis IH : forall (a : A) (l1 : list A) (b : B) (l2 : list B),
      P l1 l2 -> P (a :: l1) (b :: l2).

  Theorem list_biind : forall (l1 : list A) (l2 : list B), length l1 = length l2 -> P l1 l2.
  Proof.
    induction l1.
    - intros l2 H. apply eq_sym, length_zero_iff_nil in H. rewrite H. assumption.
    - intros l2 H. destruct l2; try discriminate.
      apply IH. apply IHl1. injection H. tauto.
  Defined.

End list_biind.

Unset Implicit Arguments.

Open Scope nat_scope.



Lemma in_some_dec {A B : Type} {EDB : EqDec B} (b : B) (l : list A) (f : A -> list B) :
  {a | a ∈ l & b ∈ f a} + {forall a, a ∈ l -> b ∉ f a}.
Proof.
  induction l as [|a' l]; try (right; tauto).
  destruct IHl as [[a Ha Hb]| H].
  - left. exists a; simpl; tauto.
  - destruct (in_dec eqdec b (f a')) as [Hb|Hb].
    + left. exists a'; simpl; tauto.
    + right. intros x [Hx|Hx].
      * rewrite <- Hx. assumption.
      * apply H. assumption.
Defined.



Definition nxorb (b1 b2 : bool) : bool := if b1 then b2 else negb b2.

Lemma eqb_nxorb : forall b1 b2 b3, eqb (nxorb b1 b2) (nxorb b3 b2) = eqb b1 b3.
Proof. intros [|] [|] [|]; reflexivity. Qed.

Lemma eqb_nxorb_swap : forall b1 b2 b3, eqb (nxorb b1 b2) b3 = eqb b1 (nxorb b3 b2).
Proof. intros [|] [|] [|]; reflexivity. Qed.

Lemma nxorb_invol : forall b1 b2, nxorb (nxorb b1 b2) b2 = b1.
Proof. intros [|] [|]; reflexivity. Qed.


Section ListMore.

  Context {A B C D : Type}.
  Context `{AED : EqDec A}.


(* MISCELLANEOUS *)

  Lemma NoDup_single : forall a : A, NoDup [a].
  Proof.
    intro a. constructor; [apply in_nil|constructor].
  Qed.

  Lemma NoDupA_cons_inv (eqA : A -> A -> Prop) (x : A) (l : list A) :
    NoDupA eqA (x :: l) -> ~ InA eqA x l /\ NoDupA eqA l.
  Proof. intro H. inversion H. tauto. Qed.

  Lemma in_singleton_eq : forall (x a : A), In x [a] -> a = x.
  Proof.
    intros x a H. destruct H as [H|H].
    - assumption.
    - contradiction.
  Qed.

  Lemma incl_cons_cons (l l' : list A) (a : A) : incl l l' -> incl (a :: l) (a :: l').
  Proof.
    intro H. apply incl_cons; try now left. apply incl_tl. assumption.
  Qed.

  Lemma not_in_map (f : A -> B) (l : list A) (x : A) :
    ~ In (f x) (map f l) -> ~ In x l.
  Proof.
    intros Hnin. contradict Hnin. apply in_map. assumption.
  Qed.

  Lemma not_In_incl_drop_hd (l l' : list A) (a : A) :
    ~ In a l -> incl l (a :: l') -> incl l l'.
  Proof.
    intros Hnin Hinc x Hx. specialize (Hinc x Hx).
    destruct Hinc as [Heq|Hinc]; try assumption.
    contradict Hnin. rewrite Heq. assumption.
  Qed.

  Lemma app_singl_eq_cons (l : list A) (a : A) : a :: l = [a] ++ l.
  Proof. reflexivity. Qed.


(* ERASE *)

  Fixpoint listerase (l1 l2 : list A) : list A :=
    match l2 with
    | []      => l1
    | a :: l2' => erase a (listerase l1 l2')
    end.

  Lemma count_In : forall (l : list A) (x : A), In x l <-> count l x > 0.
  Proof. apply count_occ_In. Qed.

  Lemma count_not_In : forall (l : list A) (x : A), ~ In x l <-> count l x = 0.
  Proof. apply count_occ_not_In. Qed.
  
  Lemma Permutation_count : forall (l1 l2 : list A),
      Permutation l1 l2 <-> (forall x : A, count l1 x = count l2 x).
  Proof. apply Permutation_count_occ. Qed.

  Lemma NoDup_count : forall (l : list A), NoDup l <-> (forall x : A, count l x <= 1).
  Proof. apply NoDup_count_occ. Qed.

  Lemma count_app : forall (l1 l2 : list A) (x : A),
      count (l1 ++ l2) x = (count l1 x + count l2 x).
  Proof. apply count_occ_app. Qed.

  Lemma count_cons_eq : forall (l : list A) [x y : A],
      x = y -> count (x :: l) y = S (count l y).
  Proof. apply count_occ_cons_eq. Qed.

  Lemma count_cons_neq : forall (l : list A) [x y : A],
      x <> y -> count (x :: l) y = count l y.
  Proof. apply count_occ_cons_neq. Qed.

  Lemma count_bound (x : A) (l : list A) : count l x <= length l.
  Proof. apply count_occ_bound. Qed.

  Lemma count_ltlen_ex (a : A) (l : list A) :
    count l a < length l -> {x : A | x <> a /\ In x l}.
  Proof.
    intro H. induction l as [|a0 l]; try (simpl in H; lia).
    destruct (eqdec a0 a) as [Heq|Hneq].
    - destruct IHl as [x [Hneqx Hinx]].
      rewrite count_cons_eq in H; try assumption.
      simpl in H. lia.
      exists x. split; try assumption. now right.
    - exists a0. split; try assumption. now left.
  Defined.

  Lemma count_ge_length_ge :
    forall (l : list A) x n, count l x >= n -> length l >= n.
  Proof.
    intros l x n H. eapply Nat.le_trans; try eassumption. apply count_bound.
  Qed.

  Lemma count_map_inj {EDB : EqDec B} :
    forall (l : list A) (f : A -> B) a, ssrfun.injective f -> count (map f l) (f a) = count l a.
  Proof.
    intros l f a Hinj. induction l; [reflexivity|].
    simpl. rewrite IHl.
    destruct (eqdec (f a0) (f a)) as [Heqf|Hneqf];
    destruct (eqdec a0 a) as [Heq|Hneq]; try reflexivity.
    - contradict Hneq. apply Hinj. assumption.
    - contradict Hneqf. rewrite Heq. reflexivity.
  Qed.

  Lemma erase_cons_eq (l : list A) (a : A) : erase a (a :: l) = l.
  Proof. simpl. destruct (eqdec a a); tauto. Qed.
  
  Lemma erase_cons_neq (l : list A) (a b : A) : a <> b -> erase a (b :: l) = b :: erase a l.
  Proof. intro Hneq. simpl. destruct (eqdec a b); tauto. Qed.

  Lemma count_erase_same (l : list A) (a : A) :
    count (erase a l) a = count l a - 1.
  Proof.
    induction l; simpl; try reflexivity.
    destruct (eqdec a a0) as [Heq|Hneq].
    - apply eq_sym in Heq. destruct (eqdec a0 a); try contradiction. lia.
    - simpl. apply not_eq_sym in Hneq. destruct (eqdec a0 a); try contradiction. apply IHl.
  Qed.

  Lemma count_erase_not_same (l : list A) (a b : A) :
    a <> b -> count (erase a l) b = count l b.
  Proof.
    intros Hab. induction l; simpl; try reflexivity.
    destruct (eqdec a a0) as [Heq|Hneq].
    - rewrite <- Heq. destruct (eqdec a b); try contradiction. reflexivity.
    - simpl. destruct (eqdec a0 b); rewrite IHl; reflexivity.
  Qed.

  Lemma count_erase_same_In (l : list A) (a : A) :
      In a l -> S (count (erase a l) a) = count l a.
  Proof.
    intro Hina. rewrite count_In in Hina.
    pose proof (count_erase_same l a). lia.
  Qed.

  Lemma erase_not_In (l : list A) (x : A) :
    ~ In x l -> erase x l = l.
  Proof.
    intro Hnin. induction l; try reflexivity.
    simpl. destruct (eqdec x a) as [Heq|Hneq].
    - rewrite Heq in Hnin. simpl in Hnin. tauto.
    - rewrite IHl; try reflexivity. simpl in Hnin. tauto.
  Qed.

  Lemma erase_incl (l : list A) (x : A) :
    incl (erase x l) l.
  Proof. intro a. apply set_remove_1. Qed.

  Lemma erase_app_in_l (l1 l2 : list A) (x : A) :
    In x l1 -> erase x (l1 ++ l2) = (erase x l1) ++ l2.
  Proof.
    intros Hin. induction l1; try contradiction.
    destruct Hin as [Heq|Hin].
    - rewrite Heq. simpl. destruct (eqdec x x); try contradiction.
      reflexivity.
    - simpl. destruct (eqdec x a); try reflexivity.
      rewrite IHl1; tauto.
  Qed.

  Lemma erase_app_not_in_l (l1 l2 : list A) (x : A) :
    ~ In x l1 -> erase x (l1 ++ l2) = l1 ++ (erase x l2).
  Proof.
    intros Hnin. induction l1; try reflexivity.
    simpl. destruct (eqdec x a) as [Heq|Hneq];
      try (contradict Hnin; now left).
    destruct (in_dec eqdec x l1) as [Hin'|Hnin'];
      try (contradict Hnin; now right).
    rewrite IHl1; tauto.
  Qed.

  Lemma count_listerase (l1 l2 : list A) :
    forall x, count (listerase l1 l2) x = count l1 x - count l2 x.
  Proof.
    induction l2; intro x.
    - simpl. lia.
    - simpl. destruct (eqdec a x) as [Heq|Hneq].
      + rewrite Heq, count_erase_same, IHl2. lia.
      + rewrite count_erase_not_same; try assumption.
        rewrite IHl2. reflexivity.
  Qed.



(* ZIP *)

  Fixpoint zip {E : Type} (f : A -> B -> E) (lA : list A) (lB : list B) : list E :=
    match lA, lB with
    | a :: tA, b :: tB => f a b :: zip f tA tB
    | _, _ => []
    end.

  Lemma zip_nil_r {E : Type} (f : A -> B -> E) (l : list A) : zip f l [] = [].
  Proof. destruct l; reflexivity. Qed.

  Lemma in_zip_pair_fst {lA : list A} {lB : list B} {p : A * B} :
    p ∈ zip pair lA lB -> fst p ∈ lA.
  Proof.
    revert lB. induction lA; try tauto.
    intros lB H. destruct lB; try contradiction.
    destruct H as [H|H].
    - rewrite <- H. now left.
    - right. apply (IHlA lB). assumption.
  Qed.

  Lemma in_zip_pair_snd {lA : list A} {lB : list B} {p : A * B} :
    p ∈ zip pair lA lB -> snd p ∈ lB.
  Proof.
    revert lA. induction lB; try now setoid_rewrite zip_nil_r.
    intros lA H. destruct lA; try contradiction.
    destruct H as [H|H].
    - rewrite <- H. now left.
    - right. apply (IHlB lA). assumption.
  Qed.

  Lemma zip_pair_in_map_l (f : A -> A)  (lA : list A) (lB : list B) (a : A) (b : B) :
    (a, b) ∈ zip pair lA lB -> (f a, b) ∈ zip pair (map f lA) lB.
  Proof.
    revert lB. induction lA as [|a' lA]; intro lB;
      [simpl; contradiction|].
    destruct lB as [|b' lB]; try contradiction.
    simpl. intros [H|H].
    - injection H. intros Heqb Heqa. left. rewrite Heqa, Heqb. reflexivity.
    - right. apply IHlA. assumption.
  Qed.

  Lemma zip_pair_in_map_r (f : B -> B)  (lA : list A) (lB : list B) (a : A) (b : B) :
    (a, b) ∈ zip pair lA lB -> (a, f b) ∈ zip pair lA (map f lB).
  Proof.
    revert lA. induction lB as [|b' lB]; intro lA;
      [simpl; rewrite zip_nil_r; contradiction|].
    destruct lA as [|a' lA]; try contradiction.
    simpl. intros [H|H].
    - injection H. intros Heqb Heqa. left. rewrite Heqa, Heqb. reflexivity.
    - right. apply IHlB. assumption.
  Qed.

  Lemma zip_pair_bij_fst (lA : list A) (lB : list B) :
    length lA = length lB -> forall a, a ∈ lA -> exists p, p ∈ zip pair lA lB /\ fst p = a.
  Proof.
    intro H. pattern lA, lB. revert lA lB H. apply list_biind; try contradiction.
    intros a lA b lB IH a' Ha'. destruct Ha' as [Ha'|Ha'].
    - exists (a, b). simpl. tauto.
    - destruct (IH a' Ha') as [p Hp]. exists p. simpl. tauto.
  Qed.

  Lemma zip_pair_bij_snd (lA : list A) (lB : list B) :
    length lA = length lB -> forall b, b ∈ lB -> exists p, p ∈ zip pair lA lB /\ snd p = b.
  Proof.
    intro H. pattern lA, lB. revert lA lB H. apply list_biind; try contradiction.
    intros a lA b lB IH b' Hb'. destruct Hb' as [Hb'|Hb'].
    - exists (a, b). simpl. tauto.
    - destruct (IH b' Hb') as [p Hp]. exists p. simpl. tauto.
  Qed.

  Lemma map_eq_zip_pair {lA : list A} {lB : list B} {f : A -> B} :
    map f lA = lB -> forall p, p ∈ zip pair lA lB -> f (fst p) = snd p.
  Proof.
    intro H. pose proof (f_equal (@length _) H) as Hlen.
    rewrite map_length in Hlen. revert H. pattern lA, lB.
    revert lA lB Hlen. apply list_biind; try contradiction.
    intros a lA b lB IH H p Hp. destruct Hp as [Hp|Hp].
    - rewrite <- Hp. simpl in H |- *. injection H. tauto.
    - apply IH. injection H. tauto. assumption.
  Qed.

  Lemma zip_pair_eq_length (lA : list A) (lB : list B) :
    length lA = length lB -> length (zip pair lA lB) = length lA.
  Proof.
    revert lA lB. apply list_biind; [reflexivity|].
    intros a lA b lB Hlen. simpl. apply f_equal. assumption.
  Qed.

  
(* SET EQUALITY *)

  Lemma set_eq_refl (l : list A) : set_eq l l.
  Proof. unfold set_eq. tauto. Qed.

  Lemma set_eq_sym (l l' : list A) : set_eq l l' -> set_eq l' l.
  Proof. unfold set_eq. intros H x. rewrite H. tauto. Qed.

  Lemma set_eq_tran (l1 l2 l3 : list A) :
    set_eq l1 l2 -> set_eq l2 l3 -> set_eq l1 l3.
  Proof. unfold set_eq. intros H1 H2. setoid_rewrite H1. setoid_rewrite H2. tauto. Qed.

  Definition Equivalence_set_eq : Equivalence set_eq :=
  {|
    Equivalence_Reflexive := set_eq_refl;
    Equivalence_Symmetric := set_eq_sym;
    Equivalence_Transitive := set_eq_tran
  |}.

  Lemma set_eq_double_incl (l l' : list A) : set_eq l l' <-> incl l l' /\ incl l' l.
  Proof.
    split.
    - intro H. split; intro x; apply H.
    - intros [H1 H2]. intro x. split; [apply H1 | apply H2].
  Qed.

  Lemma set_eq_incl (l l' : list A) : set_eq l l' -> incl l l'.
  Proof. rewrite set_eq_double_incl. tauto. Qed.

  Lemma set_eq_app_app (l1 l2 m1 m2 : list A) :
    set_eq l1 m1 -> set_eq l2 m2 -> set_eq (l1 ++ l2) (m1 ++ m2).
  Proof.
    repeat rewrite set_eq_double_incl. intros H1 H2.
    split; apply incl_app_app; tauto.
  Qed.

  Lemma set_eq_cons (l1 l2 : list A) (a : A) :
    set_eq l1 l2 -> set_eq (a :: l1) (a :: l2).
  Proof.
    intro H. fold ([a] ++ l1). fold ([a] ++ l2).
    apply set_eq_app_app; [apply set_eq_refl | assumption].
  Qed.



(* MULTISET EQUALITY *)

  Lemma mset_eq_double_incl (l l' : list A) : mset_eq l l' <-> mset_incl l l' /\ mset_incl l' l.
  Proof.
    split.
    - intro H. split; intro x; rewrite H; apply le_n.
    - intros [H1 H2] x. specialize (H1 x). specialize (H2 x). lia.
  Qed.

  Lemma mset_eq_Permutation (l l' : list A) :
    mset_eq l l' <-> Permutation l l'.
  Proof. unfold mset_eq. rewrite <- Permutation_count. tauto. Qed.

  Lemma mset_eq_length (l l' : list A) :
    mset_eq l l' -> length l = length l'.
  Proof. rewrite mset_eq_Permutation. apply Permutation_length. Qed.

  Lemma mset_eq_refl (l : list A) : mset_eq l l.
  Proof. intro x. reflexivity. Qed.

  Lemma mset_eq_sym (l l' : list A) : mset_eq l l' -> mset_eq l' l.
  Proof. intros H x. rewrite H. reflexivity. Qed.

  Lemma mset_eq_tran (l1 l2 l3 : list A) :
    mset_eq l1 l2 -> mset_eq l2 l3 -> mset_eq l1 l3.
  Proof. unfold mset_eq. intros H1 H2. setoid_rewrite H1. setoid_rewrite H2. tauto. Qed.

  Definition Equivalence_mset_eq : Equivalence mset_eq :=
  {|
    Equivalence_Reflexive := mset_eq_refl;
    Equivalence_Symmetric := mset_eq_sym;
    Equivalence_Transitive := mset_eq_tran
  |}.

  Lemma mset_eq_app_app (l1 l2 m1 m2 : list A) :
    mset_eq l1 m1 -> mset_eq l2 m2 -> mset_eq (l1 ++ l2) (m1 ++ m2).
  Proof.
    unfold mset_eq. intros H1 H2 x. repeat rewrite count_app.
    rewrite H1, H2. reflexivity.
  Qed.

  Lemma mset_eq_app_comm (l1 l2 : list A) : mset_eq (l1 ++ l2) (l2 ++ l1).
  Proof. intro x. repeat rewrite count_app. lia. Qed.

  Lemma mset_eq_app_swap_app (l1 l2 l3 : list A) :
    mset_eq (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
  Proof.
    repeat rewrite app_assoc.
    apply mset_eq_app_app; try apply mset_eq_refl.
    apply mset_eq_app_comm.
  Qed.

  Lemma mset_eq_incl (l l' : list A) : mset_eq l l' -> mset_incl l l'.
  Proof. intros H x. rewrite H. apply le_n. Qed.

  Lemma mset_eq_singl_eq (l : list A) (a : A) :
    mset_eq l [a] -> l = [a].
  Proof.
    intro H. pose proof mset_eq_length _ _ H as Heqlen.
    destruct l; try discriminate; destruct l; try discriminate.
    specialize (H a). destruct (eqdec a0 a) as [Heq|Hneq];
      try (rewrite Heq; reflexivity).
    rewrite count_cons_neq in H; try assumption.
    rewrite count_cons_eq in H; try reflexivity.
    simpl in H. discriminate.
  Qed.

  Lemma mset_eq_cons_append (l : list A) (x : A) : mset_eq (x :: l) (l ++ [x]).
  Proof.
    rewrite mset_eq_Permutation. apply Permutation_cons_append.
  Qed.

  Lemma mset_eq_app_inv_l (l l1 l2 : list A) : mset_eq (l ++ l1) (l ++ l2) -> mset_eq l1 l2.
  Proof.
    rewrite ! mset_eq_Permutation. apply Permutation_app_inv_l.
  Qed.

  Lemma mset_eq_length_2 {a1 a2 b1 b2 : A} :
    mset_eq [a1; a2] [b1; b2] -> a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.
  Proof.
    rewrite mset_eq_Permutation. apply Permutation_length_2.
  Qed.

  Lemma mset_eq_length_2_inv {l : list A} {a1 a2 : A} :
    mset_eq [a1; a2] l -> l = [a1; a2] \/ l = [a2; a1].
  Proof.
    rewrite mset_eq_Permutation. apply Permutation_length_2_inv.
  Qed.

  Lemma mset_incl_refl (l : list A) : mset_incl l l.
  Proof. apply mset_eq_incl, mset_eq_refl. Qed.

  Lemma mset_incl_tran (l1 l2 l3 : list A) : mset_incl l1 l2 -> mset_incl l2 l3 -> mset_incl l1 l3.
  Proof. intros H1 H2 x. eapply Nat.le_trans; try apply H1. apply H2. Qed.

  Lemma mset_incl_refl_tl (l : list A) (a : A) : mset_incl l (a :: l).
  Proof.
    intros x. simpl. destruct (eqdec a x); [apply le_S | idtac]; apply le_n.
  Qed.

  Lemma mset_incl_incl (l l' : list A) : mset_incl l l' -> incl l l'.
  Proof.
    intros H x Hx. specialize (H x).
    rewrite count_In in Hx |- *. lia.
  Qed.

  Lemma mset_incl_not_In (l l' : list A) (a : A) : mset_incl l l' -> ~ In a l' -> ~ In a l.
  Proof.
    intros Hincl Hnin. rewrite count_not_In in Hnin |- *.
    specialize (Hincl a). lia.
  Qed.

  Lemma mset_incl_l_nil (l : list A) : mset_incl l [] -> l = [].
  Proof. intro H. apply incl_l_nil, mset_incl_incl. assumption. Qed.

  Lemma mset_incl_appr (l1 l2 l3 : list A) : mset_incl l1 l3 -> mset_incl l1 (l2 ++ l3).
  Proof. intros H x. rewrite count_app. specialize (H x). lia. Qed.

  Lemma mset_incl_appl (l1 l2 l3 : list A) : mset_incl l1 l2 -> mset_incl l1 (l2 ++ l3).
  Proof. intros H x. rewrite count_app. specialize (H x). lia. Qed.

  Lemma mset_incl_app_app (l1 l2 m1 m2 : list A) :
    mset_incl l1 m1 -> mset_incl l2 m2 -> mset_incl (l1 ++ l2) (m1 ++ m2).
  Proof.
    intros H1 H2 x. repeat rewrite count_app.
    specialize (H1 x). specialize (H2 x). lia.
  Qed.

  Lemma set_eq_incl_r (l1 l2 l2' : list A) :
    set_eq l2 l2' -> (incl l1 l2 <-> incl l1 l2').
  Proof.
    intro H. unfold incl. unfold set_eq in H. setoid_rewrite H. tauto.
  Qed.

  Lemma set_eq_incl_l (l1 l1' l2 : list A) :
    set_eq l1 l1' -> (incl l1 l2 <-> incl l1' l2).
  Proof.
    intro H. unfold incl. unfold set_eq in H. setoid_rewrite H. tauto.
  Qed.

  Lemma mset_eq_incl_l (l1 l1' l2 : list A) :
    mset_eq l1 l1' -> (mset_incl l1 l2 <-> mset_incl l1' l2).
  Proof. unfold mset_eq, mset_incl. intro H. setoid_rewrite H. tauto. Qed.

  Lemma mset_eq_set_eq {l l' : list A} :
    mset_eq l l' -> set_eq l l'.
  Proof.
    intro H. unfold mset_eq in H. unfold set_eq.
    setoid_rewrite (count_occ_In eqdec l).
    setoid_rewrite (count_occ_In eqdec l').
    setoid_rewrite H. tauto.
  Qed.

  Lemma mset_incl_NoDup (l l' : list A) : NoDup l' -> mset_incl l l' -> NoDup l.
  Proof.
    repeat rewrite NoDup_count. unfold mset_incl.
    intros HND Hinc. intros x. specialize (HND x). specialize (Hinc x). lia.
  Qed.

  Lemma mset_eq_NoDup (l l' : list A) : mset_eq l l' -> NoDup l -> NoDup l'.
  Proof.
    intros. apply (mset_incl_NoDup l' l); try assumption.
    apply mset_eq_incl, mset_eq_sym. assumption.
  Qed.

  Lemma NoDup_l_mset_incl_iff (l l': list A) : NoDup l -> mset_incl l l' <-> incl l l'.
  Proof.
    rewrite NoDup_count. unfold mset_incl. unfold incl.
    setoid_rewrite count_In. intros HND. split.
    - intros H x. specialize (HND x). specialize (H x). lia.
    - intros H x. specialize (HND x). specialize (H x). lia.
  Qed.

  Lemma mset_eq_erase_cons (l l' : list A) (a : A) :
    In a l -> mset_eq (erase a l) l' ->
      mset_eq l (a :: l').
  Proof.
    intros Hina Hmeq. intros x.
    destruct (eqdec a x) as [Heq|Hneq].
    - rewrite <- Heq. rewrite count_cons_eq; try reflexivity.
      specialize (Hmeq a). rewrite count_erase_same in Hmeq.
      rewrite count_In in Hina. lia.
    - rewrite count_cons_neq; try assumption.
      specialize (Hmeq x). rewrite count_erase_not_same in Hmeq; try assumption.
  Qed.

  Lemma mset_incl_cons_cons (l l' : list A) (a : A) :
    mset_incl l l' -> mset_incl (a :: l) (a :: l').
  Proof.
    intros H x.
    destruct (eqdec a x) as [Heq|Hneq].
    - rewrite <- Heq. repeat rewrite count_cons_eq; try reflexivity.
      specialize (H a). lia.
    - repeat rewrite count_cons_neq; try assumption.
      apply H.
  Qed.

  Lemma mset_incl_cons_l (l l' : list A) (a : A) :
    mset_incl (a :: l) l' -> mset_incl l l'.
  Proof. intros H x. specialize (H x). simpl in H. destruct (eqdec a x); lia. Qed.

  Lemma mset_incl_tl (l l' : list A) (a : A) :
    mset_incl l l' -> mset_incl l (a :: l').
  Proof.
    intro H. eapply mset_incl_tran; try eassumption. apply mset_incl_refl_tl.
  Qed.

  Lemma mset_incl_filter (f : A -> bool) (l : list A) :
    mset_incl (filter f l) l.
  Proof.
    induction l.
    - simpl. apply mset_incl_refl.
    - simpl. destruct (f a); try now apply mset_incl_cons_cons.
      now apply mset_incl_tl.
  Qed.

  Fixpoint mset_compl (l Ω : list A) : list A :=
    match l with
    | [] => Ω
    | a :: l' => erase a (mset_compl l' Ω)
    end.

  Lemma mset_compl_ppty (l Ω : list A) : mset_incl l Ω -> mset_eq (l ++ (mset_compl l Ω)) Ω.
  Proof.
    intro Hinc. induction l.
    - simpl. apply mset_eq_refl.
    - lapply IHl. 2:{ eapply mset_incl_tran; try apply Hinc. apply mset_incl_refl_tl. }
      intros Hmeq x. specialize (Hmeq x). specialize (Hinc x).
      rewrite count_app in Hmeq |- *.
      simpl. destruct (eqdec a x) as [Heq|Hneq].
      + rewrite <- Heq in Hmeq, Hinc |- *. rewrite <- Hmeq. rewrite count_erase_same.
        simpl in Hinc. destruct (eqdec a a); try contradiction. lia.
      + rewrite (count_erase_not_same _ _ _ Hneq). assumption.
  Qed.

  Lemma mset_eq_app_mset_compl (l1 l2 l3 : list A) :
    mset_eq (l1 ++ l2) l3 -> mset_eq l2 (mset_compl l1 l3).
  Proof.
    intro Heq.
    assert (mset_incl l1 l3) as Hinc13.
    { pose proof (mset_eq_incl _ _ Heq) as Hinc.
      apply (mset_incl_tran _ (l1 ++ l2)).
      apply mset_incl_appl, mset_incl_refl.
      assumption. }
    pose proof (mset_eq_tran _ _ _ Heq (mset_eq_sym _ _ (mset_compl_ppty l1 l3 Hinc13))) as H.
    apply mset_eq_app_inv_l in H. assumption.
  Qed.

  Lemma mset_compl_length (l Ω : list A) :
    mset_incl l Ω -> length (mset_compl l Ω) = length Ω - length l.
  Proof.
    intro H. pose proof (mset_compl_ppty l Ω H) as Hmeq.
    apply mset_eq_length in Hmeq.
    rewrite app_length in Hmeq. lia.
  Qed.

  Lemma mset_compl_mset_incl (l Ω : list A) :
    mset_incl l Ω -> mset_incl (mset_compl l Ω) Ω.
  Proof.
    intro H. apply mset_compl_ppty in H.
    apply mset_eq_incl in H. eapply mset_incl_tran; try eassumption.
    apply mset_incl_appr, mset_incl_refl.
  Qed.

  Lemma mset_compl_mset_eq_l (l l' Ω : list A) :
    mset_incl l Ω -> mset_eq l l' -> mset_eq (mset_compl l Ω) (mset_compl l' Ω).
  Proof.
    intros Hinc Hmeq. apply mset_eq_app_mset_compl.
    eapply mset_eq_tran; [idtac | apply mset_compl_ppty; eassumption].
    apply mset_eq_app_app.
    - apply mset_eq_sym. assumption.
    - apply mset_eq_refl.
  Qed.
  
  Fixpoint power_mset (l : list A) : list (list A) :=
    match l with
    | []      => [[]]
    | a :: l' => (map (cons a) (power_mset l')) ++ (power_mset l')
    end.

  Lemma power_mset_all (l' : list A) :
    forall l, mset_incl l l' <-> InA mset_eq l (power_mset l').
  Proof.
    induction l'.
    - intro l. split.
      + intro H. rewrite (mset_incl_l_nil _ H). simpl. constructor 1.
        apply mset_eq_refl.
      + intro H. simpl in H. inversion H; now apply mset_eq_incl.
    - intro l. split.
      + intro Hminc. simpl. rewrite InA_app_iff. pose proof (Hminc a) as Hca.
        rewrite count_cons_eq in Hca; try reflexivity.
        destruct (le_lt_eq_dec _ _ Hca) as [Hcalt|Hcale].
        * right. apply IHl'. intro x. destruct (eqdec a x) as [Heqa|Hneqa].
         -- rewrite <- Heqa. lia.
         -- specialize (Hminc x). rewrite count_cons_neq in Hminc; assumption.
        * left. assert (In a l) as Hina by (rewrite count_In; lia).
          cut (InA mset_eq (erase a l) (power_mset l')).
          { repeat rewrite InA_alt. intros [l0 [Hmeql0 Hinl0]].
            exists (a :: l0). split.
            - apply (mset_eq_erase_cons); assumption.
            - apply in_map_iff. exists l0. split; tauto. }
          apply IHl'. intro x. destruct (eqdec a x) as [Heqa|Hneqa].
         -- rewrite <- Heqa. pose proof (count_erase_same_In l a Hina). lia.
         -- rewrite (count_erase_not_same _ _ _ Hneqa).
            specialize (Hminc x).
            rewrite (count_cons_neq _ Hneqa) in Hminc.
            assumption.
      + intro HInA. simpl in HInA. rewrite InA_app_iff in HInA.
        destruct HInA as [HInA|HInA].
        * rewrite InA_alt in HInA. destruct HInA as [l0 [Hmeql0 Hinl0]].
          rewrite in_map_iff in Hinl0. destruct Hinl0 as [l1 [Heql0 Hinl1]].
          apply (In_InA Equivalence_mset_eq) in Hinl1.
          apply IHl' in Hinl1. apply mset_eq_incl in Hmeql0.
          eapply mset_incl_tran; try eassumption.
          rewrite <- Heql0. apply mset_incl_cons_cons. assumption.
        * apply IHl' in HInA. eapply mset_incl_tran; try eassumption.
          apply mset_incl_refl_tl.
  Qed.    


(* AAC Instances *)

  #[export] Instance mset_eq_Equiv : Equivalence mset_eq := {|
    Equivalence_Reflexive := mset_eq_refl;
    Equivalence_Symmetric := mset_eq_sym;
    Equivalence_Transitive := mset_eq_tran |}.

  #[export] Instance mset_eq_app_Assoc :
    Associative mset_eq (@app A).
  Proof. intros x y z. rewrite app_assoc. apply mset_eq_refl. Qed.

  #[export] Instance mset_eq_app_Comm :
    Commutative mset_eq (@app A).
  Proof. intros x y. rewrite mset_eq_Permutation. apply Permutation_app_comm. Qed.

  #[export] Instance mset_eq_app_Prop :
    Proper (mset_eq ==> mset_eq ==> mset_eq) (@app A).
  Proof. intros x x' Heqx y y' Heqy. apply mset_eq_app_app; assumption. Qed.


  #[export] Instance set_eq_Equiv : Equivalence (@set_eq A).
  Proof.
    constructor.
    - intro x. apply set_eq_refl.
    - intros x y. apply set_eq_sym.
    - intros x y z. apply set_eq_tran.
  Qed.

  #[export] Instance set_eq_app_Assoc : Associative set_eq (@app A).
  Proof. intros x y z. rewrite app_assoc. apply set_eq_refl. Qed.

  #[export] Instance set_eq_app_Comm : Commutative set_eq (@app A).
  Proof. intros x y x0. repeat rewrite in_app_iff. split; intros [H|H]; tauto. Qed.

  #[export] Instance set_eq_app_Unit : Unit set_eq (@app A) (@nil A).
  Proof.
    constructor.
    - intro x. simpl. apply set_eq_refl.
    - intro x. rewrite app_nil_r. apply set_eq_refl.
  Qed.

  #[export] Instance set_eq_app_Prop :
    Proper (set_eq ==> set_eq ==> set_eq) (@app A).
  Proof. intros x x' Heqx y y' Heqy. apply set_eq_app_app; assumption. Qed.


(* ERASE AGAIN *)



  Lemma erase_In_length (l : list A) (x : A) :
    In x l -> S (length (erase x l)) = length l.
  Proof.
    intro Hx. apply (@eq_trans _ _ (length (x :: (erase x l))));
      try reflexivity.
    apply (mset_eq_length). intro y. simpl.
    destruct (eqdec x y) as [Heq|Hneq].
    - rewrite <- Heq. rewrite count_erase_same.
      rewrite count_In in Hx. lia.
    - rewrite count_erase_not_same; try assumption. reflexivity.
  Qed.

  Lemma erase_In_length' (l : list A) (x : A) :
    In x l -> length (erase x l) = length l - 1.
  Proof.
    intro H. pose proof (erase_In_length _ _ H).
    rewrite (count_occ_In eqdec) in H. lia.
  Qed.

  Lemma erase_not_In_length (l : list A) (x : A) :
    ~ In x l -> length (erase x l) = length l.
  Proof.
    intro Hnin. rewrite (erase_not_In _ _ Hnin). reflexivity.
  Qed.

  Lemma erase_or_length (l : list A) (x : A) :
    length (erase x l) = length l \/
    length (erase x l) = length l - 1.
  Proof.
    destruct (in_dec eqdec x l).
    - right. now apply erase_In_length'.
    - left. now apply erase_not_In_length.
  Qed.

  Lemma erase_length_bound (l : list A) (a : A) : length (erase a l) <= length l.
  Proof. destruct (erase_or_length l a); lia. Qed.

  Lemma erase_length_bound' (l : list A) (a : A) : length l <= S (length (erase a l)).
  Proof. destruct (erase_or_length l a); lia. Qed.
  
  Lemma mset_incl_erase (l : list A) (a : A) : mset_incl (erase a l) l.
  Proof.
    intro x. destruct (eqdec a x) as [Heq|Hneq].
    - rewrite Heq. rewrite count_erase_same. lia.
    - rewrite  count_erase_not_same; [constructor | assumption].
  Qed.

  Lemma mset_incl_erase_erase (l l' : list A) (a : A) :
    mset_incl l l' ->
    mset_incl (erase a l) (erase a l').
  Proof.
    intro H. intro x. destruct (eqdec a x) as [Heq|Hneq].
    - rewrite <- Heq. repeat rewrite count_erase_same.
      specialize (H a). lia.
    - repeat rewrite count_erase_not_same; try assumption. apply H.
  Qed.

  Lemma mset_incl_length (E F : list A) : mset_incl E F -> length E <= length F.
  Proof.
    revert F E. induction F; intros E Hincl.
    - apply mset_incl_l_nil in Hincl. rewrite Hincl. constructor.
    - assert (length (erase a E) <= length F) as Hlen.
      { apply IHF. intro x. specialize (Hincl x). simpl in Hincl.
        destruct (eqdec a x) as [Heq|Hneq].
        - rewrite Heq. rewrite count_erase_same. lia.
        - rewrite count_erase_not_same; assumption. }
      simpl. pose proof (erase_length_bound' E a). lia.
  Qed.

  Lemma listerase_app_mset_eq (l1 l2 : list A) :
    mset_incl l2 l1 -> mset_eq ((listerase l1 l2) ++ l2) l1.
  Proof.
    intros H x. rewrite count_app, count_listerase.
    specialize (H x). lia.
  Qed.

  Lemma listerase_mset_incl (l1 l2 : list A) : mset_incl (listerase l1 l2) l1.
  Proof.
    intro x. rewrite count_listerase. lia.
  Qed.

  Lemma listerase_incl (l1 l2 : list A) : incl (listerase l1 l2) l1.
  Proof.
    apply mset_incl_incl. apply listerase_mset_incl.
  Qed.

  Lemma listerase_nil_mset_eq (l1 l2 : list A) :
    mset_incl l2 l1 -> listerase l1 l2 = [] -> mset_eq l1 l2.
  Proof.
    intros Hinc Hnil x. pose proof (count_listerase l1 l2 x) as Hcnt.
    rewrite Hnil in Hcnt. simpl in Hcnt.
    specialize (Hinc x). lia.
  Qed.
    



(* LIST MINUS *)

  Fixpoint listminus (l1 l2 : list A) : list A :=
    match l2 with
    | []      => l1
    | a :: l2' => remove eqdec a (listminus l1 l2')
    end.

  Lemma in_listminus_iff (l1 l2 : list A) :
    forall x, In x (listminus l1 l2) <-> (In x l1 /\ ~ In x l2).
  Proof.
    revert l1. induction l2; intros l1 x; try tauto.
    simpl. split.
    - intro H. apply in_remove in H.
      destruct H as [Hin Hneq].
      apply IHl2 in Hin. destruct Hin as [Hin Hnin].
      apply not_eq_sym in Hneq. tauto.
    - intros [Hin Hnin]. apply in_in_remove.
      apply not_eq_sym. tauto.
      apply IHl2. tauto.
  Qed.

  Lemma incl_listminus (l1 l2 : list A) : incl (listminus l1 l2) l1.
  Proof. intros x Hx. apply in_listminus_iff in Hx. tauto. Qed.

  Lemma not_in_listminus (l1 l2 : list A) : forall x, In x l2 -> ~ In x (listminus l1 l2).
  Proof. intros x Hx Hctr. apply in_listminus_iff in Hctr. tauto. Qed.

  Lemma listminus_recover (l1 l2 : list A) : set_eq ((listminus l1 l2) ++ l2) (l1 ++ l2).
  Proof.
    intro x. repeat rewrite in_app_iff. split; intro H.
    - destruct H as [H|H].
      + left. apply (incl_listminus _ l2). assumption.
      + now right.
    - destruct (in_dec eqdec x l2) as [Hin|Hnin].
      + now right.
      + destruct H as [H|]; try contradiction.
        left. apply in_listminus_iff. tauto.
  Qed.

  Lemma listminus_nil_l : forall F : list A, listminus [] F = [].
  Proof.
    induction F.
    - reflexivity.
    - simpl. rewrite IHF. reflexivity.
  Qed.

  Lemma listminus_remove_comm : forall (E F : list A) (a : A),
      remove eqdec a (listminus E F) = listminus (remove eqdec a E) F.
  Proof.
    intros E F. revert E. induction F.
    - simpl. intros E a. reflexivity.
    - simpl. intros E x. rewrite <- IHF.
      rewrite remove_remove_comm. reflexivity.
  Qed.

  Lemma listminus_empty : forall E F : list A, listminus E F = [] -> E ⊆ F.
  Proof.
    intros E F. revert E. induction F.
    - intros E H. simpl in H. rewrite H. apply incl_refl.
    - intros E H. simpl in H. rewrite listminus_remove_comm in H.
      intros x Hx. destruct (eqdec x a) as [Heq|Hneq].
      + rewrite Heq. left. reflexivity.
      + right. apply (IHF _ H). apply in_in_remove; assumption.
  Qed.


  Fixpoint find_dup (l : list A) : option A :=
    match l with
    | x :: xs => if in_dec eqdec x xs then Some x else find_dup xs
    | []     => None
    end.

  Lemma find_dup_in (l : list A) (x : A) : find_dup l = Some x -> List.In x l.
  Proof.
    intro H. induction l; try discriminate.
    simpl in H. destruct (in_dec eqdec a l).
    - injection H. intro Heqa. rewrite Heqa. now left.
    - right. apply IHl. assumption.
  Qed.

  Lemma find_dup_is_dup (l : list A) (x : A) : find_dup l = Some x -> count l x >= 2.
  Proof.
    intro Hdup. induction l; try discriminate.
    simpl in Hdup. destruct (in_dec eqdec a l) as [Hin|Hnin].
    - injection Hdup. intro Heqa. rewrite Heqa in Hin |- *.
      rewrite count_cons_eq; try reflexivity.
      rewrite count_In in Hin. lia.
    - specialize (IHl Hdup). simpl.
      destruct (eqdec a x); lia.
  Qed.

  Lemma find_dup_not_NoDup (l : list A) (x : A) : find_dup l = Some x -> ~ NoDup l.
  Proof.
    intros Hdup HND. rewrite NoDup_count in HND.
    apply find_dup_is_dup in Hdup. specialize (HND x). lia.
  Qed.

  Lemma find_dup_eq_nodup : forall l, find_dup l = None -> l = nodup eqdec l.
  Proof.
    induction l; try tauto.
    simpl. destruct (in_dec eqdec a l); try discriminate.
    intro H. rewrite <- IHl; try assumption. reflexivity.
  Qed.

  Lemma find_dup_NoDup : forall l, find_dup l = None -> NoDup l.
  Proof.
    intros l H. rewrite find_dup_eq_nodup; try assumption. apply NoDup_nodup.
  Qed.

  Definition distinct (l l' : list A) : Prop := forall x, In x l -> ~ In x l'.

  Lemma NoDup_app_distinct (l l' : list A) : NoDup (l ++ l') -> distinct l l'.
  Proof.
    intro ND. unfold distinct. induction l'; try tauto.
    intros x Hx Hcont. apply NoDup_remove in ND.
    destruct ND as [ND Hnin]. specialize (IHl' ND).
    destruct Hcont as [Hcont|Hcont].
    - contradict Hnin. rewrite Hcont. apply in_app_iff. tauto.
    - apply (IHl' x); assumption.
  Qed.

End ListMore.

Section NTPower.

  Context {A : Type}.
  Context `{AED : EqDec A}.

  Definition nt_power_mset (l : list A) : list (list A) :=
    listminus (power_mset l) [[]; l]. 

  Lemma power_mset_max_length (l' l : list A) :
    In l (power_mset l') -> length l = length l' -> l = l'.
  Proof.
    revert l. induction l'; intros l Hinl Hlen.
    - destruct Hinl; try contradiction. now apply eq_sym.
    - simpl in Hinl. rewrite in_app_iff in Hinl.
      destruct Hinl as [Hinl|Hinl]. 
      + apply in_map_iff in Hinl.
        destruct Hinl as [sl [Heqsl Hinsl]].
        specialize (IHl' sl Hinsl).
        rewrite <- IHl'; try now apply eq_sym.
        rewrite <- Heqsl in Hlen. simpl in Hlen. lia.
      + exfalso. cut (length l <= length l').
        simpl in Hlen. lia.
        apply mset_incl_length, power_mset_all.
        apply (In_InA _). assumption.
  Qed.

  Lemma nt_power_mset_all (l' l : list A) :
    (mset_incl l l' /\ length l <> 0 /\ length l <> length l') <-> InA mset_eq l (nt_power_mset l').
  Proof.
    split.
    - intros [Hinc [Hlen0 Hlenl']].
      apply power_mset_all in Hinc.
      rewrite InA_alt in Hinc |- *.
      destruct Hinc as [sl [Hmeqsl Hinsl]].
      exists sl. split; try assumption.
      apply in_listminus_iff. split; try assumption.
      intros [H|[H|]]; try contradiction;
        rewrite <- H in Hmeqsl; apply mset_eq_length in Hmeqsl; contradiction.
    - intro HInA. apply InA_alt in HInA.
      destruct HInA as [sl [Hmeqsl Hinsl]].
      apply in_listminus_iff in Hinsl.
      destruct Hinsl as [Hinsl Hninsl].
      split; try split.
      + apply power_mset_all. apply InA_alt.
        exists sl. tauto.
      + contradict Hninsl. left.
        apply mset_eq_length in Hmeqsl. rewrite Hninsl in Hmeqsl.
        apply eq_sym in Hmeqsl. apply eq_sym.
        apply length_zero_iff_nil in Hmeqsl. assumption.
      + contradict Hninsl. right. left.
        apply mset_eq_length in Hmeqsl. rewrite Hninsl in Hmeqsl.
        apply eq_sym. apply power_mset_max_length; try assumption.
        now apply eq_sym.
  Qed.

End NTPower.

Section MsetMore.

  Context {A B C D : Type}.
  Context `{AED : EqDec A}.
  Context `{BED : EqDec B}.

End MsetMore.
  
  
  

(*
Module ListSetNotations.

  Notation "x ∈ S" := (In x S) (at level 75).
  Notation "x ∉ S" := (~ x ∈ S) (at level 75).
  Notation "S ≃ T" := (set_eq S T) (at level 70).
  Notation "S ⊆ T" := (incl S T) (at level 70).
  Notation "S ≡ T" := (mset_eq S T) (at level 70).
  Notation "S ⫅ T" := (mset_incl S T) (at level 70).
  Notation "S ∖ T" := (listminus S T) (at level 60).

End ListSetNotations.
*)


Section FoldRight.
  
  Context {A B C D : Type}.
  Context `{AED : EqDec A}.
(*  Hypothesis Aeq_dec : forall (x y : A), {x = y} + {x <> y}.*)

  Definition app2 (p1 p2 : list A * list B) : list A * list B :=
    ((fst p1) ++ (fst p2), (snd p1) ++ (snd p2)).

  Definition app3 (p1 p2 : list A * list B * list C) : list A * list B * list C :=
    (app2 (fst p1) (fst p2), (snd p1) ++ (snd p2)).

  Lemma list_2_elems_dec : forall (l : list A),
      {a & {b & l = [a; b]} } + {forall a b, l <> [a; b]}.
  Proof.
    intro l.
    destruct l as [|a l]; try (right; intros; intro; discriminate).
    destruct l as [|b l]; try (right; intros; intro; discriminate).
    destruct l;try (right; intros; intro; discriminate).
    left. exists a, b. reflexivity.
  Defined.

  Lemma map_id (l : list A) : map id l = l.
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. unfold id at 1. rewrite IHl. reflexivity.
  Qed.

  Lemma app_eq_nil_iff (l l' : list A) : l ++ l' = [] <-> l = [] /\ l' = [].
  Proof.
    split; try apply app_eq_nil.
    intros [Hl Hl']. rewrite Hl, Hl'. reflexivity.
  Qed.

  Lemma dec_list_eq : forall (l l' : list A), decidable (l = l').
  Proof. intros l l'. unfold decidable. destruct (list_eq_dec eqdec l l'); tauto. Qed.

  Lemma Forall_rw_fold_right [f g : B -> C] [h : C -> A -> A] [a : A] [l : list B] :
    Forall (fun x => f x = g x) l ->
    fold_right (fun x => h (f x)) a l = fold_right (fun x => h (g x)) a l.
  Proof.
    intro Hall. induction Hall.
    - simpl. reflexivity.
    - simpl. rewrite H, IHHall. reflexivity.
  Qed.

  Lemma fold_right_id (l : list B) (a : A) :
    fold_right (fun _ b => b) a l = a.
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. apply IHl.
  Qed.

  Lemma in_map_inv_sig {f : B -> A} {l : list B} {y : A} :
    List.In y (map f l) -> {x : B | f x = y /\ List.In x l}.
  Proof.
    intro H. induction l; try contradiction.
    destruct (eqdec (f a) y) as [Heq|Hneq].
    - exists a. simpl. tauto.
    - destruct (in_dec eqdec y (map f l)) as [Hin|Hnin];
        try (exfalso; destruct H; contradiction).
      destruct (IHl Hin) as [x Hx]. exists x. simpl. tauto.
  Defined.

  Lemma fold_right_cons {l : list A} :
    fold_right (fun x => cons x) [] l = l.
  Proof.
    induction l; try reflexivity. simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma fold_right_map (f : B -> C -> C) (g : A -> B) (c : C) (l : list A) :
    fold_right (fun x => f (g x)) c l = fold_right (fun x => f x) c (map g l).
  Proof.
    induction l; try reflexivity. simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma fold_right_app_incl {a : list A} {l : list (list A)} :
    List.In a l -> incl a (fold_right (fun x => app x) [] l).
  Proof.
    intro Hin. induction l as [|b l]; try contradiction.
    simpl. destruct Hin as [Heq|Hin].
    - rewrite Heq. apply incl_appl, incl_refl.
    - apply incl_appr. apply IHl. assumption.
  Qed.

  Lemma Forall_incl_fold_right_incl {l : list (list A)} {l' : list A} :
    Forall (fun a => incl a l') l -> incl (fold_right (fun a => app a) [] l) l'.
  Proof.
    intro H. induction l; try apply incl_nil_l.
    simpl. pose proof (Forall_inv H). pose proof (Forall_inv_tail H).
    apply incl_app; try assumption. apply IHl. assumption.
  Qed.

  Lemma In_fold_right_app {l : list A} {f : A -> list B} {b : B} :
    In b (fold_right (fun x => app (f x)) [] l) -> exists x, In x l /\ In b (f x).
  Proof.
    induction l; simpl; try tauto.
    intro H. rewrite in_app_iff in H. destruct H as [H|H].
    - exists a. split; try now left. assumption.
    - specialize (IHl H). destruct IHl as [x [Hinx Hinb]].
      exists x. split; try now right. assumption.
  Qed.

  Lemma In_fold_right_app_iff {l : list A} {f : A -> list B} {b : B} :
    In b (fold_right (fun x => app (f x)) [] l) <-> exists x, In x l /\ In b (f x).
  Proof.
    split; try apply In_fold_right_app.
    intros [x [Hinx Hinb]]. induction l; try contradiction.
    simpl. rewrite in_app_iff. destruct Hinx as [Hx|Hx].
    - left. rewrite Hx. assumption.
    - right. apply IHl. assumption.
  Qed.

  Lemma In_fold_right_app_iff' {l : list A} {f : A -> list B} (l' : list B) :
    l' = fold_right (fun x => app (f x)) [] l ->
      forall b, In b l' <-> exists x, In x l /\ In b (f x).
  Proof.
    intros Heql' b. rewrite Heql'. apply In_fold_right_app_iff.
  Qed.
  
  Lemma bc_incl_fold_right_app_bc (l : list A) (bc : list B) (f : A -> list B) :
    bc ⊆ (fold_right (fun x => app (f x)) bc l).
  Proof.
    induction l.
    - simpl. apply incl_refl.
    - simpl. apply incl_appr. assumption.
  Qed.

  Lemma In_fold_right_app_bc {l : list A} {f : A -> list B} {bc : list B} {b : B} :
    In b (fold_right (fun x => app (f x)) bc l) -> (exists x, In x l /\ In b (f x)) \/ b ∈ bc.
  Proof.
    induction l; simpl; try tauto.
    intro H. rewrite in_app_iff in H. destruct H as [H|H].
    - left. exists a. split; try now left. assumption.
    - specialize (IHl H). destruct IHl as [[x [Hinx Hinb]]|Hin].
      + left. exists x. split; try now right. assumption.
      + right. assumption.
  Qed.

  Lemma In_fold_right_app_bc_iff {l : list A} {f : A -> list B} {bc : list B} {b : B} :
    In b (fold_right (fun x => app (f x)) bc l) <-> (exists x, In x l /\ In b (f x)) \/ b ∈ bc.
  Proof.
    split; try apply In_fold_right_app_bc.
    intros [[x [Hinx Hinb]]|Hin].
    - induction l; try contradiction.
      simpl. rewrite in_app_iff. destruct Hinx as [Hx|Hx].
      + left. rewrite Hx. assumption.
      + right. apply IHl. assumption.
    - pose proof (bc_incl_fold_right_app_bc l bc f) as H.
      apply H. assumption.
  Qed.

  Lemma fold_right_cons_eq (f : B -> A -> A) (a0 : A) (b : B) (l : list B) :
    fold_right f a0 (b :: l) = f b (fold_right f a0 l).
  Proof. reflexivity. Qed.

End FoldRight.

Definition list_union {A B : Type} (l : list A) (f : A -> list B) : list B :=
  fold_right (fun x => app (f x)) [] l.

Lemma list_union_alt {A B : Type} (l : list A) (f : A -> list B) :
  list_union l f = fold_right (@app B) [] (map f l).
Proof. unfold list_union. apply fold_right_map. Qed.

Section ListUnion.

  Context {A B C D : Type}.

  Lemma union_map (l : list A) (f : A -> list B) :
    list_union l f = list_union (map f l) id.
  Proof.
    unfold list_union. unfold id. apply fold_right_map.
  Qed.

  Lemma In_union {l : list A} {f : A -> list B} {b : B} :
    In b (list_union l f) -> exists x, In x l /\ In b (f x).
  Proof. apply In_fold_right_app. Qed.
  
  Lemma In_union_iff {l : list A} {f : A -> list B} {b : B} :
    In b (list_union l f) <-> exists x, In x l /\ In b (f x).
  Proof. apply In_fold_right_app_iff. Qed.

End ListUnion.


Section ForallMore.
  
  Context {A B C D : Type}.
  Context `{AED : EqDec A}.

  Lemma sing_incl_in (x : A) (l : list A) : [x] ⊆ l -> x ∈ l.
  Proof.
    intro H. apply H. now left.
  Qed.

  Lemma Forall_mp {P Q : A -> Prop} {l : list A} :
    Forall P l -> Forall (fun x => P x -> Q x) l -> Forall Q l.
  Proof.
    intros HP HPQ. induction l; try constructor 1.
    inversion HP. inversion HPQ. constructor 2. 
    - apply H5. assumption.
    - apply IHl; assumption.
  Qed.

  Lemma Forall_and_iff {P Q : A -> Prop} {l : list A} :
    Forall (fun x : A => P x /\ Q x) l <-> Forall P l /\ Forall Q l.
  Proof.
    split. apply Forall_and_inv. intro H. apply Forall_and; tauto.
  Qed.

  Lemma Forall_iff : forall {P Q : A -> Prop}, (forall a, P a <-> Q a) ->
    forall l, Forall P l <-> Forall Q l.
  Proof.
    intros P Q HPQ l. split; apply Forall_impl; intro a; apply HPQ.
  Qed.

  Lemma Forall_cons_iff {P : A -> Prop} {l : list A} {a : A} :
    Forall P (a :: l) <-> P a /\ Forall P l.
  Proof.
    split; try (intro; apply Forall_cons; tauto).
    intro H. split; [apply (Forall_inv H) | apply (Forall_inv_tail H)].
  Qed.

  Lemma Forall_one {P : A -> Prop} {a : A} : P a -> Forall P [a].
  Proof. exact (fun H => Forall_cons _ H (Forall_nil _)). Qed.

  Inductive ForallT (P : A -> Type) : list A -> Type :=
  | ForallT_nil : ForallT P []
  | ForallT_cons : forall {x l}, P x -> ForallT P l -> ForallT P (x::l).

  Lemma ForallT_inv {P : A -> Type} {a : A} {l : list A} : ForallT P (a :: l) -> P a.
  Proof. intro H. inversion H. assumption. Defined.

  Lemma ForallT_inv_tail {P : A -> Type} {a : A} {l : list A} : ForallT P (a :: l) -> ForallT P l.
  Proof. intro H. inversion H. assumption. Defined.

  Lemma ForallT_forall {P : A -> Type} :
    forall l : list A, ForallT P l <+> (forall x, List.In x l -> P x).
  Proof.
    split.
    - intro H. induction l; try contradiction.
      intros x Hx. inversion H. clear H2 H1 l0 x0. rename X into HPa, X0 into HPl.
      destruct (eqdec a x) as [Heq|Hneq]; try now rewrite <- Heq.
      destruct (in_dec eqdec x l) as [Hin|Hnin]; try now apply IHl.
      exfalso. simpl in Hx. tauto.
    - intro H. induction l; try constructor.
      + apply H. now left.
      + apply IHl. intros x Hx. apply H. now right.
  Defined.

  Lemma ForallT_mp {P Q : A -> Type} {l : list A} :
    ForallT P l -> ForallT (fun x => P x -> Q x) l -> ForallT Q l.
  Proof.
    intros HP HPQ. induction l; try constructor 1.
    inversion HP. inversion HPQ. clear H3 H2 l1 x0 H1 H0 l0 x.
    rename X into HPa, X0 into HPl, X1 into HPaQa, X2 into HPQl.
    constructor 2.
    - apply HPaQa. assumption.
    - apply IHl; assumption.
  Defined.

  Lemma ForallT_mp_dep {P : B -> A -> Type} {l : list A} (b : B) :
    ForallT (fun x => forall y, P y x) l -> ForallT (P b) l.
  Proof.
    intros HP. induction l; try constructor.
    - apply (ForallT_inv HP).
    - apply IHl. apply (ForallT_inv_tail HP).
  Defined.

  Lemma ForallT_act {P Q : A -> Type} {l : list A} (f : forall x, P x -> Q x) :
    ForallT P l -> ForallT Q l.
  Proof.
    intro H. apply (ForallT_mp H). induction l; try constructor.
    exact (f a). inversion H. apply IHl. assumption.
  Qed.
  
  Lemma ForallT_act_iff {P Q : A -> Type} {l : list A} :
      (forall x : A, P x <+> Q x) -> ForallT P l <+> ForallT Q l.
  Proof.
    intro H. split; apply ForallT_act; intro x; apply H.
  Defined.

  Lemma ForallT_sig_elim {R : A -> B -> Prop} {l : list A} :
    ForallT (fun x => {y : B | R x y}) l -> {l' | Forall2 R l l'}.
  Proof.
    intro H. induction l; try (exists []; constructor).
    inversion H. clear H2 H1 l0 x. destruct X as [b Rab]. rename X0 into Hl.
    destruct (IHl Hl) as [l' Rll']. exists (b :: l').
    constructor; assumption.
  Defined.

  Lemma Forall_ForallT {P : A -> Prop} : forall l : list A, Forall P l <+> ForallT P l.
  Proof.
    split.
    - intro H. apply ForallT_forall, Forall_forall. assumption.
    - intro H. apply Forall_forall, ForallT_forall. assumption.
  Defined.

  Lemma Forall2_and_inv {R1 R2 : A -> B -> Prop} {l : list A} {l' : list B} :
    Forall2 (fun x y => R1 x y /\ R2 x y) l l' -> Forall2 R1 l l' /\ Forall2 R2 l l'.
  Proof.
    intro H. induction H; auto. split; constructor; tauto.
  Qed.

  Lemma Forall2_Forall_r {P : B -> Prop} {l : list A} {l' : list B} :
    Forall2 (fun x y => P y) l l' -> Forall P l'.
  Proof.
    intro H. induction H; auto.
  Qed.

  Lemma Forall2_map_iff {R : C -> D -> Prop} {f : A -> C} {g : B -> D} {l : list A} {l' : list B} :
    Forall2 (fun x y => R (f x) (g y)) l l' <-> Forall2 R (map f l) (map g l').
  Proof.
    split.
    - intro H. induction H; [constructor | constructor; assumption].
    - intro H. revert l' H. induction l.
      + intros l' H. destruct l'; [constructor | inversion H].
      + intros l' H. destruct l'; try inversion H.
        constructor; [idtac | apply IHl]; assumption.
  Qed.

  Lemma Forall2_eq_same {l : list A} : Forall2 eq l l.
  Proof.
    induction l.
    - constructor.
    - constructor; tauto.
  Qed.

  Lemma Forall2_eq_iff {l l' : list A} : Forall2 eq l l' <-> l = l'.
  Proof.
    split.
    - intro H. induction H; try reflexivity. rewrite H, IHForall2. reflexivity.
    - intro H. rewrite <- H. apply Forall2_eq_same.
  Qed.

  Lemma Forall2_sig_l {R : B -> A -> Prop} {l : list B} {l' : list A} :
    Forall2 R l l' -> forall x', List.In x' l' -> {x | List.In x l /\ R x x'}.
  Proof.
    intros Hall2. pose proof (Forall2_length Hall2) as Hlen. revert Hall2. pattern l, l'.
    revert l l' Hlen. apply list_biind; try (simpl; tauto).
    intros a l b l' IH Hall2 x' H. apply Forall2_cons_iff in Hall2.
    destruct Hall2 as [Hab Hall2]. destruct (eqdec b x') as [Heq|Hneq].
    - exists a. rewrite <- Heq. simpl. tauto.
    - destruct (in_dec eqdec x' l') as [Hin|Hnin]; try (exfalso; destruct H; tauto).
      destruct (IH Hall2 x' Hin) as [x Hx]. exists x. simpl. tauto.
  Defined.

  Lemma Forall2_iff : forall {R S : A -> B -> Prop}, (forall a b, R a b <-> S a b) ->
    forall l l', Forall2 R l l' <-> Forall2 S l l'.
  Proof.
    intros R S HRS l l'. split; apply Forall2_impl; intro a; apply HRS.
  Qed.


  Inductive ExistsT (P : A -> Type) : list A -> Type :=
  | ExistsT_cons_hd : forall (x : A) (l : list A), P x -> ExistsT P (x :: l)
  | Exists_cons_tl : forall (x : A) (l : list A), ExistsT P l -> ExistsT P (x :: l).

  Lemma ExistsT_exists {P : A -> Type} (l : list A) :
    ExistsT P l <+> {a & In a l & P a}.
  Proof.
    split.
    - intro Hex. induction Hex.
      + exists x; [now left | assumption].
      + destruct IHHex as [a Hina HPa].
        exists a; [now right | assumption].
    - intros [a Hina HPa]. induction l as [|x l]; try contradiction.
      destruct (eqdec x a) as [Heq|Hneq].
      + rewrite Heq. constructor 1. assumption.
      + constructor 2. apply IHl. destruct (in_dec eqdec a l); try assumption.
        destruct Hina; contradiction.
  Defined.

End ForallMore.


Lemma in_if_in_dec_eq {A B : Type} {Aeq_dec : forall x y : A, {x = y} + {x <> y}} (a : A) (l : list A) :
  a ∈ l -> forall (b b' : B), (if in_dec Aeq_dec a l then b else b') = b.
Proof.
  intro H. destruct (in_dec Aeq_dec a l). reflexivity. contradiction.
Qed.

Lemma fold_right_in_dec_incl {A B C : Type} {EDA : EqDec A} (l l' : list A) (op : B -> C -> C) (c0 : C) (f g : A -> B) :
  l ⊆ l' ->
  fold_right (fun x => op (if in_dec eqdec x l' then f x else g x)) c0 l
  = fold_right (fun x => op (if in_dec eqdec x l then f x else g x)) c0 l.
Proof.
  revert l'. induction l; try reflexivity.
  intros l' H. rewrite ! fold_right_cons_eq.
  rewrite ! in_if_in_dec_eq.
  rewrite IHl. rewrite <- (IHl (a :: l)). reflexivity.
  - apply incl_tl, incl_refl.
  - eapply incl_tran; try apply H. apply incl_tl, incl_refl.
  - now left.
  - apply H. now left.
Qed.

Lemma fold_right_in_dec {A B C : Type} {EDA : EqDec A} (op : B -> C -> C) (f g : A -> B) (c0 : C) (l : list A) :
  fold_right (fun x => op (if (in_dec eqdec x l) then f x else g x)) c0 l
  = fold_right (fun x => op (f x)) c0 l.
Proof.
  induction l; try reflexivity.
  rewrite fold_right_cons_eq. rewrite fold_right_in_dec_incl.
  rewrite IHl. rewrite in_if_in_dec_eq. reflexivity.
  - now left.
  - apply incl_tl, incl_refl.
Qed.

Lemma union_in_dec  {A B : Type} {EDA : EqDec A} (f g : A -> list B) (l : list A) :
  list_union l (fun x => if in_dec eqdec x l then f x else g x) = list_union l f.
Proof. apply fold_right_in_dec. Qed.

Lemma fold_right_in_dec_map {A B : Type} {EDA : EqDec A} (f : A -> B) (l : list A) :
  fold_right (fun x => app (if (in_dec eqdec x l) then [f x] else [])) [] l
  = map f l.
Proof.
  induction l; try reflexivity.
  rewrite fold_right_cons_eq. rewrite fold_right_in_dec_incl.
  rewrite IHl. rewrite in_if_in_dec_eq. reflexivity.
  - now left.
  - apply incl_tl, incl_refl.
Qed.

Lemma union_in_dec_map  {A B : Type} {EDA : EqDec A} (f : A -> B) (l : list A) :
  list_union l (fun x => if in_dec eqdec x l then [f x] else []) = map f l.
Proof. apply fold_right_in_dec_map. Qed.

Lemma in_zip_pair_23_sig_1 {A B C : Type} {BED : EqDec B} {CED : EqDec C} (lA : list A) (lB : list B) (lC : list C) (b : B) (c : C) :
  length lA = length lB -> length lB = length lC ->
  (b, c) ∈ zip pair lB lC -> {a | (a, b, c) ∈ zip pair (zip pair lA lB) lC}.
Proof.
  revert lA lC. induction lB as [|b' lB]; try contradiction.
  intros lA lC HlenAB HlenBC Hbc.
  destruct lA as [|a' lA]; try discriminate.
  destruct lC as [|c' lC]; try discriminate.
  simpl in Hbc. destruct (eqdec (b', c') (b, c)) as [Heq|Hneq];
    [|destruct (in_dec eqdec (b, c) (zip pair lB lC)) as [Hin|Hnin]].
  - exists a'. injection Heq. intros Heqc Heqb. rewrite <- Heqc, <- Heqb.
    simpl. left. reflexivity.
  - simpl in HlenAB, HlenBC.
    injection HlenAB. intro HlenAB'.
    injection HlenBC. intro HlenBC'.
    destruct (IHlB lA lC) as [a Habc]; try assumption.
    exists a. simpl. right. assumption.
  - exfalso. destruct Hbc; contradiction.
Defined.

Lemma zip_pair_bij_fst_sig {A B : Type} {AED : EqDec A} (lA : list A) (lB : list B) :
  length lA = length lB -> forall a, a ∈ lA -> {p | p ∈ zip pair lA lB /\ fst p = a}.
Proof.
  intro H. pattern lA, lB. revert lA lB H. apply list_biind; try contradiction.
  intros a lA b lB IH a' Ha'.
  destruct (eqdec a a') as [Heqa|Hneqa];
    [|destruct (in_dec eqdec a' lA) as [Hin|Hnin]].
  - exists (a, b). simpl. tauto.
  - destruct (IH a' Hin) as [p Hp]. exists p. simpl. tauto.
  - exfalso. destruct Ha'; contradiction.
Qed.

Lemma zip_pair_bij_snd_sig {A B : Type} {BED : EqDec B} (lA : list A) (lB : list B) :
  length lA = length lB -> forall b, b ∈ lB -> {p | p ∈ zip pair lA lB /\ snd p = b}.
Proof.
  intro H. pattern lA, lB. revert lA lB H. apply list_biind; try contradiction.
  intros a lA b lB IH b' Hb'.
  destruct (eqdec b b') as [Heqb|Hneqb];
    [|destruct (in_dec eqdec b' lB) as [Hin|Hnin]].
  - exists (a, b). simpl. tauto.
  - destruct (IH b' Hin) as [p Hp]. exists p. simpl. tauto.
  - exfalso. destruct Hb'; contradiction.
Qed.
  
Lemma Forall_eq_zip_pair {A : Type} (l l' : list A) :
  length l = length l' -> Forall (fun xy => fst xy = snd xy) (zip pair l l') -> l = l'.
Proof.
  intro Hlen. pattern l, l'. revert l l' Hlen.
  apply list_biind; [reflexivity|].
  intros a l a' l' IH Hall. simpl in Hall.
  apply Forall_cons_iff in Hall. destruct Hall as [Ha Hl].
  simpl in Ha. rewrite Ha. apply f_equal.
  apply IH. assumption.
Qed.  

Lemma Forall_zip_pair_map_fst {A B C : Type} (R : C -> B -> Prop) (f : A -> C) (l : list A) (l' : list B) :
  Forall (fun xy => R (f (fst xy)) (snd xy)) (zip pair l l') ->
  Forall (fun xy => R (fst xy) (snd xy)) (zip pair (map f l) l').
Proof.
  revert l'. induction l; intros l' H; [|destruct l' as [|a' l']];
    try apply Forall_nil.
   simpl in H |- *. apply Forall_cons_iff in H.
   destruct H as [Ha Hl]. apply Forall_cons; try assumption.
   apply IHl. assumption.
Qed.   


Lemma zip_pair_in_map_23 {A B B1 B2 : Type} (f : B -> B1) (g : B -> B2) (lA : list A) (lB : list B) (a : A) (b : B) :
  (a, b) ∈ zip pair lA lB -> (a, f b, g b) ∈ zip pair (zip pair lA (map f lB)) (map g lB).
Proof.
  revert lA. induction lB as [|b' lB]; intro lA;
    [simpl; rewrite zip_nil_r; contradiction|].
  destruct lA as [|a' lA]; try contradiction.
  simpl. intros [H|H].
  - injection H. intros Heqb Heqa. left. rewrite Heqa, Heqb. reflexivity.
  - right. apply IHlB. assumption.
Qed.

Lemma zip_pair_map_in_23_inv {A B B1 B2 : Type} (f : B -> B1) (g : B -> B2) (lA : list A) (lB : list B) (a : A) (b1 : B1) (b2 : B2) :
  (a, b1, b2) ∈ zip pair (zip pair lA (map f lB)) (map g lB) ->
  exists b, b1 = f b /\ b2 = g b /\ (a, b) ∈ zip pair lA lB.
Proof.
  revert lA. induction lB as [|b lB]; intro lA;
    [simpl; rewrite zip_nil_r; contradiction|].
  destruct lA as [|a' lA]; try contradiction.
  simpl. intros [H|H].
  - injection H. intros Heqg Heqf Heqa. exists b.
    repeat split; try (apply eq_sym; assumption).
    left. rewrite Heqa. reflexivity.
  - specialize (IHlB lA H). destruct IHlB as [b' Hb'].
    exists b'. repeat split; tauto.
Qed.
  

Lemma fold_right_in_dec_incl_zip_pair_fst {A A' B C : Type} {EDA : EqDec A}
(op : B -> C -> C) (f g : A * A' -> B) (c0 : C) (l l0 : list A) (l' : list A') :
  l ⊆ l0 ->
  fold_right (fun x => op (if in_dec eqdec (fst x) l0 then f x else g x)) c0 (zip pair l l')
  = fold_right (fun x => op (if in_dec eqdec (fst x) l then f x else g x)) c0 (zip pair l l').
Proof.
  revert l0 l'. induction l; try reflexivity.
  intros l0 l' H.
  destruct l' as [|a' l']; try reflexivity. simpl zip.
  rewrite ! fold_right_cons_eq.
  rewrite ! in_if_in_dec_eq.
  rewrite IHl. rewrite <- (IHl (a :: l)). reflexivity.
  - apply incl_tl, incl_refl.
  - eapply incl_tran; try apply H. apply incl_tl, incl_refl.
  - now left.
  - apply H. now left.
Qed.

Lemma fold_right_in_dec_incl_zip_pair_snd {A A' B C : Type} {EDA : EqDec A'}
(op : B -> C -> C) (f g : A * A' -> B) (c0 : C) (l : list A) (l' l0 : list A') :
  l' ⊆ l0 ->
  fold_right (fun x => op (if in_dec eqdec (snd x) l0 then f x else g x)) c0 (zip pair l l')
  = fold_right (fun x => op (if in_dec eqdec (snd x) l' then f x else g x)) c0 (zip pair l l').
Proof.
  revert l0 l. induction l' as [|a' l' IHl'];
    try (intros; rewrite zip_nil_r; reflexivity).
  intros l0 l H.
  destruct l as [|a l]; try reflexivity. simpl zip.
  rewrite ! fold_right_cons_eq.
  rewrite ! in_if_in_dec_eq.
  rewrite IHl'. rewrite <- (IHl' (a' :: l')). reflexivity.
  - apply incl_tl, incl_refl.
  - eapply incl_tran; try apply H. apply incl_tl, incl_refl.
  - now left.
  - apply H. now left.
Qed.

Lemma fold_right_in_dec_zip_pair_fst {A A' B C : Type} {EDA : EqDec A}
(op : B -> C -> C) (f g : A * A' -> B) (c0 : C) (l : list A) (l' : list A') :
  fold_right (fun x => op (if (in_dec eqdec (fst x) l) then f x else g x)) c0 (zip pair l l')
  = fold_right (fun x => op (f x)) c0 (zip pair l l').
Proof.
  revert l'. induction l; try reflexivity.
  destruct l' as [|a' l']; try reflexivity. simpl zip.
  rewrite fold_right_cons_eq.
  rewrite fold_right_in_dec_incl_zip_pair_fst.
  rewrite IHl. rewrite in_if_in_dec_eq. reflexivity.
  - now left.
  - apply incl_tl, incl_refl.
Qed.

Lemma fold_right_in_dec_zip_pair_snd {A A' B C : Type} {EDA : EqDec A'}
(op : B -> C -> C) (f g : A * A' -> B) (c0 : C) (l : list A) (l' : list A') :
  fold_right (fun x => op (if (in_dec eqdec (snd x) l') then f x else g x)) c0 (zip pair l l')
  = fold_right (fun x => op (f x)) c0 (zip pair l l').
Proof.
  revert l'. induction l; try reflexivity.
  destruct l' as [|a' l']; try reflexivity. simpl zip.
  rewrite fold_right_cons_eq.
  rewrite fold_right_in_dec_incl_zip_pair_snd.
  rewrite IHl. rewrite in_if_in_dec_eq. reflexivity.
  - now left.
  - apply incl_tl, incl_refl.
Qed.

Lemma union_in_dec_zip_pair_fst {A A' B : Type} {EDA : EqDec A}
  (f g : A * A' -> list B) (l : list A) (l' : list A') :
  list_union (zip pair l l') (fun x => if in_dec eqdec (fst x) l then f x else g x)
  = list_union (zip pair l l') f.
Proof. apply fold_right_in_dec_zip_pair_fst. Qed.

Lemma union_in_dec_zip_pair_snd {A A' B : Type} {EDA' : EqDec A'}
  (f g : A * A' -> list B) (l : list A) (l' : list A') :
  list_union (zip pair l l') (fun x => if in_dec eqdec (snd x) l' then f x else g x)
  = list_union (zip pair l l') f.
Proof. apply fold_right_in_dec_zip_pair_snd. Qed.

Lemma map_fst_zip_pair {A B : Type} (l : list A) (l' : list B) :
  length l = length l' -> map fst (zip pair l l') = l.
Proof.
  revert l'. induction l; try reflexivity.
  intros l' Hlen. destruct l' as [|a' l']; try discriminate.
  simpl. apply f_equal. apply IHl.
  simpl in Hlen. injection Hlen. tauto.
Qed.

Definition distinct_all {A : Type} (ll : list (list A)) :=
  NoDupA (fun l l' => exists x, x ∈ l /\ x ∈ l') ll.

Lemma NoDup_union_distinct {A B : Type} (l : list A) (f : A -> list B) :
  NoDup (list_union l f) -> distinct_all (map f l).
Proof.
  intro H. induction l; [apply NoDupA_nil|].
  simpl. apply NoDupA_cons.
  - simpl in H. apply NoDup_app_distinct in H.
    intro Hctr. apply InA_alt in Hctr.
    destruct Hctr as [l' [[b [Hin1 Hin2]] Hinl']].
    apply (H _ Hin1). rewrite union_map.
    apply In_union_iff. exists l'. tauto.
  - apply IHl. simpl in H. apply NoDup_app_remove_l in H.
    assumption.
Qed.

Lemma union_empty {A B : Type} (l : list A) (f : A -> list B) (a : A) :
  a ∈ l -> list_union l f = [] -> f a = [].
Proof.
  induction l as [|a' l]; try contradiction.
  intros Ha H. simpl in H. apply app_eq_nil in H. destruct Ha as [Ha|Ha].
  - rewrite Ha in H. tauto.
  - apply IHl; tauto.
Qed.

Lemma NoDup_union {A B : Type} (l : list A) (f : A -> list B) (a : A) :
  a ∈ l -> NoDup (list_union l f) -> NoDup (f a).
Proof.
  intros Ha HND. induction l as [|a' l]; try contradiction.
  destruct Ha as [Ha|Ha].
  - rewrite Ha in HND. simpl in HND.
    apply NoDup_app_remove_r in HND.
    assumption.
  - simpl in HND. apply NoDup_app_remove_l in HND.
    apply IHl; assumption.
Qed.

Close Scope nat_scope.

Section ForallMore'.

  Context {A : Type}.
  Context `{AED : EqDec A}.
  
  Lemma ForallT_dec_E {P Q : A -> Type} (l : list A) :
    ForallT (fun x => P x + Q x) l -> ExistsT P l + ForallT Q l.
  Proof.
    intros Hdec. induction l; try (right; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdeca.
    pose proof (ForallT_inv_tail Hdec) as Hdecl.
    specialize (IHl Hdecl). destruct Hdeca as [HPa|HQa].
    - left. constructor 1. assumption.
    - destruct IHl as [HPl|HQl].
      + left. constructor; assumption.
      + right. constructor 2; assumption.
  Defined.

  Lemma ForallT_dec_F {P Q : A -> Type} (l : list A) :
    ForallT (fun x => P x + Q x) l -> ForallT P l + ExistsT Q l.
  Proof.
    intros Hdec. induction l; try (left; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdeca.
    pose proof (ForallT_inv_tail Hdec) as Hdecl.
    specialize (IHl Hdecl). destruct Hdeca as [HPa|HQa].
    - destruct IHl as [HPl|HQl].
      + left. constructor; assumption.
      + right. constructor 2. assumption.
    - right. constructor 1. assumption.
  Defined.

  Lemma ForallT_dec_EF {P Q : A -> Type} (ll : list (list A)) :
    ForallT (ForallT (fun x => P x + Q x)) ll ->
      ExistsT (ForallT P) ll + ForallT (ExistsT Q) ll.
  Proof.
    intros Hdec. induction ll as [|l ll]; try (right; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdecl.
    pose proof (ForallT_inv_tail Hdec) as Hdecll.
    specialize (IHll Hdecll). destruct (ForallT_dec_F l Hdecl) as [HPl|HQl].
    - left. constructor 1. assumption.
    - destruct IHll as [HPll|HQll].
      + left. constructor 2. assumption.
      + right. constructor; assumption.
  Defined.

  Lemma ForallT_dec_EEF {P Q : A -> Type} (lll : list (list (list A))) :
    ForallT (ForallT (ForallT (fun x => P x + Q x))) lll ->
      ExistsT (ExistsT (ForallT P)) lll +
      ForallT (ForallT (ExistsT Q)) lll.
  Proof.
    intros Hdec. induction lll as [|ll lll]; try (right; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdecll.
    pose proof (ForallT_inv_tail Hdec) as Hdeclll.
    specialize (IHlll Hdeclll). destruct (ForallT_dec_EF ll Hdecll) as [HPll|HQll].
    - left. constructor 1. assumption.
    - destruct IHlll as [HPlll|HQlll].
      + left. constructor 2. assumption.
      + right. constructor; assumption.
  Defined.

  
  Lemma ForallT_dec_E_sumbool {P Q : A -> Prop} (l : list A) :
    ForallT (fun x => {P x} + {Q x}) l -> ExistsT P l + ForallT Q l.
  Proof.
    intros Hdec. induction l; try (right; constructor; fail).
    pose proof (ForallT_inv Hdec) as Hdeca.
    pose proof (ForallT_inv_tail Hdec) as Hdecl.
    specialize (IHl Hdecl). destruct Hdeca as [HPa|HQa].
    - left. constructor 1. assumption.
    - destruct IHl as [HPl|HQl].
      + left. constructor; assumption.
      + right. constructor 2; assumption.
  Defined.

End ForallMore'.


Lemma Forall2_sig_r {A B} `{BED : EqDec B} {R : B -> A -> Prop} {l : list B} {l' : list A} :
  Forall2 R l l' -> forall x, List.In x l -> {x' | List.In x' l' /\ R x x'}.
Proof.
  intro H. apply Forall2_flip in H. apply Forall2_sig_l; assumption.
Defined.


Lemma ForallT_map : forall [A B : Type] (f : A -> B) (P : B -> Type) (l : list A),
    ForallT P (map f l) <+> ForallT (fun x : A => P (f x)) l.
Proof.
  intros A B f P l. split.
  - intro H. induction l; constructor; inversion H; try assumption.
    apply IHl. assumption.
  - intro H. induction H; constructor; assumption.
Defined.


Lemma all_msets_len {A : Type} (la : list A) (n : nat) :
  {ls | forall l, In l ls <-> length l = n /\ incl l la}.
Proof.
  induction n.
  - exists [[]]. intro l. split.
    + intro H. destruct H; try contradiction. rewrite <- H.
      split; [reflexivity | apply incl_nil_l].
    + intros [H _]. apply length_zero_iff_nil in H. now left.
  - destruct IHn as [ls Hls].
    exists (fold_right (fun l => app (map (fun x => x :: l) la)) [] ls). intro l. split.
    + intro H. destruct (In_fold_right_app H) as [l' [Hinl' Hinl]].
      rewrite in_map_iff in Hinl. destruct Hinl as [x [Heql Hinx]].
      specialize (Hls l'). destruct Hls as [Hls _]. specialize (Hls Hinl').
      destruct Hls as [Hlenl' Hincl']. rewrite <- Heql. split.
      * simpl. rewrite Hlenl'. reflexivity.
      * intros x0 Hx0. destruct Hx0 as [Hx0|Hx0]; try (now rewrite <- Hx0).
        apply Hincl'. assumption.
    + intros [Hlenl Hincl]. apply In_fold_right_app_iff.
      destruct l; try (simpl in Hlenl; discriminate).
      exists l. split.
      * apply Hls. simpl in Hlenl. split; try lia.
        eapply incl_tran; try apply Hincl. apply incl_tl, incl_refl.
      * rewrite in_map_iff. exists a. split; try reflexivity. apply Hincl. now left.
Defined.




(* Tactics on lists *)

Ltac specialize_Forall_H HF :=
  match type of HF with
  | Forall _ [] => clear HF
  | _ =>
      apply Forall_cons_iff in HF;
      match type of HF with
      | _ /\ Forall _ _ =>
          let H := fresh HF in destruct HF as [H HF]; specialize_Forall_H HF
      | _ => idtac
      end
  end.

Ltac specialize_Forall :=
  match goal with
  | [ HF : Forall _ _ |- _ ] => specialize_Forall_H HF
  end.

Ltac specialize_ForallT_H HF :=
  match type of HF with
  | ForallT _ [] => clear HF
  | _ =>
      let H := fresh HF in
      pose proof (ForallT_inv HF) as H;
      apply ForallT_inv_tail in HF;
      specialize_ForallT_H HF
  end.

Ltac specialize_list :=
  match goal with
  | Hall : forall x, List.In x _ -> _ |- _ => rewrite <- Forall_forall in Hall; specialize_Forall_H Hall
  end.


Ltac specialize_Forall2_H HF2 :=
  match type of HF2 with
  | Forall2 _ [] [] => clear HF2
  | _ =>
      apply Forall2_cons_iff in HF2;
      match type of HF2 with
      | _ /\ Forall2 _ _ _ =>
          let H := fresh in destruct HF2 as [H HF2]; specialize_Forall2_H HF2
      | _ => idtac
      end
  end.

Ltac NoDup_two :=
  let H := fresh in 
  apply NoDup_cons; [|apply NoDup_single];
  simpl; intros [H|H]; [discriminate|assumption].


Theorem not_and_iff_or_not [A B : Prop] : Decidable.decidable A -> ~ (A /\ B) <-> ~ A \/ ~ B.
Proof. intro dec. split; [now apply not_and | tauto]. Qed.


Lemma Some_eq_iff {A : Type} {x y : A} : Some x = Some y <-> x = y.
Proof.
  split.
  - intro H. injection H. tauto.
  - intro H. rewrite H. reflexivity.
Qed.


Lemma comp_disjunct {A : Type} {P : A -> Type} (Aeq_dec : eq_dec A) (a b : A) :
  P a -> P b -> forall x, x = a \/ x = b -> P x.
Proof.
  intros Pa Pb x Hx.
  destruct (Aeq_dec x a) as [Heq1|Hneq1];
    destruct (Aeq_dec x b) as [Heq2|Hneq2];
    try ((rewrite Heq1 || rewrite Heq2); assumption).
  simpl in Hx. exfalso. tauto.
Qed.

Lemma list_1_eq_iff {A : Type} {a b : A} : [a] = [b] <-> a = b.
Proof.
  split. intro H. now injection H. intro H. now rewrite H.
Qed.


Lemma eqb_swap_negb : forall b1 b2, eqb (negb b1) b2 = eqb b1 (negb b2).
Proof.
  intros b1 b2. destruct b1; destruct b2; reflexivity.
Qed.

Lemma eqb_true_r : forall b, eqb b true = b.
Proof.
  intro b. destruct b; reflexivity.
Qed.

Lemma eq_sym_iff {A : Type} : forall x y : A, x = y <-> y = x.
Proof. split; apply eq_sym; assumption. Qed.
