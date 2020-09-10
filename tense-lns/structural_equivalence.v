Require Import List.
Export ListNotations.

Require Import gen_tacs lntT List_lemmasT.
Require Import existsT.
Require Import contractedT.
Require Import Coq.Classes.CRelationClasses.

Ltac clear_useless :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         | [H : [?a] = [?a] |- _] => clear H
         | [H : ?a :: ?b = ?a :: ?b |- _] => clear H
         | [H1 : ?a, H2 : ?a |- _] => clear H2
         end.

Ltac inversion_cons :=
  repeat match goal with
         | [ H : ?a :: ?l1 = ?b :: ?l2 |- _] => inversion H; subst; clear_useless
         end.

(* Use this one to help with full structural equivalence definition. *)
Inductive struct_equiv_str {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type :=
| se_nil2 : struct_equiv_str [] []
| se_step2 Γ1 Δ1 d Γ2 Δ2 ns1 ns2 ns3 ns4 :
    ns3 = ((Γ1, Δ1, d) :: ns1) ->
    ns4 = ((Γ2, Δ2, d) :: ns2) ->
    struct_equiv_str ns1 ns2 ->
    struct_equiv_str ns3 ns4.

(* Use this one for structural equivalence. *)
Inductive struct_equiv_weak {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type :=
| se_wk2_extL ns1 ns2 ns3 ns4 :
    ns4 = (ns1 ++ ns3) -> struct_equiv_str ns1 ns2 -> struct_equiv_weak ns4 ns2
| se_wk2_extR ns1 ns2 ns3 ns4 :
    ns4 = (ns2 ++ ns3) -> struct_equiv_str ns1 ns2 -> struct_equiv_weak ns1 ns4.

Inductive struct_equiv {V : Set} n1 n2 : Type :=
| se : @struct_equiv_weak V n1 n2 -> struct_equiv n1 n2.

Lemma struct_equiv_str_weak : forall {V : Set} G1 G2,
   @struct_equiv_str V G1 G2 -> @struct_equiv_weak V G1 G2.
Proof.
  intros V G1 G2 H.
  eapply se_wk2_extL in H. 2 : reflexivity.
  erewrite app_nil_r in H.  exact H.
Qed.

Lemma struct_equiv_str_length : forall {V : Set} G1 G2,
    @struct_equiv_str V G1 G2 -> length G1 = length G2.
Proof.
  induction G1; intros H2 H; destruct H2;
    subst; (reflexivity || inversion H).
  discriminate. discriminate. 
  subst. simpl. erewrite IHG1. reflexivity.
  inversion H1. inversion H0. subst.
  assumption.
Qed.

Lemma struct_equiv_weak_str : forall {V : Set} G1 G2,
    @struct_equiv_weak V G1 G2 -> length G1 = length G2 ->
    @struct_equiv_str V G1 G2.
Proof.
  intros V G1 G2 H1 H2.
  inversion H1; subst;
    rewrite app_length in H2.
  inversion H0; subst. simpl in *.
  apply length_zero_iff_nil in H2. subst.
  constructor.
  simpl; pose proof H4 as H4';
  eapply struct_equiv_str_length in H4;
  simpl in H2; rewrite H4 in H2;
  destruct ns3; simpl in *; [
  rewrite app_nil_r;  econstructor; try reflexivity; try assumption |
  firstorder ].

  inversion H0; subst. simpl in *.
  symmetry in H2.
  apply length_zero_iff_nil in H2. subst.
  constructor.
  simpl; pose proof H4 as H4';
  eapply struct_equiv_str_length in H4;
  simpl in H2; rewrite H4 in H2;
  destruct ns3; simpl in *; [
  rewrite app_nil_r;  econstructor; try reflexivity; try assumption |
  firstorder ].
Qed.

Lemma struct_equiv_weak_cons : forall {V : Set} l1 l2 a1 a2,
    struct_equiv_weak (a1::l1) (a2::l2) ->
    @struct_equiv_weak V l1 l2.
Proof.
  intros V l1 l2 a1 a2 H3.
  inversion H3 as [l3 H4 l4 H5 H6 H7 | H4 l3 l4 H5 H6 H7]; subst.
  destruct l3 as [| a ns1];
    inversion H7; try discriminate; subst.
  simpl in *. unfold rel in *.
  inversion_cons.
  econstructor. reflexivity. assumption.

  destruct l3 as [| a ns1];
    inversion H7; try discriminate; subst.
  simpl in *. unfold rel in *.
  inversion_cons.
  econstructor 2. reflexivity. assumption.
Qed.

Lemma struct_equiv_weak_cons_rev : forall {V : Set} l1 l2 a1 a2 b1 b2 d,
    @struct_equiv_weak V l1 l2 ->
    struct_equiv_weak ((a1,b1,d)::l1) ((a2,b2,d)::l2).
Proof.
  intros V l1 l2 a1 a2 b1 b2 d H3.
  inversion H3; subst.
  econstructor.
  rewrite cons_singleton. rewrite app_assoc.
  reflexivity.
  econstructor 2; try reflexivity. assumption.

  econstructor 2.  rewrite cons_singleton. rewrite app_assoc.
  reflexivity.
  econstructor 2; try reflexivity. assumption.
Qed.

Ltac struct_equiv_str_nil :=
  match goal with
  | [H : struct_equiv_str [] ?n |- _] => inversion H; discriminate
  | [H : struct_equiv_str ?n [] |- _] => inversion H; discriminate
  end.

Ltac struct_equiv_str_cons :=
  match goal with
  | [H : struct_equiv_str (?a :: ?la) (?b :: ?lb) |- _] => inversion H; subst
  end.

Lemma struct_equiv_weak_d : forall {V : Set} ns1 ns2 seq1 seq2 d1 d2,
    @struct_equiv_weak V ((seq1,d1)::ns1) ((seq2,d2)::ns2) ->
    d1 = d2.
Proof.
  intros until 0; intros H3.
  inversion H3 as [l3 H4 l4 H5 H6 H7 | H4 l3 l4 H5 H6 H7]; subst. 
  destruct l3. simpl in *.
  struct_equiv_str_nil.
  simpl in *.
  inversion_cons.
  struct_equiv_str_cons. 
  unfold rel in *. inversion_cons.
  reflexivity.
  
  destruct l3. simpl in *.
  struct_equiv_str_nil.
  simpl in *.
  inversion_cons.
  struct_equiv_str_cons. 
  unfold rel in *. inversion_cons.
  reflexivity.
Qed.  

Lemma struct_equiv_str_weak_equiv : forall {V : Set} G1 G2,
    iffT (@struct_equiv_str V G1 G2)
         (struct_equiv_weak G1 G2 * (length G1 = length G2)).
Proof.
  intros.
  split; intros HH. split. apply struct_equiv_str_weak.
  assumption. apply struct_equiv_str_length. assumption.
  apply struct_equiv_weak_str; apply HH.
Qed.

Lemma struct_equiv_weak_nil : forall (V : Set),
    @struct_equiv_weak V nil nil.
Proof.
  econstructor. erewrite app_nil_r.
  reflexivity. econstructor.
Qed.
  
Lemma struct_equiv_str_refl : forall {V : Set} G, @struct_equiv_str V G G.
Proof.
  induction G as [|a G IHG]. constructor.
  destruct a as [ [Γ Δ] d].
  econstructor 2. reflexivity.
  reflexivity. assumption.
Qed.

Lemma struct_equiv_weak_refl : forall {V : Set} G,
    @struct_equiv_weak V G G.
Proof.
  intros V G. econstructor.
  erewrite app_nil_r. reflexivity.
  apply struct_equiv_str_refl.
Qed.
