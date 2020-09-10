Require Export List.
Require Import Omega.

Set Implicit Arguments.
Export ListNotations.

Delimit Scope My_scope with M.
Open Scope My_scope.

Parameter PropVars : Set.
Hypothesis Varseq_dec : forall x y:PropVars, {x = y} + {x <> y}.

(** * Definitions

definition of Propositional Formulas*)
Inductive PropF : Set :=
 | Var  : PropVars -> PropF
 | Bot  : PropF
 | Impl : PropF -> PropF -> PropF
 | WBox : PropF -> PropF
 | BBox : PropF -> PropF.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Impl A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.
Notation "[.] A" := (WBox A) (at level 10) : My_scope.
Notation "[#] A" := (BBox A) (at level 10) : My_scope.

(** Defined connectives *)
Notation "¬ A" := (A → ⊥) (at level 11)  : My_scope.
Notation "A ∧ B" := ((A → (B → ⊥)) → ⊥) (at level 15, right associativity) : My_scope.
Notation "A ∨ B" := ((A → ⊥) → B) (at level 15, right associativity) : My_scope.
Notation "<.> A" := (¬ [.] ¬ A) (at level 10) : My_scope.
Notation "<#> A" := (¬ [#] ¬ A) (at level 10) : My_scope.


(** Decideability of PropF *)
Lemma PropF_dec : forall a b : PropF,
    {a = b} + {~a = b}.
Proof.
  induction a; intros b; destruct b;
    try (right; intros H; discriminate H).
  - destruct (Varseq_dec p p0) as [H | H].
    left. rewrite H. reflexivity.
    right. intros H2. inversion H2 as [H3].
    rewrite H3 in *.
    contradiction (H eq_refl).
  -  left. reflexivity.
  - destruct (IHa1 b1) as [IH1 | IH1].
    destruct (IHa2 b2) as [IH2 | IH2].
    rewrite IH1. rewrite IH2.
    left. reflexivity.
    right. intros H.
    rewrite IH1 in H.
    inversion H as [H2].
    contradiction (IH2 H2).
    right. intros H.
    inversion H as [[H1 H2]].
    contradiction (IH1 H1).
  - destruct (IHa b) as [IH1 | IH2].
    rewrite IH1. left. reflexivity.
    right. intros H. inversion H.
    subst. contradiction (IH2 eq_refl).
  - destruct (IHa b) as [IH1 | IH2].
    rewrite IH1. left. reflexivity.
    right. intros H. inversion H.
    subst. contradiction (IH2 eq_refl).        
Qed.


(* Insert semantics here... *)