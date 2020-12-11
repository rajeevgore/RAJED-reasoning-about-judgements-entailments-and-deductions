

(* Reflexive_Transitive_Closure stuff, using Type rather than Prop *)

Set Implicit Arguments.
Require Import List.
Import ListNotations.

Add LoadPath "../tense-lns".
Require Import gen genT.

(* compare 
  https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html
  https://coq.inria.fr/stdlib/Coq.Relations.Relation_Operators.html
  https://coq.inria.fr/stdlib/Coq.Relations.Operators_Properties.html
  Require Import Coq.Relations.Relation_Definitions.
  Require Import Coq.Relations.Relation_Operators.
  Require Import Coq.Relations.Operators_Properties.  
  Print Module Relation_Definitions.
  Print Module Relation_Operators.
  Print Module Operators_Properties.  
  *)
(* this in genT.v in ../lnt/tense-logic-in-Coq 
Definition relationT (A : Type) := A -> A -> Type.
*)

Definition transitiveT W (R : relationT W) :=
  forall (x y z : W), R x y -> R y z -> R x z.
Check transitiveT.

(* see https://coq.inria.fr/stdlib/Coq.Relations.Relation_Operators.html *)
Section Transitive_Closure.
  Variable A : Type.
  Variable R : relationT A.

(* Definition by direct transitive closure *)

  Inductive clos_transT (x: A) : A -> Type :=
    | tT_step (y:A) : R x y -> clos_transT x y
    | tT_trans (y z:A) : clos_transT x y -> clos_transT y z -> clos_transT x z.

(* Alternative definition by transitive extension on the left *)

  Inductive clos_transT_1n (x: A) : A -> Type :=
    | t1nT_step (y:A) : R x y -> clos_transT_1n x y
    | t1nT_trans (y z:A) : R x y -> clos_transT_1n y z -> clos_transT_1n x z.

(* Alternative definition by transitive extension on the right *)

  Inductive clos_transT_n1 (x: A) : A -> Type :=
    | tn1T_step (y:A) : R x y -> clos_transT_n1 x y
    | tn1T_trans (y z:A) : R y z -> clos_transT_n1 x y -> clos_transT_n1 x z.

End Transitive_Closure.

Section Reflexive_ClosureT.
  Variable A : Type.
  Variable R : relationT A.

Inductive clos_reflT (x: A) : A -> Type :=
  | rT_step (y:A) : R x y -> clos_reflT x y
  | rT_refl : clos_reflT x x.

End Reflexive_ClosureT.

Section Reflexive_Transitive_ClosureT.
  Variable A : Type.
  Variable R : relationT A.

Inductive clos_refl_transT (x:A) : A -> Type :=
  | rtT_step (y:A) : R x y -> clos_refl_transT x y
  | rtT_refl : clos_refl_transT x x
  | rtT_trans (y z:A) :
	clos_refl_transT x y -> clos_refl_transT y z -> clos_refl_transT x z.

(* Alternative definition by transitive extension on the left/right *)

Inductive clos_refl_transT_1n (x: A) : A -> Type :=
  | rt1nT_refl : clos_refl_transT_1n x x
  | rt1nT_trans (y z:A) :
       R x y -> clos_refl_transT_1n y z -> clos_refl_transT_1n x z.

Inductive clos_refl_transT_n1 (x: A) : A -> Type :=
  | rtn1T_refl : clos_refl_transT_n1 x x
  | rtn1T_trans (y z:A) :
      R y z -> clos_refl_transT_n1 x y -> clos_refl_transT_n1 x z.

End Reflexive_Transitive_ClosureT.

(* equivalences between above, need to reprove for ...T *)
Lemma clos_rt1n_rtT : forall A R (x y : A),
  clos_refl_transT_1n R x y -> clos_refl_transT R x y.
Proof. intros. induction X. apply rtT_refl.
eapply rtT_trans. apply rtT_step. eassumption. eassumption. Qed.

Lemma clos_rt_rt1nT : forall A R (x y : A),
  clos_refl_transT R x y -> clos_refl_transT_1n R x y.
Proof. intros. induction X. 
eapply rt1nT_trans. eassumption. apply rt1nT_refl.
apply rt1nT_refl. 
clear X1 X2.  induction IHX1. assumption.
apply IHIHX1 in IHX2. eapply rt1nT_trans ; eassumption. Qed.

Lemma clos_rtn1_rtT : forall A R (x y : A),
  clos_refl_transT_n1 R x y -> clos_refl_transT R x y.
Proof. intros. induction X.  apply rtT_refl.
eapply rtT_trans. eassumption. apply rtT_step. eassumption.  Qed.

Lemma clos_rt_rtn1T : forall A R (x y : A),
  clos_refl_transT R x y -> clos_refl_transT_n1 R x y.
Proof. intros. induction X. 
eapply rtn1T_trans. eassumption. apply rtn1T_refl.
apply rtn1T_refl. 
clear X1 X2.  induction IHX2. assumption.
eapply rtn1T_trans ; eassumption. Qed.

(*
Lemma clos_rt_rt1n_iffT : forall A R (x y : A),
  clos_refl_transT R x y <-> clos_refl_transT_1n R x y.

Lemma clos_rt_rtn1_iffT : forall A R (x y : A),
  clos_refl_transT R x y <-> clos_refl_transT_n1 R x y.
*)

(* equivalences between above, need to reprove for ...T *)
Lemma clos_t1n_tT : forall A R (x y : A),
  clos_transT_1n R x y -> clos_transT R x y.
Proof. intros. induction X. apply tT_step. assumption.
eapply tT_trans. apply tT_step. eassumption. eassumption. Qed.

Lemma clos_t_t1nT : forall A R (x y : A),
  clos_transT R x y -> clos_transT_1n R x y.
Proof. intros. induction X. 
eapply t1nT_step. eassumption.
clear X1 X2.  induction IHX1.
eapply t1nT_trans ; eassumption.
eapply t1nT_trans. eassumption.
apply IHIHX1.  apply IHX2. Qed.

Lemma clos_tn1_tT : forall A R (x y : A),
  clos_transT_n1 R x y -> clos_transT R x y.
Proof. intros. induction X.  apply tT_step. assumption.
eapply tT_trans. eassumption. apply tT_step. eassumption.  Qed.

Lemma clos_t_tn1T : forall A R (x y : A),
  clos_transT R x y -> clos_transT_n1 R x y.
Proof. intros. induction X. 
eapply tn1T_step. eassumption. 
clear X1 X2.  induction IHX2.
eapply tn1T_trans ; eassumption.
eapply tn1T_trans. eassumption.
apply IHIHX2. Qed.

(*
Lemma clos_t_t1n_iffT : forall A R (x y : A),
  clos_transT R x y <-> clos_transT_1n R x y.

Lemma clos_t_tn1_iffT : forall A R (x y : A),
  clos_transT R x y <-> clos_transT_n1 R x y.
*)

Lemma clos_transT_mono U R S : 
  @rsub U U R S -> rsub (clos_transT R) (clos_transT S).
Proof. intros rs u v ctr. induction ctr.
- apply tT_step.  exact (rs x y r).
- eapply tT_trans ; eassumption. Qed.

Lemma clos_transT_measure U f : rsub (clos_transT (measure f)) (@measure U f).
Proof. intros u v ctm. induction ctm. exact r.
exact (Lt.lt_trans _ _ _ IHctm1 IHctm2). Qed.

(* AccT for Transitive_Closure *)
Lemma AccT_tc_n1 A R (x : A) : AccT R x -> AccT (clos_transT_n1 R) x.
Proof. intro a. induction a.
apply AccT_intro. intros y crxy.
destruct crxy. exact (X y r).
apply X in r.  inversion r.  exact (X0 y crxy). Qed.

Lemma AccT_tc A R (x : A) : AccT R x -> AccT (clos_transT R) x.
Proof. intro a. apply AccT_tc_n1 in a.
induction a. clear a.
apply AccT_intro. intros y crxy.  apply X.
apply clos_t_tn1T. exact crxy. Qed.


