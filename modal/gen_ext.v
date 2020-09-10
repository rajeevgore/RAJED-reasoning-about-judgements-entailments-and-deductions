
Require Export List.
Export ListNotations.  
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../tense-lns".
Require Import gen. 
Require Import genT.
Require Import gen_tacs.
Require Import gen_seq.

(* generalised extension *)
Inductive gen_ext W : relationT (list W) := 
  | gen_ext_nil : gen_ext [] []
  | gen_ext_cons : forall x l le, gen_ext l le -> gen_ext (x :: l) (x :: le)
  | gen_ext_extra : forall x l le, gen_ext l le -> gen_ext l (x :: le)
  .
  
Lemma gen_ext_refl: forall W (l : list W), gen_ext l l.
Proof. induction l. apply gen_ext_nil. apply gen_ext_cons. exact IHl. Qed.

Lemma gen_ext_appL: forall W (xs ys zs : list W),
  gen_ext xs ys -> gen_ext xs (zs ++ ys).
Proof. induction zs. tauto.  intros. apply gen_ext_extra. tauto. Qed.

Lemma gen_ext_appR: forall W (xs ys zs : list W),
  gen_ext xs ys -> gen_ext xs (ys ++ zs).
Proof. intros. induction X. 
induction zs. apply gen_ext_nil. apply gen_ext_extra. assumption.
simpl. apply gen_ext_cons. assumption.
simpl. apply gen_ext_extra. assumption. Qed.

Definition gen_ext_appL' W xs ys := gen_ext_appL ys (@gen_ext_refl W xs).
Definition gen_ext_appR' W xs ys := gen_ext_appR ys (@gen_ext_refl W xs).

Lemma gen_ext_nil_any: forall W (xs : list W), gen_ext [] xs.
Proof. induction xs. apply gen_ext_nil. apply gen_ext_extra. tauto. Qed. 

Lemma gen_ext_trans: forall W (ys zs : list W),
  gen_ext ys zs -> forall xs, gen_ext xs ys -> gen_ext xs zs.
Proof. intros until 1. induction X. tauto.
intros. inversion X0. subst. apply gen_ext_cons. firstorder.
subst. apply gen_ext_extra. firstorder.
intros. apply gen_ext_extra. firstorder.  Qed.

Lemma gen_ext_app: forall W (ys zs : list W),
  gen_ext ys zs -> forall us vs, gen_ext us vs -> gen_ext (us ++ ys) (vs ++ zs).
Proof. intros. induction X0 ; simpl. exact X.
apply gen_ext_cons. assumption.
apply gen_ext_extra. assumption. Qed.  

Definition gen_ext_sameL W xs ys zs ge :=
  @gen_ext_app W ys zs ge xs xs (@gen_ext_refl W xs).
Definition gen_ext_sameR W xs ys zs ge :=
  @gen_ext_app W xs xs (@gen_ext_refl W xs) ys zs ge.

Lemma gen_ext_lem: forall A (x : A) Z Y,
  gen_ext (x :: Z) Y -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ x :: Y2) (gen_ext Z Y2))). 
Proof.  intros A x Z. induction Y.
intro. inversion X. intro. inversion X ; subst.
exists []. exists Y. simpl. tauto.
apply IHY in X0. cD. subst.
exists (a :: X0). exists X1. simpl. tauto. Qed.

Lemma gen_ext_splitL: forall A Z2 Z1 Y,
  gen_ext (Z1 ++ Z2 : list A) Y -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ Y2) (prod (gen_ext Z1 Y1) (gen_ext Z2 Y2)))). 
Proof. intros A Z2. induction Z1 ; simpl.
exists []. exists Y. simpl. split. trivial. 
split. apply gen_ext_nil. trivial.
intro. intro. apply gen_ext_lem in X. cD. subst. 
apply IHZ1 in X2. cD. subst.
exists (X ++ a :: X2). exists X1. 
split. rewrite app_comm_cons. rewrite app_assoc. trivial.
split. apply gen_ext_appL. apply gen_ext_cons. assumption. assumption. Qed.

Lemma gen_ext_splitR: forall A Z2 Z1 Y,
  gen_ext Y (Z1 ++ Z2 : list A) -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ Y2) (prod (gen_ext Y1 Z1) (gen_ext Y2 Z2)))). 
Proof. intros A Z2. induction Z1 ; simpl. 
exists []. exists Y. simpl. split. trivial. 
split. apply gen_ext_nil. trivial.
intro. intro. inversion X ; subst.
apply IHZ1 in X0. cD. subst.
exists (a :: X0). exists X1. simpl. split. trivial.
split. apply gen_ext_cons.  assumption. assumption.
apply IHZ1 in X0. cD. subst.
exists X0. exists X1. split. trivial.
split. apply gen_ext_extra.  assumption. assumption. Qed.

Lemma gen_ext_single: forall A (l : list A), sing_empty l ->
  forall Y Z le, gen_ext (Z ++ l ++ Y) le -> sigT (fun Ze => sigT (fun Ye =>
    prod (prod (gen_ext Z Ze) (gen_ext Y Ye)) (le = Ze ++ l ++ Ye))).
Proof. intros A l es Y.  destruct es ; simpl ; intros.
apply gen_ext_splitL in X. cD. subst. firstorder.
apply gen_ext_splitL in X. cD.
apply gen_ext_lem in X3. cD. subst.
exists (X ++ X3). exists X4.
split. split.  apply gen_ext_appR. assumption. assumption.
rewrite app_assoc. trivial. Qed.

Check gen_ext_splitL.  Check gen_ext_splitR.
Check gen_ext_lem.  Check gen_ext_single.

Lemma gen_ext_one': forall A (x : A) (xs l : list A),
  xs = [x] -> gen_ext xs l -> InT x l.
Proof. intros. induction X.
- discriminate H. 
- injection H as . subst. apply InT_eq.
- apply InT_cons. apply (IHX H). Qed.

Definition gen_ext_one A x l := @gen_ext_one' A x [x] l eq_refl.
(* and note result InT_split *)

Check gen_ext_one.

Lemma InT_gen_ext A x l: InT x l -> gen_ext [x : A] l.
Proof. intros. apply InT_split in X. cD. subst.
apply gen_ext_appL.  apply gen_ext_cons.  apply gen_ext_nil_any. Qed.

Lemma gen_ext_InT A (x : A) l m: gen_ext l m -> InT x l -> InT x m.
Proof. intro ge. induction ge. tauto.
intro. inversion X ; subst. apply InT_eq.
apply InT_cons. exact (IHge X0).
intro. apply InT_cons. exact (IHge X). Qed.

Lemma gen_ext_diff' V X r : gen_ext X r -> forall (y : V) Y Z,
    r = (Y ++ y :: Z) -> InT y X + gen_ext X (Y ++ Z). 
Proof. intro ge. induction ge.
- intros. list_eq_ncT. contradiction.
- intros. acacD'T2 ; subst.
+ left. apply InT_eq.
+ erequire IHge.  erequire IHge.  erequire IHge.  require IHge.
  reflexivity.  destruct IHge.
 * left. apply InT_cons.  assumption.
 * right. simpl. apply gen_ext_cons. assumption.
- intros. acacD'T2 ; subst.
+ right. simpl. assumption. 
+ erequire IHge.  erequire IHge.  erequire IHge.  require IHge.
  reflexivity.  destruct IHge.
 * left.  assumption.
 * right. simpl. apply gen_ext_extra. assumption.
Qed.

Definition gen_ext_diff V X y Y Z ge := @gen_ext_diff' V X _ ge y Y Z eq_refl.

Ltac solve_gen_ext := 
  repeat (apply gen_ext_appL' || apply gen_ext_appR' ||
    apply gen_ext_nil_any || apply gen_ext_refl ||
    apply gen_ext_sameL || apply gen_ext_appL ||
    apply gen_ext_cons || apply gen_ext_extra).

