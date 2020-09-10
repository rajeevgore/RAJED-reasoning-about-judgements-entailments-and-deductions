Require Import Lexicographic_Product.
Require Import Relation_Operators.
Require Import Wf_nat.
Require Import Inverse_Image.

(* Type version (for P : nat -> Type) of lt_wf_ind, still based off Prop lt. *)
Lemma lt_wf_indT :
  forall n (P:nat -> Type), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  induction n; intros P IH.
  apply IH. intros m Hm.
  apply PeanoNat.Nat.nlt_0_r in Hm.
  contradiction.

  apply IHn.
  intros u Hu.
  apply IH.
  intros v Hv.
  destruct v.
  apply IH. intros m Hm.
  apply PeanoNat.Nat.nlt_0_r in Hm. contradiction.
  apply Lt.lt_S_n in Hv.
  apply Hu in Hv. assumption.
Qed.

(* The following was adapted from Pierre Casteran's answer to this coq-club question:
https://coq-club.inria.narkive.com/7Mts7wuN/how-to-show-lexicographic-product-of-three-well-founded-sets-is-well-founded
 *)

Definition dep2 := sigT (A:=nat) (fun a => nat).

Definition mk2 :=
(fun H : nat * nat => let (p, q) := H in existT (fun _ : nat => nat) p q).
(*  nat*nat -> dep2.
intros (p,q).
exists p.
exact q.
Defined.
 *)

Definition lt_pq :dep2->dep2->Prop :=
(lexprod nat (fun a => nat) Peano.lt (fun a:nat =>Peano.lt)).

Definition le_pq (a b : dep2) : Prop :=
  lt_pq a b \/ a = b.

Lemma wf_lexprod : well_founded lt_pq.
Proof.
  unfold lt_pq; apply wf_lexprod.
  apply lt_wf.
  intro n.
  apply lt_wf.
Qed.

(* Definition of lex lt. *)
Definition llt : (nat*nat) -> (nat*nat) -> Prop :=
  fun a b => lt_pq (mk2 a) (mk2 b).

(* Definition of lex le. *)
Definition lle : (nat*nat) -> (nat*nat) -> Prop :=
  fun a b => le_pq (mk2 a) (mk2 b).

Lemma wf_llt : well_founded llt.
Proof.
  unfold llt.
  eapply wf_inverse_image.
  apply wf_lexprod.
Qed.

Definition induction_llt := (well_founded_induction wf_llt).
