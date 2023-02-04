Add LoadPath "../general".
Require Import Lexicographic_Product.
Require Import Relation_Operators.
Require Import Wf_nat.
Require Import Inverse_Image.


Require Import Lia.

(* found elsewhere *)
Ltac clear_useless_refl :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         end.

(* found elsewhere *)
Ltac inversion_pair_refl :=
  repeat (clear_useless_refl; match goal with
  | [ H : (?a,?b)=(?c,?d) |- _ ] => inversion H; subst
  end; clear_useless_refl).

Inductive lt_lex_nat : (nat * nat) -> (nat * nat) -> Prop :=
| le_lex_nat_fst p q a b n m : p = (a,b) -> q = (n,m) -> a < n -> lt_lex_nat p q
| le_lex_nat_snd p q a b n m : p = (a,b) -> q = (n,m) -> a = n -> b < m -> lt_lex_nat p q.

Theorem wf_le_lex_nat : well_founded lt_lex_nat.
Proof.
  unfold well_founded.
  intros a. destruct a as [a b].
  revert b.
  induction a; intros b.
  + induction b. constructor. intros [n m] H.
    inversion H. inversion_pair_refl.
    contradiction (PeanoNat.Nat.nlt_0_r _ H2).
    inversion_pair_refl.
    contradiction (PeanoNat.Nat.nlt_0_r _ H3).
    constructor. intros [n m] H. inversion H. subst.
    inversion H1. subst.
    contradiction (PeanoNat.Nat.nlt_0_r _ H2).
    inversion_pair_refl.
    destruct (PeanoNat.Nat.eq_dec b0 b). subst.
    assumption.
    apply IHb.
    econstructor 2; try reflexivity.
    lia.

  + induction b. econstructor.
    intros [n m] H. inversion H. inversion_pair_refl.
    destruct (PeanoNat.Nat.eq_dec a0 a). subst.
    apply IHa.
    eapply IHa. econstructor; try reflexivity. lia.
    inversion_pair_refl. lia.

    inversion IHb as [H].
    constructor. intros [n m] H2.
    inversion H2. inversion_pair_refl.
    destruct (PeanoNat.Nat.eq_dec a0 a). subst. apply IHa.
    eapply IHa. econstructor; try reflexivity. lia.
    inversion_pair_refl. 
    specialize (IHa b0).

    destruct (PeanoNat.Nat.eq_dec b0 b).
    subst. assumption.
    apply H. econstructor 2; try reflexivity. lia.
    Unshelve. all : exact 0.
Qed. 

Definition wf_le_lex_nat_induction := well_founded_induction_type wf_le_lex_nat.

Infix "<<" := lt_lex_nat (at level 70, no associativity).

Lemma lt_lex_nat_lem1 : forall n m1 m2,
    (n,m1) << (S n, m2).
Proof. intros. econstructor; firstorder. Qed.

(*

Section My_Lex_Prod.
  Variable A : Type.
  Variable ltA : A -> A -> Prop.
  Variable eqA : A -> A -> Prop.

  Inductive lt_lexA : (A * A) -> (A * A) -> Prop :=
  | le_lexA_fst p q a b n m : p = (a,b) -> q = (n,m) -> ltA a n -> lt_lexA p q
  | le_lexA_snd p q a b n m : p = (a,b) -> q = (n,m) -> eqA a n -> ltA b m -> lt_lexA p q.

  Lemma induction_le_lexA :
    well_founded ltA ->
    forall P : A * A -> Type,
       (forall x : A * A, (forall y : A * A, lt_lexA y x -> P y) -> P x) ->
       forall a : A * A, P a.
  Proof.
    intros Hwf P IH [a1 a2]. revert a1 a2.
    eapply (well_founded_induction_type Hwf).
    intros a2 IH2.
    *)

(* Adapted from std lib to use on type level leA. *)
Section Lexicographic_Product.

  Variable A : Type.
  Variable B : A -> Type.
  Variable leA : A -> A -> Type.
  Variable leB : forall x:A, B x -> B x -> Type.

  Inductive lexprodT : sigT B -> sigT B -> Type :=
    | left_lex :
      forall (x x':A) (y:B x) (y':B x'),
        leA x x' -> lexprodT (existT B x y) (existT B x' y')
    | right_lex :
      forall (x:A) (y y':B x),
        leB x y y' -> lexprodT (existT B x y) (existT B x y').

End Lexicographic_Product.

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

Definition lt_pqT :dep2->dep2->Type :=
(lexprodT nat (fun a => nat) Peano.lt (fun a:nat =>Peano.lt)).

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

Definition lltT : (nat*nat) -> (nat*nat) -> Type :=
  fun a b => lt_pqT (mk2 a) (mk2 b).

(* Definition of lex le. *)
Definition lle : (nat*nat) -> (nat*nat) -> Prop :=
  fun a b => le_pq (mk2 a) (mk2 b).

Lemma wf_llt : well_founded llt.
Proof.
  unfold llt.
  eapply wf_inverse_image.
  apply wf_lexprod.
Qed.

(* Adapted from std library for well_foundedT. *)

Section Well_foundedT.
Set Implicit Arguments.
 Variable A : Type.
 Variable R : A -> A -> Type.

 Inductive AccT (x: A) : Type :=
     AccT_intro : (forall y:A, R y x -> AccT y) -> AccT x.

 Lemma Acc_invT : forall x:A, AccT x -> forall y:A, R y x -> AccT y.
 Proof.
   apply (fun (x : A) (H : AccT x) =>
            match H with
            | AccT_intro H0 => H0
            end).
 Qed.
  
 Definition well_foundedT := forall a:A, AccT a.

End Well_foundedT.

(* ------ *)

Print wf_inverse_image.
Print Acc_inverse_image.
Print Acc_lemma.

Definition Acc_lemma2 := 
fun (A B : Type) (R : B -> B -> Prop) (f : A -> B) =>
let Rof := fun x y : A => R (f x) (f y) in
fun (y : B) (H : Acc R y) =>
Acc_ind (fun y0 : B => forall x : A, y0 = f x -> Acc Rof x)
  (fun (y0 : B) (_ : forall y1 : B, R y1 y0 -> Acc R y1)
     (IHAcc : forall y1 : B, R y1 y0 -> forall x : A, y1 = f x -> Acc Rof x) 
     (x : A) (H0 : y0 = f x) =>
   Acc_intro x
     (fun (y1 : A) (H1 : Rof y1 x) =>
        IHAcc (f y1) (eq_ind_r (fun y2 : B => R (f y1) y2) H1 H0) y1 eq_refl)) H.
SearchAbout "AccT_ind".
(*
Definition AccT_lemma := 
fun (A B : Type) (R : B -> B -> Type) (f : A -> B) =>
let Rof := fun x y : A => R (f x) (f y) in
fun (y : B) (H : AccT R y) =>
AccT_ind (fun y0 : B => forall x : A, y0 = f x -> AccT Rof x)
  (fun (y0 : B) (_ : forall y1 : B, R y1 y0 -> AccT R y1)
     (IHAcc : forall y1 : B, R y1 y0 -> forall x : A, y1 = f x -> AccT Rof x) 
     (x : A) (H0 : y0 = f x) =>
   AccT_intro x
     (fun (y1 : A) (H1 : Rof y1 x) =>
        IHAcc (f y1) (eq_ind_r (fun y2 : B => R (f y1) y2) H1 H0) y1 eq_refl)) H.

Definition Acc_inverse_image := 
fun (A B : Type) (R : B -> B -> Type) (f : A -> B) =>
let Rof := fun x y : A => R (f x) (f y) in
fun (x : A) (H : AccT R (f x)) => Acc_lemma A B R f (f x) H x eq_refl
     : forall (A B : Type) (R : B -> B -> Prop) (f : A -> B) (x : A),
       Acc R (f x) -> Acc (fun x0 y : A => R (f x0) (f y)) x
Definition wfT_inverse_image = 
fun (A B : Type) (R : B -> B -> Type) (f : A -> B) =>
let Rof := fun x y : A => R (f x) (f y) in
fun (H : well_foundedT R) (a : A) => Acc_inverse_image A B R f a (H (f a))
     : forall (A B : Type) (R : B -> B -> Prop) (f : A -> B),
       well_founded R -> well_founded (fun x y : A => R (f x) (f y)).

Lemma wf_lltT : well_foundedT lltT.
Proof.
  unfold llt.
  eapply wf_inverse_image.
  apply wf_lexprod.
Qed.
*)
Definition induction_llt := (well_founded_induction_type wf_llt).

Definition induction_llt2 := (well_founded_induction wf_llt).

Lemma my_induction_llt : forall P : nat * nat -> Type,
       (forall x : nat * nat, (forall y : nat * nat, llt y x -> P y) -> P x) ->
       forall a : nat * nat, P a.
Proof.
  intros P IH [n m]. revert m.
  induction n; intros m.
  induction m. apply IH.
  intros [a b] Hlt. unfold llt in Hlt.
  simpl in Hlt. unfold lt_pq in Hlt.
Admitted.

Print induction_llt.
Print Assumptions induction_llt2.
Print Assumptions induction_llt.
Print well_founded_induction_type.
Print Assumptions well_founded.