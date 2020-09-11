Require Import gen genT.
Require Import lntT.
Require Import lntacsT.
Require Import List_lemmasT.


Inductive size {V : Set} (A : PropF V) (n : nat) : Type :=
| VarSize v : A = Var v -> n = 1 -> size A n
| BotSize : A = (Bot V) -> n = 1 -> size A n
| ImpSize B C bn cn : A = Imp B C -> n = S (bn + cn)%nat ->
                      size B bn -> size C cn -> size A n
| WBoxSize B bn : A = WBox B -> n = S bn -> size B bn -> size A n
| BBoxSize B bn : A = BBox B -> n = S bn -> size B bn -> size A n.

Lemma size_unique : forall {V : Set} (A : PropF V) n m,
    size A n -> size A m -> n = m.
Proof.
  induction A as [ | | B IH1 C IH2 | B IH | B IH ] ; intros n m Hs1 Hs2;
    inversion Hs1 as [ | | B' C' bn cn HBC' Hbcn Hsb' Hsc' |
                       D' dn' HD' Hdn' HsD' |
                     E' en' HE' Hen' HsE'];
    inversion Hs2 as [ | | B'' C'' bn' cn' HBC'' Hbcn' Hsb'' Hsc'' |
                       D'' dn'' HD'' Hdn'' HsD'' |
                      E'' en'' HE'' Hen'' HsE'']; subst;
      repeat (try inv_contr_PropF);
      try reflexivity.

  rewrite (IH1 _ _ Hsb' Hsb'').
  rewrite (IH2 _ _ Hsc' Hsc'').
  reflexivity.

  rewrite (IH _ _ HsD' HsD''). reflexivity.
  rewrite (IH _ _ HsE' HsE''). reflexivity.
Qed.

Fixpoint fsize {V : Set} (A : PropF V) : nat :=
  match A with
  | Var _ => 1
  | Bot _ => 1
  | Imp B C => S ((fsize B) + (fsize C))
  | WBox B => S (fsize B)
  | BBox B => S (fsize B)
  end.

Lemma size_fsize : forall {V : Set} (A : PropF V) n,
    size A n -> fsize A = n.
Proof.
  induction A; intros n Hs;
  inversion Hs; subst; try reflexivity;
    repeat (try inv_contr_PropF).
  simpl. erewrite IHA1. erewrite IHA2.
  reflexivity. assumption. assumption.
  simpl. erewrite IHA. reflexivity. assumption.
  simpl. erewrite IHA. reflexivity. assumption.
Qed.

Lemma fsize_not_0 : forall {V : Set} A, @fsize V A <> 0.
Proof. destruct A; intros Hcontr; discriminate. Qed.




Inductive not_box {V : Set} (A : PropF V) :=
| nb_Var p : A = Var p -> not_box A
| nb_Bot : A = Bot V -> not_box A
| nb_Imp B C : A = Imp B C -> not_box A.
(*
| nb_WBox B : A = WBox B -> not_box A
| nb_BBox B : A = BBox B -> not_box A.
*)

Inductive not_wbox {V : Set} (A : PropF V) :=
| nwb_Var p : A = Var p -> not_wbox A
| nwb_Bot : A = Bot V -> not_wbox A
| nwb_Imp B C : A = Imp B C -> not_wbox A
| nwb_BBox B : A = BBox B -> not_wbox A.

Inductive not_wbox_exp {V : Set} : PropF V -> Type :=
| nwbe_Var p : not_wbox_exp (Var p)
| nwbe_Bot : not_wbox_exp (Bot V)
| nwbe_Imp B C :not_wbox_exp (Imp B C)
| nwbe_BBox B : not_wbox_exp (BBox B).


Lemma not_wbox__exp : forall {V : Set} (A : PropF V),
    iffT (not_wbox A) (not_wbox_exp A).
Proof.
  intros V A; destruct A;
    (split; intros H; [try econstructor | ]).
  eapply_refl (@nwb_Var V).
  eapply_refl (@nwb_Bot V).
  eapply_refl (@nwb_Imp V).
  inversion H; discriminate.
  inversion H.
  eapply_refl (@nwb_BBox V).
Qed.

Lemma not_wbox__exp_fwd : forall {V : Set} (A : PropF V),
    (not_wbox A) -> (not_wbox_exp A).
Proof. intros V A. apply not_wbox__exp. Qed.

Lemma not_wbox__exp_rev : forall {V : Set} (A : PropF V),
    (not_wbox_exp A) -> (not_wbox A).
Proof. intros V A. apply not_wbox__exp. Qed.

Inductive not_bbox {V : Set} (A : PropF V) :=
| nbb_Var p : A = Var p -> not_bbox A
| nbb_Bot : A = Bot V -> not_bbox A
| nbb_Imp B C : A = Imp B C -> not_bbox A
| nbb_WBox B : A = BBox B -> not_bbox A.

Inductive is_wbox {V : Set} (A : PropF V) :=
  | wb_I B : A = WBox B -> is_wbox A.

Inductive is_bbox {V : Set} (A : PropF V) :=
| bb_I B : A = BBox B -> is_bbox A.


Lemma not_wbox_dec : forall {V : Set} (A : PropF V),
    (not_wbox A) + (not_wbox A -> empty).
Proof.
  intros V A; destruct A;
    try solve [left; eapply not_wbox__exp; econstructor].
  right. intros H. inversion H; discriminate.
Qed.

