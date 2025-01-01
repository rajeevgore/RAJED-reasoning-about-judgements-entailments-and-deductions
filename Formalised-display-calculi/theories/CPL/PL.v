Require Import String.
Open Scope string_scope.
Require Import Relations.
Require Import List ListSet.
Import ListNotations.
Require Import ListSetNotations.
Require Import ListSet.
Require Import Arith.
Require Import ssrbool.
Require Import Wellfounded.
Require Import Datatypes.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import FunAgree.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.

Open Scope nat_scope.


(* Application of our framework to PL (propositional logic).
   At this point, nothing forces us to clarify whether we want
   CPL (classical PL) or IPL (intuitionistic PL) or something else
   as we are doing pure syntax for now.

   We can use this same syntax to later define display calculi
   for both CPL and IPL. *)


Module PL.
  Inductive formula : Set :=
    | Atf (p : string)
    | FVf (A : string)
    | Top
    | Bot
    | Neg (phi : formula)
    | Imp (phi psi : formula)
    | Dis (phi psi : formula)
    | Con (phi psi : formula).
End PL.

Module PL_LOG.

  Import PL.

  Theorem fml_eq_dec : eq_dec formula.
  Proof. unfold eq_dec. decide equality; apply string_dec. Defined.

  Definition ipse (A : formula) : list formula :=
    match A with
    | Neg A0      => [A0]
    | Imp A1 A2   => [A1; A2]
    | Dis A1 A2   => [A1; A2]
    | Con A1 A2   => [A1; A2]
    | _           => []
    end.
    
  Theorem ipse_rect (P : formula -> Type) :
    (forall A, (forall B, B ∈ (ipse A) -> P B) -> P A) -> forall A, P A.
  Proof.
    intro H. induction A; apply H;
      try (simpl; tauto);
      try (intros B HB; simpl ipse in HB;
           dec_destruct_List_In fml_eq_dec B;
           rewrite Heq; assumption).
  Defined.

  (* Requires functional extensionality *)
  Theorem ipse_rect_cmp :
    forall P P_IS A, ipse_rect P P_IS A = P_IS A (fun B HB => ipse_rect _ P_IS B).
  Proof.
    intros P f. induction A;
    simpl; apply f_equal; extensionality B; extensionality HB;
    try contradiction.
    all:
    repeat match goal with
      |- context[match ?C with _ => _ end] =>
          let Heq := fresh "Heq" in
          let Hneq := fresh "Hneq" in
          destruct C as [Heq|Hneq]
    end;
    try (rewrite Heq; unfold eq_rect_r; simpl; reflexivity);
    exfalso.
    repeat match goal with H : B <> _ |- _ => apply not_eq_sym in H end;
    repeat destruct HB as [HB|HB]; tauto.
    repeat match goal with H : B <> _ |- _ => apply not_eq_sym in H end;
    repeat destruct HB as [HB|HB]; tauto.
    repeat match goal with H : B <> _ |- _ => apply not_eq_sym in H end;
    repeat destruct HB as [HB|HB]; tauto.
    repeat match goal with H : B <> _ |- _ => apply not_eq_sym in H end;
    repeat destruct HB as [HB|HB]; tauto.
  Qed.

  Definition fml_df : formula := Atf "".

  Definition conn (A : formula) : list formula -> formula :=
    match A with
    | Neg A0      => fun l => match l with B0 :: _ => Neg B0 | _ => fml_df end
    | Imp A1 A2   => fun l => match l with B1 :: B2 :: _ => Imp B1 B2 | _ => fml_df end
    | Dis A1 A2   => fun l => match l with B1 :: B2 :: _ => Dis B1 B2 | _ => fml_df end
    | Con A1 A2   => fun l => match l with B1 :: B2 :: _ => Con B1 B2 | _ => fml_df end
    | A0          => fun _ => A0
    end.

  Lemma conn_ipse : forall A : formula, A = conn A (ipse A).
  Proof. destruct A; reflexivity. Qed.

  Lemma conn_inj : forall (A B : formula) (l l' : list formula),
      length l = length (ipse A) ->
      length l' = length (ipse B) -> conn A l = conn B l' -> conn A = conn B /\ l = l'.
  Proof.
    destruct A; destruct B; intros l l' Hl Hl' Heq; simpl in *;
      try (apply length_zero_iff_nil in Hl, Hl'; now rewrite Hl, Hl');
    repeat (let B := fresh "B" in destruct l as [|B l]; try discriminate);
    repeat (let C := fresh "C" in destruct l' as [|C l']; try discriminate);
    injection Heq; intros; all_rewrite; split; reflexivity.
  Qed.    

  Definition Atm := Atf.
  Definition FV := FVf.

  Lemma Atm_dec : forall A : formula, {p : string | A = Atm p} + {forall p : string, A <> Atm p}.
  Proof.
    destruct A; try (right; intro; discriminate).
    left. exists p. reflexivity.
  Defined.

  Lemma FV_dec : forall A : formula, {V : string | A = FV V} + {forall V : string, A <> FV V}.
  Proof.
    destruct A; try (right; intro; discriminate).
    left. exists A. reflexivity.
  Defined.

  Lemma Atm_FV_disc : forall p V : string, Atm p <> FV V.
  Proof. intros p V. discriminate. Qed.

  Lemma Atm_inj : forall p q : string, Atm p = Atm q -> p = q.
  Proof. intros p q H. injection H. tauto. Qed.

  Lemma FV_inj : forall V W : string, FV V = FV W -> V = W.
  Proof. intros V W H. injection H. tauto. Qed.

  Lemma Atm_ipse : forall p : string, ipse (Atm p) = [].
  Proof. reflexivity. Qed.

  Lemma FV_ipse : forall V : string, ipse (FV V) = [].
  Proof. reflexivity. Qed.

End PL_LOG.

#[export] Instance EqDec_formula : EqDec PL.formula := {| eqdec := PL_LOG.fml_eq_dec |}.

#[export] Instance f_PL : @FLANG PL.formula _ := {|
  ipse   := PL_LOG.ipse;
  ipse_rect := PL_LOG.ipse_rect;
  ipse_rect_cmp := PL_LOG.ipse_rect_cmp;
  conn := PL_LOG.conn;
  conn_ipse := PL_LOG.conn_ipse;
  conn_inj := PL_LOG.conn_inj |}.

#[export] Instance PL_Atm : @IXEXP _ _ f_PL string PL_LOG.Atm := {|
  Var_dec := PL_LOG.Atm_dec;
  Var_inj := PL_LOG.Atm_inj;
  Var_ipse := PL_LOG.Atm_ipse; |}.

#[export] Instance PL_FV : @IXEXP _ _ f_PL string PL_LOG.FV := {|
  Var_dec := PL_LOG.FV_dec;
  Var_inj := PL_LOG.FV_inj;
  Var_ipse := PL_LOG.FV_ipse; |}.

#[export] Instance PL : @LOGLANG _ _ f_PL := {|
  Atm := PL.Atf;
  FV := PL.FVf;
  ATMVAR := PL_Atm;
  FVVAR := PL_FV;
  Atm_FV_disc := PL_LOG.Atm_FV_disc; |}.

Module PLNotations.
(*  Export PL.*)
  
  Notation "% p" := (PL.Atf p) (at level 10).
  Notation "? A" := (PL.FVf A) (at level 10).
  Notation "¬ phi" := (PL.Neg phi) (at level 20).
  Notation "⊤" := (PL.Top) (at level 20).
  Notation "⊥" := (PL.Bot) (at level 20).
  Notation "phi → psi" := (PL.Imp phi psi) (at level 30).
  Notation "phi ∨ psi" := (PL.Dis phi psi) (at level 30).
  Notation "phi ∧ psi" := (PL.Con phi psi) (at level 30).
End PLNotations.


Module CPL.
  Inductive structr : Set :=
    | SVf (X : string)
    | FSf (A : PL.formula)
    | I
    | Star (X : structr)
    | Comma (phi psi : structr).

End CPL.

Module CPL_STR.
  
  Import CPL.

  Theorem str_eq_dec : eq_dec structr.
  Proof. unfold eq_dec. decide equality; apply eqdec. Defined.

  Definition ipse (X : structr) : list structr :=
    match X with
    | Star X      => [X]
    | Comma X1 X2 => [X1; X2]
    | _           => []
    end.
    
  Theorem ipse_rect (P : structr -> Type) :
    (forall A, (forall B, B ∈ (ipse A) -> P B) -> P A) -> forall A, P A.
  Proof.
    intro H. induction A; apply H;
      try (simpl; tauto);
      try (intros B HB; simpl ipse in HB;
           dec_destruct_List_In str_eq_dec B;
           rewrite Heq; assumption).
  Defined.

  (* Requires functional extensionality *)
  Theorem ipse_rect_cmp :
    forall P P_IS A, ipse_rect P P_IS A = P_IS A (fun B HB => ipse_rect _ P_IS B).
  Proof.
    intros P f. induction A;
    simpl; apply f_equal; extensionality B; extensionality HB;
    try contradiction.
    all:
    repeat match goal with
      |- context[match ?C with _ => _ end] =>
          let Heq := fresh "Heq" in
          let Hneq := fresh "Hneq" in
          destruct C as [Heq|Hneq]
    end;
    try (rewrite Heq; unfold eq_rect_r; simpl; reflexivity);
    exfalso.
    repeat match goal with H : B <> _ |- _ => apply not_eq_sym in H end;
    repeat destruct HB as [HB|HB]; tauto.
    repeat match goal with H : B <> _ |- _ => apply not_eq_sym in H end;
    repeat destruct HB as [HB|HB]; tauto.
  Qed.

  Definition str_df : structr := SVf "".

  Definition conn (X : structr) : list structr -> structr :=
    match X with
    | Star X0     => fun l => match l with Y0 :: _ => Star Y0 | _ => str_df end
    | Comma X1 X2 => fun l => match l with Y1 :: Y2 :: _ => Comma Y1 Y2 | _ => str_df end
    | X0          => fun _ => X0
    end.

  Lemma conn_ipse : forall X : structr, X = conn X (ipse X).
  Proof. destruct X; reflexivity. Qed.

  Lemma conn_inj : forall (X Y : structr) (l l' : list structr),
      length l = length (ipse X) ->
      length l' = length (ipse Y) -> conn X l = conn Y l' -> conn X = conn Y /\ l = l'.
  Proof.
    destruct X; destruct Y; intros l l' Hl Hl' Heq; simpl in *;
      try (apply length_zero_iff_nil in Hl, Hl'; now rewrite Hl, Hl');
    repeat (let Y := fresh "Y" in destruct l as [|Y l]; try discriminate);
    repeat (let C := fresh "C" in destruct l' as [|C l']; try discriminate);
    injection Heq; intros; all_rewrite; split; reflexivity.
  Qed.

  Definition SV := SVf.
  Definition FS := FSf.

  Lemma SV_dec : forall X : structr, {v : string | X = SV v} + {forall v : string, X <> SV v}.
  Proof.
    destruct X; try (right; intro; discriminate).
    left. exists X. reflexivity.
  Defined.

  Lemma FS_dec : forall X : structr, {A : PL.formula | X = FS A} + {forall A : PL.formula, X <> FS A}.
  Proof.
    destruct X; try (right; intro; discriminate).
    left. exists A. reflexivity.
  Defined.

  Lemma SV_FS_disc : forall v A, SV v <> FS A.
  Proof. intros. discriminate. Qed.

  Lemma SV_inj : forall v w : string, SV v = SV w -> v = w.
  Proof. intros v w H. injection H. tauto. Qed.

  Lemma FS_inj : forall A B : PL.formula, FS A = FS B -> A = B.
  Proof. intros A B H. injection H. tauto. Qed.

  Lemma SV_ipse : forall v : string, ipse (SV v) = [].
  Proof. reflexivity. Qed.

  Lemma FS_ipse : forall A : PL.formula, ipse (FS A) = [].
  Proof. reflexivity. Qed.
  
  Definition sgnips (X : structr) : list bool :=
    match X with
    | Star X0     => [false]
    | Comma X1 X2 => [true; true]
    | _           => []
    end.

  Lemma sgnips_length : forall X : structr, length (sgnips X) = length (ipse X).
  Proof. intro X. destruct X; reflexivity. Qed.

  Lemma sgnips_conn : forall (X : structr) (l : list structr),
      length l = length (ipse X) -> sgnips (conn X l) = sgnips X.
  Proof.
    intros X l H. destruct X; try reflexivity.
    all: destruct_list_easy l X.
  Qed.
  
End CPL_STR.

#[export] Instance EqDec_structr : EqDec CPL.structr := {| eqdec := CPL_STR.str_eq_dec |}.

#[export] Instance f_CPL : @FLANG CPL.structr _ := {|
  ipse   := CPL_STR.ipse;
  ipse_rect := CPL_STR.ipse_rect;
  ipse_rect_cmp := CPL_STR.ipse_rect_cmp;
  conn := CPL_STR.conn;
  conn_ipse := CPL_STR.conn_ipse;
  conn_inj := CPL_STR.conn_inj |}.

#[export] Instance CPL_SV : @IXEXP _ _ f_CPL string CPL_STR.SV := {|
  Var_dec := CPL_STR.SV_dec;
  Var_inj := CPL_STR.SV_inj;
  Var_ipse := CPL_STR.SV_ipse; |}.

#[export] Instance CPL_FS : @IXEXP _ _ f_CPL PL.formula CPL_STR.FS := {|
  Var_dec := CPL_STR.FS_dec;
  Var_inj := CPL_STR.FS_inj;
  Var_ipse := CPL_STR.FS_ipse; |}.

#[export] Instance CPL : @STRLANG _ CPL.structr _ _ PL _ f_CPL := {|
  SV := CPL.SVf;
  FS := CPL.FSf;
  SVVAR := CPL_SV;
  FSVAR := CPL_FS;
  SV_FS_disc := CPL_STR.SV_FS_disc;
  sgnips := CPL_STR.sgnips;
  sgnips_length := CPL_STR.sgnips_length;
  sgnips_conn := CPL_STR.sgnips_conn |}.

Module CPLNotations.
  Export CPL.
  Export PLNotations.
  
  Notation "$ X" := (CPL.SVf X) (at level 35).
  Notation "£ A" := (CPL.FSf A) (at level 35).
  Notation "∗ X" := (CPL.Star X) (at level 40).
  Notation "X ,, Y" := (CPL.Comma X Y) (at level 50).
End CPLNotations.
