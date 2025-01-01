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


(* Application of our framework to Kt (Tense logic). *)


Module Kt.
  Inductive formula : Set :=
    | Atf (p : string)
    | FVf (A : string)
    | Top
    | Bot
    | Neg (phi : formula)
    | Imp (phi psi : formula)
    | Dis (phi psi : formula)
    | Con (phi psi : formula)
    | Boxn (phi : formula)
    | Dian (phi : formula)
    | Boxp (phi : formula)
    | Diap (phi : formula).

  Inductive structr : Set :=
    | SVf (X : string)
    | FSf (A : formula)
    | I
    | Star (X : structr)
    | Comma (X Y : structr)
    | BCirc (X : structr).
End Kt.

Module KtNotations.
  
  Export Kt.
  
  Notation "% p" := (Kt.Atf p) (at level 10).
  Notation "? A" := (Kt.FVf A) (at level 10).
  Notation "¬ phi" := (Kt.Neg phi) (at level 20).
  Notation "⊤" := (Kt.Top) (at level 20).
  Notation "⊥" := (Kt.Bot) (at level 20).
  Notation "phi → psi" := (Kt.Imp phi psi) (at level 30).
  Notation "phi ∨ psi" := (Kt.Dis phi psi) (at level 30).
  Notation "phi ∧ psi" := (Kt.Con phi psi) (at level 30).
  Notation "◻ phi" := (Kt.Boxn phi) (at level 20).
  Notation "◊ phi" := (Kt.Dian phi) (at level 20).
  Notation "◼ phi" := (Kt.Boxp phi) (at level 20).
  Notation "⧫ phi" := (Kt.Diap phi) (at level 20).
  
  Notation "$ X" := (Kt.SVf X) (at level 35).
  Notation "£ A" := (Kt.FSf A) (at level 35).
  Notation "∗ X" := (Kt.Star X) (at level 40).
  Notation "X ,, Y" := (Kt.Comma X Y) (at level 50).
  Notation "● X" := (Kt.BCirc X) (at level 40).
End KtNotations.

Module Kt_LOG.

  Import Kt.

  Theorem fml_eq_dec : eq_dec formula.
  Proof. unfold eq_dec. decide equality; apply string_dec. Defined.

  Definition ipse (A : formula) : list formula :=
    match A with
    | Neg A0      => [A0]
    | Imp A1 A2   => [A1; A2]
    | Dis A1 A2   => [A1; A2]
    | Con A1 A2   => [A1; A2]
    | Boxn A0     => [A0]
    | Dian A0     => [A0]
    | Boxp A0     => [A0]
    | Diap A0     => [A0]
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
    exfalso;
    repeat destruct HB as [HB|HB]; contradict HB; apply not_eq_sym; assumption.
  Qed.

  Definition fml_df : formula := Atf "".

  Definition conn (A : formula) : list formula -> formula :=
    match A with
    | Neg A0      => fun l => match l with B0 :: _ => Neg B0 | _ => fml_df end
    | Imp A1 A2   => fun l => match l with B1 :: B2 :: _ => Imp B1 B2 | _ => fml_df end
    | Dis A1 A2   => fun l => match l with B1 :: B2 :: _ => Dis B1 B2 | _ => fml_df end
    | Con A1 A2   => fun l => match l with B1 :: B2 :: _ => Con B1 B2 | _ => fml_df end
    | Boxn A0     => fun l => match l with B0 :: _ => Boxn B0 | _ => fml_df end
    | Boxp A0     => fun l => match l with B0 :: _ => Boxp B0 | _ => fml_df end
    | Dian A0     => fun l => match l with B0 :: _ => Dian B0 | _ => fml_df end
    | Diap A0     => fun l => match l with B0 :: _ => Diap B0 | _ => fml_df end
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

End Kt_LOG.

#[export] Instance EqDec_formula : EqDec Kt.formula := {| eqdec := Kt_LOG.fml_eq_dec |}.

#[export] Instance f_Kt_log : @FLANG Kt.formula _ := {|
  ipse   := Kt_LOG.ipse;
  ipse_rect := Kt_LOG.ipse_rect;
  ipse_rect_cmp := Kt_LOG.ipse_rect_cmp;
  conn := Kt_LOG.conn;
  conn_ipse := Kt_LOG.conn_ipse;
  conn_inj := Kt_LOG.conn_inj |}.

#[export] Instance Kt_Atm : @IXEXP _ _ f_Kt_log string Kt_LOG.Atm := {|
  Var_dec := Kt_LOG.Atm_dec;
  Var_inj := Kt_LOG.Atm_inj;
  Var_ipse := Kt_LOG.Atm_ipse; |}.

#[export] Instance Kt_FV : @IXEXP _ _ f_Kt_log string Kt_LOG.FV := {|
  Var_dec := Kt_LOG.FV_dec;
  Var_inj := Kt_LOG.FV_inj;
  Var_ipse := Kt_LOG.FV_ipse; |}.

#[export] Instance Kt_log : @LOGLANG _ _ f_Kt_log := {|
  Atm := Kt.Atf;
  FV := Kt.FVf;
  ATMVAR := Kt_Atm;
  FVVAR := Kt_FV;
  Atm_FV_disc := Kt_LOG.Atm_FV_disc; |}.

Module Kt_STR.
  
  Import Kt.

  Theorem str_eq_dec : eq_dec structr.
  Proof. unfold eq_dec. decide equality; apply eqdec. Defined.

  Definition ipse (X : structr) : list structr :=
    match X with
    | Star X0     => [X0]
    | Comma X1 X2 => [X1; X2]
    | BCirc X0    => [X0]
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
    exfalso;
    repeat destruct HB as [HB|HB]; contradict HB; apply not_eq_sym; assumption.
  Qed.

  Definition str_df : structr := SVf "".

  Definition conn (X : structr) : list structr -> structr :=
    match X with
    | Star X0     => fun l => match l with Y0 :: _ => Star Y0 | _ => str_df end
    | Comma X1 X2 => fun l => match l with Y1 :: Y2 :: _ => Comma Y1 Y2 | _ => str_df end
    | BCirc X0    => fun l => match l with Y0 :: _ => BCirc Y0 | _ => str_df end
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

  Lemma FS_dec : forall X : structr, {A : formula | X = FS A} + {forall A : formula, X <> FS A}.
  Proof.
    destruct X; try (right; intro; discriminate).
    left. exists A. reflexivity.
  Defined.

  Lemma SV_FS_disc : forall v A, SV v <> FS A.
  Proof. intros. discriminate. Qed.

  Lemma SV_inj : forall v w : string, SV v = SV w -> v = w.
  Proof. intros v w H. injection H. tauto. Qed.

  Lemma FS_inj : forall A B : formula, FS A = FS B -> A = B.
  Proof. intros A B H. injection H. tauto. Qed.

  Lemma SV_ipse : forall v : string, ipse (SV v) = [].
  Proof. reflexivity. Qed.

  Lemma FS_ipse : forall A : formula, ipse (FS A) = [].
  Proof. reflexivity. Qed.
  
  Definition sgnips (X : structr) : list bool :=
    match X with
    | Star X0     => [false]
    | Comma X1 X2 => [true; true]
    | BCirc X0    => [true]
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
  
End Kt_STR.

#[export] Instance EqDec_structr : EqDec Kt.structr := {| eqdec := Kt_STR.str_eq_dec |}.

#[export] Instance f_Kt : @FLANG Kt.structr _ := {|
  ipse   := Kt_STR.ipse;
  ipse_rect := Kt_STR.ipse_rect;
  ipse_rect_cmp := Kt_STR.ipse_rect_cmp;
  conn := Kt_STR.conn;
  conn_ipse := Kt_STR.conn_ipse;
  conn_inj := Kt_STR.conn_inj |}.

#[export] Instance Kt_SV : @IXEXP _ _ f_Kt string Kt_STR.SV := {|
  Var_dec := Kt_STR.SV_dec;
  Var_inj := Kt_STR.SV_inj;
  Var_ipse := Kt_STR.SV_ipse; |}.

#[export] Instance Kt_FS : @IXEXP _ _ f_Kt Kt.formula Kt_STR.FS := {|
  Var_dec := Kt_STR.FS_dec;
  Var_inj := Kt_STR.FS_inj;
  Var_ipse := Kt_STR.FS_ipse; |}.

#[export] Instance Kt : @STRLANG _ Kt.structr _ _ Kt_log _ f_Kt := {|
  SV := Kt.SVf;
  FS := Kt.FSf;
  SVVAR := Kt_SV;
  FSVAR := Kt_FS;
  SV_FS_disc := Kt_STR.SV_FS_disc;
  sgnips := Kt_STR.sgnips;
  sgnips_length := Kt_STR.sgnips_length;
  sgnips_conn := Kt_STR.sgnips_conn |}.
