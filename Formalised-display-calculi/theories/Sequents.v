Require Import String.
Open Scope string_scope.
Require Import Relations Datatypes.
Require Import List.
Import ListNotations.
Require Import ListSetNotations.
Require Import ListSet.
Require Import Ring.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.


Close Scope nat_scope.


Section Structr.

  Class STRLANG {formula structr : Type} `{LL : LOGLANG formula}
  {EDs : EqDec structr} {Ls : FLANG} := {
    SV : string -> structr; (* structure variable *)
    FS : formula -> structr; (* formula structure (inclusion formula -> structr) *)
    SVVAR :: IXEXP SV;
    FSVAR :: IXEXP FS;
    SV_FS_disc : forall X A, SV X <> FS A;
    sgnips : structr -> list bool; (* sign of each immediate proper substructr *)
    sgnips_length : forall X, length (sgnips X) = length (ipse X);
    sgnips_conn : forall X l, length l = length (ipse X) -> sgnips (conn X l) = sgnips X}.

End Structr.

Inductive sequent `{SL : STRLANG} := Sequent (X Y : structr).
Definition rule `{SL : STRLANG} := list sequent * sequent.
Definition DISPCALC `{SL : STRLANG} := list rule.


(* Notations for the basic datatypes *)
(*
Notation "X ,, Y" := (Comma X Y) (at level 50).
Notation "∗ X" := (Star X) (at level 40).
Notation "$ X" := (SV X) (at level 30).
Notation "£ A" := (FS A) (at level 30).
Notation "? A" := (FV A) (at level 15).


Notation "£? A" := (£ ? A) (at level 30).
Notation "£p p" := (£ Atm p) (at level 30).
*)

Notation "X ⊢ Y" := (Sequent X Y) (at level 60).


Section Sequents.

  Context `{SL : STRLANG}.

  Definition FS_eq_iff := Var_inj_iff FS.

  Lemma Sequent_eq_iff {X1 X2 Y1 Y2 : structr} : X1 ⊢ X2 = Y1 ⊢ Y2 <-> X1 = Y1 /\ X2 = Y2.
  Proof.
    split.
    - intro H. injection H. tauto.
    - intros [H1 H2]. rewrite H1, H2. reflexivity.
  Qed.

  Definition Seqmap (f : trf structr) : trf sequent :=
    fun S => match S with X ⊢ Y => f X ⊢ f Y end.

  Definition antec (s : sequent) : structr := match s with X ⊢ Y => X end.
  Definition succ (s : sequent) : structr := match s with X ⊢ Y => Y end.
  Definition side (b : bool) (S : sequent) :=
    match S with X ⊢ Y => if b then Y else X end.

  Definition conclRule (r : rule) : sequent := snd r.
  Definition premsRule (r : rule) : list (sequent) := fst r.

  Lemma surj_rule_pair (r : rule) : r = (premsRule r, conclRule r).
  Proof. unfold premsRule, conclRule. apply surjective_pairing. Qed.

  Lemma sequent_eq_dec : forall (s1 s2 : sequent), {s1 = s2} + {s1 <> s2}.
  Proof. decide equality; apply eqdec. Defined.

  #[export] Instance EqDec_sequent : EqDec sequent := {| eqdec := sequent_eq_dec |}.

  Lemma rule_eq_dec : forall (r1 r2 : rule), {r1 = r2} + {r1 <> r2}.
  Proof. decide equality; apply eqdec. Defined.

  #[export] Instance EqDec_rule : EqDec rule := {| eqdec := rule_eq_dec |}.

  Definition remove_seq := remove sequent_eq_dec.
  Definition remove_rule := remove rule_eq_dec.

(*
  Inductive strCtnsV : structr -> Prop :=
  | strCtnsV_isSV : forall X, strCtnsV (SV X)
  | strCtnsV_isFV : forall A, strCtnsV (FS (FV A))
  | strCtnsV_inips : forall X X', X' ∈ ipse X -> strCtnsV X' -> strCtnsV X.  

  (* strNoV X iff X has no FV and no SV *)
  Definition strNoV : structr -> Prop :=
    ipse_rect _ (fun X IH =>
      match Var_dec SV X with
        inleft (exist _ V _) => False | inright _ =>
      match Var_dec FS X with
        inleft (exist _ A _) => fmlNoFV A | inright _ =>
      fold_right (fun B => and
                          (match in_dec eqdec B (ipse A) with
                         left Hin => IH B Hin | right _  => True end))
                               True (ipse A)
      end).

  Fixpoint strNoV (Z : structr) : Prop :=
    match Z with
    | X,,Y => strNoV X /\ strNoV Y
    | ∗Y   => strNoV Y
    | I    => True
    | $X   => False
    | £A   => fmlNoFV A
    end.

  Definition seqNoV (U : sequent) : Prop :=
    match U with X ⊢ Y => strNoV X /\ strNoV Y end.
*)

  Definition strIsFml : structr -> Prop := isVar FS.
  Definition strCtnsFml : structr -> Prop := CtnsVar FS.

  Definition seqCtnsFml (seq : sequent) :=
    match seq with X ⊢ Y => strCtnsFml X \/ strCtnsFml Y end.

  Lemma strIsFml_sig (X : structr) : strIsFml X -> {A : formula | X = FS A}.
  Proof.
    intro H. destruct (Var_dec FS X) as [[A HA]|HnFS].
    - exists A. assumption.
    - exfalso. destruct H as [A]. apply (HnFS A). reflexivity.
  Defined.

  Lemma strIsFml_dec : forall X, {strIsFml X} + {~ strIsFml X}.
  Proof.
    intro X. destruct (Var_dec FS X) as [[A HA]|HnFS].
    - left. rewrite HA. apply isVar_intro.
    - right. intro Hctr. destruct Hctr. apply (HnFS v). reflexivity.
  Defined.

  Lemma strCtnsFml_dec : forall X, {strCtnsFml X} + {~ strCtnsFml X}.
  Proof.
    apply ipse_rect. intros X IHX.
    destruct (Var_dec FS X) as [[A HA]|HnFS].
    - left. rewrite HA. apply CtnsVar_isVar.
    - apply ForallT_forall in IHX.
      apply ForallT_dec_E_sumbool in IHX.
      destruct IHX as [Hex|Hall].
      + apply ExistsT_exists in Hex.
        destruct Hex as [X' HinX' HX'].
        left. eapply CtnsVar_inips; eassumption.
      + right. intro Hctr. destruct Hctr.
        * apply (HnFS v). reflexivity.
        * rewrite ForallT_forall in Hall.
          contradict Hctr. apply Hall. assumption.
  Defined.

  Lemma seqCtnsFml_dec : forall s, {seqCtnsFml s} + {~ seqCtnsFml s}.
  Proof.
    destruct s. simpl. destruct (strCtnsFml_dec X); destruct (strCtnsFml_dec Y); tauto.
  Defined.

  (* If one side of a sequent contains a formula then it takes up the whole side *)
  Definition seqNoSSF (seq : sequent) :=
    match seq with X ⊢ Y => (strIsFml X \/ ~ strCtnsFml X) /\ (strIsFml Y \/ ~ strCtnsFml Y) end.

  Definition strAtms : structr -> list string :=
    ipse_rect _ (fun X IH =>
      match Var_dec FS X with
      | inleft (exist _ A _) => fmlAtms A
      | inright _ => list_union (ipse X) (fun X' =>
                      match in_dec eqdec X' (ipse X) with
                        left Hin => IH X' Hin | right _  => [] end)
      end).

  Lemma strAtms_eq' (X : structr) :
    strAtms X =
      match Var_dec FS X with
      | inleft (exist _ A _) => fmlAtms A
      | inright _ => list_union (ipse X)
                      (fun X' => if in_dec eqdec X' (ipse X) then strAtms X' else [])
      end.
  Proof. unfold strAtms at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Lemma strAtms_eq (X : structr) :
    strAtms X =
      match Var_dec FS X with
      | inleft (exist _ A _) => fmlAtms A
      | inright _ => list_union (ipse X) strAtms
      end.
  Proof. rewrite strAtms_eq'. rewrite union_in_dec. reflexivity. Qed.

  Definition strFVs : structr -> list string :=
    ipse_rect _ (fun X IH =>
      match Var_dec FS X with
      | inleft (exist _ A _) => fmlFVs A
      | inright _ => list_union (ipse X)
                      (fun X' => match in_dec eqdec X' (ipse X) with
                                left Hin => IH X' Hin | right _  => [] end)
      end).

  Lemma strFVs_eq' (X : structr) :
    strFVs X =
      match Var_dec FS X with
      | inleft (exist _ A _) => fmlFVs A
      | inright _ => list_union (ipse X)
                      (fun X' => if in_dec eqdec X' (ipse X) then strFVs X' else [])
      end.
  Proof. unfold strFVs at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Lemma strFVs_eq (X : structr) :
    strFVs X =
      match Var_dec FS X with
      | inleft (exist _ A _) => fmlFVs A
      | inright _ => list_union (ipse X) strFVs
      end.
  Proof. rewrite strFVs_eq'. rewrite union_in_dec. reflexivity. Qed.


  (* List of structure variables *)
  Definition strSVs : structr -> list string := allVars SV.
  Definition strFmls : structr -> list formula := allVars FS.

  Lemma strSVs_eq (X : structr) :
    strSVs X =
      match Var_dec SV X with
      | inleft (exist _ v _) => [v]
      | inright _ => list_union (ipse X) strSVs
      end.
  Proof. apply allVars_eq. Qed.

  Lemma strFmls_eq (X : structr) :
    strFmls X =
      match Var_dec FS X with
      | inleft (exist _ A _) => [A]
      | inright _ => list_union (ipse X) strFmls
      end.
  Proof. apply allVars_eq. Qed.

  Lemma strSVs_SV (v : string) : strSVs (SV v) = [v].
  Proof. rewrite strSVs_eq. rewrite Var_dec_Var. reflexivity. Qed.

  Lemma strSVs_FS (A : formula) : strSVs (FS A) = [].
  Proof.
    rewrite strSVs_eq.
    destruct (Var_dec SV (FS A)) as [[v Hv]|HnSV].
    - contradict Hv. apply not_eq_sym, SV_FS_disc.
    - rewrite (Var_ipse FS). reflexivity.
  Qed.

  Lemma strFmls_FS (A : formula) : strFmls (FS A) = [A].
  Proof. rewrite strFmls_eq. rewrite Var_dec_Var. reflexivity. Qed.

  Lemma strFmls_SV (v : string) : strFmls (SV v) = [].
  Proof.
    rewrite strFmls_eq.
    destruct (Var_dec FS (SV v)) as [[A HA]|HnFS].
    - contradict HA. apply SV_FS_disc.
    - rewrite (Var_ipse SV). reflexivity.
  Qed.


  (* List of structure variables in antecedent/consequent part *)
  Definition strSVsSgn : structr -> bool -> list string :=
    ipse_rect _ (fun X IH => fun b : bool =>
      match Var_dec SV X with
      | inleft (exist _ V _) => if b then [V] else []
      | inright _ => list_union (zip pair (sgnips X) (ipse X))
                      (fun bX' : bool * structr =>
                         match in_dec eqdec (snd bX') (ipse X) with
                           left Hin => IH (snd bX') Hin (nxorb b (fst bX'))
                         | right _  => [] end)
      end).

  Lemma strSVsSgn_eq' (X : structr) (b : bool) :
    strSVsSgn X b =
      match Var_dec SV X with
      | inleft (exist _ V _) => if b then [V] else []
      | inright _ => list_union (zip pair (sgnips X) (ipse X))
                      (fun bX' : bool * structr =>
                         if in_dec eqdec (snd bX') (ipse X)
                         then strSVsSgn (snd bX') (nxorb b (fst bX')) else [])
      end.
  Proof. unfold strSVsSgn at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Lemma strSVsSgn_eq (X : structr) (b : bool) :
    strSVsSgn X b =
      match Var_dec SV X with
      | inleft (exist _ V _) => if b then [V] else []
      | inright _ =>
          list_union (zip pair (sgnips X) (ipse X))
            (fun bX' : bool * structr => strSVsSgn (snd bX') (nxorb b (fst bX')))
      end.
  Proof.
    rewrite strSVsSgn_eq' at 1.
    rewrite union_in_dec_zip_pair_snd.
    reflexivity.
  Qed.

  Definition seqFmls (u : sequent) : list formula :=
    match u with X ⊢ Y => strFmls X ++ strFmls Y end.

  Definition seqAtms (seq : sequent) : list string := strAtms (antec seq) ++ strAtms (succ seq).
  Definition seqFVs (seq : sequent) : list string := strFVs (antec seq) ++ strFVs (succ seq).
  Definition seqSVs (seq : sequent) : list string := strSVs (antec seq) ++ strSVs (succ seq).

  Definition seqSVsSgn (seq : sequent) (b : bool) : list string :=
    strSVsSgn (antec seq) (negb b) ++ strSVsSgn (succ seq) b.

  Lemma strSVs_decouple : forall X : structr,
    forall x, x ∈ strSVs X <-> x ∈ strSVsSgn X true \/ x ∈ strSVsSgn X false.
  Proof.
    intro X. pattern X. revert X. apply ipse_rect.
    intros X IHX v. rewrite strSVs_eq, ! strSVsSgn_eq.
    destruct (Var_dec SV X) as [[x Hx]|HnSV]; try (simpl; tauto).
    split.
    - intro H. apply In_fold_right_app in H.
      destruct H as [X' [HinX' HX']].
      apply IHX in HX'; try assumption.
      destruct HX' as [HX'|HX'].
      + apply (zip_pair_bij_snd (sgnips X)) in HinX';
          try now rewrite sgnips_length.
        destruct HinX' as [X'b [HinX'b HX'b]].
        remember (fst X'b) as b eqn:Heqb. destruct b.
        * left. apply In_union_iff.
          exists X'b. rewrite HX'b, <- Heqb. tauto.
        * right. apply In_union_iff.
          exists X'b. rewrite HX'b, <- Heqb. tauto.
      + apply (zip_pair_bij_snd (sgnips X)) in HinX';
          try now rewrite sgnips_length.
        destruct HinX' as [X'b [HinX'b HX'b]].
        remember (fst X'b) as b eqn:Heqb. destruct b.
        * right. apply In_union_iff.
          exists X'b. rewrite HX'b, <- Heqb. tauto.
        * left. apply In_union_iff.
          exists X'b. rewrite HX'b, <- Heqb. tauto.
    - intros [H|H].
      + apply In_union in H.
        destruct H as [X'b [HinX'b HX'b]].
        remember (snd X'b) as X'.
        assert (X' ∈ ipse X) as HinX' by
            (rewrite HeqX'; apply (in_zip_pair_snd HinX'b)).
        destruct (fst X'b).
        * apply In_union_iff. exists X'. split; try assumption.
          apply IHX; try assumption. now left.
        * apply In_union_iff. exists X'. split; try assumption.
          apply IHX; try assumption. now right.
      + apply In_union in H.
        destruct H as [X'b [HinX'b HX'b]].
        remember (snd X'b) as X'.
        assert (X' ∈ ipse X) as HinX' by
            (rewrite HeqX'; apply (in_zip_pair_snd HinX'b)).
        destruct (fst X'b).
        * apply In_union_iff. exists X'. split; try assumption.
          apply IHX; try assumption. now right.
        * apply In_union_iff. exists X'. split; try assumption.
          apply IHX; try assumption. now left.
  Qed.

  Lemma seqSVs_decouple : forall seq : sequent,
    forall x, x ∈ seqSVs seq <-> x ∈ seqSVsSgn seq true \/ x ∈ seqSVsSgn seq false.
  Proof.
    intro seq. destruct seq as [X Y]. unfold seqSVs, seqSVsSgn. simpl.
    setoid_rewrite in_app_iff. setoid_rewrite strSVs_decouple. tauto.
  Qed.
    

End Sequents.
