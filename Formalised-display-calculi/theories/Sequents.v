Require Import String.
Open Scope string_scope.
Require Import Relations.
Require Import List.
Import ListNotations.
Require Import ListSetNotations.
Require Import ListSet.
Require Import Ring.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Llang.


Close Scope nat_scope.

Section BasicDatatypes.

  Context {formula : Type}.

  Inductive structr :=
  | SV (X : string) (* Structure variable *)
  | I
  | FS (A : formula)
  | Star (X : structr)
  | Comma (X Y : structr).

  Inductive sequent := Sequent (X Y : structr).
  Definition rule := list sequent * sequent.

End BasicDatatypes.

Definition DISPCALC `{SL : SUBSTLLANG} := list (@rule formula).

(* Notations for the basic datatypes *)
Notation "X ,, Y" := (Comma X Y) (at level 50).
Notation "∗ X" := (Star X) (at level 40).
Notation "$ X" := (SV X) (at level 30).
Notation "£ A" := (FS A) (at level 30).
Notation "? A" := (FV A) (at level 15).

Notation "£? A" := (£ ? A) (at level 30).
Notation "£p p" := (£ Atm p) (at level 30).

Notation "X ⊢ Y" := (Sequent X Y) (at level 60).


Section Sequents.

  Context `{SL : SUBSTLLANG}.

  Definition listsubfmls (l : list formula) : list formula :=
    fold_right (fun A => app (subfmls A)) [] l.

  Lemma listsubfmls_refl : forall l, incl l (listsubfmls l).
  Proof.
    intros l A H. unfold listsubfmls. rewrite In_fold_right_app_iff.
    exists A. split; try assumption. apply subfmls_refl.
  Qed.

  Lemma listsubfmls_subclosed :
    forall l l', incl l (listsubfmls l') -> incl (listsubfmls l) (listsubfmls l').
  Proof.
    intros l l' H A HAin. unfold listsubfmls in HAin |- *.
    rewrite In_fold_right_app_iff in HAin.
    rewrite In_fold_right_app_iff.
    destruct HAin as [B [HBin HAin]].
    apply H in HBin. unfold listsubfmls in HBin.
    rewrite In_fold_right_app_iff in HBin.
    destruct HBin as [C [HCin HBin]].
    exists C. split; try assumption. eapply subfmls_tran; eassumption.
  Qed.    

  Lemma Comma_eq_iff (X1 X2 Y1 Y2 : @structr formula) : X1,,X2 = Y1,,Y2 <-> X1 = Y1 /\ X2 = Y2.
  Proof. injection_iff. Qed.

  Lemma Star_eq_iff (X Y : @structr formula) : ∗X = ∗Y <-> X = Y.
  Proof. injection_iff. Qed.

  Lemma FS_eq_iff (A B : formula) : £A = £B <-> A = B.
  Proof. injection_iff. Qed.

  Lemma Sequent_eq_iff {X1 X2 Y1 Y2 : @structr formula} : X1 ⊢ X2 = Y1 ⊢ Y2 <-> X1 = Y1 /\ X2 = Y2.
  Proof.
    split.
    - intro H. injection H. tauto.
    - intros [H1 H2]. rewrite H1, H2. reflexivity.
  Qed.

  Definition Seqmap (f : trf (@structr formula)) : trf (@sequent formula) :=
    fun S => match S with X ⊢ Y => f X ⊢ f Y end.

  Definition antec (s : @sequent formula) : structr := match s with X ⊢ Y => X end.
  Definition succ (s : @sequent formula) : structr := match s with X ⊢ Y => Y end.
  Definition side (b : bool) (S : @sequent formula) :=
    match S with X ⊢ Y => if b then Y else X end.

  Definition conclRule (r : rule) : @sequent formula := snd r.
  Definition premsRule (r : rule) : list (@sequent formula) := fst r.

  Lemma surj_rule_pair (r : rule) : r = (premsRule r, conclRule r).
  Proof. unfold premsRule, conclRule. apply surjective_pairing. Qed.

  Lemma structr_eq_dec : forall (X Y : @structr formula), {X = Y} + {X <> Y}.
  Proof. decide equality; apply eqdec. Defined.

  Lemma sequent_eq_dec : forall (s1 s2 : @sequent formula), {s1 = s2} + {s1 <> s2}.
  Proof. decide equality; apply structr_eq_dec. Defined.

  Lemma rule_eq_dec : forall (r1 r2 : @rule formula), {r1 = r2} + {r1 <> r2}.
  Proof. decide equality; [apply sequent_eq_dec | apply (list_eq_dec sequent_eq_dec)]. Defined.

  #[export] Instance EqDec_structr : EqDec structr := {| eqdec := structr_eq_dec |}.
  #[export] Instance EqDec_sequent : EqDec sequent := {| eqdec := sequent_eq_dec |}.
  #[export] Instance EqDec_rule : EqDec rule := {| eqdec := rule_eq_dec |}.

  Definition remove_seq := remove sequent_eq_dec.

  Definition remove_rule := remove rule_eq_dec.

  (* strNoV X iff X has no FV and no SV *)
  Fixpoint strNoV (Z : @structr formula) : Prop :=
    match Z with
    | X,,Y => strNoV X /\ strNoV Y
    | ∗Y   => strNoV Y
    | I    => True
    | $X   => False
    | £A   => fmlNoFV A
    end.

  Definition seqNoV (U : sequent) : Prop :=
    match U with X ⊢ Y => strNoV X /\ strNoV Y end.

  (* strCtnsFml X iff X contains a formula *)
  Fixpoint strCtnsFml (Z : @structr formula) : Prop :=
    match Z with
    | X,,Y => strCtnsFml X \/ strCtnsFml Y
    | ∗Y   => strCtnsFml Y
    | I    => False
    | $str => False
    | £phi   => True
    end.

  Definition seqCtnsFml (seq : sequent) :=
    match seq with X ⊢ Y => strCtnsFml X \/ strCtnsFml Y end.

  Proposition strCtnsFml_dec : forall X, {strCtnsFml X} + {~ strCtnsFml X}.
  Proof.
    induction X; simpl; auto.
    destruct IHX1; destruct IHX2; simpl; tauto.
  Defined.

  Proposition seqCtnsFml_dec : forall s, {seqCtnsFml s} + {~ seqCtnsFml s}.
  Proof.
    destruct s. simpl. destruct (strCtnsFml_dec X); destruct (strCtnsFml_dec Y); tauto.
  Defined.

  Definition strIsFml (X : @structr formula) : Prop :=
    match X with
    | £ phi => True
    | _   => False
    end.

  Theorem strIsFml_dec : forall X, {strIsFml X} + {~ strIsFml X}.
  Proof. destruct X; simpl; tauto. Defined.

  (* If one side of a sequent contains a formula then it takes up the whole side *)
  Definition seqNoSSF (seq : sequent) :=
    match seq with X ⊢ Y => (strIsFml X \/ ~ strCtnsFml X) /\ (strIsFml Y \/ ~ strCtnsFml Y) end.

  Fixpoint strAtms (Z : structr) : list string :=
    match Z with
    | X,,Y => strAtms X ++ strAtms Y
    | ∗Y   => strAtms Y
    | I    => []
    | $x   => []
    | £A   => fmlAtms A
    end.

  Fixpoint strFVs (Z : structr) : list string :=
    match Z with
    | X,,Y => strFVs X ++ strFVs Y
    | ∗Y   => strFVs Y
    | I    => []
    | $x   => []
    | £A   => fmlFVs A
    end.

  (* List of structure variables *)
  Fixpoint strSVs (Z : @structr formula) : list string :=
    match Z with
    | X,,Y => strSVs X ++ strSVs Y
    | ∗Y   => strSVs Y
    | I    => []
    | $x   => [x]
    | £A   => []
    end.

  (* List of structure variables in antecedent/consequent part *)
  Fixpoint strSVs' (b : bool) (Z : @structr formula) : list string :=
    match Z with
    | X,,Y => strSVs' b X ++ strSVs' b Y
    | ∗Y   => strSVs' (negb b) Y
    | I    => []
    | $x   => if b then [x] else []
    | £A   => []
    end.

  Fixpoint strFmls (Z : structr) : list formula :=
    match Z with
    | X,,Y => strFmls X ++ strFmls Y
    | ∗Y   => strFmls Y
    | I    => []
    | $x   => []
    | £A   => [A]
    end.

  Definition seqFmls (u : sequent) : list formula :=
    match u with X ⊢ Y => strFmls X ++ strFmls Y end.

  Definition seqAtms (seq : sequent) : list string := strAtms (antec seq) ++ strAtms (succ seq).
  Definition seqFVs (seq : sequent) : list string := strFVs (antec seq) ++ strFVs (succ seq).
  Definition seqSVs (seq : sequent) : list string := strSVs (antec seq) ++ strSVs (succ seq).

  Definition seqSVs' (b : bool) (seq : sequent) : list string :=
    strSVs' (negb b) (antec seq) ++ strSVs' b (succ seq).

  Lemma strSVs_decouple : forall X : structr,
    forall x, x ∈ strSVs X <-> x ∈ strSVs' true X \/ x ∈ strSVs' false X.
  Proof.
    induction X; simpl; try tauto.
    - simpl. setoid_rewrite IHX. tauto.
    - simpl. setoid_rewrite in_app_iff. setoid_rewrite IHX1. setoid_rewrite IHX2. tauto.
  Qed.

  Lemma seqSVs_decouple : forall seq : sequent,
    forall x, x ∈ seqSVs seq <-> x ∈ seqSVs' true seq \/ x ∈ seqSVs' false seq.
  Proof.
    intro seq. destruct seq as [X Y]. unfold seqSVs, seqSVs'. simpl.
    setoid_rewrite in_app_iff. setoid_rewrite strSVs_decouple. tauto.
  Qed.

End Sequents.
