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
Require Import Llang.
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

(*
End PL.

Import PL.

Module LPL.
*)

  Theorem fml_eq_dec : eq_dec formula.
  Proof. unfold eq_dec. decide equality; apply string_dec. Defined.

  Definition ipsubfmls (A : formula) : list formula :=
    match A with
    | Neg A0      => [A0]
    | Imp A1 A2   => [A1; A2]
    | Dis A1 A2   => [A1; A2]
    | Con A1 A2   => [A1; A2]
    | _           => []
    end.
    
  Theorem ipsubfmls_rect (P : formula -> Type) :
    (forall A, (forall B, B ∈ (ipsubfmls A) -> P B) -> P A) -> forall A, P A.
  Proof.
    intro H. induction A; apply H;
      try (simpl; tauto);
      try (intros B HB; simpl ipsubfmls in HB;
           dec_destruct_List_In fml_eq_dec B;
           rewrite Heq; assumption).
  Defined.

  (* Requires functional extensionality *)
  Theorem ipsubfmls_rect_cmp :
    forall P P_IS A, ipsubfmls_rect P P_IS A = P_IS A (fun B HB => ipsubfmls_rect _ P_IS B).
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

  Lemma conn_ipsubfmls_eq : forall A : formula, A = conn A (ipsubfmls A).
  Proof. destruct A; reflexivity. Qed.

  Lemma conn_inj : forall (A B : formula) (l l' : list formula),
      length l = length (ipsubfmls A) ->
      length l' = length (ipsubfmls B) -> conn A l = conn B l' -> conn A = conn B /\ l = l'.
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

  Lemma Atm_ipsubfmls : forall p : string, ipsubfmls (Atm p) = [].
  Proof. reflexivity. Qed.

  Lemma FV_ipsubfmls : forall V : string, ipsubfmls (FV V) = [].
  Proof. reflexivity. Qed.

End PL.

#[export] Instance EqDec_formula : EqDec PL.formula := {| eqdec := PL.fml_eq_dec |}.

#[export] Instance pl : @LLANG PL.formula _ := {|
  ipsubfmls   := PL.ipsubfmls;
  ipsubfmls_rect := PL.ipsubfmls_rect;
  ipsubfmls_rect_cmp := PL.ipsubfmls_rect_cmp;
  conn := PL.conn;
  conn_ipsubfmls_eq := PL.conn_ipsubfmls_eq;
  conn_inj := PL.conn_inj |}.

#[export] Instance pl_Atm : @SUBVAR _ _ pl PL.Atm := {|
  Var_dec := PL.Atm_dec;
  Var_inj := PL.Atm_inj;
  Var_ipsubfmls := PL.Atm_ipsubfmls; |}.

#[export] Instance pl_FV : @SUBVAR _ _ pl PL.FV := {|
  Var_dec := PL.FV_dec;
  Var_inj := PL.FV_inj;
  Var_ipsubfmls := PL.FV_ipsubfmls; |}.

#[export] Instance substpl : @SUBSTLLANG _ _ pl := {|
  Atm := PL.Atm;
  FV := PL.FV;
  ATMVAR := pl_Atm;
  FVVAR := pl_FV;
  Atm_FV_disc := PL.Atm_FV_disc; |}.

Module PLNotations.
  Import PL.
  
  Notation "% p" := (Atf p) (at level 10).
  Notation "¬ phi" := (Neg phi) (at level 20).
  Notation "⊤" := (Top) (at level 20).
  Notation "⊥" := (Bot) (at level 20).
  Notation "phi → psi" := (Imp phi psi) (at level 30).
  Notation "phi ∨ psi" := (Dis phi psi) (at level 30).
  Notation "phi ∧ psi" := (Con phi psi) (at level 30).
End PLNotations.


(*
Import PLNotations.

Fixpoint fml_list_matchsub (sch ins : formula) :
  list (string * string) * list (string * formula) :=
  match sch, ins with
  | Atf p, Atf q  => ([(p, q)], [])
  | ¬ A, ¬ B      => fml_list_matchsub A B
  | A ∧ B, C ∧ D  => app2 (fml_list_matchsub A C) (fml_list_matchsub B D)
  | A ∨ B, C ∨ D  => app2 (fml_list_matchsub A C) (fml_list_matchsub B D)
  | A → B, C → D  => app2 (fml_list_matchsub A C) (fml_list_matchsub B D)
  | FVf A, B      => ([], [(A, B)])
  | _, _          => ([], [])
  end.

    
Fixpoint str_list_matchsub (sch ins : @structr formula) :
  (list (string * string)) * (list (string * formula)) * (list (string * structr)) :=
  match sch, ins with
  | X,,Y, Z,,W => app3 (str_list_matchsub X Z) (str_list_matchsub Y W)
  | ∗X, ∗Y     => str_list_matchsub X Y
  | £A, £B     => (fml_list_matchsub A B, [])
  | $X, Y      => ([], [], [(X, Y)])
  | _, _       => ([], [], [])
  end.

Definition seq_list_matchsub (sch ins : @sequent formula) :=
  match sch, ins with X ⊢ Y, Z ⊢ W => app3 (str_list_matchsub X Z) (str_list_matchsub Y W) end.

Fixpoint listseq_list_matchsub (lsch lins : list (@sequent formula)) :=
  match lsch, lins with
  | U :: lU, V :: lV => app3 (seq_list_matchsub U V) (listseq_list_matchsub lU lV)
  | _, _           => ([], [], [])
  end.

Definition seq_matchsub_alt (lsch lins : @sequent formula) :=
  uncurry (uncurry afs_spec) (seq_list_matchsub lsch lins).

Definition listseq_matchsub_alt (lsch lins : list (@sequent formula)) :=
  uncurry (uncurry afs_spec) (listseq_list_matchsub lsch lins).

Definition rule_list_matchsub (sch ins : @rule formula) :=
  app3 (listseq_list_matchsub (premsRule sch) (premsRule ins))
    (seq_list_matchsub (conclRule sch) (conclRule ins)).

Definition rule_matchsub_alt (sch ins : @rule formula) : afsSubst :=
  uncurry (uncurry afs_spec) (rule_list_matchsub sch ins).


Definition fml_matchsub' (sch ins : formula) : afSubst :=
  uncurry af_spec (fml_lmatchsub' sch ins).
*)
