Require Import String.
Open Scope string_scope.
Require Import Relations Datatypes.
Require Import List.
Import ListNotations.
Require Import ListSetNotations.

Require Import EqDec.
Require Import Utils.
Require Import FunAgree.
Require Import Tactics.

Definition psc (A : Type) : Type := list A * A.
Definition trf (A : Type) : Type := A -> A.
Definition pscmap {A B : Type} (f : A -> B) : psc A -> psc B :=
  fun x => match x with (ps, c) => (map f ps, f c) end.

(* Class for a plain formal language with sub-expressions and connectives *) 
Class FLANG {expr : Type} {ED : EqDec expr} := {
  ipse : expr -> list expr; (* immediate proper sub-expressions *)
  ipse_rect : forall P : expr -> Type,
      (forall A, (forall A', A' ∈ ipse A -> P A') -> P A) -> forall A, P A;
  ipse_rect_cmp : forall (P : expr -> Type) F A,
      ipse_rect P F A = F A (fun B _ => ipse_rect P F B);
  conn : expr -> list expr -> expr; (* main connective *)
  conn_ipse : forall A, A = conn A (ipse A);
  conn_inj : forall A B l l', length l = length (ipse A) ->
                         length l' = length (ipse B) ->
                         conn A l = conn B l' -> conn A = conn B /\ l = l'}.
  

Section Subexprs.

  Context `{L : FLANG}.

  (* Subexpressions *)
  Definition subexprs : expr -> list expr :=
    ipse_rect _ (fun A IH =>
      A :: list_union (ipse A) (fun A' =>
        (match (in_dec eqdec A' (ipse A)) with
         | left Hin => IH A' Hin
         | right _  => []
         end))).

  Lemma subexprs_eq' (A : expr) :
    subexprs A =
      A :: list_union (ipse A) (fun A' =>
        (if in_dec eqdec A' (ipse A)
         then subexprs A' else [])).
  Proof. unfold subexprs at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Lemma subexprs_eq (A : expr) :
    subexprs A = A :: list_union (ipse A) subexprs.
  Proof. rewrite subexprs_eq'. rewrite union_in_dec. reflexivity. Qed.    

  Lemma in_subexprs_iff : forall A B,
    B ∈ subexprs A <-> B = A \/ exists A', A' ∈ ipse A /\ B ∈ subexprs A'.
  Proof.
    intros A B. rewrite subexprs_eq. simpl.
    setoid_rewrite eq_sym_iff at 1.
    setoid_rewrite In_union_iff. tauto.
  Qed.

  Lemma subexprs_refl : forall A, A ∈ subexprs A.
  Proof. intro A. rewrite subexprs_eq. now left. Qed.

  Lemma subexprs_tran :
    forall A B C, A ∈ subexprs B -> B ∈ subexprs C -> A ∈ subexprs C.
  Proof.
    intros A B C. revert C A B.
    induction C using (@ipse_rect _ _ L).
    rename H into IH. intros A B HA HB.
    rewrite in_subexprs_iff in HB.
    destruct HB as [HB|[C' [HC'in HBin]]].
    - rewrite <- HB. assumption.
    - rewrite in_subexprs_iff. right. exists C'. split; try assumption.
      apply (IH C' HC'in A B); assumption.
  Qed.

  Lemma conn_inj_iff (A B : expr) (l l' : list expr) :
    length l = length (ipse A) ->
    length l' = length (ipse B) ->
      conn A l = conn B l' <-> conn A = conn B /\ l = l'.
  Proof.
    intros Hl Hl'. split; [apply (conn_inj _ _ _ _ Hl Hl')|].
    intros [Heqconn Heql]. rewrite Heqconn, Heql. reflexivity.
  Qed.

  Lemma conn_conn : forall A l,
      length l = length (ipse A) -> conn (conn A l) = conn A.
  Proof.
    intros A l H. eapply conn_inj. reflexivity. eassumption. apply eq_sym, conn_ipse.
  Qed.

  Lemma ipse_conn : forall A l,
      length l = length (ipse A) -> ipse (conn A l) = l.
  Proof.
    intros A l H. eapply conn_inj. reflexivity. eassumption. apply eq_sym, conn_ipse.
  Qed.


  Definition listsubexprs (l : list expr) : list expr := list_union l subexprs.

  Lemma listsubexprs_refl : forall l, incl l (listsubexprs l).
  Proof.
    intros l A H. unfold listsubexprs.
    rewrite In_union_iff.
    exists A. split; try assumption. apply subexprs_refl.
  Qed.

  Lemma listsubexprs_subclosed :
    forall l l', l ⊆ listsubexprs l' -> listsubexprs l ⊆ listsubexprs l'.
  Proof.
    intros l l' H A HAin. unfold listsubexprs in HAin |- *.
    rewrite In_union_iff in HAin.
    rewrite In_union_iff.
    destruct HAin as [B [HBin HAin]].
    apply H in HBin. unfold listsubexprs in HBin.
    rewrite In_union_iff in HBin.
    destruct HBin as [C [HCin HBin]].
    exists C. split; try assumption. eapply subexprs_tran; eassumption.
  Qed.

End Subexprs.


(* Class of indexed expressions, used in particular for substitutions *)
Class IXEXP {expr : Type} `{L : FLANG expr} {Ix : Type} (Var : Ix -> expr) := {
  Var_dec : forall A, {v : Ix | A = Var v} + {forall v, A <> Var v};
  Var_inj : forall v w, Var v = Var w -> v = w;
  Var_ipse : forall v, ipse (Var v) = []; }.


Section Subst.

  Context {formula : Type}.
  Context {EDf : EqDec formula}.
  Context {Lf : @FLANG formula EDf}.

  (* Class of substitutive logics, i.e. logic with means to make substitutions *)
  Class LOGLANG := {
    Atm : string -> formula; (* Atoms *)
    FV : string -> formula; (* Formula variables *)
    ATMVAR :: IXEXP Atm;
    FVVAR :: IXEXP FV;
    Atm_FV_disc : forall p V, Atm p <> FV V; }.

  Definition aSubst := string -> string. (* Atm-substitution *)
  Definition fSubst := string -> formula. (* FV-substitution *)
  Definition afSubst : Type := aSubst * fSubst. (* AtmFV-substition *)

End Subst.


Section Subvar.

  Context `{L : FLANG}.
  Context {Ix : Type}.
  Context (Var : Ix -> expr).
  Context {SVAR : IXEXP Var}.


  Lemma Var_dec_Var (T : Type) (f : Ix -> T) (t : T) : forall V,
    match Var_dec (Var V) with
    | inleft (exist _ W _) => f W
    | inright _ => t
    end = f V.
  Proof.
    intro V. destruct (Var_dec (Var V)) as [[V0 HV0]|HnVar].
    - apply Var_inj in HV0. rewrite HV0. reflexivity.
    - specialize (HnVar V). contradict HnVar. reflexivity.
  Qed.

  Lemma Var_dec_Var_2 (T : Type) (a b : T) :
    forall v, (if Var_dec (Var v) then a else b) = a.
  Proof.
    intro v. destruct (Var_dec (Var v)) as [[v0 Hv0]|HnVar].
    - reflexivity.
    - specialize (HnVar v). contradict HnVar. reflexivity.
  Qed.
  
  Lemma Var_dec_not_Var (T : Type) (f : Ix -> T) (t : T) (A : expr) :
    (forall V, A <> Var V) ->
    match Var_dec A with
    | inleft (exist _ V _) => f V
    | inright _ => t
    end = t.
  Proof.
    intro H. destruct (Var_dec A) as [[V HV]|HnVar]; try reflexivity.
    contradict HV. apply H.
  Qed.

  
  (* Retrieve all Vars of an expr *)
  Definition allVars : expr -> list Ix :=
    ipse_rect _ (fun A IH =>
      match Var_dec A with
      | inleft (exist _ p _) => [p]
      | inright _ => list_union (ipse A) (fun B =>
                      (match in_dec eqdec B (ipse A) with
                         left Hin => IH B Hin | right _  => [] end))
      end).

  Lemma allVars_eq' (A : expr) :
    allVars A =
      match Var_dec A with
      | inleft (exist _ p _) => [p]
      | inright _ => list_union (ipse A) (fun B =>
                      (match in_dec eqdec B (ipse A) with
                         left _ => allVars B | right _  => [] end))
      end.
  Proof. unfold allVars at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Lemma allVars_eq (A : expr) :
    allVars A =
      match Var_dec A with
      | inleft (exist _ p _) => [p]
      | inright _ => list_union (ipse A) allVars
      end.
  Proof. rewrite allVars_eq'. rewrite union_in_dec. reflexivity. Qed.


  Inductive isVar : expr -> Prop := isVar_intro : forall v, isVar (Var v).

  Inductive CtnsVar : expr -> Prop :=
  | CtnsVar_isVar : forall v, CtnsVar (Var v)
  | CtnsVar_inips : forall A A', A' ∈ ipse A -> CtnsVar A' -> CtnsVar A.

  Inductive noVar : expr -> Prop :=
  | noVar_intro : forall A, (forall A', A' ∈ ipse A -> noVar A') -> ~ isVar A -> noVar A.

  Definition isVar_cpt (A : expr) : Prop := if Var_dec A then True else False.

  Lemma isVar_iff_isVar_cpt : forall A, isVar A <-> isVar_cpt A.
  Proof.
    intro A. split.
    - intro H. destruct H. unfold isVar_cpt. rewrite Var_dec_Var_2. exact Logic.I.
    - intro H. unfold isVar_cpt in H. destruct (Var_dec A) as [[v Hv]|HnVar].
      + rewrite Hv. constructor.
      + contradiction.
  Qed.

  Definition CtnsVar_cpt :=
    ipse_rect _ (fun A IH =>
      if Var_dec A then True
      else fold_right (fun B => or
                      (match in_dec eqdec B (ipse A) with
                         left Hin => IH B Hin | right _  => False end))
                               False (ipse A)).

  Lemma CtnsVar_cpt_eq' (A : expr) :
    CtnsVar_cpt A = 
      if Var_dec A then True
      else fold_right (fun B => or
                      (match in_dec eqdec B (ipse A) with
                         left Hin => CtnsVar_cpt B | right _  => False end))
                               False (ipse A).
  Proof. unfold CtnsVar_cpt at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Lemma CtnsVar_cpt_eq (A : expr) :
    CtnsVar_cpt A = 
      if Var_dec A then True
      else fold_right (fun B => or (CtnsVar_cpt B)) False (ipse A).
  Proof. rewrite CtnsVar_cpt_eq'. rewrite fold_right_in_dec. reflexivity. Qed.
  
  Lemma CtnsVar_iff_CtnsVar_cpt : forall A, CtnsVar A <-> CtnsVar_cpt A.
  Proof.
    intro A. split; intro H; [induction H; rewrite CtnsVar_cpt_eq|].
    - rewrite Var_dec_Var_2. exact Logic.I.
    - destruct (Var_dec A) as [[v Hv]|HnVar]; [exact Logic.I|].
      rewrite <- Exists_fold_right. apply Exists_exists.
      exists A'. tauto.
    - revert H. pattern A. revert A. apply ipse_rect.
      intros A IH H. rewrite CtnsVar_cpt_eq in H.
      destruct (Var_dec A) as [[v Hv]|HnVar].
      + rewrite Hv. apply CtnsVar_isVar.
      + rewrite <- Exists_fold_right in H. apply Exists_exists in H.
        destruct H as [A' [Hin HA']].
        apply (CtnsVar_inips A A'); [assumption|].
        apply IH; assumption.
  Qed.

  Definition noVar_cpt : expr -> Prop :=
    ipse_rect _ (fun A IH =>
      match Var_dec A with
      | inleft (exist _ V _) => False
      | inright _ => fold_right (fun B => and
                      (match in_dec eqdec B (ipse A) with
                         left Hin => IH B Hin | right _  => True end))
                               True (ipse A)
      end).

  Lemma noVar_cpt_eq' (A : expr) :
    noVar_cpt A =
      match Var_dec A with
      | inleft (exist _ V _) => False
      | inright _ => fold_right (fun B => and
                      (match in_dec eqdec B (ipse A) with
                         left _ => noVar_cpt B | right _  => True end))
                               True (ipse A)
      end.
  Proof. unfold noVar_cpt at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Lemma noVar_cpt_eq (A : expr) :
    noVar_cpt A =
      match Var_dec A with
      | inleft (exist _ V _) => False
      | inright _ => fold_right (fun B => and (noVar_cpt B)) True (ipse A)
      end.
  Proof. rewrite noVar_cpt_eq'. rewrite fold_right_in_dec. reflexivity. Qed.

  Lemma isVar_not_noVar (A : expr) : isVar A -> ~ noVar A.
  Proof.
    intros His Hno. destruct Hno as [H H0]. contradiction.
  Qed.

  Lemma not_isVar_iff (A : expr) : ~ isVar A <-> (forall v, A <> Var v).
  Proof.
    split.
    - intros His v Heq. contradict His. rewrite Heq. constructor.
    - intros Hall His. destruct His as [x]. apply (Hall x). reflexivity.
  Qed.

  Lemma noVar_iff_noVar_cpt : forall A, noVar A <-> noVar_cpt A.
  Proof.
    intro A. split.
    - intro H. induction H. rewrite noVar_cpt_eq.
      destruct (Var_dec A) as [[v Hv]|HnVar].
      + contradict H1. rewrite Hv. constructor.
      + apply Forall_fold_right, Forall_forall. assumption.
    - pattern A. revert A. apply ipse_rect.
      intros A IH H. rewrite noVar_cpt_eq in H.
      destruct (Var_dec A) as [[v Hv]|HnVar].
      + contradiction.
      + constructor.
        * intros A' HA'. apply IH; try assumption.
          apply Forall_fold_right in H. rewrite Forall_forall in H.
          apply H. assumption.
        * apply not_isVar_iff. assumption.
  Qed.

  Lemma not_CtnsVar_noVar (A : expr) : ~ CtnsVar A <-> noVar A.
  Proof.
    revert A. apply ipse_rect. intros A IH. split.
    - intro H. destruct (Var_dec A) as [[v Hv]|HnVar].
      + contradict H. rewrite Hv. apply CtnsVar_isVar.
      + constructor; try now apply not_isVar_iff.
        intros A' HA'. apply IH; try assumption.
        intro Hctr. apply H. eapply CtnsVar_inips; eassumption.
    - intros Hno Hctns. destruct Hno as [A Hnoips Hneq].
      destruct Hctns as [v|A A' Hin HA'].
      + contradict Hneq. constructor.
      + revert HA'. apply IH; try assumption.
        apply Hnoips. assumption.
  Qed.

  Lemma noVar_ipse (A : expr) : (forall V, A <> Var V) ->
    noVar A <-> Forall noVar (ipse A).
  Proof.
    intro H. split.
    - intro HnVar. destruct HnVar. rewrite not_isVar_iff in H1.
      apply Forall_forall. assumption.
    - intro Hall. apply not_isVar_iff in H.
      rewrite Forall_forall in Hall. apply noVar_intro; assumption.
  Qed.
    
(*    rewrite noVar_eq.
    destruct (Var_dec A) as [[V HV]|HnFV].
    - contradict HV. apply H.
    - rewrite <- Forall_fold_right. tauto.
  Qed.*)

  Lemma not_Var_conn (A : expr) (l : list expr) :
    length l = length (ipse A) -> (forall V, A <> Var V) -> forall V, conn A l <> Var V.
  Proof.
    intros Hlen HnVar V. specialize (HnVar V). contradict HnVar.
    rewrite (conn_ipse (Var V)) in HnVar.
    rewrite Var_ipse in HnVar.
    apply conn_inj in HnVar.
    - destruct HnVar as [Heqconn Heql]. rewrite Heql in Hlen. simpl in Hlen.
      apply eq_sym, length_zero_iff_nil in Hlen.
      rewrite (conn_ipse A). rewrite Heqconn, Hlen.
      rewrite (conn_ipse (Var V)) at 2. rewrite Var_ipse. reflexivity.
    - assumption.
    - rewrite Var_ipse. reflexivity.
  Qed.

  Lemma Var_inj_iff : forall v w, Var v = Var w <-> v = w.
  Proof.
    intros V W. split; [apply Var_inj|].
    intro H. rewrite H. reflexivity.
  Qed.

  Lemma conn_eq_Var (E : expr) (l : list expr) (v : Ix) :
    length l = length (ipse E) -> conn E l = Var v -> E = Var v.
  Proof.
    intros Hlen Heq. rewrite conn_ipse in Heq.
    apply conn_inj in Heq; try assumption; try reflexivity.
    destruct Heq as [HeqX Heql]. rewrite Var_ipse in Heql.
    rewrite Heql in Hlen. rewrite (conn_ipse E).
    destruct (ipse E); [|discriminate].
    rewrite (conn_ipse (Var v)). rewrite HeqX.
    rewrite Var_ipse. reflexivity.
  Qed.

End Subvar.


Arguments Var_dec {expr ED L Ix} (Var) {IXEXP}.
Arguments Var_inj {expr ED L Ix} (Var) {IXEXP}.
Arguments Var_ipse {expr ED L Ix} (Var) {IXEXP}.

Section SubstMore.

  Context `{LL : LOGLANG}.

  Definition fmlAtms := allVars Atm.
  Definition fmlFVs := allVars FV.

  Definition fmlAtms_eq := allVars_eq Atm.
  Definition fmlFVs_eq := allVars_eq FV.

  (* fmlNoFV A iff A has no formula variable *)
  Definition fmlNoFV := noVar FV.
  Definition fmlNoFV_ipse := noVar_ipse FV.

  Definition Atm_dec_Atm {T : Type} := Var_dec_Var Atm T.
  Definition FV_dec_FV {T : Type} := Var_dec_Var FV T.

  Definition Atm_dec_not_Atm {T : Type} := Var_dec_not_Var Atm T.
  Definition FV_dec_not_FV {T : Type} := Var_dec_not_Var FV T.

  Definition not_Atm_conn := not_Var_conn Atm.
  Definition not_FV_conn := not_Var_conn FV.

  Definition Atm_inj_iff := Var_inj_iff Atm.
  Definition FV_inj_iff := Var_inj_iff FV.


  (* Substitution function that applies mappings of variables to a expr *)
  Definition fmlSubst (af : @afSubst formula) : formula -> formula :=
    ipse_rect _ (fun A IH =>
      match Var_dec Atm A with
        inleft (exist _ p _) => Atm (fst af p) | inright _ =>
      match Var_dec FV A with
        inleft (exist _ V _) => snd af V | inright _ =>
      conn A (list_union (ipse A) (fun B =>
                    (match (in_dec eqdec B (ipse A)) with
                       left Hin => [IH B Hin] | right _ => [] end)))
      end end).

  Lemma fmlSubst_eq' (af : @afSubst formula) (A : formula) :
    fmlSubst af A =
      match Var_dec Atm A with
        inleft (exist _ p _) => Atm (fst af p) | inright _ =>
      match Var_dec FV A with
        inleft (exist _ V _) => snd af V | inright _ =>
      conn A (list_union (ipse A) (fun B =>
                    (if in_dec eqdec B (ipse A)
                     then [fmlSubst af B] else [])))
      end end.
  Proof.
    unfold fmlSubst at 1. rewrite ipse_rect_cmp. reflexivity.
  Qed.

  Lemma fmlSubst_eq (af : afSubst) (A : formula) :
    fmlSubst af A =
      match Var_dec Atm A with
        inleft (exist _ p _) => Atm (fst af p) | inright _ =>
      match Var_dec FV A with
        inleft (exist _ V _) => snd af V | inright _ =>
      conn A (map (fmlSubst af) (ipse A))
      end end.
  Proof.
    rewrite fmlSubst_eq' at 1. rewrite union_in_dec_map. reflexivity.
  Qed.

  (* Composing substitutions *)
  Definition a_comp : aSubst -> aSubst -> aSubst := comp.
  Definition f_comp (af1 af2 : afSubst) : fSubst := fun V => fmlSubst (af1) (snd af2 V).
  Definition af_comp (af1 af2 : afSubst) : afSubst :=
    (a_comp (fst af1) (fst af2), f_comp af1 af2).


  Lemma fmlSubst_Atm : forall af p, fmlSubst af (Atm p) = Atm ((fst af) p).
  Proof.
    intros af p. rewrite fmlSubst_eq. rewrite Atm_dec_Atm. reflexivity.
  Qed.

  Lemma fmlSubst_FV : forall af V, fmlSubst af (FV V) = (snd af) V.
  Proof.
    intros af V. rewrite fmlSubst_eq. rewrite FV_dec_FV.
    destruct (Var_dec Atm (FV V)) as [[p Hp]|HnAtm]; try reflexivity.
    apply eq_sym in Hp. contradict Hp. apply Atm_FV_disc.
  Qed.

  Lemma fmlSubst_af_comp : forall {af1 af2 A},
    fmlSubst (af_comp af1 af2) A = fmlSubst af1 (fmlSubst af2 A).
  Proof.
    intros af1 af2. apply ipse_rect. intros A IH.
    rewrite ! (fmlSubst_eq _ A).
    destruct (Var_dec Atm A) as [[p Hp]|HnAtm]; [|destruct (Var_dec FV A) as [[V HV]|HnFV]].
    - rewrite fmlSubst_Atm. reflexivity.
    - simpl. unfold f_comp. reflexivity.
    - pose proof (map_length (fmlSubst af2) (ipse A)) as Hlen.
      pose proof (not_Atm_conn _ _ Hlen HnAtm) as HnAtm'.
      pose proof (not_FV_conn _ _ Hlen HnFV) as HnFV'.
      rewrite fmlSubst_eq.
      rewrite (Atm_dec_not_Atm _ _ _ HnAtm').
      rewrite (FV_dec_not_FV _ _ _ HnFV').
      rewrite conn_conn. rewrite ipse_conn.
      all: try apply map_length.
      rewrite (map_ext_in _ _ _ IH).
      rewrite map_map. reflexivity.
  Qed.
    

  (* Identity substitutions *)
  Definition I_a : aSubst := id.
  Definition I_f : fSubst := fun f => FV f.
  Definition I_af : afSubst := (I_a, I_f).

  Lemma I_af_id : forall A : formula, fmlSubst I_af A = A.
  Proof.
    apply ipse_rect. intros A IH.
    rewrite fmlSubst_eq.
    destruct (Var_dec Atm A) as [[p Hp]|nA];
      [idtac | destruct (Var_dec FV A) as [[V HV]|nF]].
    - rewrite Hp. reflexivity.
    - rewrite HV. reflexivity.
    - rewrite (map_ext_in _ id).
      + rewrite map_id. apply eq_sym, conn_ipse.
      + intros B HB. apply IH. assumption.
  Qed.

  Lemma fmlSubst_fun_agree_iff {a1 f1 a2 f2 A} :
    fmlSubst (a1, f1) A = fmlSubst (a2, f2) A <->
      fun_agree a1 a2 (fmlAtms A) /\
      fun_agree f1 f2 (fmlFVs A).
  Proof.
    revert A. apply ipse_rect. intros A IH.
    rewrite ! fmlSubst_eq. rewrite fmlAtms_eq, fmlFVs_eq.
    destruct (Var_dec Atm A) as [[p Hp]|nA];
      destruct (Var_dec FV A) as [[V HV]|nF].
    - rewrite Hp in HV. contradict HV. apply Atm_FV_disc.
    - rewrite Hp, (Var_ipse Atm). simpl.
      rewrite Atm_inj_iff, fun_agree_Singleton, fun_agree_Empty_iff. tauto.
    - rewrite HV, (Var_ipse FV). simpl.
      rewrite fun_agree_Singleton, fun_agree_Empty_iff. tauto.
    - rewrite union_map. rewrite (union_map (ipse A)).
      rewrite <- ! fun_agree_multi_Union_iff.
      rewrite conn_inj_iff; try apply map_length.
      split.
      + intros [_ H]. split;
          intros l Hl; apply in_map_iff in Hl;
          destruct Hl as [B [HeqB HinB]];
          rewrite <- HeqB; apply IH; try assumption;
          apply (ext_in_map H); assumption.
      + intro H. split; try reflexivity. apply map_ext_in.
        intros B HB. apply IH; try assumption.
        split; apply H; apply in_map_iff; exists B; tauto.
  Qed.


  (* Substitution deduced from matching two expressions *)

  Definition fml_matchsub_Atm : formula -> formula -> aSubst :=
    ipse_rect _ (fun A IH => fun B =>
      match Var_dec Atm A, Var_dec Atm B with
      | inleft (exist _ p _), inleft (exist _ q _) => fun _ => q
      | _, _ => fun p =>
        match in_some_dec p (zip pair (ipse A) (ipse B)) (comp fmlAtms fst) with
        | inleft (exist2 _ _ A'B' Hin _) =>
            IH (fst A'B') (in_zip_pair_fst Hin) (snd A'B') p
        | inright _ => p
        end
      end).

  Lemma fml_matchsub_Atm_eq (A B : formula) :
    fml_matchsub_Atm A B = 
      match Var_dec Atm A, Var_dec Atm B with
      | inleft (exist _ p _), inleft (exist _ q _) => fun _ => q
      | _, _ => fun p =>
        match in_some_dec p (zip pair (ipse A) (ipse B)) (comp fmlAtms fst) with
        | inleft (exist2 _ _ A'B' _ _) => fml_matchsub_Atm (fst A'B') (snd A'B') p
        | inright _ => p
        end
      end.
  Proof. unfold fml_matchsub_Atm at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Definition fml_matchsub_FV : formula -> formula -> fSubst :=
    ipse_rect _ (fun A IH => fun B =>
      match Var_dec FV A with
      | inleft (exist _ V _) => fun _ => B
      | _ => fun V =>
        match in_some_dec V (zip pair (ipse A) (ipse B)) (comp fmlFVs fst) with
        | inleft (exist2 _ _ A'B' Hin _) => IH (fst A'B') (in_zip_pair_fst Hin) (snd A'B') V
        | inright _ => FV V
        end
      end).

  Lemma fml_matchsub_FV_eq (A B : formula) :
    fml_matchsub_FV A B = 
      match Var_dec FV A with
      | inleft (exist _ V _) => fun _ => B
      | _ => fun V =>
        match in_some_dec V (zip pair (ipse A) (ipse B)) (comp fmlFVs fst) with
        | inleft (exist2 _ _ A'B' _ _) => fml_matchsub_FV (fst A'B') (snd A'B') V
        | inright _ => FV V
        end
      end.
  Proof. unfold fml_matchsub_FV at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Definition fml_matchsub (A B : formula) : afSubst :=
    (fml_matchsub_Atm A B, fml_matchsub_FV A B).


  Lemma fmlInst_matchsub (af : afSubst) : forall A B,
    fmlSubst af A = B -> fmlSubst (fml_matchsub A B) A = B.
  Proof.
    intro A. pattern A. revert A. apply ipse_rect.
    intros A IH B Haf. unfold fml_matchsub.
    rewrite fml_matchsub_Atm_eq, fml_matchsub_FV_eq. rewrite fmlSubst_eq in Haf |- *.
    destruct (Var_dec Atm A) as [[p HAtmA]|HnAtmA];
      [destruct (Var_dec Atm B) as [[q HAtmB]|HnAtmB]|
       destruct (Var_dec FV A) as [[V HFVA]|HnFVA]]; simpl.
    - apply eq_sym. assumption.
    - apply eq_sym in Haf. apply HnAtmB in Haf. contradiction.
    - reflexivity.
    - rewrite <- Haf at 1. apply (f_equal (conn A)).
      assert (map (fmlSubst af) (ipse A) = ipse B) as Heqips.
      { rewrite (conn_ipse B) in Haf.
        apply conn_inj in Haf; [|apply map_length|reflexivity]. tauto. }
      assert (length (ipse A) = length (ipse B)) as Hlen.
      { rewrite <- Heqips. apply eq_sym, map_length. }
      assert (forall A'B', A'B' ∈ zip pair (ipse A) (ipse B) ->
      fmlSubst af (fst A'B') = fmlSubst (fml_matchsub (fst A'B') (snd A'B')) (fst A'B'))
        as Hallaf.
      { intros (A', B') Hin. pose proof (map_eq_zip_pair Heqips (A', B') Hin) as Heq.
        apply in_zip_pair_fst in Hin. simpl in Hin, Heq |- *.
        rewrite (IH A' Hin B' Heq). assumption. }
      apply map_ext_in. intros A' HA'.
      destruct (zip_pair_bij_fst _ _ Hlen A' HA') as [A'B' [HA'B' Hfst]].
      destruct af as [a f]. apply fmlSubst_fun_agree_iff. split.
      + intros p Hp.
        destruct (in_some_dec p (zip pair (ipse A) (ipse B)) (comp fmlAtms fst))
          as [[[A0 B0] Hin HpA0]|Hcont].
        * specialize (Hallaf (A0, B0) Hin).
          apply fmlSubst_fun_agree_iff in Hallaf. destruct Hallaf as [HAtm HFV].
          simpl in HAtm, HFV |- *. unfold comp in HpA0. simpl in HpA0.
          specialize (HAtm p HpA0). apply eq_sym. assumption.
        * specialize (Hcont A'B' HA'B'). contradict Hcont.
          unfold comp. rewrite Hfst. assumption.
      + intros V HV.
        destruct (in_some_dec V (zip pair (ipse A) (ipse B)) (comp fmlFVs fst))
          as [[[A0 B0] Hin HVA0]|Hcont].
        * specialize (Hallaf (A0, B0) Hin).
          apply fmlSubst_fun_agree_iff in Hallaf. destruct Hallaf as [HAtm HFV].
          simpl in HAtm, HFV |- *. unfold comp in HVA0. simpl in HVA0.
          specialize (HFV V HVA0). apply eq_sym. assumption.
        * specialize (Hcont A'B' HA'B'). contradict Hcont.
          unfold comp. rewrite Hfst. assumption.
  Qed.

  Lemma fmlSubst_dec : forall A B,
    {af | fmlSubst af A = B} + {forall af, fmlSubst af A <> B}.
  Proof.
    intros A B. destruct (eqdec (fmlSubst (fml_matchsub A B) A) B) as [Heq|Hneq].
    - left. exists (fml_matchsub A B). assumption.
    - right. intro af. contradict Hneq. apply (fmlInst_matchsub af). assumption.
  Defined.

  Lemma In_ipse_subst : forall A A' af,
    A' ∈ ipse A -> fmlSubst af A' ∈ ipse (fmlSubst af A).
  Proof.
    intros A A' af Hin. rewrite ! fmlSubst_eq. rewrite <- fmlSubst_eq.
    destruct (Var_dec Atm A) as [[p Hp]|HnAtm]; [|destruct (Var_dec FV A) as [[V HV]|HnFV]].
    - rewrite Hp in Hin. rewrite (Var_ipse Atm) in Hin. contradiction.
    - rewrite HV in Hin. rewrite (Var_ipse FV) in Hin. contradiction.
    - rewrite ipse_conn. apply in_map. assumption. apply map_length.
  Qed.
    
  Theorem In_subexprs_subst : forall A B pf, A ∈ subexprs B -> fmlSubst pf A ∈ subexprs (fmlSubst pf B).
  Proof.
    intros A B af. revert A. induction B using (@ipse_rect _ _ Lf).
    rename H into IH. intros A HAB. apply in_subexprs_iff in HAB.
    destruct HAB as [HAB|[A' [HA' HA]]].
    - rewrite HAB. apply subexprs_refl.
    - apply in_subexprs_iff. right. specialize (IH A' HA' A HA).
      exists (fmlSubst af A'). split; try assumption.
      apply In_ipse_subst. assumption.
  Qed.

  (* An alternative way of defining a substitutions by matching expre *)
(*  Definition fml_lmatchsub' : expr -> expr ->
    (list (string * string)) * (list (string * expr)) :=
    ipse_rect _ (fun A IH => fun B =>
      match Var_dec Atm A, Var_dec Atm B with
      | inleft (exist _ p _), inleft (exist _ q _) => ([(p, q)], [])
      | _, _ =>
          match Var_dec FV A with
          | inleft (exist _ V _) => ([], [(V, B)])
          | inright _ =>
              fold_right (fun A'B' => let A' := fst A'B' in let B' := snd A'B' in
                                   app2 (
                                   match in_dec eqdec A' (ipse A) with
                                   | left Hin => IH A' Hin B'
                                   | right _ => ([], [])
                                   end))
                         ([], [])
                         (zip pair (ipse A) (ipse B))
          end
      end).
*)

End SubstMore.
