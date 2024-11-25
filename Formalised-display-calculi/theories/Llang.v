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

(* Class for a plain language of logic *) 
Class LLANG {formula : Type} {ED : EqDec formula} := {
  ipsubfmls  : formula -> list formula; (* immediate proper subformulae *)
  ipsubfmls_rect : forall P : formula -> Type,
      (forall A, (forall A', A' ∈ ipsubfmls A -> P A') -> P A) -> forall A, P A;
  ipsubfmls_rect_cmp : forall (P : formula -> Type) F A,
      ipsubfmls_rect P F A = F A (fun B _ => ipsubfmls_rect P F B);
  conn : formula -> list formula -> formula; (* main connective *)
  conn_ipsubfmls_eq : forall A, A = conn A (ipsubfmls A);
  conn_inj : forall A B l l', length l = length (ipsubfmls A) ->
                         length l' = length (ipsubfmls B) ->
                         conn A l = conn B l' -> conn A = conn B /\ l = l'}.
  

Section SUBFML.

  Context `{L : LLANG}.

  (* Subformulae *)
  Definition subfmls : formula -> list formula :=
    ipsubfmls_rect _ (fun A IH =>
      fold_right (fun B => app 
        (match (in_dec eqdec B (ipsubfmls A)) with
         | left Hin => IH B Hin
         | right _  => []
         end)) [A] (ipsubfmls A)).

  Lemma in_subfmls_iff : forall A B,
    B ∈ (subfmls A) <-> (exists A', A' ∈ (ipsubfmls A) /\ B ∈ (subfmls A')) \/ B = A.
  Proof.
    intros A B. unfold subfmls at 1.
    rewrite ipsubfmls_rect_cmp.
    rewrite In_fold_right_app_bc_iff. split.
    - intro H. destruct H as [H|H].
      + left. destruct H as [A' [HA'in H]].
        destruct (in_dec eqdec A' (ipsubfmls A)); try contradiction.
        exists A'. split; assumption.
      + right. destruct H; try contradiction. apply eq_sym. assumption.
    - intros [H|H].
      + left. destruct H as [A' [HA'in H]].
        exists A'. split; try assumption.
        destruct (in_dec eqdec A' (ipsubfmls A)); tauto.
      + right. left. apply eq_sym. assumption.
  Qed.

  Lemma subfmls_refl : forall A, A ∈ (subfmls A).
  Proof.
    intro A. unfold subfmls. rewrite ipsubfmls_rect_cmp.
    apply sing_incl_in. apply bc_incl_fold_right_app_bc.
  Qed.

  Lemma subfmls_tran :
    forall A B C, A ∈ (subfmls B) -> B ∈ (subfmls C) -> A ∈ (subfmls C).
  Proof.
    intros A B C. revert C A B.
    induction C using (@ipsubfmls_rect _ _ L).
    rename H into IH. intros A B HA HB.
    rewrite in_subfmls_iff in HB.
    destruct HB as [[C' [HC'in HBin]]|HB].
    - rewrite in_subfmls_iff. left. exists C'. split; try assumption.
      apply (IH C' HC'in A B); assumption.
    - rewrite <- HB. assumption.
  Qed.

  Lemma conn_inj_iff (A B : formula) (l l' : list formula) :
    length l = length (ipsubfmls A) ->
    length l' = length (ipsubfmls B) -> conn A l = conn B l' <-> conn A = conn B /\ l = l'.
  Proof.
    intros Hl Hl'. split; [apply (conn_inj _ _ _ _ Hl Hl')|].
    intros [Heqconn Heql]. rewrite Heqconn, Heql. reflexivity.
  Qed.

  Lemma conn_conn : forall A l,
      length l = length (ipsubfmls A) -> conn (conn A l) = conn A.
  Proof.
    intros A l H. eapply conn_inj. reflexivity. eassumption. apply eq_sym, conn_ipsubfmls_eq.
  Qed.

  Lemma ipsubfmls_conn : forall A l,
      length l = length (ipsubfmls A) -> ipsubfmls (conn A l) = l.
  Proof.
    intros A l H. eapply conn_inj. reflexivity. eassumption. apply eq_sym, conn_ipsubfmls_eq.
  Qed.

End SUBFML.

Section Subst.

  Context `{formula : Type}.

  (* Class of variables allowing substitutions *)
  Class SUBVAR `{L : LLANG formula} (Var : string -> formula) := {
    Var_dec : forall A, {v : string | A = Var v} + {forall v, A <> Var v};
    Var_inj : forall v w, Var v = Var w -> v = w;
    Var_ipsubfmls : forall v, ipsubfmls (Var v) = []; }.

  (* Class of substitutive logics, i.e. logic with means to make substitutions *)
  Class SUBSTLLANG `{L : LLANG formula} := {
    Atm : string -> formula; (* Atoms *)
    FV : string -> formula; (* Formula variables *)
    ATMVAR :: SUBVAR Atm;
    FVVAR :: SUBVAR FV;
    Atm_FV_disc : forall p V, Atm p <> FV V; }.

  Definition aSubst := string -> string. (* Atm-substitution *)
  Definition fSubst := string -> formula. (* FV-substitution *)
  Definition afSubst : Type := aSubst * fSubst. (* AtmFV-substition *)

End Subst.

Arguments Var_dec {formula ED L} (Var) {SUBVAR}.
Arguments Var_inj {formula ED L} (Var) {SUBVAR}.
Arguments Var_ipsubfmls {formula ED L} (Var) {SUBVAR}.

Section SubstMore.

  Context `{SL : SUBSTLLANG}.
  
  (* Retrieve atoms *)
  Definition fmlAtms : formula -> list string :=
    ipsubfmls_rect _ (fun A IH =>
      match Var_dec Atm A with
      | inleft (exist _ p _) => [p]
      | inright _ => fold_right (fun B => app
                      (match in_dec eqdec B (ipsubfmls A) with
                         left Hin => IH B Hin | right _  => [] end))
                               [] (ipsubfmls A)
      end).

  Lemma fmlAtms_eq' (A : formula) :
    fmlAtms A =
      match Var_dec Atm A with
      | inleft (exist _ p _) => [p]
      | inright _ => fold_right (fun B => app
                      (match in_dec eqdec B (ipsubfmls A) with
                         left _ => fmlAtms B | right _  => [] end))
                               [] (ipsubfmls A)
      end.
  Proof. unfold fmlAtms at 1. rewrite ipsubfmls_rect_cmp. reflexivity. Qed.

  Lemma fmlAtms_eq (A : formula) :
    fmlAtms A =
      match Var_dec Atm A with
      | inleft (exist _ p _) => [p]
      | inright _ => fold_right (fun B => app (fmlAtms B)) [] (ipsubfmls A)
      end.
  Proof. rewrite fmlAtms_eq'. rewrite fold_right_in_dec. reflexivity. Qed.
  
  
  (* Retrieve formula variables *)
  Definition fmlFVs : formula -> list string :=
    ipsubfmls_rect _ (fun A IH =>
      match Var_dec FV A with
      | inleft (exist _ V _) => [V]
      | inright _ => fold_right (fun B => app
                      (match in_dec eqdec B (ipsubfmls A) with
                         left Hin => IH B Hin | right _  => [] end))
                               [] (ipsubfmls A)
      end).

  Lemma fmlFVs_eq' (A : formula) :
    fmlFVs A =
      match Var_dec FV A with
      | inleft (exist _ V _) => [V]
      | inright _ => fold_right (fun B => app
                      (match in_dec eqdec B (ipsubfmls A) with
                         left _ => fmlFVs B | right _  => [] end))
                               [] (ipsubfmls A)
      end.
  Proof. unfold fmlFVs at 1. rewrite ipsubfmls_rect_cmp. reflexivity. Qed.

  Lemma fmlFVs_eq (A : formula) :
    fmlFVs A =
      match Var_dec FV A with
      | inleft (exist _ V _) => [V]
      | inright _ => fold_right (fun B => app (fmlFVs B)) [] (ipsubfmls A)
      end.
  Proof. rewrite fmlFVs_eq'. rewrite fold_right_in_dec. reflexivity. Qed.


  (* fmlNoFV A iff A has no formula variable *)
  Definition fmlNoFV : formula -> Prop :=
    ipsubfmls_rect _ (fun A IH =>
      match Var_dec FV A with
      | inleft (exist _ V _) => False
      | inright _ => fold_right (fun B => and
                      (match in_dec eqdec B (ipsubfmls A) with
                         left Hin => IH B Hin | right _  => True end))
                               True (ipsubfmls A)
      end).

  Lemma fmlNoFV_eq' (A : formula) :
    fmlNoFV A =
      match Var_dec FV A with
      | inleft (exist _ V _) => False
      | inright _ => fold_right (fun B => and
                      (match in_dec eqdec B (ipsubfmls A) with
                         left _ => fmlNoFV B | right _  => True end))
                               True (ipsubfmls A)
      end.
  Proof. unfold fmlNoFV at 1. rewrite ipsubfmls_rect_cmp. reflexivity. Qed.

  Lemma fmlNoFV_eq (A : formula) :
    fmlNoFV A =
      match Var_dec FV A with
      | inleft (exist _ V _) => False
      | inright _ => fold_right (fun B => and (fmlNoFV B)) True (ipsubfmls A)
      end.
  Proof. rewrite fmlNoFV_eq'. rewrite fold_right_in_dec. reflexivity. Qed.


  Lemma fmlNoFV_ipsubfmls (A : formula) : (forall V, A <> FV V) ->
    fmlNoFV A <-> Forall fmlNoFV (ipsubfmls A).
  Proof.
    intro H. rewrite fmlNoFV_eq.
    destruct (Var_dec FV A) as [[V HV]|HnFV].
    - contradict HV. apply H.
    - rewrite <- Forall_fold_right. tauto.
  Qed.


  (* Substitution function that applies mappings of variables to a formula *)
  Definition fmlSubst (af : @afSubst formula) : formula -> formula :=
    ipsubfmls_rect _ (fun A IH =>
      match Var_dec Atm A with
        inleft (exist _ p _) => Atm (fst af p) | inright _ =>
      match Var_dec FV A with
        inleft (exist _ V _) => snd af V | inright _ =>
      conn A (fold_right (fun B => app
                    (match (in_dec eqdec B (ipsubfmls A)) with
                       left Hin => [IH B Hin] | right _ => [] end))
                    [] (ipsubfmls A))
      end end).

  Lemma fmlSubst_eq' (af : @afSubst formula) (A : formula) :
    fmlSubst af A =
      match Var_dec Atm A with
        inleft (exist _ p _) => Atm (fst af p) | inright _ =>
      match Var_dec FV A with
        inleft (exist _ V _) => snd af V | inright _ =>
      conn A (fold_right (fun B => app
                    (if in_dec eqdec B (ipsubfmls A)
                     then [fmlSubst af B] else []))
                    [] (ipsubfmls A))
      end end.
  Proof.
    unfold fmlSubst at 1. rewrite ipsubfmls_rect_cmp. reflexivity.
  Qed.

  Lemma fmlSubst_eq (af : afSubst) (A : formula) :
    fmlSubst af A =
      match Var_dec Atm A with
        inleft (exist _ p _) => Atm (fst af p) | inright _ =>
      match Var_dec FV A with
        inleft (exist _ V _) => snd af V | inright _ =>
      conn A (map (fmlSubst af) (ipsubfmls A))
      end end.
  Proof.
    rewrite fmlSubst_eq' at 1. rewrite fold_right_in_dec_map. reflexivity.
  Qed.

  (* Composing substitutions *)
  Definition a_comp : aSubst -> aSubst -> aSubst := compose.
  Definition f_comp (af1 af2 : afSubst) : fSubst := fun V => fmlSubst (af1) (snd af2 V).
  Definition af_comp (af1 af2 : afSubst) : afSubst :=
    (a_comp (fst af1) (fst af2), f_comp af1 af2).


  Lemma Atm_dec_Atm {T : Type} (f : string -> T) (t : T) : forall p,
    match Var_dec Atm (Atm p) with
    | inleft (exist _ q _) => f q
    | inright _ => t
    end = f p.
  Proof.
    intro p. destruct (Var_dec Atm (Atm p)) as [[p0 Hp0]|HnAtm].
    - apply (Var_inj Atm) in Hp0. rewrite Hp0. reflexivity.
    - specialize (HnAtm p). contradict HnAtm. reflexivity.
  Qed.

  Lemma FV_dec_FV {T : Type} (f : string -> T) (t : T) : forall V,
    match Var_dec FV (FV V) with
    | inleft (exist _ W _) => f W
    | inright _ => t
    end = f V.
  Proof.
    intro V. destruct (Var_dec FV (FV V)) as [[V0 HV0]|HnFV].
    - apply (Var_inj FV) in HV0. rewrite HV0. reflexivity.
    - specialize (HnFV V). contradict HnFV. reflexivity.
  Qed.
  
  Lemma Atm_dec_not_Atm {T : Type} (f : string -> T) (t : T) (A : formula) :
    (forall p, A <> Atm p) ->
    match Var_dec Atm A with
    | inleft (exist _ p _) => f p
    | inright _ => t
    end = t.
  Proof.
    intro H. destruct (Var_dec Atm A) as [[p Hp]|HnAtm]; try reflexivity.
    contradict Hp. apply H.
  Qed.
  
  Lemma FV_dec_not_FV {T : Type} (f : string -> T) (t : T) (A : formula) :
    (forall V, A <> FV V) ->
    match Var_dec FV A with
    | inleft (exist _ V _) => f V
    | inright _ => t
    end = t.
  Proof.
    intro H. destruct (Var_dec FV A) as [[V HV]|HnFV]; try reflexivity.
    contradict HV. apply H.
  Qed.


  Lemma not_Atm_conn (A : formula) (l : list formula) :
    length l = length (ipsubfmls A) -> (forall p, A <> Atm p) -> forall p, conn A l <> Atm p.
  Proof.
    intros Hlen HnAtm p. specialize (HnAtm p). contradict HnAtm.
    rewrite (conn_ipsubfmls_eq (Atm p)) in HnAtm.
    rewrite (Var_ipsubfmls Atm) in HnAtm.
    apply conn_inj in HnAtm.
    - destruct HnAtm as [Heqconn Heql]. rewrite Heql in Hlen. simpl in Hlen.
      apply eq_sym, length_zero_iff_nil in Hlen.
      rewrite (conn_ipsubfmls_eq A). rewrite Heqconn, Hlen.
      rewrite (conn_ipsubfmls_eq (Atm p)) at 2. rewrite (Var_ipsubfmls Atm). reflexivity.
    - assumption.
    - rewrite (Var_ipsubfmls Atm). reflexivity.
  Qed.    

  Lemma not_FV_conn (A : formula) (l : list formula) :
    length l = length (ipsubfmls A) -> (forall V, A <> FV V) -> forall V, conn A l <> FV V.
  Proof.
    intros Hlen HnFV V. specialize (HnFV V). contradict HnFV.
    rewrite (conn_ipsubfmls_eq (FV V)) in HnFV.
    rewrite (Var_ipsubfmls FV) in HnFV.
    apply conn_inj in HnFV.
    - destruct HnFV as [Heqconn Heql]. rewrite Heql in Hlen. simpl in Hlen.
      apply eq_sym, length_zero_iff_nil in Hlen.
      rewrite (conn_ipsubfmls_eq A). rewrite Heqconn, Hlen.
      rewrite (conn_ipsubfmls_eq (FV V)) at 2. rewrite (Var_ipsubfmls FV). reflexivity.
    - assumption.
    - rewrite (Var_ipsubfmls FV). reflexivity.
  Qed.


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
    intros af1 af2. apply ipsubfmls_rect. intros A IH.
    rewrite ! (fmlSubst_eq _ A).
    destruct (Var_dec Atm A) as [[p Hp]|HnAtm]; [|destruct (Var_dec FV A) as [[V HV]|HnFV]].
    - rewrite fmlSubst_Atm. reflexivity.
    - simpl. unfold f_comp. reflexivity.
    - pose proof (map_length (fmlSubst af2) (ipsubfmls A)) as Hlen.
      pose proof (not_Atm_conn _ _ Hlen HnAtm) as HnAtm'.
      pose proof (not_FV_conn _ _ Hlen HnFV) as HnFV'.
      rewrite fmlSubst_eq.
      rewrite (Atm_dec_not_Atm _ _ _ HnAtm').
      rewrite (FV_dec_not_FV _ _ _ HnFV').
      rewrite conn_conn. rewrite ipsubfmls_conn.
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
    apply ipsubfmls_rect. intros A IH.
    rewrite fmlSubst_eq.
    destruct (Var_dec Atm A) as [[p Hp]|nA];
      [idtac | destruct (Var_dec FV A) as [[V HV]|nF]].
    - rewrite Hp. reflexivity.
    - rewrite HV. reflexivity.
    - rewrite (map_ext_in _ id).
      + rewrite map_id. apply eq_sym, conn_ipsubfmls_eq.
      + intros B HB. apply IH. assumption.
  Qed.

  Lemma Atm_inj_iff : forall p q, Atm p = Atm q <-> p = q.
  Proof.
    intros p q. split; [apply (Var_inj Atm)|].
    intro H. rewrite H. reflexivity.
  Qed.

  Lemma FV_inj_iff : forall V W, FV V = FV W <-> V = W.
  Proof.
    intros V W. split; [apply (Var_inj FV)|].
    intro H. rewrite H. reflexivity.
  Qed.

  Lemma fmlSubst_fun_agree_iff {a1 f1 a2 f2 A} :
    fmlSubst (a1, f1) A = fmlSubst (a2, f2) A <->
      fun_agree a1 a2 (fmlAtms A) /\
      fun_agree f1 f2 (fmlFVs A).
  Proof.
    revert A. apply ipsubfmls_rect. intros A IH.
    rewrite ! fmlSubst_eq. rewrite fmlAtms_eq, fmlFVs_eq.
    destruct (Var_dec Atm A) as [[p Hp]|nA];
      destruct (Var_dec FV A) as [[V HV]|nF].
    - rewrite Hp in HV. contradict HV. apply Atm_FV_disc.
    - rewrite Hp, (Var_ipsubfmls Atm). simpl.
      rewrite Atm_inj_iff, fun_agree_Singleton, fun_agree_Empty_iff. tauto.
    - rewrite HV, (Var_ipsubfmls FV). simpl.
      rewrite fun_agree_Singleton, fun_agree_Empty_iff. tauto.
    - rewrite fold_right_map. rewrite (@fold_right_map _ _ _ _ fmlFVs).
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


  (* Substitution deduced from matching two formulae *)

  Definition fml_matchsub_Atm : formula -> formula -> aSubst :=
    ipsubfmls_rect _ (fun A IH => fun B =>
      match Var_dec Atm A, Var_dec Atm B with
      | inleft (exist _ p _), inleft (exist _ q _) => fun _ => q
      | _, _ => fun p =>
        match in_some_dec p (zip pair (ipsubfmls A) (ipsubfmls B)) (fmlAtms ∘ fst) with
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
        match in_some_dec p (zip pair (ipsubfmls A) (ipsubfmls B)) (fmlAtms ∘ fst) with
        | inleft (exist2 _ _ A'B' _ _) => fml_matchsub_Atm (fst A'B') (snd A'B') p
        | inright _ => p
        end
      end.
  Proof. unfold fml_matchsub_Atm at 1. rewrite ipsubfmls_rect_cmp. reflexivity. Qed.

  Definition fml_matchsub_FV : formula -> formula -> fSubst :=
    ipsubfmls_rect _ (fun A IH => fun B =>
      match Var_dec FV A with
      | inleft (exist _ V _) => fun _ => B
      | _ => fun V =>
        match in_some_dec V (zip pair (ipsubfmls A) (ipsubfmls B)) (fmlFVs ∘ fst) with
        | inleft (exist2 _ _ A'B' Hin _) => IH (fst A'B') (in_zip_pair_fst Hin) (snd A'B') V
        | inright _ => FV V
        end
      end).

  Lemma fml_matchsub_FV_eq (A B : formula) :
    fml_matchsub_FV A B = 
      match Var_dec FV A with
      | inleft (exist _ V _) => fun _ => B
      | _ => fun V =>
        match in_some_dec V (zip pair (ipsubfmls A) (ipsubfmls B)) (fmlFVs ∘ fst) with
        | inleft (exist2 _ _ A'B' _ _) => fml_matchsub_FV (fst A'B') (snd A'B') V
        | inright _ => FV V
        end
      end.
  Proof. unfold fml_matchsub_FV at 1. rewrite ipsubfmls_rect_cmp. reflexivity. Qed.

  Definition fml_matchsub (A B : formula) : afSubst :=
    (fml_matchsub_Atm A B, fml_matchsub_FV A B).


  Lemma fmlInst_matchsub (af : afSubst) : forall A B,
    fmlSubst af A = B -> fmlSubst (fml_matchsub A B) A = B.
  Proof.
    intro A. pattern A. revert A. apply ipsubfmls_rect.
    intros A IH B Haf. unfold fml_matchsub.
    rewrite fml_matchsub_Atm_eq, fml_matchsub_FV_eq. rewrite fmlSubst_eq in Haf |- *.
    destruct (Var_dec Atm A) as [[p HAtmA]|HnAtmA];
      [destruct (Var_dec Atm B) as [[q HAtmB]|HnAtmB]|
       destruct (Var_dec FV A) as [[V HFVA]|HnFVA]]; simpl.
    - apply eq_sym. assumption.
    - apply eq_sym in Haf. apply HnAtmB in Haf. contradiction.
    - reflexivity.
    - rewrite <- Haf at 1. apply (f_equal (conn A)).
      assert (map (fmlSubst af) (ipsubfmls A) = ipsubfmls B) as Heqips.
      { rewrite (conn_ipsubfmls_eq B) in Haf.
        apply conn_inj in Haf; [|apply map_length|reflexivity]. tauto. }
      assert (length (ipsubfmls A) = length (ipsubfmls B)) as Hlen.
      { rewrite <- Heqips. apply eq_sym, map_length. }
      assert (forall A'B', A'B' ∈ zip pair (ipsubfmls A) (ipsubfmls B) ->
      fmlSubst af (fst A'B') = fmlSubst (fml_matchsub (fst A'B') (snd A'B')) (fst A'B'))
        as Hallaf.
      { intros (A', B') Hin. pose proof (map_eq_zip_pair Heqips (A', B') Hin) as Heq.
        apply in_zip_pair_fst in Hin. simpl in Hin, Heq |- *.
        rewrite (IH A' Hin B' Heq). assumption. }
      apply map_ext_in. intros A' HA'.
      destruct (zip_pair_eq_length Hlen A' HA') as [A'B' [HA'B' Hfst]].
      destruct af as [a f]. apply fmlSubst_fun_agree_iff. split.
      + intros p Hp.
        destruct (in_some_dec p (zip pair (ipsubfmls A) (ipsubfmls B)) (fmlAtms ∘ fst))
          as [[[A0 B0] Hin HpA0]|Hcont].
        * specialize (Hallaf (A0, B0) Hin).
          apply fmlSubst_fun_agree_iff in Hallaf. destruct Hallaf as [HAtm HFV].
          simpl in HAtm, HFV |- *. unfold compose in HpA0. simpl in HpA0.
          specialize (HAtm p HpA0). apply eq_sym. assumption.
        * specialize (Hcont A'B' HA'B'). contradict Hcont.
          unfold compose. rewrite Hfst. assumption.
      + intros V HV.
        destruct (in_some_dec V (zip pair (ipsubfmls A) (ipsubfmls B)) (fmlFVs ∘ fst))
          as [[[A0 B0] Hin HVA0]|Hcont].
        * specialize (Hallaf (A0, B0) Hin).
          apply fmlSubst_fun_agree_iff in Hallaf. destruct Hallaf as [HAtm HFV].
          simpl in HAtm, HFV |- *. unfold compose in HVA0. simpl in HVA0.
          specialize (HFV V HVA0). apply eq_sym. assumption.
        * specialize (Hcont A'B' HA'B'). contradict Hcont.
          unfold compose. rewrite Hfst. assumption.
  Qed.

  Lemma fmlSubst_dec : forall A B,
    {af | fmlSubst af A = B} + {forall af, fmlSubst af A <> B}.
  Proof.
    intros A B. destruct (eqdec (fmlSubst (fml_matchsub A B) A) B) as [Heq|Hneq].
    - left. exists (fml_matchsub A B). assumption.
    - right. intro af. contradict Hneq. apply (fmlInst_matchsub af). assumption.
  Defined.

  Lemma In_ipsubfmls_subst : forall A A' af,
    A' ∈ ipsubfmls A -> fmlSubst af A' ∈ ipsubfmls (fmlSubst af A).
  Proof.
    intros A A' af Hin. rewrite ! fmlSubst_eq. rewrite <- fmlSubst_eq.
    destruct (Var_dec Atm A) as [[p Hp]|HnAtm]; [|destruct (Var_dec FV A) as [[V HV]|HnFV]].
    - rewrite Hp in Hin. rewrite (Var_ipsubfmls Atm) in Hin. contradiction.
    - rewrite HV in Hin. rewrite (Var_ipsubfmls FV) in Hin. contradiction.
    - rewrite ipsubfmls_conn. apply in_map. assumption. apply map_length.
  Qed.
    
  Theorem In_subfmls_subst : forall A B pf, A ∈ subfmls B -> fmlSubst pf A ∈ subfmls (fmlSubst pf B).
  Proof.
    intros A B af. revert A. induction B using (@ipsubfmls_rect _ _ L).
    rename H into IH. intros A HAB. apply in_subfmls_iff in HAB.
    destruct HAB as [[A' [HA' HA]]|HAB].
    - apply in_subfmls_iff. left. specialize (IH A' HA' A HA).
      exists (fmlSubst af A'). split; try assumption.
      apply In_ipsubfmls_subst. assumption.
    - rewrite HAB. apply subfmls_refl.
  Qed.

  (* An alternative way of defining a substitutions by matching formulae *)
(*  Definition fml_lmatchsub' : formula -> formula ->
    (list (string * string)) * (list (string * formula)) :=
    ipsubfmls_rect _ (fun A IH => fun B =>
      match Var_dec Atm A, Var_dec Atm B with
      | inleft (exist _ p _), inleft (exist _ q _) => ([(p, q)], [])
      | _, _ =>
          match Var_dec FV A with
          | inleft (exist _ V _) => ([], [(V, B)])
          | inright _ =>
              fold_right (fun A'B' => let A' := fst A'B' in let B' := snd A'B' in
                                   app2 (
                                   match in_dec eqdec A' (ipsubfmls A) with
                                   | left Hin => IH A' Hin B'
                                   | right _ => ([], [])
                                   end))
                         ([], [])
                         (zip pair (ipsubfmls A) (ipsubfmls B))
          end
      end).
*)

End SubstMore.
