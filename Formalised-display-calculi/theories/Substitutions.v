Require Import String.
Open Scope string_scope.
Require Import Datatypes.
Require Import List ListSet.
Import ListNotations.
Require Import ListSetNotations.
Require Import Arith.
Require Import Wellfounded.
Require Import Lia.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import FunAgree.
Require Import Lang.
Require Import Sequents.


Open Scope nat_scope.

Section Substitutions.
  
  Context `{SL : STRLANG}.

  Definition sSubst : Type := string -> (structr).
  Definition afsSubst : Type := (@afSubst formula) * sSubst.


  Definition strSubst (afs : afsSubst) : structr -> structr :=
    ipse_rect _ (fun X IH =>
      match Var_dec SV X with
        inleft (exist _ V _) => (snd afs V) | inright _ =>
      match Var_dec FS X with
        inleft (exist _ A _) => FS (fmlSubst (fst afs) A) | inright _ =>
      conn X (list_union (ipse X) (fun X' =>
                    match (in_dec eqdec X' (ipse X)) with
                      left Hin => [IH X' Hin] | right _ => [] end))
      end end).

  Lemma strSubst_eq' (afs : afsSubst) (X : structr) :
    strSubst afs X =
      match Var_dec SV X with
        inleft (exist _ V _) => (snd afs V) | inright _ =>
      match Var_dec FS X with
        inleft (exist _ A _) => FS (fmlSubst (fst afs) A) | inright _ =>
      conn X (list_union (ipse X) (fun X' =>
                    if in_dec eqdec X' (ipse X) then [strSubst afs X'] else []))

      end end.
  Proof.
    unfold strSubst at 1. rewrite ipse_rect_cmp. reflexivity.
  Qed.

  Lemma strSubst_eq (afs : afsSubst) (X : structr) :
    strSubst afs X =
      match Var_dec SV X with
        inleft (exist _ V _) => (snd afs V) | inright _ =>
      match Var_dec FS X with
        inleft (exist _ A _) => FS (fmlSubst (fst afs) A) | inright _ =>
      conn X (map (strSubst afs) (ipse X))
      end end.
  Proof.
    rewrite strSubst_eq' at 1. rewrite union_in_dec_map. reflexivity.
  Qed.

  Lemma strSubst_SV : forall afs V, strSubst afs (SV V) = snd afs V.
  Proof.
    intros afs V. rewrite strSubst_eq.
    rewrite Var_dec_Var. reflexivity.
  Qed.

  Lemma strSubst_FS : forall afs A, strSubst afs (FS A) = FS (fmlSubst (fst afs) A).
  Proof.
    intros afs A. rewrite strSubst_eq.
    destruct (Var_dec SV (FS A)) as [[V HV]|HneqSV];
      [contradict HV; apply not_eq_sym; apply SV_FS_disc|].
    rewrite Var_dec_Var. reflexivity.
  Qed.

  Definition seqSubst (afs : afsSubst) (s : sequent) : sequent :=
    match s with X ⊢ Y => strSubst afs X ⊢ strSubst afs Y end.
  Definition ruleSubst (afs : afsSubst) (r : rule) : rule :=
    match r with (ps, c) => (map (seqSubst afs) ps, seqSubst afs c) end.

  Lemma subst_strIsFml {afs} {X Y : structr} : strSubst afs X = Y -> strIsFml X -> strIsFml Y.
  Proof.
    intros Hsub HfmlX. destruct HfmlX as [A].
    rewrite strSubst_FS in Hsub. rewrite <- Hsub.
    constructor.
  Qed.

  Lemma seqSubst_strSubst {afs X1 Y1 X2 Y2} :
    seqSubst afs (X1 ⊢ Y1) = X2 ⊢ Y2 <-> strSubst afs X1 = X2 /\ strSubst afs Y1 = Y2.
  Proof.
    split.
    - intro H. simpl in H. injection H. tauto.
    - intro H. simpl. rewrite (proj1 H), (proj2 H). reflexivity.
  Qed.

  Lemma NoDup_seqSVs_strSVs {X Y : structr} :
    NoDup (seqSVs (X ⊢ Y)) -> NoDup (strSVs X) /\ NoDup (strSVs Y).
  Proof.
    intro H. split; [apply (NoDup_app_remove_r _ _ H) | apply (NoDup_app_remove_l _ _ H)].
  Qed.

  Lemma strSubst_fml {X af} : forall (s1 s2 : sSubst), strIsFml X ->
    strSubst (af, s1) X = strSubst (af, s2) X.
  Proof.
    intros s1 s2 H. destruct H as [A].
    rewrite ! strSubst_FS. reflexivity.
  Qed.

  Lemma premsRule_ruleSubst {r : rule} {pfs : afsSubst} :
    premsRule (ruleSubst pfs r) = map (seqSubst pfs) (premsRule r).
  Proof. destruct r. simpl. reflexivity. Qed.

  Lemma conclRule_ruleSubst {r : rule} {pfs : afsSubst} :
    conclRule (ruleSubst pfs r) = seqSubst pfs (conclRule r).
  Proof. destruct r. simpl. reflexivity. Qed.

  Definition I_s : sSubst := fun x => SV x.
  Definition I_afs : afsSubst := (I_af, I_s).

  Lemma I_afs_id_str : forall X : structr, strSubst I_afs X = X.
  Proof.
    apply ipse_rect.
    intros X IHX. rewrite strSubst_eq.
    destruct (Var_dec SV X) as [[V HV]|HneqSV];
      [|destruct (Var_dec FS X) as [[A HA]|HneqFS]].
    - simpl. rewrite HV. reflexivity.
    - simpl. rewrite I_af_id. apply eq_sym. assumption.
    - rewrite (map_ext_in _ id).
      + rewrite map_id. apply eq_sym, conn_ipse.
      + intros X' HX'. apply IHX. assumption.
  Qed.

  Lemma I_afs_id_seq : forall U : sequent, seqSubst I_afs U = U.
  Proof.
    intro U. destruct U. simpl. repeat rewrite I_afs_id_str. reflexivity.
  Qed.

  Lemma I_afs_id_listseq : forall l : list sequent, map (seqSubst I_afs) l = l.
  Proof.
    induction l; try reflexivity.
    simpl. rewrite I_afs_id_seq, IHl. reflexivity.
  Qed.

  Lemma I_afs_id_rule : forall r : rule, ruleSubst I_afs r = r.
  Proof.
    intro r. destruct r. simpl. rewrite I_afs_id_listseq, I_afs_id_seq. reflexivity.
  Qed.

  Definition s_comp (afs1 afs2 : afsSubst) : sSubst :=
    fun x => strSubst afs1 (snd afs2 x).
  Definition afs_comp (afs1 afs2 : afsSubst) : afsSubst :=
    (af_comp (fst afs1) (fst afs2), s_comp afs1 afs2).

  Lemma strSubst_afs_comp {afs1 afs2 X} :
    strSubst (afs_comp afs1 afs2) X = strSubst afs1 (strSubst afs2 X).
  Proof.
    revert X. apply ipse_rect.
    intros X IHX. rewrite ! (strSubst_eq _ X).
    destruct (Var_dec SV X) as [[V HV]|HnSV];
      [|destruct (Var_dec FS X) as [[A HA]|HnFS]].
    - simpl. reflexivity.
    - simpl. rewrite fmlSubst_af_comp.
      rewrite strSubst_FS. reflexivity.
    - pose proof (map_length (strSubst afs2) (ipse X)) as Hlen.
      pose proof (not_Var_conn SV _ _ Hlen HnSV) as HnSV'.
      pose proof (not_Var_conn FS _ _ Hlen HnFS) as HnFS'.
      rewrite strSubst_eq.
      rewrite (Var_dec_not_Var SV _ _ _ _ HnSV').
      rewrite (Var_dec_not_Var FS _ _ _ _ HnFS').
      rewrite conn_conn. rewrite ipse_conn.
      all: try apply map_length.
      rewrite (map_ext_in _ _ _ IHX).
      rewrite map_map. reflexivity.
  Qed.

  Lemma seqSubst_afs_comp {afs1 afs2 U} :
    seqSubst (afs_comp afs1 afs2) U = seqSubst afs1 (seqSubst afs2 U).
  Proof.
    destruct U. simpl. repeat rewrite strSubst_afs_comp. reflexivity.
  Qed.

  Lemma listseqSubt_afs_comp {afs1 afs2 l} :
    map (seqSubst (afs_comp afs1 afs2)) l = map (seqSubst afs1) (map (seqSubst afs2) l).
  Proof.
    induction l; try (simpl; reflexivity).
    simpl. rewrite seqSubst_afs_comp. rewrite IHl. reflexivity.
  Qed.

  Lemma ruleSubst_afs_comp {afs1 afs2 r} :
    ruleSubst (afs_comp afs1 afs2) r = ruleSubst afs1 (ruleSubst afs2 r).
  Proof.
    destruct r. simpl. rewrite listseqSubt_afs_comp. rewrite seqSubst_afs_comp. reflexivity.
  Qed.

  (* Rule instance *)
  Definition ruleInst (r r' : rule) : Prop := exists afs, r' = ruleSubst afs r.

  Lemma ruleInst_tran {r1 r2 r3} :
    ruleInst r2 r1 -> ruleInst r3 r2 -> ruleInst r3 r1.
  Proof.
    intros H1 H2. destruct H1 as [afs1 Hafs1]. destruct H2 as [afs2 Hafs2].
    exists (afs_comp afs1 afs2). rewrite ruleSubst_afs_comp, <- Hafs2. assumption.
  Qed.

  Lemma ruleInst_length (r r' : rule) :
    ruleInst r r' -> length (premsRule r) = length (premsRule r').
  Proof.
    intro H. destruct r as [prr cor]. destruct r' as [prr' cor'].
    destruct H as [afs Hafs]. injection Hafs.
    intros Heqcor Heqprr. simpl. rewrite Heqprr.
    apply eq_sym, map_length.
  Qed.

  Definition str_matchsub_Atm : structr -> structr -> aSubst :=
    ipse_rect _ (fun X IH => fun Y =>
      match Var_dec FS X, Var_dec FS Y with
      | inleft (exist _ A _), inleft (exist _ B _) => fml_matchsub_Atm A B
      | _, _ => fun p =>
        match in_some_dec p (zip pair (ipse X) (ipse Y)) (comp strAtms fst) with
        | inleft (exist2 _ _ X'Y' Hin _) =>
            IH (fst X'Y') (in_zip_pair_fst Hin) (snd X'Y') p
        | inright _ => p
        end
      end).

  Lemma str_matchsub_Atm_eq (X Y : structr) :
    str_matchsub_Atm X Y =
      match Var_dec FS X, Var_dec FS Y with
      | inleft (exist _ A _), inleft (exist _ B _) => fml_matchsub_Atm A B
      | _, _ => fun p =>
        match in_some_dec p (zip pair (ipse X) (ipse Y)) (comp strAtms fst) with
        | inleft (exist2 _ _ X'Y' Hin _) => str_matchsub_Atm (fst X'Y') (snd X'Y') p
        | inright _ => p
        end
      end.
  Proof. unfold str_matchsub_Atm at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Definition str_matchsub_FV : structr -> structr -> fSubst :=
    ipse_rect _ (fun X IH => fun Y =>
      match Var_dec FS X, Var_dec FS Y with
      | inleft (exist _ A _), inleft (exist _ B _) => fml_matchsub_FV A B
      | _, _ => fun v =>
        match in_some_dec v (zip pair (ipse X) (ipse Y)) (comp strFVs fst) with
        | inleft (exist2 _ _ X'Y' Hin _) =>
            IH (fst X'Y') (in_zip_pair_fst Hin) (snd X'Y') v
        | inright _ => FV v
        end
      end).

  Lemma str_matchsub_FV_eq (X Y : structr) :
    str_matchsub_FV X Y =
      match Var_dec FS X, Var_dec FS Y with
      | inleft (exist _ A _), inleft (exist _ B _) => fml_matchsub_FV A B
      | _, _ => fun v =>
        match in_some_dec v (zip pair (ipse X) (ipse Y)) (comp strFVs fst) with
        | inleft (exist2 _ _ X'Y' Hin _) => str_matchsub_FV (fst X'Y') (snd X'Y') v
        | inright _ => FV v
        end
      end.
  Proof. unfold str_matchsub_FV at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Definition str_matchsub_SV : structr -> structr -> sSubst :=
    ipse_rect _ (fun X IH => fun Y =>
      match Var_dec SV X with
      | inleft (exist _ v _) => fun _ => Y
      | _ => fun v =>
        match in_some_dec v (zip pair (ipse X) (ipse Y)) (comp strSVs fst) with
        | inleft (exist2 _ _ X'Y' Hin _) =>
            IH (fst X'Y') (in_zip_pair_fst Hin) (snd X'Y') v
        | inright _ => SV v
        end
      end).

  Lemma str_matchsub_SV_eq (X Y : structr) :
    str_matchsub_SV X Y =
      match Var_dec SV X with
      | inleft (exist _ v _) => fun _ => Y
      | _ => fun v =>
        match in_some_dec v (zip pair (ipse X) (ipse Y)) (comp strSVs fst) with
        | inleft (exist2 _ _ X'Y' Hin _) => str_matchsub_SV (fst X'Y') (snd X'Y') v
        | inright _ => SV v
        end
      end.
  Proof. unfold str_matchsub_SV at 1. rewrite ipse_rect_cmp. reflexivity. Qed.

  Definition str_matchsub (X Y : structr) : afsSubst :=
    (str_matchsub_Atm X Y, str_matchsub_FV X Y, str_matchsub_SV X Y).

  Definition seq_matchsub_Atm (s t : sequent) : aSubst :=
    match s, t with X1 ⊢ Y1, X2 ⊢ Y2 =>
      fun p => if in_dec eqdec p (strAtms X1) then str_matchsub_Atm X1 X2 p
            else if in_dec eqdec p (strAtms Y1) then str_matchsub_Atm Y1 Y2 p
            else p end.

  Definition seq_matchsub_FV (s t : sequent) : fSubst :=
    match s, t with X1 ⊢ Y1, X2 ⊢ Y2 =>
      fun V => if in_dec eqdec V (strFVs X1) then str_matchsub_FV X1 X2 V
            else if in_dec eqdec V (strFVs Y1) then str_matchsub_FV Y1 Y2 V
            else FV V end.

  Definition seq_matchsub_SV (s t : sequent) : sSubst :=
    match s, t with X1 ⊢ Y1, X2 ⊢ Y2 =>
      fun V => if in_dec eqdec V (strSVs X1) then str_matchsub_SV X1 X2 V
            else if in_dec eqdec V (strSVs Y1) then str_matchsub_SV Y1 Y2 V
            else SV V end.

  Definition seq_matchsub (s t : sequent) : afsSubst :=
    (seq_matchsub_Atm s t, seq_matchsub_FV s t, seq_matchsub_SV s t).

  Definition listseq_matchsub_Atm (ls lt : list (sequent)) : aSubst :=
    fun p =>
      match in_some_dec p (zip pair ls lt) (comp seqAtms fst) with
      | inleft (exist2 _ _ (s, t) _ _) => seq_matchsub_Atm s t p
      | inright _ => p
      end.

  Definition listseq_matchsub_FV (ls lt : list (sequent)) : fSubst :=
    fun V =>
      match in_some_dec V (zip pair ls lt) (comp seqFVs fst) with
      | inleft (exist2 _ _ (s, t) _ _) => seq_matchsub_FV s t V
      | inright _ => FV V
      end.

  Definition listseq_matchsub_SV (ls lt : list (sequent)) : sSubst :=
    fun V =>
      match in_some_dec V (zip pair ls lt) (comp seqSVs fst) with
      | inleft (exist2 _ _ (s, t) _ _) => seq_matchsub_SV s t V
      | inright _ => SV V
      end.

  Definition listseq_matchsub (ls lt : list (sequent)) : afsSubst :=
    (listseq_matchsub_Atm ls lt, listseq_matchsub_FV ls lt, listseq_matchsub_SV ls lt).

  Definition rule_matchsub (r r' : rule) : afsSubst :=
    listseq_matchsub (conclRule r :: premsRule r) (conclRule r' :: premsRule r').

  Lemma strSubst_fun_agree_iff (a1 : aSubst) (f1 : fSubst) (s1 : sSubst) (a2 : aSubst) (f2 : fSubst) (s2 : sSubst) (X : structr) :
    strSubst (a1, f1, s1) X = strSubst (a2, f2, s2) X <->
      fun_agree a1 a2 (strAtms X) /\
      fun_agree f1 f2 (strFVs X) /\
      fun_agree s1 s2 (strSVs X).
  Proof.
    revert X. apply ipse_rect. intros X IH.
    rewrite ! strSubst_eq. rewrite strAtms_eq, strFVs_eq, strSVs_eq.
    destruct (Var_dec SV X) as [[v Hv]|HnSV];
      destruct (Var_dec FS X) as [[A HA]|HnFS].
    - rewrite Hv in HA. contradict HA. apply SV_FS_disc.
    - rewrite Hv, (Var_ipse SV). simpl.
      rewrite fun_agree_Singleton, ! fun_agree_Empty_iff. tauto.
    - rewrite HA. rewrite (Var_ipse FS).
      rewrite (Var_inj_iff FS), fun_agree_Empty_iff. simpl.
      pose proof (@fmlSubst_fun_agree_iff _ _ _ _ a1 f1 a2 f2 A). tauto.
    - rewrite (union_map _ strAtms).
      rewrite (union_map _ strFVs).
      rewrite (union_map _ strSVs).
      rewrite <- ! fun_agree_multi_Union_iff.
      rewrite conn_inj_iff; try apply map_length.
      split.
      + intros [_ H]. split; [|split];
          intros l Hl; apply in_map_iff in Hl;
          destruct Hl as [B [HeqB HinB]];
          rewrite <- HeqB; apply IH; try assumption;
          apply (ext_in_map H); assumption.
      + intro H. split; try reflexivity. apply map_ext_in.
        intros X' HX'. apply IH; try assumption.
        split; [|split]; apply H; apply in_map_iff; exists X'; tauto.
  Qed.

  Lemma strInst_matchsub (afs : afsSubst) : forall X Y,
    strSubst afs X = Y -> strSubst (str_matchsub X Y) X = Y.
  Proof.
    intro X. pattern X. revert X. apply ipse_rect.
    intros X IH Y Hafs. unfold str_matchsub.
    rewrite str_matchsub_Atm_eq, str_matchsub_FV_eq, str_matchsub_SV_eq.
    rewrite strSubst_eq in Hafs |- *.
    destruct (Var_dec SV X) as [[v Hv]|HXnSV];
      [destruct (Var_dec FS Y) as [[A' HA']|HYnFS] |
(*        destruct (Var_dec FS Y) as [[A' HA']|HYnFS];*)
        destruct (Var_dec FS X) as [[A HA]|HXnFS]];
      simpl; try reflexivity; [destruct (Var_dec FS Y) as [[A' HA']|HYnFS]|].
    - rewrite HA' in Hafs |- *. apply f_equal.
      apply (fmlInst_matchsub (fst afs)).
      apply (Var_inj FS). assumption.
    - apply eq_sym in Hafs. apply HYnFS in Hafs. contradiction.
    - rewrite <- Hafs at 1. apply (f_equal (conn X)).
      assert (map (strSubst afs) (ipse X) = ipse Y) as Heqips.
      { rewrite (conn_ipse Y) in Hafs.
        apply conn_inj in Hafs; [|apply map_length|reflexivity]. tauto. }
      assert (length (ipse X) = length (ipse Y)) as Hlen.
      { rewrite <- Heqips. apply eq_sym, map_length. }
      assert (forall X'Y', X'Y' ∈ zip pair (ipse X) (ipse Y) ->
      strSubst afs (fst X'Y') = strSubst (str_matchsub (fst X'Y') (snd X'Y')) (fst X'Y'))
        as Hallafs.
      { intros (X', Y') Hin. pose proof (map_eq_zip_pair Heqips (X', Y') Hin) as Heq.
        apply in_zip_pair_fst in Hin. simpl in Hin, Heq |- *.
        rewrite (IH X' Hin Y' Heq). assumption. }
      apply map_ext_in. intros X' HX'.
      destruct (zip_pair_bij_fst _ _ Hlen X' HX') as [X'Y' [HX'Y' Hfst]].
      destruct afs as [[a f] s]. apply strSubst_fun_agree_iff. split; [|split].
      + intros p Hp.
        destruct (in_some_dec p (zip pair (ipse X) (ipse Y)) (comp strAtms fst))
          as [[[X0 Y0] Hin HpX0]|Hcont].
        * specialize (Hallafs (X0, Y0) Hin).
          apply strSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HAtm HFV].
          simpl in HAtm, HFV |- *. unfold comp in HpX0. simpl in HpX0.
          specialize (HAtm p HpX0). apply eq_sym. assumption.
        * specialize (Hcont X'Y' HX'Y'). contradict Hcont.
          unfold comp. rewrite Hfst. assumption.
      + intros V HV.
        destruct (in_some_dec V (zip pair (ipse X) (ipse Y)) (comp strFVs fst))
          as [[[X0 Y0] Hin HVX0]|Hcont].
        * specialize (Hallafs (X0, Y0) Hin).
          apply strSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HAtm [HFV HSV]].
          simpl in HAtm, HFV, HSV |- *. unfold comp in HVX0. simpl in HVX0.
          specialize (HFV V HVX0). apply eq_sym. assumption.
        * specialize (Hcont X'Y' HX'Y'). contradict Hcont.
          unfold comp. rewrite Hfst. assumption.
      + intros V HV.
        destruct (in_some_dec V (zip pair (ipse X) (ipse Y)) (comp strSVs fst))
          as [[[X0 Y0] Hin HVX0]|Hcont].
        * specialize (Hallafs (X0, Y0) Hin).
          apply strSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HAtm [HFV HSV]].
          simpl in HAtm, HFV, HSV |- *. unfold comp in HVX0. simpl in HVX0.
          specialize (HSV V HVX0). apply eq_sym. assumption.
        * specialize (Hcont X'Y' HX'Y'). contradict Hcont.
          unfold comp. rewrite Hfst. assumption.
  Qed.

  Lemma strInst_matchsub' (afs : afsSubst) : forall X Y,
    strSubst afs X = Y -> strSubst (str_matchsub X Y) X = strSubst afs X.
  Proof.
    intros X Y H. rewrite H. apply (strInst_matchsub afs _ _ H).
  Qed.

  Lemma strSubst_dec : forall X Y, {afs | strSubst afs X = Y} + {forall afs, strSubst afs X <> Y}.
  Proof.
    intros X Y. destruct (eqdec (strSubst (str_matchsub X Y) X) Y) as [Heq|Hneq].
    - left. exists (str_matchsub X Y). assumption.
    - right. intro afs. contradict Hneq. apply (strInst_matchsub afs). assumption.
  Defined.

  Lemma seqSubst_fun_agree_iff {fp1 ff1 fs1 fp2 ff2 fs2 u} :
    seqSubst (fp1, ff1, fs1) u = seqSubst (fp2, ff2, fs2) u <->
      fun_agree fp1 fp2 (seqAtms u) /\
      fun_agree ff1 ff2 (seqFVs u) /\
      fun_agree fs1 fs2 (seqSVs u).
  Proof.
    destruct u. setoid_rewrite seqSubst_strSubst.
    setoid_rewrite strSubst_fun_agree_iff.
    unfold seqAtms, seqFVs, seqSVs. repeat rewrite app_is_Union.
    repeat rewrite <- fun_agree_Union_iff. simpl. tauto.
  Qed.

  Lemma seqInst_matchsub (afs : afsSubst) : forall s t,
    seqSubst afs s = t -> seqSubst (seq_matchsub s t) s = t.
  Proof.
    intros [X1 Y1] [X2 Y2] H. injection H. intros HY HX.
    rewrite <- HX, <- HY at 2. simpl. unfold seq_matchsub.
    destruct afs as [[a f] s]. 
    apply strInst_matchsub', strSubst_fun_agree_iff in HX, HY.
    destruct HX as [HAX [HFX HSX]]. destruct HY as [HAY [HFY HSY]].
    apply f_equal2; apply strSubst_fun_agree_iff; repeat split;
    intros V HV; simpl; rewrite (in_if_in_dec_eq V _ HV);
      try now (apply HAX || apply HFX || apply HSX).
    destruct (in_dec string_dec V (strAtms X1)); now (apply HAX || apply HAY).
    destruct (in_dec string_dec V (strFVs X1)); now (apply HFX || apply HFY).
    destruct (in_dec string_dec V (strSVs X1)); now (apply HSX || apply HSY).
  Qed.

  Lemma seqSubst_dec : forall s t, {afs | seqSubst afs s = t} + {forall afs, seqSubst afs s <> t}.
  Proof.
    intros s t. destruct (eqdec (seqSubst (seq_matchsub s t) s) t) as [Heq|Hneq].
    - left. exists (seq_matchsub s t). assumption.
    - right. intro afs. contradict Hneq. apply (seqInst_matchsub afs). assumption.
  Qed.

  Lemma listseqInst_matchsub (afs : afsSubst) : forall ls lt,
    map (seqSubst afs) ls = lt -> map (seqSubst (listseq_matchsub ls lt)) ls = lt.
  Proof.
    intros ls lt H.
    assert (length ls = length lt) as Hlen.
    { rewrite <- H. apply eq_sym. apply map_length. }
    assert (forall st, st ∈ zip pair ls lt ->
      seqSubst (seq_matchsub (fst st) (snd st)) (fst st) = seqSubst afs (fst st)) as Hallafs.
    { intros st Hst. pose proof (map_eq_zip_pair H st Hst) as Hsteq.
      rewrite Hsteq. rewrite (seqInst_matchsub _ _ _ Hsteq). reflexivity. }      
    rewrite <- H at 2. apply map_ext_in.
    intros s Hs. unfold listseq_matchsub.
    destruct (zip_pair_bij_fst _ _ Hlen s Hs) as [st [Hstin Hsteq]].
    destruct afs as [[fa ff] fs].
    apply seqSubst_fun_agree_iff.
    unfold listseq_matchsub_Atm, listseq_matchsub_FV, listseq_matchsub_SV.
    repeat split.
    - intros V HV.
      destruct (in_some_dec V (zip pair ls lt) (comp seqAtms fst)) as [[[s' t'] Hs't' HVin]|Hn].
      + specialize (Hallafs (s', t') Hs't'). simpl in Hallafs.
        apply seqSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HA [HF HS]].
        unfold comp in HVin. simpl in HVin.
        specialize (HA _ HVin). assumption.
      + specialize (Hn st Hstin). contradict Hn. unfold comp. rewrite Hsteq. assumption.
    - intros V HV.
      destruct (in_some_dec V (zip pair ls lt) (comp seqFVs fst)) as [[[s' t'] Hs't' HVin]|Hn].
      + specialize (Hallafs (s', t') Hs't'). simpl in Hallafs.
        apply seqSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HA [HF HS]].
        unfold comp in HVin. simpl in HVin.
        specialize (HF _ HVin). assumption.
      + specialize (Hn st Hstin). contradict Hn. unfold comp. rewrite Hsteq. assumption.
    - intros V HV.
      destruct (in_some_dec V (zip pair ls lt) (comp seqSVs fst)) as [[[s' t'] Hs't' HVin]|Hn].
      + specialize (Hallafs (s', t') Hs't'). simpl in Hallafs.
        apply seqSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HA [HF HS]].
        unfold comp in HVin. simpl in HVin.
        specialize (HS _ HVin). assumption.
      + specialize (Hn st Hstin). contradict Hn. unfold comp. rewrite Hsteq. assumption.
  Qed.

  Lemma listseqSubst_dec :
    forall ls lt, {afs | map (seqSubst afs) ls = lt} + {forall afs, map (seqSubst afs) ls <> lt}.
  Proof.
    intros ls lt. destruct (eqdec (map (seqSubst (listseq_matchsub ls lt)) ls) lt) as [Heq|Hneq].
    - left. exists (listseq_matchsub ls lt). assumption.
    - right. intro afs. contradict Hneq. apply (listseqInst_matchsub afs). assumption.
  Defined.

  Lemma ruleSubst_dec :
    forall r r', {afs | ruleSubst afs r = r'} + {forall afs, ruleSubst afs r <> r'}.
  Proof.
    intros [p c] [p' c']. destruct (listseqSubst_dec (c :: p) (c' :: p')) as [[afs Hafs]|Hn].
    - left. exists afs. simpl. injection Hafs. intros Heqp Heqc.
      rewrite Heqc, Heqp. reflexivity.
    - right. intro afs. specialize (Hn afs). contradict Hn.
      simpl in Hn. injection Hn. intros Heqc Heqp. simpl.
      rewrite Heqc, Heqp. reflexivity.
  Defined.

  Theorem ruleInst_ruleSubst {r r'} : ruleInst r r' -> {afs | r' = ruleSubst afs r}.
  Proof.
    intro H. destruct (ruleSubst_dec r r') as [s|no].
    - destruct s as [afs Hafs]. exists afs. apply eq_sym. assumption.
    - exfalso. destruct H as [afs Heq]. apply eq_sym in Heq. revert Heq. apply no.
  Defined.

  Theorem ruleInst_ruleSubst_iff {r r'} : (ruleInst r r') <+> {afs | r' = ruleSubst afs r}.
  Proof. split; try apply ruleInst_ruleSubst. intros [afs Hafs]. exists afs. assumption. Defined.

  Lemma ruleInst_dec : forall r r', {ruleInst r r'} + {~ ruleInst r r'}.
  Proof.
    intros r r'. destruct (ruleSubst_dec r r') as [yes|no].
    - left. destruct yes as [afs Hafs]. apply eq_sym in Hafs. exists afs. assumption.
    - right. intros [afs Hafs]. apply (no afs). apply eq_sym. assumption.
  Defined.


  (* An easy way of specifying a substitution *)

  Fixpoint a_spec (l : list (string * string)) : aSubst :=
    match l with
      | []           => I_a
      | (s, t) :: l' => fun x => if string_dec x s then t else a_spec l' x
    end.

  Fixpoint f_spec (l : list (string * formula)) : fSubst :=
    match l with
      | []           => I_f
      | (s, A) :: l' => fun x => if string_dec x s then A else f_spec l' x
    end.  

  Fixpoint s_spec (l : list (string * structr)) : sSubst :=
    match l with
      | []           => I_s
      | (s, X) :: l' => fun x => if string_dec x s then X else s_spec l' x
    end.

  Definition af_spec
    (lp : list (string * string)) (lf : list (string * formula))
    : afSubst := (a_spec lp, f_spec lf).

  Definition afs_spec
    (lp : list (string * string)) (lf : list (string * formula)) (ls : list (string * structr))
    : afsSubst := (af_spec lp lf, s_spec ls).


End Substitutions.
