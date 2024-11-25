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
Require Import Llang.
Require Import Sequents.


Open Scope nat_scope.

Section Substitutions.
  
  Context `{SL : SUBSTLLANG}.

  Definition sSubst : Type := string -> (@structr formula).
  Definition afsSubst : Type := (@afSubst formula) * sSubst.

  Fixpoint strSubst (afs : afsSubst) (Z : structr) : structr :=
    match Z with
    | $X   => (snd afs) X
    | I    => I
    | £A   => £(fmlSubst (fst afs) A)
    | ∗X   => ∗(strSubst afs X)
    | X,,Y => (strSubst afs X),,(strSubst afs Y)
    end.
  Definition seqSubst (afs : afsSubst) (s : sequent) : sequent :=
    match s with X ⊢ Y => strSubst afs X ⊢ strSubst afs Y end.
  Definition ruleSubst (afs : afsSubst) (r : rule) : rule :=
    match r with (ps, c) => (map (seqSubst afs) ps, seqSubst afs c) end.

  Lemma subst_strIsFml {pfs} {X Y : structr} : strSubst pfs X = Y -> strIsFml X -> strIsFml Y.
  Proof.
    intros Hsub HfmlX. destruct X; try contradiction. simpl in Hsub.
    destruct Y; try discriminate. tauto.
  Qed.

  Lemma seqSubst_strSubst {pfs X1 Y1 X2 Y2} :
    seqSubst pfs (X1 ⊢ Y1) = X2 ⊢ Y2 <-> strSubst pfs X1 = X2 /\ strSubst pfs Y1 = Y2.
  Proof.
    split.
    - intro H. simpl in H. injection H. tauto.
    - intro H. simpl. rewrite (proj1 H), (proj2 H). reflexivity.
  Qed.

  Lemma NoDup_seqSVs_strSVs {X Y : @structr formula} :
    NoDup (seqSVs (X ⊢ Y)) -> NoDup (strSVs X) /\ NoDup (strSVs Y).
  Proof.
    intro H. split; [apply (NoDup_app_remove_r _ _ H) | apply (NoDup_app_remove_l _ _ H)].
  Qed.

  Lemma strSubst_fml {X pf} : forall (sub1 sub2 : sSubst), strIsFml X ->
    strSubst (pf, sub1) X = strSubst (pf, sub2) X.
  Proof.
    intros sub1 sub2 H. destruct X; try contradiction. simpl. reflexivity.
  Qed.

  Lemma premsRule_ruleSubst {r : rule} {pfs : afsSubst} :
    premsRule (ruleSubst pfs r) = map (seqSubst pfs) (premsRule r).
  Proof. destruct r. simpl. reflexivity. Qed.

  Lemma conclRule_ruleSubst {r : rule} {pfs : afsSubst} :
    conclRule (ruleSubst pfs r) = seqSubst pfs (conclRule r).
  Proof. destruct r. simpl. reflexivity. Qed.

  Definition I_s : sSubst := fun x => $x.
  Definition I_afs : afsSubst := (I_af, I_s).

  Lemma I_afs_id_str : forall X : structr, strSubst I_afs X = X.
  Proof.
    induction X.
    - reflexivity.
    - reflexivity.
    - simpl. now rewrite I_af_id.
    - now rewrite <- IHX at 2.
    - now rewrite <- IHX1, <- IHX2 at 2.
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
    induction X.
    - simpl. unfold s_comp. reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite fmlSubst_af_comp. reflexivity.
    - simpl. rewrite IHX. reflexivity.
    - simpl. rewrite IHX1, IHX2. reflexivity.
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

  Fixpoint str_matchsub_Atm (X Y : @structr formula) : aSubst :=
    match X, Y with
    | £A, £B => fml_matchsub_Atm A B
    | ∗X0, ∗Y0 => fun p => if in_dec eqdec p (strAtms X0) then str_matchsub_Atm X0 Y0 p else p
    | X1,,X2, Y1,,Y2 => fun p => if in_dec eqdec p (strAtms X1) then str_matchsub_Atm X1 Y1 p
                             else if in_dec eqdec p (strAtms X2) then str_matchsub_Atm X2 Y2 p
                             else p
    | _, _ => fun p => p
    end.

  Fixpoint str_matchsub_FV (X Y : @structr formula) : fSubst :=
    match X, Y with
    | £A, £B => fml_matchsub_FV A B
    | ∗X0, ∗Y0 => fun V => if in_dec eqdec V (strFVs X0) then str_matchsub_FV X0 Y0 V else FV V
    | X1,,X2, Y1,,Y2 => fun V => if in_dec eqdec V (strFVs X1) then str_matchsub_FV X1 Y1 V
                             else if in_dec eqdec V (strFVs X2) then str_matchsub_FV X2 Y2 V
                             else FV V
    | _, _ => fun V => FV V
    end.

  Fixpoint str_matchsub_SV (X Y : @structr formula) : sSubst :=
    match X, Y with
    | $V, _ => fun _ => Y
    | ∗X0, ∗Y0 => fun V => if in_dec eqdec V (strSVs X0) then str_matchsub_SV X0 Y0 V else $V
    | X1,,X2, Y1,,Y2 => fun V => if in_dec eqdec V (strSVs X1) then str_matchsub_SV X1 Y1 V
                             else if in_dec eqdec V (strSVs X2) then str_matchsub_SV X2 Y2 V
                             else $V
    | _, _ => fun V => $V
    end.

  Lemma str_matchsub_Atm_eq (X Y : @structr formula) :
    str_matchsub_Atm X Y =
    match X, Y with
    | £A, £B => fml_matchsub_Atm A B
    | ∗X0, ∗Y0 => fun p => if in_dec eqdec p (strAtms X0) then str_matchsub_Atm X0 Y0 p else p
    | X1,,X2, Y1,,Y2 => fun p => if in_dec eqdec p (strAtms X1) then str_matchsub_Atm X1 Y1 p
                             else if in_dec eqdec p (strAtms X2) then str_matchsub_Atm X2 Y2 p
                             else p
    | _, _ => fun p => p
    end.
  Proof. destruct X, Y; reflexivity. Qed.

  Lemma str_matchsub_FV_eq (X Y : @structr formula) :
    str_matchsub_FV X Y =
    match X, Y with
    | £A, £B => fml_matchsub_FV A B
    | ∗X0, ∗Y0 => fun V => if in_dec eqdec V (strFVs X0) then str_matchsub_FV X0 Y0 V else FV V
    | X1,,X2, Y1,,Y2 => fun V => if in_dec eqdec V (strFVs X1) then str_matchsub_FV X1 Y1 V
                             else if in_dec eqdec V (strFVs X2) then str_matchsub_FV X2 Y2 V
                             else FV V
    | _, _ => fun V => FV V
    end.
  Proof. destruct X, Y; reflexivity. Qed.

  Fixpoint str_matchsub_SV_eq (X Y : @structr formula) :
    str_matchsub_SV X Y =
    match X, Y with
    | $V, _ => fun _ => Y
    | ∗X0, ∗Y0 => fun V => if in_dec eqdec V (strSVs X0) then str_matchsub_SV X0 Y0 V else $V
    | X1,,X2, Y1,,Y2 => fun V => if in_dec eqdec V (strSVs X1) then str_matchsub_SV X1 Y1 V
                             else if in_dec eqdec V (strSVs X2) then str_matchsub_SV X2 Y2 V
                             else $V
    | _, _ => fun V => $V
    end.
  Proof. destruct X, Y; reflexivity. Qed.

  Definition str_matchsub (X Y : @structr formula) : afsSubst :=
    (str_matchsub_Atm X Y, str_matchsub_FV X Y, str_matchsub_SV X Y).

  Definition seq_matchsub_Atm (s t : @sequent formula) : aSubst :=
    match s, t with X1 ⊢ Y1, X2 ⊢ Y2 =>
      fun p => if in_dec eqdec p (strAtms X1) then str_matchsub_Atm X1 X2 p
            else if in_dec eqdec p (strAtms Y1) then str_matchsub_Atm Y1 Y2 p
            else p end.

  Definition seq_matchsub_FV (s t : @sequent formula) : fSubst :=
    match s, t with X1 ⊢ Y1, X2 ⊢ Y2 =>
      fun V => if in_dec eqdec V (strFVs X1) then str_matchsub_FV X1 X2 V
            else if in_dec eqdec V (strFVs Y1) then str_matchsub_FV Y1 Y2 V
            else FV V end.

  Definition seq_matchsub_SV (s t : @sequent formula) : sSubst :=
    match s, t with X1 ⊢ Y1, X2 ⊢ Y2 =>
      fun V => if in_dec eqdec V (strSVs X1) then str_matchsub_SV X1 X2 V
            else if in_dec eqdec V (strSVs Y1) then str_matchsub_SV Y1 Y2 V
            else SV V end.

  Definition seq_matchsub (s t : @sequent formula) : afsSubst :=
    (seq_matchsub_Atm s t, seq_matchsub_FV s t, seq_matchsub_SV s t).

  Definition listseq_matchsub_Atm (ls lt : list (@sequent formula)) : aSubst :=
    fun p =>
      match in_some_dec p (zip pair ls lt) (seqAtms ∘ fst) with
      | inleft (exist2 _ _ (s, t) _ _) => seq_matchsub_Atm s t p
      | inright _ => p
      end.

  Definition listseq_matchsub_FV (ls lt : list (@sequent formula)) : fSubst :=
    fun V =>
      match in_some_dec V (zip pair ls lt) (seqFVs ∘ fst) with
      | inleft (exist2 _ _ (s, t) _ _) => seq_matchsub_FV s t V
      | inright _ => FV V
      end.

  Definition listseq_matchsub_SV (ls lt : list (@sequent formula)) : sSubst :=
    fun V =>
      match in_some_dec V (zip pair ls lt) (seqSVs ∘ fst) with
      | inleft (exist2 _ _ (s, t) _ _) => seq_matchsub_SV s t V
      | inright _ => SV V
      end.

  Definition listseq_matchsub (ls lt : list (@sequent formula)) : afsSubst :=
    (listseq_matchsub_Atm ls lt, listseq_matchsub_FV ls lt, listseq_matchsub_SV ls lt).

  Definition rule_matchsub (r r' : rule) : afsSubst :=
    listseq_matchsub (conclRule r :: premsRule r) (conclRule r' :: premsRule r').

  Lemma strSubst_fun_agree_iff {fp1 ff1 fs1 fp2 ff2 fs2 X} :
    strSubst (fp1, ff1, fs1) X = strSubst (fp2, ff2, fs2) X <->
      fun_agree fp1 fp2 (strAtms X) /\
      fun_agree ff1 ff2 (strFVs X) /\
      fun_agree fs1 fs2 (strSVs X).
  Proof.
    induction X; simpl; try rewrite set_of_empty; try setoid_rewrite fun_agree_Empty_iff.
    - setoid_rewrite fun_agree_Singleton. tauto.
    - tauto.
    - setoid_rewrite FS_eq_iff.
      setoid_rewrite fmlSubst_fun_agree_iff. tauto.
    - setoid_rewrite Star_eq_iff. setoid_rewrite IHX. tauto.
    - setoid_rewrite Comma_eq_iff. setoid_rewrite IHX1.
      setoid_rewrite IHX2. repeat rewrite app_is_Union.
      setoid_rewrite <- fun_agree_Union_iff. tauto.
  Qed.

  Lemma strInst_matchsub (afs : afsSubst) : forall X Y,
    strSubst afs X = Y -> strSubst (str_matchsub X Y) X = Y.
  Proof.
    induction X; simpl; try tauto;
    intros Y H; destruct Y as [| |B| |]; try discriminate.
    - apply (f_equal FS). injection H. apply fmlInst_matchsub.
    - injection H. intro H0. specialize (IHX Y H0). clear H H0.
      rewrite <- IHX at 2. apply f_equal. unfold str_matchsub.
      apply strSubst_fun_agree_iff. split; [|split];
        (simpl; intros V HV; rewrite (in_if_in_dec_eq V _ HV); reflexivity).
    - injection H. intros H2 H1. specialize (IHX1 Y1 H1). specialize (IHX2 Y2 H2).
      rewrite <- H1, <- H2 at 3. rewrite <- H1 in IHX1 at 2. rewrite <- H2 in IHX2 at 2.
      destruct afs as [[a f] s]. unfold str_matchsub in IHX1, IHX2 |- *.
      apply strSubst_fun_agree_iff in IHX1, IHX2.
      destruct IHX1 as [HA1 [HF1 HS1]]. destruct IHX2 as [HA2 [HF2 HS2]].
      apply f_equal2; apply strSubst_fun_agree_iff; repeat split;
      simpl; intros V HV; rewrite (in_if_in_dec_eq V _ HV);
        try now (apply HA1 || apply HF1 || apply HS1).
      destruct (in_dec string_dec V (strAtms X1)); now (apply HA1 || apply HA2).
      destruct (in_dec string_dec V (strFVs X1)); now (apply HF1 || apply HF2).
      destruct (in_dec string_dec V (strSVs X1)); now (apply HS1 || apply HS2).
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
    destruct (zip_pair_eq_length Hlen s Hs) as [st [Hstin Hsteq]].
    destruct afs as [[fa ff] fs].
    apply seqSubst_fun_agree_iff.
    unfold listseq_matchsub_Atm, listseq_matchsub_FV, listseq_matchsub_SV.
    repeat split.
    - intros V HV.
      destruct (in_some_dec V (zip pair ls lt) (seqAtms ∘ fst)) as [[[s' t'] Hs't' HVin]|Hn].
      + specialize (Hallafs (s', t') Hs't'). simpl in Hallafs.
        apply seqSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HA [HF HS]].
        unfold compose in HVin. simpl in HVin.
        specialize (HA _ HVin). assumption.
      + specialize (Hn st Hstin). contradict Hn. unfold compose. rewrite Hsteq. assumption.
    - intros V HV.
      destruct (in_some_dec V (zip pair ls lt) (seqFVs ∘ fst)) as [[[s' t'] Hs't' HVin]|Hn].
      + specialize (Hallafs (s', t') Hs't'). simpl in Hallafs.
        apply seqSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HA [HF HS]].
        unfold compose in HVin. simpl in HVin.
        specialize (HF _ HVin). assumption.
      + specialize (Hn st Hstin). contradict Hn. unfold compose. rewrite Hsteq. assumption.
    - intros V HV.
      destruct (in_some_dec V (zip pair ls lt) (seqSVs ∘ fst)) as [[[s' t'] Hs't' HVin]|Hn].
      + specialize (Hallafs (s', t') Hs't'). simpl in Hallafs.
        apply seqSubst_fun_agree_iff in Hallafs. destruct Hallafs as [HA [HF HS]].
        unfold compose in HVin. simpl in HVin.
        specialize (HS _ HVin). assumption.
      + specialize (Hn st Hstin). contradict Hn. unfold compose. rewrite Hsteq. assumption.
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
