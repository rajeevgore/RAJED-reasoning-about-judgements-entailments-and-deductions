Require Import String.
Require Import Relations.
Require Import List ListDec Decidable.
Import ListNotations.
Require Import ListSetNotations.
Require Import Datatypes.
Require Import Arith.
Require Import Bool.

Require Import Tactics.
Require Import EqDec.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import Derivability.

Open Scope list.


(* Most of this file is an adaptation of Jeremy Dawson's formalisation of
   the cut-elimination theorem *)

Section CutElim.
  
  Context `{SL : STRLANG}.
  Variable (DC : DISPCALC).
  Variable (BP : BELNAP DC).

  Lemma C345_holds : C345 DC.
  Proof.
    unfold C345. intros. unfold bprops. repeat split;
    unfold C3_one, C4_one, C5_one, seqNoSSF.
    all: (apply C3_holds || apply C4_holds || apply C5_holds); assumption.
  Qed.


  Lemma strSubrep {af s1 s2 X Y Z} : forall {pn},
      (forall x b, x ∈ strSVsSgn Z b ->
              strrep X Y (eqb pn b) (s1 x) (s2 x)) ->
      strrep X Y pn (strSubst (af, s1) Z) (strSubst (af, s2) Z).
  Proof.
    pattern Z. revert Z. apply ipse_rect.
    intros Z IH pn H. rewrite ! strSubst_eq.
    destruct (Var_dec SV Z) as [[v Hv]|HnSV];
      destruct (Var_dec FS Z) as [[A HA]|HnFS].
    - rewrite Hv in HA. contradict HA. apply SV_FS_disc.
    - rewrite <- (eqb_true_r pn). apply H. rewrite Hv.
      rewrite strSVsSgn_eq, (Var_dec_Var SV). now left.
    - constructor.
    - set (l := map (strSubst (af, s1)) (ipse Z)).
      remember (conn Z l) as Z0. rewrite <- (conn_conn Z l);
        try apply map_length.
      rewrite HeqZ0. unfold l. apply strrep_conn.
      + rewrite ipse_conn; try apply map_length.
        rewrite ! map_length. reflexivity.
      + intros [[b' U] V] Hin. simpl.
        rewrite sgnips_conn, ipse_conn in Hin; try apply map_length.
        apply zip_pair_map_in_23_inv in Hin.
        destruct Hin as [Z' [HeqU [HeqV HZ']]].
        rewrite HeqU, HeqV. apply IH.
        * apply in_zip_pair_snd in HZ'. assumption.
        * intros x b Hx. rewrite eqb_nxorb_swap. apply H.
          rewrite strSVsSgn_eq, Var_dec_not_Var; try assumption.
          rewrite In_union_iff. exists (b', Z').
          split; [assumption|]. rewrite nxorb_invol. assumption.
  Qed.


  Lemma seqSubrep {pf sub1 sub2 X Y pn seq} :
    (forall x b, x ∈ seqSVsSgn seq b ->
            strrep X Y (eqb pn b) (sub1 x) (sub2 x)) ->
    seqrep X Y pn (seqSubst (pf, sub1) seq) (seqSubst (pf, sub2) seq).
  Proof.
    intro H. destruct seq as [U V]. constructor.
    - apply strSubrep. intros x b Hxb. rewrite eqb_swap_negb. apply H.
      unfold seqSVsSgn. apply in_app_iff. left. rewrite negb_involutive. assumption.
    - apply strSubrep. intros x b Hxb. apply H.
      unfold seqSVsSgn. apply in_app_iff. right. assumption.
  Qed.

  Lemma strSubrep_inv {af1 sub1 af2 sub2 A Y Z} : forall {pn},
      strrep (FS A) Y pn (strSubst (af1, sub1) Z) (strSubst (af2, sub2) Z) ->
      forall x b, x ∈ strSVsSgn Z b ->
	     strrep (FS A) Y (eqb pn b) (sub1 x) (sub2 x).
  Proof.
    intros pn Hrep. remember (strSubst (af1, sub1) Z) as sub1Z.
    remember (strSubst (af2, sub2) Z) as sub2Z. revert Z Heqsub1Z Heqsub2Z.
    induction Hrep as [| |pn Z l Hlen Hrep IH].
    - intros W Heq1 Heq2 x b' Hxb'. rewrite Heq1 in Heq2.
      destruct af1 as [a1 f1]. destruct af2 as [a2 f2].
      apply strSubst_fun_agree_iff in Heq2. destruct Heq2 as [_ [_ Hagr] ].
      rewrite Hagr; try constructor 1.
      rewrite strSVs_decouple. destruct b'; [now left | now right].
    - intros Z Heq1 Heq2 x b Hxb.
      rewrite strSubst_eq in Heq1, Heq2.
      rewrite strSVsSgn_eq in Hxb.
      destruct (Var_dec SV Z) as [[v Hv]|HnSV];
        [|destruct (Var_dec FS Z) as [[B HB]|HnFS]].
      + destruct b; try contradiction.
        destruct_List_In. rewrite <- H.
        simpl in Heq1, Heq2. rewrite <- Heq1, <- Heq2.
        apply strrep_two.
      + rewrite HB in Hxb. rewrite (Var_ipse FS) in Hxb.
        rewrite zip_nil_r in Hxb.
        simpl in Hxb. contradiction.
      + apply eq_sym, (conn_eq_Var FS) in Heq1; try apply map_length.
        rewrite Heq1, (Var_ipse FS), zip_nil_r in Hxb. contradiction.
    - intros W Heq1 Heq2 x b Hxb.
      rewrite strSVsSgn_eq in Hxb.
      rewrite strSubst_eq in Heq1, Heq2.
      destruct (Var_dec SV W) as [[v Hv]|HnSV];
        [|destruct (Var_dec FS W) as [[B HB]|HnFS]].
      + destruct b; [|contradiction].
        destruct Hxb as [Heqx|]; [|contradiction].
        rewrite Heqx in Heq1, Heq2. simpl in Heq1, Heq2.
        rewrite eqb_true_r, <- Heq1, <- Heq2.
        apply strrep_conn; assumption.
      + rewrite HB, (Var_ipse FS), zip_nil_r in Hxb.
        contradiction.
      + apply In_union in Hxb. destruct Hxb as [[b' W'] [Hinb'W' Hinx]].
        simpl in Hinx. specialize (IH (b', strSubst (af1, sub1) W', strSubst (af2, sub2) W')).
        simpl in IH. rewrite <- (eqb_nxorb _ b'). apply IH with W';
          try reflexivity; try assumption.
        rewrite Heq1. rewrite sgnips_conn, ipse_conn; try apply map_length.
        apply conn_inj in Heq2; try (now apply eq_sym); try apply map_length.
        destruct Heq2 as [_ Heq2]. rewrite Heq2.
        apply zip_pair_in_map_23. assumption.
  Qed.

  Lemma seqSubrep_inv {pf1 sub1 pf2 sub2 A Y seq} : forall {pn},
      seqrep (FS A) Y pn (seqSubst (pf1, sub1) seq) (seqSubst (pf2, sub2) seq) ->
      forall x b, x ∈ (seqSVsSgn seq b) ->
	     strrep (FS A) Y (eqb pn b) (sub1 x) (sub2 x).
  Proof.
    intros pn H x b Hxb. destruct seq as [U V].
    apply seqrep_strrep in H. destruct H as [H1 H2].
    apply in_app_iff in Hxb. destruct Hxb as [Hxb | Hxb].
    - rewrite <- (negb_involutive pn). rewrite eqb_swap_negb.
      apply (strSubrep_inv H1). assumption.
    - apply (strSubrep_inv H2). assumption.
  Qed.

  

  Lemma extSubs {pseq cseq pseqA cseqA cseqY pn A Y pf suba suby subya} :
    (forall (x : string) (b : bool),
        x ∈ seqSVsSgn cseq b -> ~ x ∈ seqSVsSgn pseq (negb b)) ->
    seqrep (FS A) Y pn cseqA cseqY ->
    seqSubst (pf, suba) cseq = cseqA ->
    seqSubst (pf, suba) pseq = pseqA ->
    seqSubst (pf, suby) cseq = cseqY ->
    subya = defSubs (seqSVs cseq) suby suba ->
    seqSubst (pf, subya) cseq = cseqY /\
      seqrep (FS A) Y pn pseqA (seqSubst (pf, subya) pseq).
  Proof.
    intros HSV Hrep HcseqA HpseqA HcseqY Hsubya.
    split.
    - rewrite Hsubya. rewrite <- HcseqY. apply defSubs_norm.
    - rewrite <- HpseqA, Hsubya. apply seqSubrep.
      intros x b Hxbp. destruct (in_dec string_dec x (seqSVsSgn cseq b)) as [Hxbc | Hnxbc].
      + rewrite defSubs_agree_sub1.
        * rewrite <- HcseqA, <- HcseqY in Hrep.
          apply (seqSubrep_inv Hrep). assumption.
        * rewrite seqSVs_decouple. destruct b; ((now left) || (now right)).
      + assert (x ∉ seqSVsSgn cseq (negb b)) as Hnxbp.
        { intro H. apply (HSV _ _ H). rewrite negb_involutive. assumption. }
        rewrite defSubs_agree_sub2; [constructor | idtac].
        rewrite seqSVs_decouple. intro H. destruct b; destruct H; contradiction.
  Qed.

  Lemma extSubs2 [r rA : rule] [conclY : sequent]
    [af : afSubst] [suba : sSubst] (ssub : sSubstfor af (conclRule r) conclY)
    (subY : afsSubst) (A : formula) (Y : structr) (pn : bool) :
    ruleSubst (af, suba) r = rA -> bprops r ->
    seqrep (FS A) Y pn (conclRule rA) conclY ->
    subY = stepSub (af, suba) (conclRule r) conclY ssub ->
    conclRule (ruleSubst subY r) = conclY /\
      seqreps (FS A) Y pn (premsRule rA) (premsRule (ruleSubst subY r)).
  Proof.
    intros Hsubr Hbprops Hseqrep HeqsubY.
    split.
    - rewrite HeqsubY. rewrite conclRule_ruleSubst. apply stepSub_norm.
    - rewrite <- Hsubr. repeat rewrite premsRule_ruleSubst. rewrite HeqsubY.
      rewrite <- Hsubr, <- (proj2_sig ssub), conclRule_ruleSubst in Hseqrep.
      apply seqreps_forall. apply Forall_forall.
      intros u Hu. eapply extSubs; try reflexivity; try assumption.
      destruct Hbprops as (_ & HC4 & _).
      intros b s. apply HC4. assumption.
  Qed.


  Lemma extSub2_fs [r rA : rule] [conclY : sequent] [pant psuc aant asuc yant ysuc : structr]
    (A : formula) (Y : structr) (pn : bool) :
    conclRule r = pant ⊢ psuc ->
    conclRule rA = aant ⊢ asuc -> conclY = yant ⊢ ysuc ->
    (strIsFml pant -> aant = FS A -> aant = yant) ->
    (strIsFml psuc -> asuc = FS A -> asuc = ysuc) ->
    ruleInst r rA -> bprops r ->
    seqrep (FS A) Y pn (conclRule rA) conclY ->
    {subY : afsSubst |
      conclRule (ruleSubst subY r) = conclY /\
        seqreps (FS A) Y pn (premsRule rA) (premsRule (ruleSubst subY r))}.
  Proof.
    intros Hconr HconrA HconY Hanteq Hsuceq Hrulefs Hbprops Hseqrep.
    destruct (ruleInst_ruleSubst Hrulefs) as [afs Hafs].
    destruct afs as [af s] eqn:Heqafs. eexists. eapply extSubs2; try eassumption.
    apply eq_sym. exact Hafs. reflexivity. Unshelve.
    eapply seqExSub2. exact Hconr. exact HconrA. exact HconY.
    1-2: pose proof (proj2 (proj2 Hbprops)) as HC5; unfold C5_one in HC5;
    rewrite Hconr in HC5; simpl in HC5; tauto.
    exact Hanteq. exact Hsuceq. rewrite Hafs. now destruct r.
    exact (proj1 Hbprops). exact Hseqrep.
  Defined.

  Lemma seqreps_length {pn : bool} {X Y : structr} {lX lY : list sequent} :
    seqreps X Y pn lX lY -> length lX = length lY.
  Proof.
    intro H. induction H; [reflexivity | idtac].
    simpl. rewrite IHseqreps. reflexivity.
  Qed.

  Lemma seqreps_map_concl {P} {pn : bool} {X Y : structr} {lX lY : list sequent} :
    seqreps X Y pn lX lY ->
    ForallT (fun s => forall t, seqrep X Y pn s t -> {dt | conclDT dt = t /\ P dt}) lX ->
    {ldt | map conclDT ldt = lY /\ Forall P ldt}.
  Proof.
    intros Hsreps. pose proof (seqreps_length Hsreps) as Hlen. revert Hsreps.
    pattern lX, lY. revert lX lY Hlen. apply list_biind.
    - intros Hsreps Hall. exists []. auto.
    - intros u lX v lY IH Hsreps Hall.
      destruct IH as [ldt Hldt]; [now inversion Hsreps | now inversion Hall | idtac].
      inversion Hall. clear H1 H0 l x. rename X0 into Hu, X1 into HlX.
      destruct (Hu v) as [dt Hdt]; try now inversion Hsreps.
      exists (dt :: ldt). split.
      + simpl. rewrite (proj1 Hldt), (proj1 Hdt). reflexivity.
      + constructor 2; tauto.
  Defined.


  Theorem makeCutLP (dtAY dtA : dertree) (A : formula) (Y : structr) :
    allDT nocut dtAY -> proper DC dtAY -> conclDT dtAY = FS A ⊢ Y ->
    allDT nocut dtA -> proper DC dtA -> forall (seqY : sequent),
        seqrep (FS A) Y true (conclDT dtA) seqY ->
        {dtY | conclDT dtY = seqY /\ allDT (cutIsLP A) dtY /\ proper DC dtY}.
  Proof.
    (* preparations, induction, break down rules *)
    intros HcutAY HvalAY HconcAY HcutA HvalA.
    induction dtA as [|s r l IH]; try (contradict HvalA; apply not_proper_Unf).
    remember (Der s r l) as dtA. intros seqY Hseqrep.
    destruct r as (ps, c) eqn:Heqr. destruct c as [U V] eqn:Heqc.
    destruct seqY as [UY VY] eqn:HeqseqY. destruct s as [UA VA] eqn:Heqs.
    remember (map conclDT l) as psA. remember (psA, s) as rA.
    rewrite <- Heqr, <- Heqc, <- HeqseqY, <- Heqs in *.
    move HeqpsA after HeqrA. move Heqs after HeqpsA.
    move HeqdtA before HeqrA. move Heqr after Heqs.
    move Heqc after Heqr. move HeqseqY after Heqc.
    rewrite HeqdtA, Heqs, HeqseqY in Hseqrep. simpl in Hseqrep.
    (* prove simple useful things *)
    assert (r ∈ DC /\ ruleInst r rA /\ bprops r) as Hutils.
    unfold proper in HvalA. rewrite HeqdtA in HvalA. simpl in HvalA.
    rewrite HeqrA, HeqpsA. split; try tauto. split; try tauto.
    apply C345_holds. unfold proper in HvalA. simpl in HvalA. tauto.
    (* highlight there are two cases *)
    assert ({strIsFml V /\ VA = FS A /\ VA <> VY}
            + {strIsFml V -> VA = FS A -> VA = VY}) as H by (
          destruct (strIsFml_dec V); destruct (eqdec VA (FS A));
          destruct (eqdec VA VY); try (now left); try (now right)).
    destruct H as [H|H].
    - destruct H as (HfmlV & HeqVA & HneqVA).
      pose proof (seqrep_trans_suc Hseqrep HeqVA HneqVA) as HeqVY.
      rewrite Heqs in HeqrA. rewrite Heqc in Heqr.
      remember (UY ⊢ FS A) as seqYl.
      destruct (extSub2_fs A Y true (f_equal conclRule Heqr) (f_equal conclRule HeqrA)
                  HeqseqYl (fun _ => seqrep_same_ant Hseqrep)) as [subY [HsubY Hseqreps] ];
        try tauto.
      rewrite HeqrA, HeqseqYl, HeqVA. simpl.
      constructor. inversion Hseqrep. tauto. constructor.
      destruct (@seqreps_map_concl (fun d => allDT (cutIsLP A) d /\ proper DC d)
                  _ _ _ _ _ Hseqreps) as (ldt & Hldtmap & Hldtall).
      rewrite HeqrA, HeqpsA. simpl. apply ForallT_map.
      rewrite ForallT_forall. rewrite ForallT_forall in IH.
      intros x Hx t Hxt.
       rewrite HeqdtA in HvalA, HcutA. apply IH with x; try assumption.
      apply (proj1 (Forall_forall _ _) (allDTUp HcutA) _ Hx).
      apply (proj1 (Forall_forall _ _) (properUp HvalA) _ Hx).
      apply Forall_and_inv in Hldtall.
      destruct Hldtall as [HldtLP Hldtproper]. apply Forall_and_inv in Hldtproper.
      destruct Hldtproper as [Hldtwfb Hldtproper]. apply Forall_and_inv in Hldtproper.
      destruct Hldtproper as [Hldtfrb Hldtprnil].
      exists (Der seqY CUT [Der seqYl r ldt; dtAY]).
      split; try reflexivity. split.
      + simpl. split; repeat try split. right.
        destruct (strIsFml_sig _ HfmlV) as [B HB]. rewrite HB in *.
        exists UY, r, ldt, dtAY. split; try reflexivity.
        rewrite HeqseqYl, Heqr. split; reflexivity.
        rewrite Heqr. tauto.
        left. rewrite HeqdtA in HcutA. simpl in HcutA. tauto.
        apply Forall_fold_right. assumption.
        apply (allDT_mono nocut); [assumption | apply nocut_impl_LRP].
      + unfold proper. simpl. unfold proper in HvalAY.
        split; repeat (try split);
          try apply Forall_fold_right; try tauto; try apply BP.
        rewrite HeqseqYl, HconcAY, HeqseqY, HeqVY.
        pose (((id, fun _ => A), fun st => if string_dec st "X" then UY else Y) : afsSubst)
          as cutsub.
        assert (ruleSubst cutsub CUT = ([UY ⊢ FS A; FS A ⊢ Y], UY ⊢ Y)) as Heqcutsub.
        unfold CUT. simpl. rewrite ! strSubst_SV, strSubst_FS.
        rewrite fmlSubst_FV. simpl. reflexivity.
        rewrite <- Heqcutsub. exists cutsub. reflexivity.
        rewrite Hldtmap, <- HsubY, <- surj_rule_pair. exists subY. reflexivity.
        rewrite (Forall_rw_fold_right Hldtprnil), fold_right_id.
        rewrite (proj2 (proj2 HvalAY)). repeat rewrite app_nil_l. reflexivity.
    - rewrite Heqc in Heqr. rewrite Heqs in HeqrA. rewrite HeqdtA in HvalA.
      destruct (extSub2_fs A Y true (f_equal conclRule Heqr) (f_equal conclRule HeqrA) HeqseqY)
        as [subY [HsubY Hseqreps] ]; try tauto.
      intros. apply (seqrep_same_ant Hseqrep H1).
      rewrite HeqrA, HeqseqY. simpl. assumption.
      remember (ruleSubst subY r) as rsubY. 
      destruct (@seqreps_map_concl (fun d => allDT (cutIsLP A) d /\ proper DC d)
                  _ _ _ _ _ Hseqreps) as (ldt & Hldtmap & Hldtall).
      rewrite HeqrA, HeqpsA. simpl. apply ForallT_map.
      rewrite ForallT_forall. rewrite ForallT_forall in IH. intros x Hx t Hxt.
      apply IH with x; try assumption.
      rewrite HeqdtA in HcutA.
      apply (proj1 (Forall_forall _ _) (allDTUp HcutA) _ Hx).
      apply (proj1 (Forall_forall _ _) (properUp HvalA) _ Hx).
      apply Forall_and_inv in Hldtall.
      destruct Hldtall as [HldtLP Hldtproper]. apply Forall_and_inv in Hldtproper.
      destruct Hldtproper as [Hldtwfb Hldtproper]. apply Forall_and_inv in Hldtproper.
      destruct Hldtproper as [Hldtfrb Hldtprnil].
      exists (Der seqY r ldt). split; try now simpl. split; try rewrite allDT_Der.
      + split. apply nocut_impl_LRP.
        rewrite HeqdtA, allDT_Der in HcutA.
        apply (nocut_dep_rule (proj1 HcutA)).
        apply Forall_fold_right. apply HldtLP.
      + split; rewrite allDT_Der. split; try tauto.
        apply Forall_fold_right. assumption. split. split.
        simpl. rewrite Hldtmap, <- HsubY, <- surj_rule_pair, HeqrsubY.
        exists subY. reflexivity.
        unfold allDTs. rewrite <- Forall_fold_right. assumption.
        simpl. unfold proper in HvalA. simpl in HvalA.
        simpl. rewrite (Forall_rw_fold_right Hldtprnil). simpl.
        apply fold_right_id.
  Defined.


  (* Turn general cuts into left-principal cuts *)
  Theorem allLP (dt : dertree) (A : formula) :
    cutOnFmls (eq A) dt -> proper DC dt -> allNextDTs nocut dt ->
    {dt' | conclDT dt' = conclDT dt /\ allDT (cutIsLP A) dt' /\ proper DC dt'}.
  Proof.
    intros Hcut Hval Hnocut. destruct dt as [s | s r l] eqn:Heqdt;
      [exists dt; rewrite Heqdt; repeat (split; tauto) | idtac].
    destruct (rule_eq_dec r CUT) as [Heqr|Hneqr].
    - pose proof (properUp Hval) as Hvalup.
      destruct Hval as (Hfrb & Hwfb & Hprems). destruct Hwfb as [Hwfb Hwfbup].
      destruct (ruleInst_ruleSubst Hwfb) as [afs Heq].
      destruct afs as [ [fp ff] fs] eqn:Heqafs.
      rewrite Heqr in Heq. simpl in Heq. injection Heq. intros Heqs Heqconcl.
      destruct l as [|d0 l]; try discriminate.
      destruct l as [|d1 l]; try discriminate.
      destruct l; try discriminate.
      simpl in Heqconcl. injection Heqconcl. intros Heqcd1 Heqcd0.
      clear Heq Heqconcl. simpl in Hnocut. simpl in Hvalup.
      assert (fmlSubst (fp, ff) (FV "A") = A) as HeqsubA.
      { destruct Hcut as [|Hcut]; try contradiction.
        destruct Hcut as (pl & pr & suc & fml & fmlinA & Heqd1d0 & Heqconc).
        injection Heqd1d0. intros Heqd1 Heqd0. rewrite <- Heqd1 in Heqconc.
        rewrite <- fmlinA in Heqconc.
        rewrite Heqcd1 in Heqconc. injection Heqconc.
        rewrite strSubst_SV, strSubst_FS, ! fmlSubst_FV. simpl.
        intros. apply (Var_inj FS). assumption. }
      rewrite strSubst_SV, strSubst_FS in Heqcd1, Heqcd0.
      rewrite fmlSubst_FV in Heqcd1, Heqcd0, HeqsubA.
      simpl in Heqcd1, Heqcd0, HeqsubA.
      rewrite HeqsubA in Heqcd1, Heqcd0.
      set (X := fs "X"). set (Y := fs "Y").
      fold X in Heqcd0, Heqs. fold Y in Heqcd1, Heqs.
      pose proof (Forall_inv Hvalup) as Hvald0.
      pose proof (Forall_inv (Forall_inv_tail Hvalup)) as Hvald1.
      simpl in Hfrb. rewrite Heqr in Hfrb.
      eapply (makeCutLP d1 d0 _ Y); try tauto.
      rewrite Heqs, Heqcd0. rewrite ! strSubst_SV. simpl.
      constructor; constructor.
    - exists dt. rewrite Heqdt. repeat (split; try tauto). simpl. now left.
      simpl in Hnocut. fold (allDTs (cutIsLP A) l). revert Hnocut.
      apply allDTs_impl. apply nocut_impl_LP.
  Defined.



  Lemma makeCutLRP (dtAY dtA : dertree) (A : formula) (Y : structr) :
    allDT nocut dtAY -> rootIsSucP dtAY -> proper DC dtAY -> conclDT dtAY = Y ⊢ FS A ->
    proper DC dtA -> allDT nocut dtA -> forall seqY,
        seqrep (FS A) Y false (conclDT dtA) seqY ->
        {dtY | conclDT dtY = seqY /\ allDT (cutIsLRP A) dtY /\ proper DC dtY}.
  Proof.      
    (* preparations, induction, break down rules *)
    intros HdtAY HsucPdtAY HvalAY HdtAY1 HvalA HdtA0.
    induction dtA as [|s r l IH]; try (contradict HvalA; apply not_proper_Unf).
    remember (Der s r l) as dtA. intros seqY Hseqrep.
    destruct r as (ps, c) eqn:Heqr. destruct c as [U V] eqn:Heqc.
    destruct seqY as [UY VY] eqn:HeqseqY. destruct s as [UA VA] eqn:Heqs.
    remember (map conclDT l) as psA. remember (psA, s) as rA.
    rewrite <- Heqr, <- Heqc, <- HeqseqY, <- Heqs in *.
    move HeqpsA after HeqrA. move Heqs after HeqpsA.
    move HeqdtA before HeqrA. move Heqr after Heqs.
    move Heqc after Heqr. move HeqseqY after Heqc.
    rewrite HeqdtA, Heqs, HeqseqY in Hseqrep. simpl in Hseqrep.
    (* prove simple useful things *)
    assert (r ∈ DC /\ ruleInst r rA /\ bprops r) as Hutils.
    unfold proper in HvalA. rewrite HeqdtA in HvalA. simpl in HvalA.
    rewrite HeqrA, HeqpsA. split; try tauto. split; try tauto.
    apply C345_holds. unfold proper in HvalA. simpl in HvalA. tauto.
    (* highlight there are two cases *)
    assert ({strIsFml U /\ UA = FS A /\ UA <> UY}
            + {strIsFml U -> UA = FS A -> UA = UY}) as H by (
          destruct (strIsFml_dec U); destruct (eqdec UA (FS A));
          destruct (eqdec UA UY); try (now left); try (now right)).
    destruct H as [H|H].
    - destruct H as (HfmlU & HeqUA & HneqUA).
      pose proof (seqrep_trans_ant Hseqrep HeqUA HneqUA) as HeqUY.
      rewrite Heqs in HeqrA. rewrite Heqc in Heqr.
      remember (FS A ⊢ VY) as seqYr.
      destruct (extSub2_fs A Y false (f_equal conclRule Heqr) (f_equal conclRule HeqrA)
                  HeqseqYr (fun _ H => H) (fun _ => seqrep_same_suc Hseqrep))
        as [subY [HsubY Hseqreps] ];
        try tauto.
      rewrite HeqrA, HeqseqYr, HeqUA. simpl.
      constructor; [constructor | idtac]. inversion Hseqrep. tauto.
      destruct (@seqreps_map_concl (fun d => allDT (cutIsLRP A) d /\ proper DC d)
                  _ _ _ _ _ Hseqreps) as (ldt & Hldtmap & Hldtall).
      rewrite HeqrA, HeqpsA. simpl. apply ForallT_map.
      rewrite ForallT_forall. rewrite ForallT_forall in IH. intros x Hx t Hxt.
      apply IH with x; try assumption. rewrite HeqdtA in HvalA, HdtA0.
      apply (proj1 (Forall_forall _ _) (properUp HvalA) _ Hx).
      rewrite HeqdtA in HdtA0.
      apply (proj1 (Forall_forall _ _) (allDTUp HdtA0) _ Hx).
      apply Forall_and_inv in Hldtall.
      destruct Hldtall as [HldtLP Hldtproper]. apply Forall_and_inv in Hldtproper.
      destruct Hldtproper as [Hldtwfb Hldtproper]. apply Forall_and_inv in Hldtproper.
      destruct Hldtproper as [Hldtfrb Hldtprnil].
      exists (Der seqY CUT [dtAY; Der seqYr r ldt]).
      split; try reflexivity. split.
      + simpl. split; repeat try split. right.
        destruct dtAY; try (contradict HvalAY; apply not_proper_Unf).
        simpl in HdtAY1, HsucPdtAY.
        exists Y, r0, l0, (Der seqYr r ldt). split. now rewrite HdtAY1. assumption.
        rewrite HeqseqYr. simpl. right. exists VY, dtAY, r, ldt.
        rewrite Heqr. tauto.
        apply (allDT_mono nocut); [assumption | apply nocut_impl_LRP].
        left. rewrite HeqdtA in HdtA0. simpl in HdtA0. tauto.
        left. rewrite HeqdtA in HdtA0. simpl in HdtA0. tauto.
        apply Forall_fold_right. assumption.
      + unfold proper. simpl. unfold proper in HvalAY.
        split; repeat (try split);
          try apply Forall_fold_right; try tauto; try apply BP.
        rewrite HeqseqYr, HdtAY1, HeqseqY, HeqUY.
        pose (((id, fun _ => A), fun st => if string_dec st "X" then Y else VY) : afsSubst)
          as cutsub.
        assert (ruleSubst cutsub CUT = ([Y ⊢ FS A; FS A ⊢ VY], Y ⊢ VY)) as Heqcutsub.
        unfold CUT. simpl. rewrite ! strSubst_SV, strSubst_FS, fmlSubst_FV.
        simpl. reflexivity.
        rewrite <- Heqcutsub. exists cutsub. reflexivity.
        rewrite Hldtmap, <- HsubY, <- surj_rule_pair. exists subY. reflexivity.
        rewrite (Forall_rw_fold_right Hldtprnil), fold_right_id.
        rewrite (proj2 (proj2 HvalAY)). repeat rewrite app_nil_l. reflexivity.
    - rewrite Heqc in Heqr. rewrite Heqs in HeqrA. rewrite HeqdtA in HvalA.
      destruct (extSub2_fs A Y false (f_equal conclRule Heqr) (f_equal conclRule HeqrA) HeqseqY)
        as [subY [HsubY Hseqreps] ]; try tauto.
      intros. apply (seqrep_same_suc Hseqrep H1).
      rewrite HeqrA, HeqseqY. simpl. assumption.
      remember (ruleSubst subY r) as rsubY.
      destruct (@seqreps_map_concl (fun d => allDT (cutIsLRP A) d /\ proper DC d)
                  _ _ _ _ _ Hseqreps) as (ldt & Hldtmap & Hldtall).
      rewrite HeqrA, HeqpsA. simpl. apply ForallT_map.
      rewrite ForallT_forall. rewrite ForallT_forall in IH. intros x Hx t Hxt.
      apply IH with x; try assumption.
      apply (proj1 (Forall_forall _ _) (properUp HvalA) _ Hx).
      rewrite HeqdtA in HdtA0.
      apply (proj1 (Forall_forall _ _) (allDTUp HdtA0) _ Hx).
      apply Forall_and_inv in Hldtall.
      destruct Hldtall as [HldtLP Hldtproper]. apply Forall_and_inv in Hldtproper.
      destruct Hldtproper as [Hldtwfb Hldtproper]. apply Forall_and_inv in Hldtproper.
      destruct Hldtproper as [Hldtfrb Hldtprnil].
      exists (Der seqY r ldt). split; try now simpl. split; try rewrite allDT_Der.
      + split. apply nocut_impl_LRP.
        rewrite HeqdtA, allDT_Der in HdtA0.
        apply (nocut_dep_rule (proj1 HdtA0)).
        apply Forall_fold_right. apply HldtLP.
      + split; rewrite allDT_Der. split.
        simpl. tauto. apply Forall_fold_right. assumption. simpl. split. split.
        rewrite Hldtmap, <- HsubY, <- surj_rule_pair, HeqrsubY.
        exists subY. reflexivity.
        unfold allDTs. rewrite <- Forall_fold_right. assumption.
        unfold proper in HvalA. simpl in HvalA. 
        simpl. rewrite (Forall_rw_fold_right Hldtprnil). simpl.
        apply fold_right_id.
  Defined.


  (* Turn left-principal cuts into (left and right) principal cuts *)
  Lemma allLRP (dt : dertree) (A : formula) :
    cutIsLP A dt -> proper DC dt -> allNextDTs nocut dt ->
    {dt' | conclDT dt' = conclDT dt /\ allDT (cutIsLRP A) dt' /\ proper DC dt'}.
  Proof.
    intros Hcut Hval Hnocut. destruct dt as [s | s r l] eqn:Heqdt;
      [exists dt; rewrite Heqdt; split; [idtac | split]; try tauto; split; tauto | idtac].
    destruct (rule_eq_dec r CUT) as [Heqr|Hneqr]. 
    - pose proof (properUp Hval) as Hvalup. destruct_proper Hval.
      destruct (ruleInst_ruleSubst Hwfb) as [afs Heq].
      destruct afs as [ [fp ff] fs] eqn:Heqafs.
      rewrite Heqr in Heq. simpl in Heq. injection Heq. intros Heqs Heqconcl.
      destruct l as [|d0 l]; try discriminate.
      destruct l as [|d1 l]; try discriminate.
      destruct l; try discriminate.
      simpl in Heqconcl. injection Heqconcl. intros Heqcd1 Heqcd0.
      clear Heq Heqconcl. simpl in Hnocut. simpl in Hvalup.
      assert (A = fmlSubst (fp, ff) (FV "A")) as HeqsubA.
      { destruct Hcut as [|Hcut]; try contradiction.
        destruct Hcut as (ant & r' & l' & pr & Heql & Hfmlr').
        injection Heql. intros Heqd1 Heqd0. rewrite Heqd0 in Heqcd0.
        injection Heqcd0. rewrite strSubst_SV, strSubst_FS, ! fmlSubst_FV.
        simpl. intros. apply (Var_inj FS). assumption. }
      rewrite strSubst_SV, strSubst_FS in Heqcd1, Heqcd0.
      rewrite fmlSubst_FV in Heqcd1, Heqcd0, HeqsubA.
      simpl in Heqcd1, Heqcd0, HeqsubA.
      rewrite <- HeqsubA in Heqcd1, Heqcd0.
      set (X := fs "X"). set (Y := fs "Y").
      fold X in Heqcd0, Heqs. fold Y in Heqcd1, Heqs.
      pose proof (Forall_inv Hvalup) as Hvald0.
      pose proof (Forall_inv (Forall_inv_tail Hvalup)) as Hvald1.
      simpl in Hfrb. rewrite Heqr in Hfrb.
      eapply (makeCutLRP d0 d1 _ X); try tauto.
      + destruct Hcut as [|Hcut]; try contradiction.
        destruct Hcut as (ant & r' & l' & pr & Heql & Hfmlr').
        injection Heql. intros Heqd1 Heqd0. rewrite Heqd0. assumption.
      + rewrite Heqs, Heqcd1. rewrite ! strSubst_SV. simpl. constructor; constructor.
    - exists dt. rewrite Heqdt. repeat (split; try tauto). simpl. now left.
      simpl in Hnocut. fold (allDTs (cutIsLRP A) l). revert Hnocut.
      apply allDTs_impl. apply nocut_impl_LRP.
  Defined.


  Definition canElim (P : dertree -> Prop) : Type :=
    forall dt, proper DC dt -> P dt -> allNextDTs nocut dt ->
          {dt' | proper DC dt' /\ conclDT dt' = conclDT dt /\ allDT nocut dt'}.

  Definition canElimAll (P : dertree -> Prop) :=
    forall dt, proper DC dt -> allDT P dt ->
          {dt' | proper DC dt' /\ conclDT dt' = conclDT dt /\ allDT nocut dt' /\
                   (botRule dt <> Some CUT -> botRule dt' = botRule dt)}.

  Lemma canElim_def' (P : dertree -> Prop) :
    canElim P <+> forall dt, P dt -> allNextDTs nocut dt -> proper DC dt ->
                        {dt' | proper DC dt' /\ conclDT dt' = conclDT dt /\ allDT nocut dt' /\
                                 (nocut dt -> dt' = dt)}.
  Proof.
    split.
    - intros H dt Pdt Hnocutnext Hproper.
      destruct (nocut_dec dt) as [Hnocut | Hnnocut].
      + exists dt. repeat (split; try tauto). apply allDT_Next. tauto.
      + destruct (H dt) as [dt' Hdt']; try assumption.
        exists dt'. repeat (split; try tauto).
    - intros H dt Pdt Hnocutnext Hproper. destruct (H dt) as [dt' Hdt']; try assumption.
      exists dt'. tauto.
  Defined.
  
  Lemma canElim_canElimAll {P : dertree -> Prop} :
    (forall s l l', P (Der s CUT l) ->
               Forall2 (fun d d' => proper DC d' /\ conclDT d' = conclDT d /\ allDT nocut d' /\
                                     (botRule d <> Some CUT -> botRule d' = botRule d)) l l' ->
               P (Der s CUT l')) ->
    canElim P -> canElimAll P.
  Proof.
    intros lem.
    intros Helim dt. pattern dt. induction dt as [|s r l IH];
      [intros H; contradict H; apply not_proper_Unf | idtac].
    intros Hval HP. pose proof (properUp Hval) as Hvalup.
    pose proof (allDTUp HP) as HPup. simpl in Hvalup, HPup.
    apply Forall_ForallT in Hvalup, HPup.
    apply (ForallT_mp Hvalup), (ForallT_mp HPup) in IH.
    apply ForallT_sig_elim in IH. destruct IH as [l' Pll'].
    pose proof Pll' as H. apply Forall2_and_inv in H.
    destruct H as [Hvalup' H].
    apply Forall2_and_inv in H. destruct H as [Hconcleq H].
    apply Forall2_and_inv in H. destruct H as [Hnocutl' _].
    apply Forall2_Forall_r in Hnocutl'. apply Forall_fold_right in Hnocutl'.
    fold (allDTs nocut l') in Hnocutl'.
    apply Forall2_Forall_r in Hvalup'.
    apply (Forall2_impl (fun x y => conclDT x = conclDT y)) in Hconcleq;
      try (intros; now apply eq_sym).
    apply Forall2_map_iff, Forall2_eq_iff in Hconcleq.
    pose proof (proper_switch Hval Hvalup' Hconcleq) as Hval'.
    destruct (rule_eq_dec r CUT) as [Heq|Hneq].
    - rewrite allDT_Der in HP. destruct HP as [HP _]. rewrite Heq in *.
      pose proof (lem _ _ _ HP Pll') as HP'.
      destruct (Helim (Der s CUT l') Hval' HP' Hnocutl') as [dt' Hdt'].
      exists dt'. tauto.
    - exists (Der s r l'). repeat (split; try tauto).
  Defined.

  
  Lemma elimFmls [fmls : formula -> Prop] :
    canElim (cutOnFmls fmls) -> canElimAll (cutOnFmls fmls).
  Proof.
    apply canElim_canElimAll.
    intros s l l' Hcut Hall. simpl in Hcut.
    destruct Hcut as [|Hcut]; try contradiction.
    destruct Hcut as (pl & pr & suc & fml & Hfmlin & Heql & Hconceq).
    rewrite Heql in Hall.
    destruct l' as [|pl' l']; try (inversion Hall; fail).
    apply Forall2_cons_iff in Hall. destruct Hall as [Hpl Hall].
    destruct l' as [|pr' l']; try (inversion Hall; fail).
    apply Forall2_cons_iff in Hall. destruct Hall as [Hpr Hall].
    inversion Hall.
    right. exists pl', pr', suc, fml. rewrite (proj1 (proj2 Hpr)). tauto.
  Defined.




  Lemma cfptv [dt : dertree] :
    allDT nocut dt -> proper DC dt -> proper (remove_rule CUT DC) dt.
  Proof.
    intros Hnocut (Hfrb & Hwfb & Hprems). repeat (split; try assumption).
    rewrite allDT_in_tree in Hnocut. rewrite allDT_in_tree in Hfrb.
    rewrite allDT_in_tree. intros d Hd.
    specialize (Hnocut d Hd). specialize (Hfrb d Hd).
    destruct d; try (simpl; tauto).
    simpl. apply in_in_remove; try assumption.
  Qed.

  Lemma noPremsD [dt : dertree] :
    allDT wfr dt -> premsDT dt = [] -> allDT (cutOnFmls (fun _ => True)) dt.
  Proof.
    intros Hwfb Hprems. rewrite allDT_in_tree in Hwfb.
    rewrite allDT_in_tree. rewrite premsDT_in_tree in Hprems.
    intros d Hd. specialize (Hwfb d Hd). specialize (Hprems d Hd).
    destruct d; try discriminate.
    destruct (rule_eq_dec r CUT) as [Heqr|Hneqr]; try now left.
    right. simpl in Hwfb. apply ruleInst_ruleSubst in Hwfb.
    destruct Hwfb as [afs Hafs]. rewrite Heqr in Hafs.
    injection Hafs. intros Heqs Heqcl.
    destruct l as [|pl l]; try discriminate.
    destruct l as [|pr l]; try discriminate.
    destruct l; try discriminate. injection Heqcl. intros Heqpr Heqpl.
    exists pl, pr, (snd afs "Y"), (fmlSubst (fst afs) (FV "A")).
    rewrite strSubst_SV, strSubst_FS in Heqpr.
    split; try constructor; try reflexivity; try assumption.
  Qed.

  Lemma proper_cutOnFull [dt : dertree] :
    proper DC dt -> allDT (cutOnFmls (fun _ => True)) dt.
  Proof.
    intro H. unfold proper in H. apply noPremsD; tauto.
  Qed.

  Definition canElimRaw :=
    forall dt : dertree, allNextDTs nocut dt -> proper DC dt ->
                    {dt' : dertree | proper DC dt' /\ conclDT dt' = conclDT dt /\ allDT nocut dt'}.

  Definition canElimAllRaw :=
    forall dt : dertree, proper DC dt ->
                    {dt' : dertree | proper DC dt' /\ conclDT dt' = conclDT dt /\ allDT nocut dt' /\
                                       (botRule dt <> Some CUT -> botRule dt' = botRule dt)}.

  Lemma canElim_cutOnFull_iff : canElimRaw <+> canElim (cutOnFmls (fun _ => True)).
  Proof.
    split.
    - intros H dt. intros. apply H; assumption.
    - intros H dt. intros. apply H; try assumption. apply proper_cutOnFull in H1.
      apply allDT_Next in H1. tauto.
  Defined.

  Lemma canElimAll_cutOnFull_iff : canElimAllRaw <+> canElimAll (cutOnFmls (fun _ => True)).
  Proof.
    split.
    - intros H dt. intros. apply H; assumption.
    - intros H dt. intros. apply H; try assumption. apply proper_cutOnFull. assumption.
  Defined.

  Lemma cutOnFmls_mono {dt fmls1 fmls2} :
    cutOnFmls fmls1 dt -> (forall A, fmls1 A -> fmls2 A) -> cutOnFmls fmls2 dt.
  Proof.
    intros Hcut Hsubset. destruct dt; try tauto.
    destruct Hcut; try now left. right.
    destruct H as (pl & pr & suc & A & HAin & Heql & Heqconcpr).
    exists pl, pr, suc, A. split; try tauto. apply Hsubset. assumption.
  Qed.

  Lemma canElim_ex {A : Type} {g : A -> dertree -> Prop} :
    (forall f, canElim (g f)) ->
    forall dt, proper DC dt -> {f | (g f) dt} -> allNextDTs nocut dt ->
          {dt' : dertree | proper DC dt' /\ conclDT dt' = conclDT dt /\ allDT nocut dt'}.
  Proof.
    intros Helim dt Hval [f Hgf] Hnocut. apply (Helim f dt); assumption.
  Defined.
  
  Lemma cutOnFmls_Full {dt : dertree} : cutOnFmls (fun _ => True) dt -> {A | cutOnFmls (eq A) dt}.
  Proof.
    intro Hcut. destruct dt; try (exists (Atm "p"); tauto).
    destruct (rule_eq_dec r CUT) as [Heqr|Hneqr].
    - destruct (right_cut_dec l) as [Hrc|Hnrc].
      + destruct Hrc as (pl & pr & suc & A & H). exists A. right.
        exists pl, pr, suc, A. split; try assumption. constructor.
      + exfalso. destruct Hcut as [|H]; try contradiction.
        destruct H as (pl & pr & suc & A & _ & H).
        specialize (Hnrc pl pr suc A). tauto.
    - exists (Atm "p"). now left.
  Defined.

  Lemma allElim (fmls : formula -> Prop) :
    (forall phi, fmls phi -> canElim (cutOnFmls (eq phi))) -> canElim (cutOnFmls fmls).
  Proof.
    intros H dt Hval Hcut Hnocut. destruct dt; try (contradict Hval; apply not_proper_Unf).
    destruct (rule_eq_dec r CUT) as [Heqr|Hneqr].
    - destruct r as [premr concr]. injection Heqr. intros Heqconcr Heqpremr.
      pose proof Hval as Hval0. destruct_proper Hval0. apply ruleInst_ruleSubst in Hwfb.
      destruct Hwfb as [afs Hafs]. injection Hafs. intros Heqs Heqconcl.
      rewrite Heqpremr in Heqconcl.
      destruct l as [|dl ds]; try discriminate.
      destruct ds as [|dr ds]; try discriminate.
      destruct ds; try discriminate.
      injection Heqconcl. intros Heqconcdr Heqconcdl.
      set (A := fmlSubst (fst afs) (FV "A")). fold A in Heqconcdr, Heqconcdl.
      apply (H A); try assumption.
      + destruct Hcut as [|Hcut]; try contradiction.
        destruct Hcut as (pl & pr & suc & B & HBin & Heql & Heqconcpr).
        injection Heql. intros Heqdr Heqdl. rewrite <- Heqdr, Heqconcdr in Heqconcpr.
        injection Heqconcpr. intros _ HeqA. unfold A.
        rewrite strSubst_FS in HeqA. apply (Var_inj FS) in HeqA.
        rewrite HeqA. assumption.
      + right. exists dl, dr, (snd afs "Y"), A.
        rewrite strSubst_SV, strSubst_FS in Heqconcdr. tauto.
    - exists (Der s r l). setoid_rewrite allDT_Next. tauto.
  Defined.

  Lemma thl {A s l l'} :
    cutIsLP A (Der s CUT l) ->
    Forall2 (fun d d' => proper DC d' /\ conclDT d' = conclDT d /\ allDT nocut d' /\
                          (botRule d <> Some CUT -> botRule d' = botRule d)) l l' ->
    cutIsLP A (Der s CUT l').
  Proof.
    intros HLP H. unfold cutIsLP in *. destruct HLP as [HLP|HLP]; try contradiction.
    destruct HLP as (ant0 & r0 & l0 & pr & Heql & Hfmlr0).
    rewrite Heql in H. inversion H. clear H3 H1 H0 l1 x.
    inversion H4. clear H5 H1 H0 l1 x. inversion H6. clear H H4 H6.
    right. destruct y as [ys | ys yr yl];
      try (destruct H2 as [H2 _]; contradict H2; apply not_proper_Unf).
    simpl in H2. destruct H2 as (_ & Heqys & [Hyrneq Hnocut] & Heqyr).
    destruct (rule_eq_dec r0 CUT) as [Heqr0|Hneqr0].
    - rewrite Heqr0 in Hfmlr0. simpl in Hfmlr0.
      inversion Hfmlr0 as [v Hctr]. apply eq_sym in Hctr.
      contradict Hctr. apply SV_FS_disc.
    - rewrite Some_eq_iff in Heqyr. specialize (Heqyr Hneqr0).
      injection Heqyr. clear Heqyr. intro Heqyr.
      exists ant0, r0, yl, y0. rewrite Heqys, Heqyr.
      repeat split; assumption.
  Qed.

  Lemma thr {A s l l'} :
    cutIsRP A (Der s CUT l) ->
    Forall2 (fun d d' => proper DC d' /\ conclDT d' = conclDT d /\ allDT nocut d' /\
                          (botRule d <> Some CUT -> botRule d' = botRule d)) l l' ->
    cutIsRP A (Der s CUT l').
  Proof.
    intros HRP H. unfold cutIsRP in *. destruct HRP as [HRP|HRP]; try contradiction.
    destruct HRP as (suc0 & s0 & r0 & l0 & Heql & Hfmlr0).
    rewrite Heql in H. inversion H. clear H3 H1 H0 l1 x.
    inversion H4. clear H5 H1 H0 l1 x. inversion H6. clear H H4 H6.
    right. destruct y0 as [ys | ys yr yl];
      try (destruct H3 as [H3 _]; contradict H3; apply not_proper_Unf).
    simpl in H3. destruct H3 as (_ & Heqys & [Hyrneq Hnocut] & Heqyr).
    destruct (rule_eq_dec r0 CUT) as [Heqr0|Hneqr0].
    - rewrite Heqr0 in Hfmlr0. simpl in Hfmlr0.
      inversion Hfmlr0 as [v Hctr]. apply eq_sym in Hctr.
      contradict Hctr. apply SV_FS_disc.
    - rewrite Some_eq_iff in Heqyr. specialize (Heqyr Hneqr0).
      injection Heqyr. clear Heqyr. intro Heqyr.
      exists suc0, y, r0, yl. rewrite Heqys, Heqyr.
      split. reflexivity. assumption.
  Qed.

  Lemma thlr {A s l l'} :
    cutIsLRP A (Der s CUT l) ->
    Forall2 (fun d d' => proper DC d' /\ conclDT d' = conclDT d /\ allDT nocut d' /\
                          (botRule d <> Some CUT -> botRule d' = botRule d)) l l' ->
    cutIsLRP A (Der s CUT l').
  Proof.
    intros [HL HR] H. exact (conj (thl HL H) (thr HR H)).
  Qed.


  Lemma elimLP {A : formula} : canElim (cutIsLP A) -> canElimAll (cutIsLP A).
  Proof.
    apply canElim_canElimAll. exact (@thl A).
  Defined.

  Lemma elimLRP {A : formula} : canElim (cutIsLRP A) -> canElimAll (cutIsLRP A).
  Proof.
    apply canElim_canElimAll. exact (@thlr A).
  Defined.

  Lemma allLP' {A : formula} : canElimAll (cutIsLP A) -> canElim (cutOnFmls (eq A)).
  Proof.
    intros Helim dt Hval Hcut Hnocut.
    destruct (allLP dt A Hcut Hval Hnocut) as [dt0 (Hconc0 & Hcut0 & Hval0)].
    destruct (Helim dt0) as [dt1 (Hval1 & Hconc1 & Hcut1 & _)]; try assumption.
    exists dt1. rewrite <- Hconc0. tauto.
  Defined.

  Lemma allLRP' {A : formula} : canElimAll (cutIsLRP A) -> canElim (cutIsLP A).
  Proof.
    intros Helim dt Hval Hcut Hnocut.
    destruct (allLRP dt A Hcut Hval Hnocut) as [dt0 (Hconc0 & Hcut0 & Hval0)].
    destruct (Helim dt0) as [dt1 (Hval1 & Hconc1 & Hcut1 & _)]; try assumption.
    exists dt1. rewrite <- Hconc0. tauto.
  Defined.

  Lemma th8 (A : formula) : canElim (cutIsLRP A) -> canElim (cutOnFmls (eq A)).
  Proof.
    exact (fun H => allLP' (elimLP (allLRP' (elimLRP H)))).
  Defined.

  Lemma allch (A : formula) : canElimAll (cutOnFmls (isipsubfml A)) -> canElim (cutIsLRP A).
  Proof.
    intros Helim dt Hdt Hdt0 Hdt1.
    destruct (C8_holds A dt Hdt Hdt0 Hdt1) as (dt' & Hdt' & Hdt'0 & Hdt'1).
    destruct (Helim dt' Hdt' Hdt'1) as (dt'' & H).
    exists dt''. rewrite Hdt'0 in H. tauto.
  Defined.

  Lemma th8ch' {A : formula} :
    (forall phi, isipsubfml A phi -> canElim (cutOnFmls (eq phi))) -> canElim (cutOnFmls (eq A)).
  Proof.
    intro H. apply th8, allch, elimFmls, allElim. assumption.
  Defined.

  Lemma canElimFml : forall A : formula, canElim (cutOnFmls (eq A)).
  Proof.
    apply ipse_rect. intro A. apply th8ch'.
  Defined.

  Lemma C3458_canElimRaw : canElimRaw.
  Proof.
    apply canElim_cutOnFull_iff. intros dt Hdt Hdt0.
    apply cutOnFmls_Full in Hdt0. revert dt Hdt Hdt0.
    apply canElim_ex. intro phi. apply canElimFml.
  Defined.

  Lemma cav : canElimAllRaw.
  Proof.
    pose proof (elimFmls ((fst canElim_cutOnFull_iff) C3458_canElimRaw)).
    apply canElimAll_cutOnFull_iff. assumption.
  Defined.

  (* Cut-elimination theorem *)
  Theorem cutElim (dt : dertree) :
    proper DC dt -> {dt' : dertree | conclDT dt' = conclDT dt
                                    /\ allDT nocut dt' /\ proper DC dt'}.
  Proof.
    intro Hproper. destruct (cav dt) as [dt' Hdt']; try assumption.
    unfold proper in Hproper. exists dt'. split; try tauto.
  Defined.

End CutElim.
