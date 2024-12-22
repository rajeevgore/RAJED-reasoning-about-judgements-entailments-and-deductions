Require Import String.
Require Import Constructive_sets.
Require Import Relations.
Require Import List ListDec Decidable.
Import ListNotations.
Require Import Datatypes.
Require Import Arith.
Require Import Bool.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.


Section C8CASE.

  Context `{SL : STRLANG}.
  Context (DC : DISPCALC).

Definition C8_case (X Y : structr) (ls : list sequent) (fmls : formula -> Prop) :=
  forall (ld : list dertree),
    Forall (proper DC) ld ->
    map conclDT ld = ls ->
    Forall (allDT nocut) ld ->
    {dt : dertree | proper DC dt /\ conclDT dt = X ⊢ Y /\ allDT (cutOnFmls fmls) dt}.

Definition C8_case_alt (X Y : structr) (ls : list sequent) (fmls : formula -> Prop) :=
  deriv_cofseqs DC fmls ls -> deriv_cofseq DC fmls (X ⊢ Y).

Lemma C8_case_alt_imp_C8_case :
  forall X Y ls fmls, C8_case_alt X Y ls fmls -> C8_case X Y ls fmls.
Proof.
  intros X Y ls fmls Halt ld Hprold Hconcld Hncld.
  apply deriv_cofseq_iff, Halt, deriv_cofseqs_iff.
  exists ld. repeat split; try assumption.
  eapply Forall_impl. eapply allDT_impl. apply nocut_impl_cut.
  assumption.
Defined.

End C8CASE.


Ltac auto_C3 :=
  let r := fresh "r" in let Hr := fresh "H" r in
  intros r Hr; simpl in Hr; destruct_List_In_name Hr;
  match goal with
    | [ H : _ = r |- _ ] =>
        rewrite <- H; unfold seqSVs; simpl; try (
        repeat (constructor; try (intro; destruct_List_In; (discriminate || tauto)));
        apply in_nil)
  end.

Ltac auto_C4 :=    
  let r := fresh "r" in let Hr := fresh "H" r in
  intros r Hr; simpl in Hr; destruct_List_In_name Hr;
  match goal with
  | [ H : _ = r |- _ ] =>
    let prems := fresh "prems" in let b := fresh "b" in let s := fresh "s" in
    rewrite <- H; try (intros prems b s; destruct b; simpl;
    try tauto; intros; repeat destruct_or; try contradiction;
    match goal with
    | [ H0 : _ = prems |- _ ] =>
      match goal with
      | [ H1 : _ = s |- _ ] =>
        rewrite <- H0, <- H1; unfold seqSVsSgn; simpl; intro; destruct_or; (discriminate || tauto)
      end
    end)
  end.

(*
Ltac auto_C5 :=
  let r := fresh "r" in let Hr := fresh "H" r in
  intros r Hr; simpl in Hr; try (destruct_List_In_name Hr;
  match goal with
  | [ H : _ = r |- _ ] =>
    rewrite <- H; unfold seqNoSSF; simpl; try tauto
  end).
*)

Ltac auto_C5 :=
  let r := fresh "r" in
  let Hr := fresh "H" r in
  intros r Hr; simpl in Hr;
   try
    (destruct_List_In_name Hr;
      match goal with
      | H:_ = r |- _ => rewrite <- H
      end);
  simpl; unfold strIsFml, strCtnsFml;
  rewrite ! (isVar_iff_isVar_cpt FS), ! (CtnsVar_iff_CtnsVar_cpt FS);
  repeat (rewrite CtnsVar_cpt_eq; unfold isVar_cpt; simpl Var_dec;
          simpl ipse; cbv iota; unfold fold_right); try tauto.

Arguments eq_rect_r /.

Ltac auto_C8 :=
  let A := fresh "A" in let dt := fresh "dt" in
  let Hpro := fresh "Hpro" in let Hproup := fresh "Hproup" in
  let Hproup0 := fresh "Hproup" in let Hproup1 := fresh "Hproup" in
  let HproL := fresh "HproL" in let HproR := fresh "HproR" in
  let Hcut := fresh "Hcut" in let Hnocut := fresh "Hnocut" in
  let HyL := fresh "HyL" in let HnL := fresh "HnL" in
  let HyR := fresh "HyR" in let HnR := fresh "HnR" in
  let HLP := fresh "HLP" in let HRP := fresh "HRP" in
  let Heqr := fresh "Heqr" in let Hneqr := fresh "Hneqr" in
  intros A dt Hpro Hcut Hnocut; destruct Hcut as [HLP HRP];
  destruct dt as [|s r l]; [contradict Hpro; apply not_proper_Unf|];
  destruct (rule_eq_dec r CUT) as [Heqr|Hneqr];
    [|exists (Der s r l); split; [assumption | split; [reflexivity|]];
      apply (allDT_impl _ _ (nocut_impl_cut _)); apply allDT_Next; tauto];
  destruct (LP_dec l A) as [HyL|HnL];
    try (exfalso; let H := fresh "H" in destruct HLP as [H|]; try contradiction;
      destruct H as (ant & r' & l' & br & H); specialize (HnL ant r' l' br); tauto);
  destruct (RP_dec l A) as [HyR|HnR];
    try (exfalso; let H := fresh "H" in destruct HRP as [H|]; try contradiction;
      destruct H as (suc & bl & r' & l' & H); specialize (HnR suc bl r' l'); tauto);
  destruct HyL as (X & rL & lL & br & HLeql & HfmlrL);
    destruct HyR as (Y & bl & rR & lR & HReql & HfmlrR);
  rewrite HReql in HLeql; injection HLeql; intros Heqbr Heqbl;
  rewrite Heqbl in HReql; clear HLeql Heqbr Heqbl;
  let Heql := fresh "Heql" in rename HReql into Heql;
  pose proof (properUp Hpro) as Hproup; rewrite Heql in Hproup;
  specialize_Forall_H Hproup;
  rename Hproup0 into HproL; rename Hproup1 into HproR;
  rewrite Heql in Hnocut;
  let Hexr := fresh "Hexr" in
  let Hwfr := fresh "Hwfr" in
  let Hprems := fresh "Hprems" in
  let Hexrup := fresh "Hexrup" in
  let Hwfrup := fresh "Hwfrup" in
  destruct Hpro as (Hexr, (Hwfr, Hprems)); rewrite allDT_Next in Hwfr, Hexr;
  destruct Hwfr as [Hwfr Hwfrup]; destruct Hexr as [Hexr Hexrup];
  rewrite Heql in Hexrup;
  simpl in Hwfr; rewrite Heqr, Heql in Hwfr;
  apply ruleInst_ruleSubst in Hwfr; destruct Hwfr as [pfs Hpfs];
  injection Hpfs; intros Heqs HeqY _ _ HeqX;
  rewrite <- HeqX, <- HeqY in Heqs; clear HeqY HeqX;
  rewrite Heqs; simpl;
  destruct Hexrup as [ [HrLin _] [ [HrRin _] _] ];
  unfold exr in HrLin, HrRin;
  unfold allNextDTs, allDTs in Hnocut;
  rewrite <- Forall_fold_right, Forall_forall in Hnocut; specialize_list;
  let HnocutL := fresh "HnocutL" in let HnocutR := fresh "HnocutR" in
  match goal with | H : allDT nocut (Der _ rL _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutL; clear H end;
  match goal with | H : allDT nocut (Der _ rR _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutR; clear H end;
  (* Consider all possible combinations of rules
     while removing those without formula variables at right places *)
  dec_destruct_List_In (@eqdec rule _) rL;
  let HeqrL := fresh "HeqrL" in
  match goal with
  | H : rL = _ |- _ =>
      rename H into HeqrL; rewrite HeqrL in *; simpl in HfmlrL;
      try (unfold strIsFml in HfmlrL;
           rewrite (isVar_iff_isVar_cpt FS) in HfmlrL;
           unfold isVar_cpt in HfmlrL; simpl Var_dec in HfmlrL;
           cbv iota in HfmlrL; contradiction)
  end;
  dec_destruct_List_In (@eqdec rule _) rR;
  let HeqrR := fresh "HeqrR" in
  match goal with
  | H : rR = _ |- _ =>
      rename H into HeqrR; rewrite HeqrR in *; simpl in HfmlrR;
      try (unfold strIsFml in HfmlrR;
           rewrite (isVar_iff_isVar_cpt FS) in HfmlrR;
           unfold isVar_cpt in HfmlrR; simpl Var_dec in HfmlrR;
           cbv iota in HfmlrR; contradiction)
  end;
  (* Remove incompatible rules *)
  pose proof (proper_root _ _ HproL) as HwfrL; destruct HwfrL as [_ HwfrL];
  apply ruleInst_ruleSubst in HwfrL; destruct HwfrL as [afsL HafsL];
  try (match type of HeqrL with rL = ?rho => unfold rho in HafsL end);
  (*unfold ruleSubst, seqSubst, strSubst in HafsL;
  try (rewrite fmlSubst_eq in HafsL); simpl in HafsL;*)
  (*rewrite <- ruleSubst_cust_ok in HafsL; simpl in HafsL;*)
  simpl in HafsL; (*unfold eq_rect_r in HafsL; simpl in HafsL;*)
  let HeqAL := fresh "HeqAL" in let HeqX := fresh "HeqX" in
  let HeqlL := fresh "HeqlL" in let dL := fresh "dL" in
  injection HafsL; intros HeqAL HeqX HeqlL;
  destruct_list_easy lL dL; try (injection HeqlL; intros);
  pose proof (properUp HproL) as HprodL; simpl in HprodL; specialize_Forall_H HprodL;
  pose proof (proper_root _ _ HproR) as HwfrR; destruct HwfrR as [_ HwfrR];
  apply ruleInst_ruleSubst in HwfrR; destruct HwfrR as [afsR HafsR];
  try (match type of HeqrR with rR = ?rho => unfold rho in HafsR end);
  (*unfold ruleSubst, seqSubst, strSubst in HafsR;
  try (rewrite fmlSubst_eq in HafsR); simpl in HafsR;*)
  (*rewrite <- ruleSubst_cust_ok in HafsR; simpl in HafsR;*)
  simpl in HafsR; (*unfold eq_rect_r in HafsR; simpl in HafsR;*)
  let HeqAR := fresh "HeqAR" in let HeqY := fresh "HeqY" in
  let HeqlR := fresh "HeqlR" in let dR := fresh "dR" in
  injection HafsR; intros HeqY HeqAR HeqlR;
  destruct_list_easy lR dR; try (injection HeqlR; intros);
  pose proof (properUp HproR) as HprodR; simpl in HprodR; specialize_Forall_H HprodR;
  (* Last details *)
  let HeqipsA := fresh "HeqipsA" in
  pose proof HeqAR as HeqipsA; rewrite HeqAL in HeqipsA;
  try discriminate; try injection HeqipsA; intros;
  move HnocutL at bottom; move HnocutR at bottom;
  specialize_list; try specialize_list.

(*
Ltac auto_C8 fml :=
  let A := fresh "A" in let dt := fresh "dt" in
  let Hpro := fresh "Hpro" in let Hproup := fresh "Hproup" in
  let Hproup0 := fresh "Hproup" in let Hproup1 := fresh "Hproup" in
  let HproL := fresh "HproL" in let HproR := fresh "HproR" in
  let Hcut := fresh "Hcut" in let Hnocut := fresh "Hnocut" in
  let HyL := fresh "HyL" in let HnL := fresh "HnL" in
  let HyR := fresh "HyR" in let HnR := fresh "HnR" in
  let HLP := fresh "HLP" in let HRP := fresh "HRP" in
  let Heqr := fresh "Heqr" in let Hneqr := fresh "Hneqr" in
  intros A dt Hpro Hcut Hnocut; destruct Hcut as [HLP HRP];
  destruct dt as [|s r l]; [contradict Hpro; apply not_proper_Unf|];
  destruct (rule_eq_dec r CUT) as [Heqr|Hneqr];
    [|exists (Der s r l); split; [assumption | split; [reflexivity|]];
      apply (allDT_impl (nocut_impl_cut _)); apply allDT_Next; tauto];
  destruct (LP_dec l A) as [HyL|HnL];
    try (exfalso; let H := fresh "H" in destruct HLP as [H|]; try contradiction;
      destruct H as (ant & r' & l' & br & H); specialize (HnL ant r' l' br); tauto);
  destruct (RP_dec l A) as [HyR|HnR];
    try (exfalso; let H := fresh "H" in destruct HRP as [H|]; try contradiction;
      destruct H as (suc & bl & r' & l' & H); specialize (HnR suc bl r' l'); tauto);
  destruct HyL as (X & rL & lL & br & HLeql & HfmlrL);
    destruct HyR as (Y & bl & rR & lR & HReql & HfmlrR);
  rewrite HReql in HLeql; injection HLeql; intros Heqbr Heqbl;
  rewrite Heqbl in HReql; clear HLeql Heqbr Heqbl;
  let Heql := fresh "Heql" in rename HReql into Heql;
  pose proof (properUp Hpro) as Hproup; rewrite Heql in Hproup;
  specialize_Forall_H Hproup;
  rename Hproup0 into HproL; rename Hproup1 into HproR;
  rewrite Heql in Hnocut;
  let Hexr := fresh "Hexr" in
  let Hwfr := fresh "Hwfr" in
  let Hprems := fresh "Hprems" in
  let Hexrup := fresh "Hexrup" in
  let Hwfrup := fresh "Hwfrup" in
  destruct Hpro as (Hexr, (Hwfr, Hprems)); rewrite allDT_Next in Hwfr, Hexr;
  destruct Hwfr as [Hwfr Hwfrup]; destruct Hexr as [Hexr Hexrup];
  rewrite Heql in Hexrup;
  simpl in Hwfr; rewrite Heqr, Heql in Hwfr;
  apply ruleInst_ruleSubst in Hwfr; destruct Hwfr as [pfs Hpfs];
  injection Hpfs; intros Heqs HeqY _ _ HeqX;
  rewrite <- HeqX, <- HeqY in Heqs; clear HeqY HeqX;
  rewrite Heqs; simpl;
  destruct Hexrup as [ [HrLin _] [ [HrRin _] _] ];
  unfold exr in HrLin, HrRin;
  unfold allNextDTs, allDTs in Hnocut;
  rewrite <- Forall_fold_right, Forall_forall in Hnocut; specialize_list;
  let HnocutL := fresh "HnocutL" in let HnocutR := fresh "HnocutR" in
  match goal with | H : allDT nocut (Der _ rL _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutL; clear H end;
  match goal with | H : allDT nocut (Der _ rR _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutR; clear H end;
  (* Consider all possible combinations of rules
     while removing those without formula variables at right places *)
  dec_destruct_List_In (@rule_eq_dec fml _) rL;
  let HeqrL := fresh "HeqrL" in
  match goal with
  | H : rL = _ |- _ =>
      rename H into HeqrL; rewrite HeqrL in *; simpl in HfmlrL;
      try (apply (False_rect _ HfmlrL))
  end;
  dec_destruct_List_In (@rule_eq_dec fml _) rR;
  let HeqrR := fresh "HeqrR" in
  match goal with
  | H : rR = _ |- _ =>
      rename H into HeqrR; rewrite HeqrR in *; simpl in HfmlrR;
      try (apply (False_rect _ HfmlrR))
  end;
  (* Remove incompatible rules *)
  pose proof (proper_root _ _ HproL) as HwfrL; destruct HwfrL as [_ HwfrL];
  apply ruleInst_ruleSubst in HwfrL; destruct HwfrL as [afsL HafsL];
  try (match type of HeqrL with rL = ?rho => unfold rho in HafsL end);
  unfold ruleSubst, seqSubst, strSubst in HafsL;
  try (rewrite fmlSubst_eq in HafsL); simpl in HafsL;
  let HeqAL := fresh "HeqAL" in let HeqX := fresh "HeqX" in
  let HeqlL := fresh "HeqlL" in let dL := fresh "dL" in
  injection HafsL; intros HeqAL HeqX HeqlL;
  destruct_list_easy lL dL; try (injection HeqlL; intros);
  pose proof (properUp HproL) as HprodL; simpl in HprodL; specialize_Forall_H HprodL;
  pose proof (proper_root _ _ HproR) as HwfrR; destruct HwfrR as [_ HwfrR];
  apply ruleInst_ruleSubst in HwfrR; destruct HwfrR as [afsR HafsR];
  try (match type of HeqrR with rR = ?rho => unfold rho in HafsR end);
  unfold ruleSubst, seqSubst, strSubst in HafsR;
  try (rewrite fmlSubst_eq in HafsR); simpl in HafsR;
  let HeqAR := fresh "HeqAR" in let HeqY := fresh "HeqY" in
  let HeqlR := fresh "HeqlR" in let dR := fresh "dR" in
  injection HafsR; intros HeqY HeqAR HeqlR;
  destruct_list_easy lR dR; try (injection HeqlR; intros);
  pose proof (properUp HproR) as HprodR; simpl in HprodR; specialize_Forall_H HprodR;
  (* Last details *)
  let HeqipsA := fresh "HeqipsA" in
  pose proof HeqAR as HeqipsA; rewrite HeqAL in HeqipsA;
  try discriminate; try injection HeqipsA; intros;
  move HnocutL at bottom; move HnocutR at bottom;
  specialize_list; try specialize_list.
*)

(*
Ltac init_C8 :=
  let A := fresh "A" in let dt := fresh "dt" in let Hval := fresh "Hval" in
  let Hcut := fresh "Hcut" in let Hnocut := fresh "Hnocut" in
  let HyL := fresh "HyL" in let HnL := fresh "HnL" in
  let HyR := fresh "HyR" in let HnR := fresh "HnR" in
  let HLP := fresh "HLP" in let HRP := fresh "HRP" in
  let Heqr := fresh "Heqr" in let Hneqr := fresh "Hneqr" in
  intros A dt Hval Hcut Hnocut; destruct Hcut as [HLP HRP];
  destruct dt as [|s r l]; try (contradict Hval; apply not_proper_Unf);
  destruct (rule_eq_dec r CUT) as [Heqr|Hneqr];
    try (exists (Der s r l); split; [assumption | split; try reflexivity];
    apply (allDT_impl (nocut_impl_cut _)); apply allDT_Next; tauto);
  destruct (LP_dec l A) as [HyL|HnL];
    try (exfalso; let H := fresh "H" in destruct HLP as [H|]; try contradiction;
        destruct H as (ant & r' & l' & br & H); specialize (HnL ant r' l' br); tauto);
  destruct (RP_dec l A) as [HyR|HnR];
    try (exfalso; let H := fresh "H" in destruct HRP as [H|]; try contradiction;
        destruct H as (suc & bl & r' & l' & H); specialize (HnR suc bl r' l'); tauto);
  destruct HyL as (X & rL & lL & br & HLeql & HfmlrL);
  destruct HyR as (Y & bl & rR & lR & HReql & HfmlrR);
  rewrite HReql in HLeql; injection HLeql; intros Heqbr Heqbl;
  rewrite Heqbl in HReql; clear HLeql Heqbr Heqbl;
  let Heql := fresh "Heql" in rename HReql into Heql;
  pose proof (properUp Hval) as Hvalup; rewrite Forall_forall, Heql in Hvalup;
  simpl in Hvalup; pose proof (Hvalup _ (or_introl eq_refl)) as HvalL;
  pose proof (Hvalup _ (or_intror (or_introl eq_refl))) as HvalR; clear Hvalup;
  rewrite Heql in Hnocut;
  let Hwfb := fresh "Hwfb" in
  let Hfrb := fresh "Hfrb" in
  let Hprems := fresh "Hprems" in
  let Hwfbup := fresh "Hwfbup" in
  let Hfrbup := fresh "Hfrbup" in
  destruct Hval as (Hwfb, (Hfrb, Hprems)); rewrite allDT_Next in Hwfb, Hfrb;
  destruct Hwfb as [Hwfb Hwfbup]; destruct Hfrb as [Hfrb Hfrbup];
  rewrite Heql in Hfrbup;
  simpl in Hwfb; rewrite Heqr, Heql in Hwfb;
  apply ruleInst_ruleSubst in Hwfb; destruct Hwfb as [pfs Hpfs];
  injection Hpfs; intros Heqs HeqY _ _ HeqX;
  rewrite <- HeqX, <- HeqY in Heqs; clear HeqY HeqX;
  rewrite Heqs; simpl;
  destruct Hfrbup as [ [HrLin _] [ [HrRin _] _] ];
  simpl in HrLin, HrRin;
  unfold allNextDTs, allDTs in Hnocut;
  rewrite <- Forall_fold_right, Forall_forall in Hnocut; specialize_list;
  let HnocutL := fresh "HnocutL" in let HnocutR := fresh "HnocutR" in
  match goal with | H : allDT nocut (Der _ rL _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutL; clear H end;
  match goal with | H : allDT nocut (Der _ rR _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutR; clear H end.

Ltac auto_C8 fml :=
  let A := fresh "A" in let dt := fresh "dt" in let Hval := fresh "Hval" in
  let Hcut := fresh "Hcut" in let Hnocut := fresh "Hnocut" in
  let HyL := fresh "HyL" in let HnL := fresh "HnL" in
  let HyR := fresh "HyR" in let HnR := fresh "HnR" in
  let HLP := fresh "HLP" in let HRP := fresh "HRP" in
  let Heqr := fresh "Heqr" in let Hneqr := fresh "Hneqr" in
  intros A dt Hval Hcut Hnocut; destruct Hcut as [HLP HRP];
  destruct dt as [|s r l]; try (contradict Hval; apply not_proper_Unf);
  destruct (rule_eq_dec r CUT) as [Heqr|Hneqr];
    try (exists (Der s r l); split; [assumption | split; try reflexivity];
    apply (allDT_impl (nocut_impl_cut _)); apply allDT_Next; tauto);
  destruct (LP_dec l A) as [HyL|HnL];
    try (exfalso; let H := fresh "H" in destruct HLP as [H|]; try contradiction;
        destruct H as (ant & r' & l' & br & H); specialize (HnL ant r' l' br); tauto);
  destruct (RP_dec l A) as [HyR|HnR];
    try (exfalso; let H := fresh "H" in destruct HRP as [H|]; try contradiction;
        destruct H as (suc & bl & r' & l' & H); specialize (HnR suc bl r' l'); tauto);
  destruct HyL as (X & rL & lL & br & HLeql & HfmlrL);
  destruct HyR as (Y & bl & rR & lR & HReql & HfmlrR);
  rewrite HReql in HLeql; injection HLeql; intros Heqbr Heqbl;
  rewrite Heqbl in HReql; clear HLeql Heqbr Heqbl;
  let Heql := fresh "Heql" in rename HReql into Heql;
  pose proof (properUp Hval) as Hvalup; rewrite Forall_forall, Heql in Hvalup;
  simpl in Hvalup; pose proof (Hvalup _ (or_introl eq_refl)) as HvalL;
  pose proof (Hvalup _ (or_intror (or_introl eq_refl))) as HvalR; clear Hvalup;
  rewrite Heql in Hnocut;
  let Hwfb := fresh "Hwfb" in
  let Hfrb := fresh "Hfrb" in
  let Hprems := fresh "Hprems" in
  let Hwfbup := fresh "Hwfbup" in
  let Hfrbup := fresh "Hfrbup" in
  destruct Hval as (Hwfb, (Hfrb, Hprems)); rewrite allDT_Next in Hwfb, Hfrb;
  destruct Hwfb as [Hwfb Hwfbup]; destruct Hfrb as [Hfrb Hfrbup];
  rewrite Heql in Hfrbup;
  simpl in Hwfb; rewrite Heqr, Heql in Hwfb;
  apply ruleInst_ruleSubst in Hwfb; destruct Hwfb as [pfs Hpfs];
  injection Hpfs; intros Heqs HeqY _ _ HeqX;
  rewrite <- HeqX, <- HeqY in Heqs; clear HeqY HeqX;
  rewrite Heqs; simpl;
  destruct Hfrbup as [ [HrLin _] [ [HrRin _] _] ];
  unfold exr in HrLin, HrRin;
  unfold allNextDTs, allDTs in Hnocut;
  rewrite <- Forall_fold_right, Forall_forall in Hnocut; specialize_list;
  let HnocutL := fresh "HnocutL" in let HnocutR := fresh "HnocutR" in
  match goal with | H : allDT nocut (Der _ rL _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutL; clear H end;
  match goal with | H : allDT nocut (Der _ rR _) |- _ =>
  pose proof (allDT_up_forall H) as HnocutR; clear H end;
  (* Consider all possible combinations of rules
       while removing those without formula variables at right places *)
  dec_destruct_List_In (@rule_eq_dec fml _) rL;
  match goal with | HeqrL : rL = _ |- _ =>
  rewrite HeqrL in *; simpl in HfmlrL; try (apply (False_rect _ HfmlrL)) end;
  dec_destruct_List_In (@rule_eq_dec fml _) rR;
  match goal with | HeqrR : rR = _ |- _ =>
  rewrite HeqrR in *; simpl in HfmlrR; try (apply (False_rect _ HfmlrR)) end;
  (* Remove incompatible rules *)
  destruct_proper_dertree HvalR; destruct_proper_dertree HvalL;
  try (rewrite_discriminate A);
  move HnocutL at bottom; move HnocutR at bottom;
  specialize_list; try specialize_list;
  (* clean up useless hypotheses *)
  repeat match goal with
    | H : exr _ _ |- _ => clear H
    | H : wfr _ |- _ => clear H
    | H : allNextDTs _ _ |- _ => clear H  
    | H : premsDT _ = _ |- _ => clear H
    | H : True |- _ => clear H
    | H : In _ _ |- _ => clear H
    | H : _ = CUT |- _ => clear H
    | H : _ = ruleSubst _ _ |- _ => clear H
    | H : cutIsLP _ _ |- _ => clear H
    | H : cutIsRP _ _ |- _ => clear H
  end;
  pose proof (proper_up_forall HvalL) as HvalL'; move HvalL' at bottom;
  pose proof (proper_up_forall HvalR) as HvalR'; move HvalR' at bottom;
  specialize_list; specialize_list;
    try (
    match reverse goal with
    | HA : A = _ |- _ =>
      match reverse goal with
      | HA' : A = _ |- _ =>
        rewrite HA in HA'; injection HA'; intros
      end
    end);
  try (match goal with | HeqrL : rL = _ |- _ => move HeqrL at bottom end);
  try (match goal with | HeqrR : rR = _ |- _ => move HeqrR at bottom end).
*)

Ltac Forall2_destruct_list_H l a HF2 :=
  pose proof (Forall2_length HF2) as Hlen;
  destruct_list_easy l a;
  specialize_Forall2_H HF2; clear Hlen.

Ltac Forall2_destruct_list l a :=
  let Hlen := fresh "Hlen" in
  match goal with
  | HF2 : Forall2 _ l _ |- _ => Forall2_destruct_list_H l a HF2
  | HF2 : Forall2 _ _ l |- _ => Forall2_destruct_list_H l a HF2
  end.

(*
Ltac prep_C8_case :=
  match goal with
  | |- C8_case _ _ _ _ ?fmls =>
      let fmls' := fresh "fmls" in let d := fresh "d" in
      set (fmls' := fmls); intros ld Hval Hconc Hcut; rewrite Forall_forall in Hval, Hcut;
      Forall2_destruct_list ld d; repeat specialize_list; repeat
      match goal with
      | H : allDT nocut _ |- _ => apply (allDT_impl (nocut_impl_cut fmls)) in H
      end
  end.
*)

Ltac prep_C8_case :=
  apply C8_case_alt_imp_C8_case;
  let Hders := fresh "Hders" in intro Hders;
  apply ForallT_deriv_cofseqs_iff in Hders;
  specialize_ForallT_H Hders.
