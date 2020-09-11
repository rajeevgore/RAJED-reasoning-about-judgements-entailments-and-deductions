Require Import Lia.

Require Import gen genT.
Require Import ddT dd_fc.
Require Import lntacsT.
Require Import lntT.
Require Import lntkt_exchT.
Require Import size.
Require Import merge.
Require Import structural_equivalence.
Require Import principal.
Require Import ind_lex.
Require Import List_lemmasT.
Require Import lnt_gen_initT.
Require Import lntb2LT.
Require Import lnt_weakeningT.
Require Import weakenedT.
Require Import lntbRT lntb1LT.
Require Import Lemma_Sixteen_setup.
Require Import lnt_contraction_mrT.
Require Import contractedT.
Require Import Lemma_Sixteen_SR_wb_fwd.
Require Import Lemma_Sixteen_SR_wb_bac.

Set Implicit Arguments.

Lemma Lemma_Sixteen_SR_wb : forall n m,
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SR_wb (S n, m).
Proof.
  intros n m IH.
  apply SR_wb_fwd_bac_rev.
  apply Lemma_Sixteen_SR_wb_fwd. assumption.
  apply Lemma_Sixteen_SR_wb_bac. assumption.
Defined.

Print Assumptions Lemma_Sixteen_SR_wb.