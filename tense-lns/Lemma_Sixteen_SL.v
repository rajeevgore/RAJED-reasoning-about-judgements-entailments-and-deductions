Add LoadPath "../general".
Require Import ssreflect.
Require Import Lia.

Require Import gen genT.
Require Import ddT.
Require Import dd_fc.
Require Import List_lemmasT.
Require Import lntT lntacsT lntlsT lntbRT lntmtacsT.
Require Import lntb1LT lntb2LT.
Require Import lntkt_exchT.
Require Import lnt_weakeningT.
Require Import lnt_contractionT.
Require Import existsT.
Require Import lnt_weakeningT lnt_contraction_mrT.
Require Import ind_lex.
Require Import contractedT weakenedT.
Require Import structural_equivalence.
Require Import merge.
Require Import lnt_gen_initT.
Require Import size principal.
Require Import cut_setup.
Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen_SR_wb.
Require Import Lemma_Sixteen_SR_bb.
Require Import Lemma_Sixteen_SR_p.


Set Implicit Arguments.


(* ---------------- *)
(* Lemma_Sixteen_SL *)
(* ---------------- *)

Lemma Lemma_Sixteen_SL : forall n m,
    SR_wb (S n, m) ->
    SR_bb (S n, m) ->
    SR_p (S n, m) ->
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SL (S n, m).
Admitted.
