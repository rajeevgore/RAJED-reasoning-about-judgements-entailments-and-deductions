Add LoadPath "../general".
Require Import ssreflect.

Require Import gen genT.
Require Import ddT.
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
Require Import Lia.


Set Implicit Arguments.


Definition can_gen_cut {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns1 ns2 :=
  forall G1 G2 G3 seq1 seq2 (d : dir) Γ Δ1 Δ2 Σ1 Σ2 Π A,
    ns1 = G1 ++ [(seq1, d)] -> seq1 = pair Γ (Δ1++[A]++Δ2) ->
    ns2 = G2 ++ [(seq2, d)] -> seq2 = pair (Σ1++[A]++Σ2) Π ->
    merge G1 G2 G3 ->
    struct_equiv_str G1 G2 ->
    derrec rules (fun _ => False) (G3 ++ [(Γ++Σ1++Σ2, Δ1++Δ2++Π, d)]).

Definition can_gen_cut_simpl {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns1 ns2 :=
  forall G seq1 seq2 (d : dir) Γ1 Γ2 Δ1 Δ2 A,
    ns1 = G ++ [(seq1, d)] -> seq1 = pair Γ1 (Δ1++[A]) ->
    ns2 = G ++ [(seq2, d)] -> seq2 = pair (Γ2++[A]) Δ2 ->
    derrec rules (fun _ => False) (G ++ [(Γ1++Γ2, Δ1++Δ2, d)]).
