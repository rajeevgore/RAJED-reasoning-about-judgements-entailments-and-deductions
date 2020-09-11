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

Set Implicit Arguments.


(* ------------------- *)
(* Lemma_Sixteen_SR_wb *)
(* ------------------- *)

Definition SR_wb_fwd_pre (n m : nat) := forall {V : Set} 
    G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH (A : PropF V)
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ1 ++ [WBox A] ++ Δ2,fwd)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ1 ++ [WBox A] ++ Σ2, Π, fwd)] ++ I))
  (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                               (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd)] ++
                           [([],[A],fwd)] )),
        principal_WBR D1 (WBox A) Γ Δ1 Δ2  ->
        ((dp D1) + (dp D2))%nat <= m ->
        struct_equiv_str G H ->
        merge G H GH ->
        fsize (WBox A) <= n ->
        derrec (@LNSKt_rules V) (fun _ => False)
                            (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd)] ++ I ).

Definition SR_wb_fwd (nm : nat * nat) :=
  let (n,m) := nm in SR_wb_fwd_pre n m.


Definition SR_wb_bac_pre (n m : nat) := forall {V : Set} 
    G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH (A : PropF V)
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ1 ++ [WBox A] ++ Δ2,bac)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ1 ++ [WBox A] ++ Σ2, Π, bac)] ++ I))
  (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac)] ++
                           [([],[A],fwd)] )),
        principal_WBR D1 (WBox A) Γ Δ1 Δ2 ->
        ((dp D1) + (dp D2))%nat <= m ->
        struct_equiv_str G H ->
        merge G H GH ->
        fsize (WBox A) <= n ->
        derrec (@LNSKt_rules V) (fun _ => False)
                              (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac)] ++ I ).

Definition SR_wb_bac (nm : nat * nat) :=
  let (n,m) := nm in SR_wb_bac_pre n m.

Definition SR_wb_pre (n m : nat) := forall {V : Set} 
    G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH (A : PropF V) d
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ1 ++ [WBox A] ++ Δ2,d)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ1 ++ [WBox A] ++ Σ2, Π, d)] ++ I))
  (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d)] ++
                           [([],[A],fwd)] )),
        principal_WBR D1 (WBox A) Γ Δ1 Δ2 ->
        ((dp D1) + (dp D2))%nat <= m ->
        struct_equiv_str G H ->
        merge G H GH ->
        fsize (WBox A) <= n ->
        derrec (@LNSKt_rules V) (fun _ => False)
                              (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d)] ++ I ).

Definition SR_wb (nm : nat * nat) :=
  let (n,m) := nm in SR_wb_pre n m.

Lemma SR_wb_fwd_bac : forall nm,
    SR_wb nm -> SR_wb_fwd nm * SR_wb_bac nm.
Proof.
  unfold SR_wb. unfold SR_wb_fwd. unfold SR_wb_bac.
  unfold SR_wb_pre. unfold SR_wb_fwd_pre. unfold SR_wb_bac_pre.
  intros [n m] H.
  split. intros until 0. eapply H.
  intros until 0. eapply H.
Qed.

Lemma SR_wb_fwd_bac_rev : forall nm,
    SR_wb_fwd nm -> SR_wb_bac nm -> SR_wb nm.
Proof.
  unfold SR_wb. unfold SR_wb_fwd. unfold SR_wb_bac.
  unfold SR_wb_pre. unfold SR_wb_fwd_pre. unfold SR_wb_bac_pre.
  intros [n m] H1 H2.
  intros until 0. destruct d. apply H1. apply H2.
Qed.

Ltac get_SR_wb_from_IH IH HSR n m :=   
  assert (SR_wb (n,m)) as HSR;
  [apply IH;
   econstructor 2; try reflexivity;
   lia | ].

Ltac get_SR_wb_fwd_pre_from_IH IH HSR n m :=  
  assert (SR_wb_fwd_pre n m) as HSR;
  fold (SR_wb_fwd ( n, m)); [
  apply SR_wb_fwd_bac;
  apply IH; econstructor 2; try reflexivity; lia | ].

Ltac get_SR_wb_bac_pre_from_IH IH HSR n m :=  
  assert (SR_wb_bac_pre n m) as HSR;
  fold (SR_wb_bac ( n, m)); [
  apply SR_wb_fwd_bac;
  apply IH; econstructor 2; try reflexivity; lia | ].

Ltac split_L16_IH IH :=
  pose proof (want_prod_under_universal4 _ _ _ _ _ IH) as IH_split;
  destruct IH_split as [[[HSR_wb HSR_bb] HSR_p] HSL];
  pose proof (prod_nat_split _ HSR_wb) as HSR_wb'; simpl in HSR_wb';
  clear HSR_wb; rename HSR_wb' into HSR_wb;
  pose proof (prod_nat_split _ HSR_bb) as HSR_bb'; simpl in HSR_bb';
  clear HSR_bb; rename HSR_bb' into HSR_bb;
  pose proof (prod_nat_split _ HSR_p) as HSR_p'; simpl in HSR_p';
  clear HSR_p; rename HSR_p' into HSR_p;
  pose proof (prod_nat_split _ HSL) as HSL'; simpl in HSL';
  clear HSL; rename HSL' into HSL.

Lemma SR_wb_pre_fwd_rev_forall : forall n m,
  (forall n0 m0 : nat, (n0, m0) << (n, m) -> SR_wb_pre n0 m0) ->
  ((forall n0 m0 : nat, (n0, m0) << (n, m) -> SR_wb_fwd_pre n0 m0) *
  (forall n0 m0 : nat, (n0, m0) << (n, m) -> SR_wb_bac_pre n0 m0)).
Proof.
  intros n m H; split;
  intros a b Hab; pose proof SR_wb_fwd_bac as Hass.
  fold (SR_wb_fwd (a,b)).
  eapply Hass. apply H. assumption.
  fold (SR_wb_bac (a,b)).
  eapply Hass. apply H. assumption.
Qed.


(* ------------------- *)
(* Lemma_Sixteen_SR_bb *)
(* ------------------- *)

Definition SR_bb_fwd_pre (n m : nat) := forall {V : Set} 
    G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH (A : PropF V)
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ1 ++ [BBox A] ++ Δ2,fwd)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ1 ++ [BBox A] ++ Σ2, Π, fwd)] ++ I))
  (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                               (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd)] ++
                           [([],[A],bac)] )),
        principal_BBR D1 (BBox A) Γ Δ1 Δ2  ->
        ((dp D1) + (dp D2))%nat <= m ->
        struct_equiv_str G H ->
        merge G H GH ->
        fsize (BBox A) <= n ->
        derrec (@LNSKt_rules V) (fun _ => False)
                            (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd)] ++ I ).

Definition SR_bb_fwd (nm : nat * nat) :=
  let (n,m) := nm in SR_bb_fwd_pre n m.

Definition SR_bb_bac_pre (n m : nat) := forall {V : Set} 
    G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH (A : PropF V)
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ1 ++ [BBox A] ++ Δ2,bac)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ1 ++ [BBox A] ++ Σ2, Π, bac)] ++ I))
  (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac)] ++
                           [([],[A],bac)] )),
        principal_BBR D1 (BBox A) Γ Δ1 Δ2 ->
        ((dp D1) + (dp D2))%nat <= m ->
        struct_equiv_str G H ->
        merge G H GH ->
        fsize (BBox A) <= n ->
        derrec (@LNSKt_rules V) (fun _ => False)
                              (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac)] ++ I ).

Definition SR_bb_bac (nm : nat * nat) :=
  let (n,m) := nm in SR_bb_bac_pre n m.


Definition SR_bb_pre (n m : nat) := forall {V : Set} 
    G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH (A : PropF V) d
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ1 ++ [BBox A] ++ Δ2,d)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ1 ++ [BBox A] ++ Σ2, Π, d)] ++ I))
  (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d)] ++
                           [([],[A],bac)] )),
        principal_BBR D1 (BBox A) Γ Δ1 Δ2 ->
        ((dp D1) + (dp D2))%nat <= m ->
        struct_equiv_str G H ->
        merge G H GH ->
        fsize (BBox A) <= n ->
        derrec (@LNSKt_rules V) (fun _ => False)
                              (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d)] ++ I ).

Definition SR_bb (nm : nat * nat) :=
  let (n,m) := nm in SR_bb_pre n m.

Lemma SR_bb_fwd_bac : forall nm,
    SR_bb nm -> SR_bb_fwd nm * SR_bb_bac nm.
Proof.
  unfold SR_bb. unfold SR_bb_fwd. unfold SR_bb_bac.
  unfold SR_bb_pre. unfold SR_bb_fwd_pre. unfold SR_bb_bac_pre.
  intros [n m] H.
  split. intros until 0. eapply H.
  intros until 0. eapply H.
Qed.

Lemma SR_bb_fwd_bac_rev : forall nm,
    SR_bb_fwd nm -> SR_bb_bac nm -> SR_bb nm.
Proof.
  unfold SR_bb. unfold SR_bb_fwd. unfold SR_bb_bac.
  unfold SR_bb_pre. unfold SR_bb_fwd_pre. unfold SR_bb_bac_pre.
  intros [n m] H1 H2.
  intros until 0. destruct d. apply H1. apply H2.
Qed.

Ltac get_SR_bb_from_IH IH HSR n m :=   
  assert (SR_bb (n,m)) as HSR;
  [apply IH;
   econstructor 2; try reflexivity;
   lia | ].

Ltac get_SR_bb_fwd_pre_from_IH IH HSR n m :=  
  assert (SR_bb_fwd_pre n m) as HSR;
  fold (SR_bb_fwd ( n, m)); [
  apply SR_bb_fwd_bac;
  apply IH; econstructor 2; try reflexivity; lia | ].

Ltac get_SR_bb_bac_pre_from_IH IH HSR n m :=  
  assert (SR_bb_bac_pre n m) as HSR;
  fold (SR_bb_bac ( n, m)); [
  apply SR_bb_fwd_bac;
  apply IH; econstructor 2; try reflexivity; lia | ].

Lemma SR_bb_pre_fwd_rev_forall : forall n m,
  (forall n0 m0 : nat, (n0, m0) << (n, m) -> SR_bb_pre n0 m0) ->
  ((forall n0 m0 : nat, (n0, m0) << (n, m) -> SR_bb_fwd_pre n0 m0) *
  (forall n0 m0 : nat, (n0, m0) << (n, m) -> SR_bb_bac_pre n0 m0)).
Proof.
  intros n m H; split;
  intros a b Hab; pose proof SR_bb_fwd_bac as Hass.
  fold (SR_bb_fwd (a,b)).
  eapply Hass. apply H. assumption.
  fold (SR_bb_bac (a,b)).
  eapply Hass. apply H. assumption.
Qed.


(* ------------------ *)
(* Lemma_Sixteen_SR_p *)
(* ------------------ *)

Definition SR_p_pre (n m : nat) := forall {V : Set} 
    G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH (A : PropF V) d 
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ1 ++ [A] ++ Δ2,d)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ1 ++ [A] ++ Σ2, Π, d)] ++ I)),
        principal_not_box_R D1 A Γ Δ1 Δ2 ->
        ((dp D1) + (dp D2))%nat <= m ->
        fsize A <= n ->
        not_box A ->
        struct_equiv_str G H ->
        merge G H GH ->
        derrec (@LNSKt_rules V) (fun _ => False)
                              (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d)] ++ I ).

Definition SR_p (nm : nat * nat) :=
  let (n,m) := nm in SR_p_pre n m.


(* ---------------- *)
(* Lemma_Sixteen_SL *)
(* ---------------- *)

Definition SL_pre (n m : nat) := forall {V : Set} 
    G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH (A : PropF V) d 
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ1 ++ [A] ++ Δ2,d)] ++ I))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ1 ++ [A] ++ Σ2, Π, d)])),
        ((dp D1) + (dp D2))%nat <= m ->
        fsize A <= n ->
        struct_equiv_str G H ->
        merge G H GH ->
        derrec (@LNSKt_rules V) (fun _ => False)
                              (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d)] ++ I ).


Definition SL (nm : nat * nat) :=
  let (n,m) := nm in SL_pre n m.


Ltac get_SL_pre_from_IH2 IH HSL n m :=  
  assert (SL_pre n m) as HSL; [
  fold (SL ( n, m));
  apply IH; econstructor 2; try reflexivity; lia | ].

Ltac get_SL_pre_from_IH1 IH HSL n m :=
  assert (HSL : SL_pre n m);
  [ fold (SL (n, m)); apply IH; econstructor 1; try reflexivity; lia |  ].



