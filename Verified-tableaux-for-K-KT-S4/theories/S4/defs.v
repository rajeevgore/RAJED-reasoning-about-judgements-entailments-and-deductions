From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.

From S4sat Require Import data.
From S4sat Require Import hintikka.

Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Arith.
Require Import Relations.
Require Import Program.
Require Import Lia.


Set Implicit Arguments.

Definition tm_children (x : treem) :=
match x with
| mcons l se req htk => l
end.

Definition tm_se (x : treem) :=
match x with
| mcons l se req htk => se
end.

Definition tm_req (x : treem) :=
match x with
| mcons l se req htk => req
end.

Definition tm_htk (x : treem) :=
match x with
| mcons l se req htk => htk
end.

Definition tm_G (x : treem) := s_G (tm_se x).

Definition tm_S (x : treem) := s_S (tm_se x).

Definition tm_H (x : treem) := s_H (tm_se x).

Definition tm_c (x : treem) := s_c (tm_se x).

Definition tm_d (x : treem) := s_d (tm_se x).

Definition is_child (x y : treem) : Prop := In x (tm_children y).

Definition desc : treem -> treem -> Prop := clos_trans _ is_child.

Definition desceq (x y : treem) : Prop := desc x y \/ x = y.

Theorem desc_not_nil [c se req htk] : ~ desc c (mcons [] se req htk).
Proof.
intro H. remember (mcons [] se req htk) as d. induction H.
- rewrite Heqd in H. contradiction.
- contradiction.
Qed.

Theorem desc_iff_eq_child_aux_imp : forall l1 l2 s1 s2 r1 r2 h1 h2 x1 x2 y,
  x1 = mcons l1 s1 r1 h1 -> x2 = mcons l2 s2 r2 h2 -> l1 = l2 ->
  (desc y x1 -> desc y x2).
Proof.
intros l1 l2 s1 s2 r1 r2 h1 h2 x1 x2 y Heq1 Heq2 Heq.
intro H. induction H.
- rewrite Heq1 in H. simpl in H.
  constructor 1. rewrite Heq2. rewrite <- Heq.
  simpl. assumption.
- constructor 2 with y; try assumption.
  apply IHclos_trans2. assumption.
Qed.

Theorem desc_iff_eq_child_aux : forall [l1 l2 s1 s2 r1 r2 h1 h2 x1 x2 y],
  x1 = mcons l1 s1 r1 h1 -> x2 = mcons l2 s2 r2 h2 -> l1 = l2 ->
  (desc y x1 <-> desc y x2).
Proof.
intros l1 l2 s1 s2 r1 r2 h1 h2 x1 x2 y Heq1 Heq2 Heq.
split.
- apply (desc_iff_eq_child_aux_imp Heq1 Heq2 Heq).
- apply (desc_iff_eq_child_aux_imp Heq2 Heq1 (eq_sym Heq)).
Qed.

Lemma imp_desc_of_eq_children [x y] :
  tm_children x = tm_children y -> forall z, desc z x -> desc z y.
Proof.
intros Heqch z zltx. induction zltx.
- left. unfold is_child. rewrite <- Heqch. assumption.
- right with y0; try assumption. apply IHzltx2. assumption.
Qed.

Theorem eq_desc_of_eq_children [x y] :
  tm_children x = tm_children y -> forall z, desc z x <-> desc z y.
Proof.
intros Heqch z. split;
apply imp_desc_of_eq_children; rewrite Heqch; reflexivity.
Qed.



Record ptreem (x : treem) : Prop :=
{ ptpseq    : pseqt (tm_se x);
  ptGinhtk  : incl (tm_G x) (tm_htk x);
  ptphhtk   : pre_hintikka (tm_htk x);
  ptmsboxS  : forall y, is_child y x -> incl (tm_S x) (tm_htk y);
  ptmsbox   : forall y, is_child y x ->
    forall phi, In (box phi) (tm_htk x) -> In (box phi) (tm_htk y);
  ptmdia    : forall phi, In (dia phi) (tm_htk x) ->
    (exists y, is_child y x /\ In phi (tm_htk y)) \/
    (exists rq, In rq (tm_req x) /\ (snd rq) = phi);
  ptdcomH   : forall y, desc y x -> forall h, In h (tm_H y) ->
    fst h <= tm_d x -> In h (tm_H x);
  ptreqH    : incl (tm_req x) (tm_H x);
  ptdcomS   : forall y, desc y x ->
    (exists rq, In rq (tm_req y) /\ fst rq <= tm_d x) -> tm_S x = tm_S y;
  ptboxhtkS : ~ tm_req x = [] ->
    forall phi, In (box phi) (tm_htk x) -> In (box phi) (tm_S x);
  ptfulfill : forall z, desc z x -> forall n, tm_d x < n < tm_d z ->
    exists y, desc z y /\ desc y x /\ n = tm_d y;
  ptadtran  : forall y, desc y x -> tm_c y = true; }.

Definition gptreem (x : treem) := forall y, desc y x -> ptreem y.

Lemma desceq_ptreem :
  forall x y, ptreem x -> gptreem x -> desceq y x -> ptreem y.
Proof.
intros x y px gpx ylex. destruct ylex as [yltx|yeqx].
- apply gpx. assumption.
- rewrite yeqx. assumption.
Qed.

(* Definition dtreem (rt : treem) := {x : treem | desceq x rt}. *)

Record tableau_treem :=
{ tt_root   : treem;
  tt_proot  : ptreem tt_root;
  tt_gproot : gptreem tt_root;
  tt_depth0 : tm_d tt_root = 0; }.

Section BuildHintikka.

  Variable tt : tableau_treem.

  Definition dtreem := {x : treem | desceq x (tt_root tt)}.

  Inductive reach_step : dtreem -> dtreem -> Prop :=
  | fwd_reach (x y : dtreem) : is_child (`y) (`x) -> reach_step x y
  | bwd_reach (x y : dtreem) : desc (`x) (`y) ->
      (exists rq, In rq (tm_req (`x)) /\ fst rq = tm_d (`y)) ->
      reach_step x y.

  Definition reach := clos_refl_trans _ reach_step.

  Definition tt_graphm : graphm :=
  {|gm_verts := dtreem;
    gm_edges := reach;
    gm_refl  := preord_refl _ _ (clos_rt_is_preorder _ reach_step);
    gm_trans := preord_trans _ _ (clos_rt_is_preorder _ reach_step);
    gm_htk   := fun x => tm_htk (`x);|}.

  Lemma tt_desceq_ptreem : forall x, desceq x (tt_root tt) -> ptreem x.
  Proof.
  intro x.
  apply (desceq_ptreem (tt_proot tt) (tt_gproot tt)).
  Qed.

  Lemma child_dtreem_desceq : forall (x : dtreem) yt,
    is_child yt (`x) -> desceq yt (tt_root tt).
  Proof.
  intros x yt ychx. left. destruct (proj2_sig x) as [xltrt|xeqrt].
  - right with (`x); try assumption. left. assumption.
  - left. rewrite <- xeqrt. assumption.
  Qed.

  Theorem hintikka_tt_graphm : hintikka tt_graphm.
  Proof.
  constructor.
  - intro x. destruct x as [x xlert]. simpl.
    pose proof (tt_desceq_ptreem xlert) as px.
    apply (ptphhtk px).
  - simpl. intros x y xRy.
    apply clos_rt_rt1n in xRy. induction xRy; try tauto.
    pose proof (tt_desceq_ptreem (proj2_sig x)) as px.
    pose proof (tt_desceq_ptreem (proj2_sig y)) as py.
    intros phi Hin. apply IHxRy. inversion H.
    + apply (ptmsbox px); assumption.
    + clear H2 H3 x0 y0.
      destruct H1 as [rq [Hrq Hrq0]].
      assert (tm_c (`y) = true) as H1.
      { apply (ptadtran (tt_proot tt)).
      destruct (proj2_sig y) as [Heqy|]; try assumption.
      destruct (earlier_H (ptpseq px) rq) as [frqge0 _].
      { apply (ptreqH px). assumption. }
      rewrite Hrq0, H1, tt_depth0 in frqge0. lia. }
      apply (ptGinhtk py). apply (S_incl_G (ptpseq py) H1).
      fold (tm_S (`y)). rewrite (ptdcomS py H0).
      2:{ exists rq. split; try assumption. lia. }
      apply (ptboxhtkS px); try assumption.
      intro Hctr. fold (In rq []). rewrite <- Hctr. assumption.
  - simpl. intros x phi Hin.
    pose proof (tt_desceq_ptreem (proj2_sig x)) as px.
    destruct (ptmdia px phi Hin) as [nbl|bl].
    + destruct nbl as [yt [ychx H]].
      set (y := exist _ yt (child_dtreem_desceq _ _ ychx) : dtreem).
      exists y. split; try assumption. constructor 1. left. assumption.
    + destruct bl as [rq [Hrq Hrq0]].
      pose proof (ptreqH px _ Hrq) as HrqH.
      pose proof (earlier_H (ptpseq px) _ HrqH) as Hfrq.
      fold (tm_d (`x)) in Hfrq.
      destruct (proj2_sig x) as [xltrt|xeqrt].
      2:{ rewrite xeqrt, tt_depth0 in Hfrq. lia. }
      destruct Hfrq as [Hgt0 Hle]. rewrite Nat.le_lteq in Hle.
      rewrite <- Hrq0. destruct Hle as [Hlt|Heq].
      * pose proof (ptfulfill (tt_proot tt) xltrt) as Hful.
        rewrite (tt_depth0 tt) in Hful.
        specialize (Hful (fst rq) (conj Hgt0 Hlt)).
        destruct Hful as [zt [H1 [H2 H3]]].
        pose proof ((tt_gproot tt) _ H2) as pz.
        set (z := exist _ zt (or_introl H2) : dtreem).
        exists z. split.
       -- constructor 1. right; try assumption.
          exists rq. split; assumption.
       -- apply (ptGinhtk pz).
          apply (same_depth_HinG (ptpseq pz)).
         ++ apply (ptadtran (tt_proot tt) H2).
         ++ apply (ptdcomH pz H1); try assumption. lia.
         ++ assumption.
      * exists x. split; try constructor 2.
        apply (ptGinhtk px).
        apply (same_depth_HinG (ptpseq px)).
       -- apply (ptadtran (tt_proot tt)). assumption.
       -- assumption.
       -- assumption.
  Qed.

  Lemma satable_S4_subset : forall G1 G2, incl G1 G2 ->
    satable_S4 G2 -> satable_S4 G1.
  Proof.
  intros G1 G2 H [M [w Hsat]]. exists M, w.
  eapply sat_subset; [apply H | apply Hsat].
  Qed.

  Theorem model_existence : satable_S4 (tm_G (tt_root tt)).
  Proof.
  apply satable_S4_subset with
  (gm_htk tt_graphm (exist _ (tt_root tt) (or_intror eq_refl))).
  2:{ apply hintikka_satisfied. apply hintikka_tt_graphm. }
  simpl. apply (ptGinhtk (tt_proot tt)).
  Qed.

End BuildHintikka.
