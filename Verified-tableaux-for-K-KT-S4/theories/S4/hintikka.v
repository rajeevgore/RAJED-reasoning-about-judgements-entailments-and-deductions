From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.

From S4sat Require Import data.

Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Arith.
Require Import Relations.
Require Import Program.
Require Import Lia.


Set Implicit Arguments.

(* Pre-Hintikka *)

Record pre_hintikka (G : list nnf) : Prop :=
{ htk_no_contra : forall [n], In (var n) G -> ~ In (neg n) G;
  htk_and       : forall [phi psi], In (and phi psi) G -> In phi G /\ In psi G;
  htk_or        : forall [phi psi], In (or phi psi) G -> In phi G \/ In psi G;
  htk_box       : forall [phi], In (box phi) G -> In phi G }.

Theorem pre_hintikka_and_htk {phi psi G} : In phi G -> In psi G -> pre_hintikka G ->
  pre_hintikka (and phi psi :: G).
Proof.
intros Hphi Hpsi phtkG. constructor.
- intros n Hvar Hneg. destruct Hvar as [Hvar|Hvar]; try discriminate.
  destruct Hneg as [Hneg|Hneg]; try discriminate.
  apply (htk_no_contra phtkG Hvar Hneg).
- intros xi1 xi2 Hin. destruct Hin as [Heq|Hin].
  + injection Heq. intros Heqpsi Heqphi.
    rewrite <- Heqphi, <- Heqpsi. split; right; assumption.
  + split; right; apply (htk_and phtkG Hin).
- intros xi1 xi2 Hin. destruct Hin as [|Hin]; try discriminate.
  destruct (htk_or phtkG Hin); [left|right]; now right.
- intros xi Hin. destruct Hin as [|Hin]; try discriminate.
  right. apply (htk_box phtkG Hin).
Qed.

Theorem pre_hintikka_or_left_htk {phi psi G} : In phi G -> pre_hintikka G ->
  pre_hintikka (or phi psi :: G).
Proof.
intros Hpsi phtkG. constructor.
- intros n Hvar Hneg. destruct Hvar as [Hvar | Hvar]; try discriminate.
  destruct Hneg as [Hneg | Hneg]; try discriminate.
  apply (htk_no_contra phtkG Hvar Hneg).
- intros xi1 xi2 Hin. destruct Hin as [|Hin]; try discriminate.
  split; right; apply (htk_and phtkG Hin).
- intros xi1 xi2 Hin. destruct Hin as [Heq|Hin].
  + injection Heq. intros Heqpsi Heqphi.
    rewrite <- Heqphi. left; right; assumption.
  + destruct (htk_or phtkG Hin); [left|right]; now right.
- intros xi Hin. destruct Hin as [Heq|Hin]; try discriminate.
  right. apply (htk_box phtkG Hin).
Qed.

Theorem pre_hintikka_or_right_htk {phi psi G} : In psi G -> pre_hintikka G ->
  pre_hintikka (or phi psi :: G).
Proof.
intros Hpsi phtkG. constructor.
- intros n Hvar Hneg. destruct Hvar as [Hvar | Hvar]; try discriminate.
  destruct Hneg as [Hneg | Hneg]; try discriminate.
  apply (htk_no_contra phtkG Hvar Hneg).
- intros xi1 xi2 Hin. destruct Hin as [|Hin]; try discriminate.
  split; right; apply (htk_and phtkG Hin).
- intros xi1 xi2 Hin. destruct Hin as [Heq|Hin].
  + injection Heq. intros Heqpsi Heqphi.
    rewrite <- Heqpsi. right; right; assumption.
  + destruct (htk_or phtkG Hin); [left|right]; now right.
- intros xi Hin. destruct Hin as [Heq|Hin]; try discriminate.
  right. apply (htk_box phtkG Hin).
Qed.

Theorem pre_hintikka_box_htk {phi G} : In phi G -> pre_hintikka G ->
  pre_hintikka (box phi :: G).
Proof.
intros Hphi phtkG. constructor.
- intros n Hvar Hneg. destruct Hvar as [Hvar|Hvar]; try discriminate.
  destruct Hneg as [Hneg|Hneg]; try discriminate.
  apply (htk_no_contra phtkG Hvar Hneg).
- intros xi1 xi2 Hin. destruct Hin as [|Hin]; try discriminate.
  split; right; apply (htk_and phtkG Hin).
- intros xi1 xi2 Hin. destruct Hin as [|Hin]; try discriminate.
  destruct (htk_or phtkG Hin); [left|right]; now right.
- intros xi Hin. destruct Hin as [Heq|Hin].
  + injection Heq. intro Heqphi. right. rewrite <- Heqphi. assumption.
  + right. apply (htk_box phtkG Hin).
Qed.

Theorem pre_hintikka_sc [s] (sc : state_conditions s) :
  pre_hintikka (s_G s).
Proof.
constructor; try (intros; contradict H; apply sc).
intros. apply sc. assumption.
Qed. 



Record graphm :=
{ gm_verts : Type;
  gm_edges : gm_verts -> gm_verts -> Prop;
  gm_refl  : reflexive _ gm_edges;
  gm_trans : transitive _ gm_edges;
  gm_htk   : gm_verts -> list nnf; }.

Record hintikka (g : graphm) :=
{ htk_prehin :> forall w, pre_hintikka (gm_htk g w);
  htk_reach_box : forall u v, gm_edges g u v ->
    forall phi, In (box phi) (gm_htk g u) -> In (box phi) (gm_htk g v);
  htk_reach_dia : forall u phi, In (dia phi) (gm_htk g u) ->
    exists v, gm_edges g u v /\ In phi (gm_htk g v); }.

Definition builder (g : graphm) : S4 :=
{|S4_kripke :=
  {|world := gm_verts g;
    rel   := gm_edges g;
    val   := fun w p => In (var p) (gm_htk g w);|};
  refl_rel  := gm_refl g;
  trans_rel := gm_trans g;|}.

Theorem hintikka_satisfied (g : graphm) : hintikka g ->
  forall w, satable_S4 (gm_htk g w).
Proof.
intro htkg.
assert (forall w, sat (builder g) w (gm_htk g w)) as Hsat.
{ intros w phi. revert w.
induction phi; intro w.
- simpl. tauto.
- simpl. intro H. intro H0. contradict H.
  apply (htk_no_contra (htkg w)). assumption.
- intro H. split; [apply IHphi1 | apply IHphi2];
  apply (htk_and (htkg w) H).
- intro H. destruct (htk_or (htkg w) H) as [H0|H0];
  [left; apply IHphi1 | right; apply IHphi2]; assumption.
- intro H. intros w' wRw'. apply IHphi.
  apply (htk_box (htkg w')).
  apply (htk_reach_box htkg _ _ wRw'). assumption.
- intro H. destruct (htk_reach_dia htkg _ _ H) as [w' [wRw' H0]].
  exists w'. split; try assumption. apply IHphi. assumption. }
intro w. exists (builder g), w. apply Hsat.
Qed.