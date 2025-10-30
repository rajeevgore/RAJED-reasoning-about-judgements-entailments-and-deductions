From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import ops.

From KTsat Require Import defs.
From KTsat Require Import size.

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Psatz.



Theorem le_of_unbox_degree : forall {G}, modal_degree (unbox G) <= modal_degree G.
Proof.
induction G as [|phi].
- simpl. apply le_n.
- destruct phi; try(simpl; eapply Nat.le_trans; [apply IHG|
  apply incl_le_list_max, incl_map, incl_tl, incl_refl]).
  simpl. repeat (rewrite cons_degree).
  apply Nat.max_lub.
  * eapply Nat.le_trans.
    2:{ apply Nat.le_max_l. }
    simpl. apply le_S. apply le_n.
  * eapply Nat.le_trans.
    2:{ apply Nat.le_max_r. }
    apply IHG.
Qed.

Theorem zero_degree_of_eq_unbox : forall {G},
  modal_degree (unbox G) = modal_degree G -> modal_degree G = 0.
Proof.
induction G as [|phi].
- unfold modal_degree. simpl. exact (fun h => h).
- destruct phi;
  simpl; repeat (rewrite cons_degree); simpl count_modal;
  destruct (Lt.le_lt_or_eq_stt _ _ (@le_of_unbox_degree G)); lia.
Qed.

Theorem unbox_degree_aux : forall {G phi}, In (dia phi) G ->
  modal_degree (unbox G) < modal_degree G.
Proof.
intros G phi.
induction G as [|psi].
- simpl. tauto.
- destruct psi; try (
  rewrite cons_degree; simpl; intro H; destruct H;
  (discriminate || (apply IHG; assumption) || (apply IHG in H; lia))).
  * simpl. repeat (rewrite cons_degree). simpl count_modal.
    intro H. destruct H; try discriminate. apply IHG in H. lia.
  * simpl. rewrite cons_degree. simpl count_modal.
    intro H. destruct H; try (apply IHG in H; lia).
    destruct (Lt.le_lt_or_eq_stt _ _ (@le_of_unbox_degree G)); try lia.
    pose proof (zero_degree_of_eq_unbox H0). lia.
Qed.

Theorem unbox_degree : forall {G phi}, In (dia phi) G ->
  modal_degree (phi :: unbox G) < modal_degree G.
Proof.
intros G phi.
intro H. rewrite cons_degree.
apply Nat.max_lub_lt.
- unfold lt.
  assert (S (count_modal phi) = count_modal (dia phi)) as H0; try auto.
  rewrite H0. apply le_of_mem_degree. assumption.
- apply (unbox_degree_aux H).
Qed.

Theorem undia_degree : forall {G phi}, In phi (undia G) ->
  modal_degree (phi :: unbox G) < modal_degree G.
Proof.
intros G phi H. apply undia_iff in H.
apply unbox_degree. assumption.
Qed.

Theorem undia_sublist {D G} : D <+ G -> undia D <+ undia G.
Proof.
intro H. induction H.
- constructor 1.
- destruct a; try (simpl; assumption).
  simpl. constructor 2. assumption.
- destruct a; try (simpl; assumption).
  simpl. constructor 3. assumption.
Qed.

Theorem undia_incl {D G} : incl D G -> incl (undia D) (undia G).
Proof.
induction D.
- unfold incl. simpl. tauto.
- destruct a; try (
  intro H; simpl; apply IHD; apply incl_cons_inv in H; tauto).
  intro H. simpl. apply incl_cons_inv in H.
  intro x. intro Hx. destruct Hx as [Hxl|Hxr].
  * rewrite <- Hxl. apply undia_iff. tauto.
  * apply IHD; tauto.
Qed.




Definition get_contra_seqt : forall G : seqt,
  {p | In (var p) (main G) /\ In (neg p) (main G)} +
  {forall n, In (var n) (main G) -> ~ In (neg n) (main G)} :=
fun G => get_contra (main G).

Definition get_and_seqt : forall G : seqt,
  {p : nnf*nnf | In (and (fst p) (snd p)) (main G)} +
  {forall phi psi, ~ In (and phi psi) (main G)} :=
fun G => get_and (main G).

Definition get_or_seqt : forall G : seqt,
  {p : nnf*nnf | In (or (fst p) (snd p)) (main G)} +
  {forall phi psi, ~ In (or phi psi) (main G)} :=
fun G => get_or (main G).

Definition get_dia_seqt : forall G : seqt,
  {p : nnf | In (dia p) (main G)} +
  {forall phi, ~ In (dia phi) (main G)} :=
fun G => get_dia (main G).

Definition get_box : forall G : list nnf,
  {p : nnf | In (box p) G} +
  {forall phi, ~ In (box phi) G}.
Proof.
induction G as [|xi G'].
- right. simpl. tauto.
- elim IHG'.
  * intro IHG'l. left. elim IHG'l. intros p' H. exists p'. simpl. right. exact H.
  * intro IHG'r. destruct xi;
    try (right; simpl; intros phi H; elim H; (discriminate || (apply IHG'r))).
    + left. exists xi. simpl. left. reflexivity.
Defined.

Definition get_box_seqt : forall G : seqt,
  {p : nnf | In (box p) (main G)} +
  {forall phi, ~ In (box phi) (main G)} :=
fun G => get_box (main G).