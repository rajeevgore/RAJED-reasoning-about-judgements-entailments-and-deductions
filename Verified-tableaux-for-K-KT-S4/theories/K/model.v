From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import ops.
From Ksat Require Import semantics.

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.



Class val_constructible (Gamma : list nnf) `{sa : saturated Gamma} :=
{ vc_no_contra : forall {n}, In (var n) Gamma -> ~ In (neg n) Gamma;
  vc_atoms : list string;
  vc_hypatoms : forall {n}, In (var n) Gamma <-> In n vc_atoms}.

Class modal_applicable (Gamma : list nnf) `{vc : val_constructible Gamma} :=
{ ma_dia : nnf;
  ma_dia_ex : In (dia ma_dia) Gamma}.

Class model_constructible (Gamma : list nnf) `{vc : val_constructible Gamma} :=
{ mc_no_dia : forall phi, ~ In (dia phi) Gamma }.





Theorem unsat_of_unsat_unmodal {G : list nnf} `(h : modal_applicable G)
  (i : list nnf) : In i (unmodal G) /\ unsatable i -> unsatable G.
Proof.
intro H. elim H. intros Hl Hr. intros M w. intro Hsat.
pose proof (unmodal_sat_of_sat G i Hl M w G
(fun x hx => hx) (fun x hx => hx) Hsat) as H0.
elim H0. intro t. apply Hr.
Qed.



Inductive model : Set :=
| mcons : list string -> list model -> model.

Definition mval (m:model) (p:string) : Prop :=
match m with mcons v r => In p v end.

Definition mrel (m1 m2 : model) : Prop :=
match m1 with mcons v r => In m2 r end.

Theorem mem_of_mrel_tt : forall {v r m}, mrel (mcons v r) m -> In m r.
Proof.
  intros v r m h. simpl in h. assumption.
Qed.

Definition builder : kripke :=
{|world := model;
  val   := fun w n => mval w n;
  rel   := fun s1 s2 => mrel s1 s2|}.

Inductive batch_sat : list model -> list (list nnf) -> Prop :=
  | bs_nil : batch_sat [] []
  | bs_cons {m G l1 l2} : sat builder m G -> batch_sat l1 l2 ->
                    batch_sat (m::l1) (G::l2).

Theorem bs_ex : forall l G, batch_sat l G -> forall m, In m l ->
  exists i, In i G /\ sat builder m i.
Proof.
intros l G H. induction H.
- simpl. tauto.
- intros n Hn. simpl in Hn. destruct Hn.
  * exists G. split.
    + simpl. tauto.
    + rewrite <- H1. assumption.
  * pose proof (IHbatch_sat n H1) as H2. destruct H2 as [l].
    exists l. simpl. tauto.
Qed.

Theorem bs_forall : forall l G,
  batch_sat l G -> forall i, In i G -> exists m, In m l /\ sat builder m i.
Proof.
intros l G H. induction H.
- simpl. tauto.
- intros i Hi. destruct Hi.
  * exists m. simpl. rewrite <- H1. tauto.
  * pose proof (IHbatch_sat i H1) as H2.
    destruct H2 as [n]. exists n. simpl. tauto.
Qed.

Theorem sat_of_batch_sat : forall l G `(h : modal_applicable G),
  batch_sat l (unmodal G) -> sat builder (mcons vc_atoms l) G.
Proof.
intros l G sa vc H Hbs phi Hphi.
destruct phi.
- simpl. apply vc_hypatoms. assumption.
- simpl. intro H0. apply vc_hypatoms in H0.
  contradict Hphi. apply vc_no_contra. assumption.
- contradict Hphi. apply sa_no_and.
- contradict Hphi. apply sa_no_or.
- simpl. intros w' Hs'.
  pose proof (bs_ex l (unmodal G) Hbs w' Hs') as H0.
  destruct H0 as [i]. destruct H0.
  pose proof (unmodal_mem_box G i H0 phi Hphi) as H2.
  apply (H1 phi H2).
- simpl. apply undia_iff in Hphi.
  pose proof (mem_unmodal G phi Hphi) as H0.
  apply (bs_forall l (unmodal G) Hbs (phi :: unbox G)) in H0.
  destruct H0 as [t]. destruct H0. exists t. split; try assumption.
  apply (H1 phi). simpl. tauto.
Qed.

Theorem build_model : forall G `(h : model_constructible G),
  sat builder (mcons vc_atoms []) G.
Proof.
intros G sa vc mc phi Hphi.
destruct phi.
- simpl. apply vc_hypatoms. assumption.
- simpl. intro H. apply vc_hypatoms in H. contradict Hphi.
  apply (vc_no_contra H).
- contradict Hphi. apply sa_no_and.
- contradict Hphi. apply sa_no_or.
- simpl. tauto.
- contradict Hphi. apply mc_no_dia.
Qed.