From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.
From Ksat Require Import full_language.

From S4sat Require Import closure.

Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Relations.
Require Import Program.
Require Import Lia.


Set Implicit Arguments.

Record S4 :=
{ S4_kripke :> kripke;
  refl_rel  : reflexive _ (rel S4_kripke);
  trans_rel : transitive _ (rel S4_kripke) }.

Definition fml_satable_S4 (G : list fml) : Prop :=
  exists (M : S4) w, fml_sat M w G.

Definition satable_S4 (G : list nnf) : Prop :=
  exists (M : S4) w, sat M w G.

Definition unsatable_S4 (G : list nnf) : Prop :=
  forall (M : S4) (w : world M), ~ sat M w G.

Record seqt : Type :=
{ s_G : list nnf;
  s_S : list nnf;
  s_H : list (nat * nnf);
  s_d : nat;
  s_c : bool;
  s_R : list nnf; }.

Definition box_only (G : list nnf) : Prop :=
  forall phi, In phi G -> exists psi, phi = box psi.

Lemma box_only_nil : box_only [].
Proof.
intros phi H. contradiction.
Qed.

Lemma cons_box_only : forall G phi, box_only G -> box_only (box phi :: G).
Proof.
intros G phi boG psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
- exists phi. apply eq_sym. assumption.
- apply boG. assumption.
Qed.

Record pseqt (s : seqt) : Prop :=
{ nodup_H         : NoDup (map snd (s_H s));
  nodup_S         : NoDup (s_S s);
  H_incl_R        : incl (map snd (s_H s)) (closure (s_R s));
  S_incl_R        : incl (s_S s) (closure (s_R s));
  G_incl_R        : incl (s_G s) (closure (s_R s));
  box_only_S      : box_only (s_S s);
  earlier_H       : forall h, In h (s_H s) -> 0 < fst h <= s_d s;
  S_incl_G        : s_c s = true -> incl (s_S s) (s_G s);
  same_depth_HinG : s_c s = true -> forall h, In h (s_H s) ->
    fst h = s_d s -> In (snd h) (s_G s) }.

Definition sseqt := {s | pseqt s}.

Record state_conditions (w : seqt) :=
{ sc_no_contra : forall n, In (var n) (s_G w) -> ~ In (neg n) (s_G w);
  sc_no_and    : forall phi psi, ~ In (and phi psi) (s_G w);
  sc_no_or     : forall phi psi, ~ In (or phi psi) (s_G w);
  sc_no_box    : forall phi, ~ In (box phi) (s_G w); }.


(* Computing lower sequents *)

Definition and_child (phi psi : nnf) (s : seqt) : seqt :=
{|
  s_G := phi :: psi :: remove_nnf (and phi psi) (s_G s);
  s_S := s_S s;
  s_H := s_H s;
  s_d := s_d s;
  s_c := false;
  s_R := s_R s;
|}.

Theorem and_child_pseqt [phi psi] [ss : sseqt]
  (Hin : In (and phi psi) (s_G (`ss))) : pseqt (and_child phi psi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *.
constructor; try ((destruct pse; assumption) || discriminate).
unfold and_child. simpl.
pose proof (G_incl_R pse _ Hin) as H. apply mem_closure_and in H.
intros xi Hxi.
destruct Hxi as [Hxi|[Hxi|Hxi]]; try (rewrite <- Hxi; tauto).
apply in_remove, proj1 in Hxi. apply (G_incl_R pse xi Hxi).
Qed.


Definition and_child_sseqt [phi psi] [ss : sseqt]
  (Hin : In (and phi psi) (s_G (`ss))) : sseqt :=
exist _ (and_child phi psi (`ss)) (and_child_pseqt Hin).


Definition or_child_left (phi psi : nnf) (s : seqt) : seqt :=
{|
  s_G := phi :: remove_nnf (or phi psi) (s_G s);
  s_S := s_S s;
  s_H := s_H s;
  s_d := s_d s;
  s_c := false;
  s_R := s_R s;
|}.

Definition or_child_right (phi psi : nnf) (s : seqt) : seqt :=
{|
  s_G := psi :: remove_nnf (or phi psi) (s_G s);
  s_S := s_S s;
  s_H := s_H s;
  s_d := s_d s;
  s_c := false;
  s_R := s_R s;
|}.

Theorem or_child_left_pseqt [phi psi] [ss : sseqt]
  (Hin : In (or phi psi) (s_G (`ss))) : pseqt (or_child_left phi psi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *.
constructor; try ((destruct pse; assumption) || discriminate).
unfold or_child_left. simpl.
pose proof (G_incl_R pse _ Hin) as H. apply mem_closure_or in H.
intros xi Hxi.
destruct Hxi as [Hxi|Hxi]; try (rewrite <- Hxi; tauto).
apply in_remove, proj1 in Hxi. apply (G_incl_R pse xi Hxi).
Qed.

Theorem or_child_right_pseqt [phi psi] [ss : sseqt]
(Hin : In (or phi psi) (s_G (`ss))) : pseqt (or_child_right phi psi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *.
constructor; try ((destruct pse; assumption) || discriminate).
unfold or_child_right. simpl.
pose proof (G_incl_R pse _ Hin) as H. apply mem_closure_or in H.
intros xi Hxi.
destruct Hxi as [Hxi|Hxi]; try (rewrite <- Hxi; tauto).
apply in_remove, proj1 in Hxi. apply (G_incl_R pse xi Hxi).
Qed.

Definition or_child_left_sseqt [phi psi] [ss : sseqt]
  (Hin : In (or phi psi) (s_G (`ss))) : sseqt :=
exist _ (or_child_left phi psi (`ss)) (or_child_left_pseqt Hin).

Definition or_child_right_sseqt [phi psi] [ss : sseqt]
  (Hin : In (or phi psi) (s_G (`ss))) : sseqt :=
exist _ (or_child_right phi psi (`ss)) (or_child_right_pseqt Hin).


Definition box_child_new (phi : nnf) (s : seqt) : seqt :=
{|
  s_G := phi :: remove_nnf (box phi) (s_G s);
  s_S := (box phi) :: s_S s;
  s_H := [];
  s_d := s_d s;
  s_c := false;
  s_R := s_R s;
|}.

Theorem box_child_new_pseqt [phi] [ss : sseqt]
  (Hin1 : In (box phi) (s_G (`ss))) (Hin2 : ~ In (box phi) (s_S (`ss))) :
  pseqt (box_child_new phi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin1, Hin2 |- *.
constructor; try discriminate.
- constructor.
- constructor; try assumption. apply (nodup_S pse).
- unfold box_child_new. simpl. apply incl_nil_l.
- unfold box_child_new. simpl. intros xi Hxi.
  destruct Hxi as [Hxi|Hxi].
  + rewrite <- Hxi. apply (G_incl_R pse). assumption.
  + apply (S_incl_R pse). assumption.
- unfold box_child_new. simpl. intros xi Hxi.
  destruct Hxi as [Hxi|Hxi].
  + rewrite <- Hxi. apply mem_closure_box.
    apply (G_incl_R pse). assumption.
  + apply (G_incl_R pse). apply in_remove, proj1 in Hxi. assumption.
- apply cons_box_only. apply (box_only_S pse).
- unfold box_child_new. simpl. tauto.
Qed.

Definition box_child_new_sseqt [phi] [ss : sseqt]
  (Hin1 : In (box phi) (s_G (`ss)))
  (Hin2 : ~ In (box phi) (s_S (`ss))) : sseqt :=
exist _ (box_child_new phi (`ss)) (box_child_new_pseqt Hin1 Hin2).


Definition box_child_dup (phi : nnf) (s : seqt) : seqt :=
{|
  s_G := phi :: remove_nnf (box phi) (s_G s);
  s_S := s_S s;
  s_H := s_H s;
  s_d := s_d s;
  s_c := false;
  s_R := s_R s;
|}.

Theorem box_child_dup_pseqt [phi] [ss : sseqt]
  (Hin1 : In (box phi) (s_G (`ss))) (Hin2 : In (box phi) (s_S (`ss))) :
  pseqt (box_child_dup phi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin1, Hin2 |- *.
constructor; try ((destruct pse; assumption) || discriminate).
unfold box_child_dup. simpl.
pose proof (G_incl_R pse _ Hin1) as H. apply mem_closure_box in H.
intros xi Hxi.
destruct Hxi as [Hxi|Hxi]; try (rewrite <- Hxi; tauto).
apply in_remove, proj1 in Hxi. apply (G_incl_R pse xi Hxi).
Qed.

Definition box_child_dup_sseqt [phi] [ss : sseqt]
  (Hin1 : In (box phi) (s_G (`ss))) (Hin2 : In (box phi) (s_S (`ss))) : sseqt :=
exist _ (box_child_dup phi (`ss)) (box_child_dup_pseqt Hin1 Hin2).


Definition dia_child (phi : nnf) (s : seqt) :=
{|
  s_G := phi :: s_S s;
  s_S := s_S s;
  s_H := (S (s_d s), phi) :: s_H s;
  s_d := S (s_d s);
  s_c := true;
  s_R := s_R s;
|}.

Definition unmodal_seqt (s : seqt) : list seqt :=
map
(fun phi => dia_child phi s)
(filter_undia (map snd (s_H s)) (s_G s)).

Theorem unmodal_pseqt (ss : sseqt) :
  forall i, In i (unmodal_seqt (`ss)) -> pseqt i.
Proof.
apply mapp. intros d Hd.
pose proof (mem_filter_dia_right_aux Hd) as HdG.
pose proof (mem_filter_dia_right Hd) as HdH.
destruct ss as [s pse]. simpl in *.
constructor; try (destruct pse; assumption).
- constructor; destruct pse; assumption.
- unfold dia_child. simpl. intros xi Hxi. destruct Hxi as [Hxi|Hxi].
  + apply mem_closure_dia. apply (G_incl_R pse).
    rewrite <- Hxi. assumption.
  + apply (H_incl_R pse). assumption.
- unfold dia_child. simpl. intros xi Hxi. destruct Hxi as [Hxi|Hxi].
  + apply mem_closure_dia. apply (G_incl_R pse).
    rewrite <- Hxi. assumption.
  + apply (S_incl_R pse). assumption.
- unfold dia_child. simpl. intros h Hh. destruct Hh as [Heq|Hin].
  + rewrite <- Heq. simpl. lia.
  + pose proof (earlier_H pse h Hin). lia.
- unfold dia_child. simpl. intros tt xi Hxi. clear tt. now right.
- unfold dia_child. simpl. intros tt h Hh Hfsth. clear tt.
  destruct Hh as [Heq|Hin].
  + left. rewrite <- Heq. simpl. reflexivity.
  + pose proof (earlier_H pse h Hin). lia.
Qed.


Inductive treem :=
| mcons : list treem -> seqt -> list (nat * nnf) -> list nnf -> treem.
