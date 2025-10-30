From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.

Require Import List.
Import ListNotations.
Require Import Relations.
Require Import String.
Open Scope string_scope.


Record KT :=
{ KT_kripke :> kripke;
  refl_rel  :  reflexive _ (rel KT_kripke) }.

Definition inhabited_KT : KT :=
{|KT_kripke :=
    {|world := nat;
      val := fun a b => True;
      rel := fun a b => True|};
  refl_rel := fun a => I|}.

Definition unsatable_KT (G : list nnf) : Prop :=
  forall (M : KT) (w : world M), ~ sat M w G.

Inductive model : Set :=
| mcons : list string -> list model -> model.

Definition mval (m:model) (p:string) : Prop :=
match m with mcons v r => In p v end.

Definition mrel (m1 m2 : model) : Prop :=
match m1 with mcons v r => In m2 r \/ m1 = m2 end.

Theorem refl_mrel : reflexive _ mrel.
Proof.
intro w. destruct w. simpl. right. reflexivity.
Qed.

Theorem mem_of_mrel_tt : forall {v r m}, mrel (mcons v r) m -> In m r \/ mcons v r = m.
Proof.
intros v r m h. simpl in h. assumption.
Qed.

Theorem mem_of_mrel_empty : forall {v m}, mrel (mcons v []) m -> mcons v [] = m.
Proof.
intros v m H. simpl in H.
destruct H; (contradiction || assumption).
Qed.

Definition builder : KT :=
{|KT_kripke :=
    {|world := model;
      val   := fun w p => mval w p;
      rel   := fun x y => mrel x y|};
  refl_rel  := refl_mrel|}.

Theorem force_box_of_leaf {v phi} :
  force builder (mcons v []) phi -> force builder (mcons v []) (box phi).
Proof.
intro H. simpl. intro t.
intro H0. destruct H0; try contradiction.
rewrite H0 in H. assumption.
Qed.

Definition srefl (m h : list nnf) :=
  forall v l phi, sat builder (mcons v l) m -> In (box phi) h ->
  (forall psi, In (box psi) h -> forall w, In w l -> force builder w psi) ->
  force builder (mcons v l) phi.

Record seqt :=
{ main  : list nnf;
  hdld  : list nnf;
  pmain : srefl main hdld;
  phdld : box_only hdld }.

Class val_constructible (G : seqt) `{sa : saturated G.(main)} :=
{ vc_no_box : forall {phi}, ~ In (box phi) G.(main);
  vc_no_contra : forall {n}, In (var n) G.(main) -> ~ In (neg n) G.(main);
  vc_atoms : list string;
  vc_hypatoms : forall {n}, In (var n) G.(main) <-> In n vc_atoms}.

Class modal_applicable (G : seqt) `{vc : val_constructible G} :=
{ ma_dia : nnf;
  ma_dia_ex : In (dia ma_dia) G.(main)}.

Class model_constructible (G : seqt) `{vc : val_constructible G} :=
{ mc_no_dia : forall phi, ~ In (dia phi) G.(main) }.

Theorem build_model : forall G `(h : model_constructible G),
  sat builder (mcons vc_atoms []) G.(main).
Proof.
intros G sa vc mc phi Hphi.
destruct phi.
- simpl. apply vc_hypatoms. assumption.
- simpl. intro H. apply vc_hypatoms in H. contradict Hphi. apply (vc_no_contra H).
- contradict Hphi. apply sa_no_and.
- contradict Hphi. apply sa_no_or.
- contradict Hphi. apply vc_no_box.
- contradict Hphi. apply mc_no_dia.
Qed.



Definition and_child {phi psi} (G : seqt) (h : In (and phi psi) G.(main)) : seqt.
refine (
{|main  := phi :: psi :: remove_nnf (and phi psi) G.(main);
  hdld  := G.(hdld);
  pmain := _;
  phdld := G.(phdld)|}).
intros v l xi Hsat Hin Hall.
apply (pmain G); try assumption.
apply (sat_and_of_sat_split Hsat).
Defined.

Inductive and_instance_seqt (G : seqt) : seqt -> Type :=
| ais_cons : forall {phi psi} (h : In (and phi psi) (main G)),
              and_instance_seqt G (and_child G h).

Arguments ais_cons {G phi psi}.

Definition or_child_left {phi psi} (G : seqt) (h : In (or phi psi) (main G)) : seqt.
refine (
{|main  := phi :: remove_nnf (or phi psi) (main G);
  hdld  := hdld G;
  pmain := _;
  phdld := phdld G|}).
intros v l xi Hsat Hin Hall.
apply (pmain G); try assumption.
apply (sat_or_of_sat_split_left _ Hsat).
Defined.

Definition or_child_right {phi psi} (G : seqt) (h : In (or phi psi) (main G)) : seqt.
refine (
{|main  := psi :: remove_nnf (or phi psi) (main G);
  hdld  := hdld G;
  pmain := _;
  phdld := phdld G|}).
intros v l xi Hsat Hin Hall.
apply (pmain G); try assumption.
apply (sat_or_of_sat_split_right _ Hsat).
Defined.

Inductive or_instance_seqt (G : seqt) : seqt -> seqt -> Type :=
| ois_cons : forall {phi psi} (h : In (or phi psi) (main G)),
         or_instance_seqt G (or_child_left G h) (or_child_right G h).

Arguments ois_cons {G phi psi}.

Definition box_child {phi} (G : seqt) (h : In (box phi) (main G)) : seqt.
refine (
{|main  := phi :: remove_nnf (box phi) (main G);
  hdld  := box phi :: hdld G;
  pmain := _;
  phdld := cons_box_only (phdld G)|}).
intros v l psi Hsat Hin Hall.
destruct Hin as [Hinl|Hinr].
- injection Hinl. intro Heq.
  rewrite <- Heq. apply Hsat.
  left. reflexivity.
- apply (pmain G); try assumption.
  * intros xi Hxi.
    destruct (nnf_eqdec xi (box phi)) as [Heq|Hneq].
    + rewrite Heq. simpl. intros t Ht. destruct Ht as [Htl|Htr].
     -- apply Hall; try assumption.
        left. reflexivity.
     -- rewrite <- Htr. apply Hsat.
        left. reflexivity.
    + apply Hsat. right. apply in_in_remove; try assumption.
  * intros xi Hxi. apply Hall.
    right. assumption.
Defined.

Inductive copy_instance_seqt (G : seqt) : seqt -> Type :=
| cis_cons : forall {phi} (h : In (box phi) (main G)),
         copy_instance_seqt G (box_child G h).

Arguments cis_cons {G phi}.

Theorem build_model_seqt : forall G `(mc : model_constructible G),
  sat builder (mcons vc_atoms []) ((main G) ++ (hdld G)).
Proof.
intros G sa vc mc.
assert (sat builder (mcons vc_atoms []) (main G)) as HsatG.
- intros phi Hphi.
  destruct phi; try (contradict Hphi;
  (apply sa_no_and || apply sa_no_or || apply vc_no_box || apply mc_no_dia)).
  * simpl. apply vc_hypatoms. assumption.
  * simpl. intro H. contradict Hphi. apply vc_hypatoms in H.
    apply vc_no_contra. assumption.
- apply sat_append; try assumption.
  intros phi Hphi.
  pose proof (G.(phdld).(bo_no_literals)) as hdld_nl.
  pose proof (G.(phdld).(bo_saturated)) as hdld_sa.
  destruct phi; try (contradict Hphi;
  (apply hdld_nl.(nl_no_var) || apply hdld_nl.(nl_no_neg)
  || apply hdld_sa.(sa_no_and) || apply hdld_sa.(sa_no_or)
  || apply G.(phdld).(bo_no_dia))).
  simpl. intros t Ht.
  destruct Ht as [Htl|Htr]; try contradiction.
  rewrite <- Htr. apply (pmain G); try assumption.
  simpl. tauto.
Qed.