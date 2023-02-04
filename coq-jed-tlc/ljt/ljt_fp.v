
(* doing stuff like in Frank Pfenning.  Structural cut elimination.
  well, not exactly, because I can't find his code, so looking at
  http://twelf.org/wiki/Admissibility_of_cut 
*)

(* at present this file requires ljt.v only for the definition of PropF *)
Require Export List.
Export ListNotations.
Set Implicit Arguments.
From Coq Require Import ssreflect.
Require Import Coq.Program.Equality. (* for dependent induction/destruction *)

Add LoadPath "../general".
Require Import ljt.
Require Import gen genT.

Parameter hyp : forall V, PropF V -> Type.

Inductive conc V : PropF V -> Type :=
  | init : forall (A : PropF V), (hyp A -> conc A) (* axiom in Pfenning *)
  | impL : forall (A B C : PropF V),
    conc A -> (hyp B -> conc C) -> (hyp (Imp A B) -> conc C)
  | impR : forall (A B : PropF V), (hyp A -> conc B) -> conc (Imp A B)
  | andL : forall (A B C : PropF V), 
    (hyp A -> hyp B -> conc C) -> (hyp (And A B) -> conc C)
  | andR : forall (A B : PropF V), conc A -> conc B -> conc (And A B)
  .

(* note, this encoding of the left rules doesn't explicitly copy
  principal formula to the premises, though given that we have contraction,
  this doesn't make any difference *)

Print Implicit conc.

(* define a well-founded ordering on derivations - but problem, 
  they have different types 
Inductive der_ord V : Type -> Type -> Type :=
  | impL1 : forall A B C ca bc hiab, der_ord V ca (@impL V A B C ca bc hiab) 
  *)

(* conc_gc - derivations without conclusion as part of the type *)
Inductive conc_gc V : Type := | gcI : forall A, @conc V A -> conc_gc V.

Definition conc_concl V A (c : @conc V A) := A.

Fixpoint conc_gc_concl V (c : @conc_gc V) :=
  match c with
    | gcI d => conc_concl d
  end.

(* type of derivations with varying numbers of hyps *)
Inductive der_hc V : Type :=
  | h0 : forall C, @conc V C -> der_hc V
  | h1 : forall A1 C, (@hyp V A1 -> @conc V C) -> der_hc V
  | h2 : forall A1 A2 C, (@hyp V A1 -> @hyp V A2 -> @conc V C) -> der_hc V
  .

(* but a deeper embedding of derivations like this removes the automatic
  weakening, contraction and contexts *)
Inductive dd_hc V : (@der_hc V) -> Type :=
  | hc_init : forall (A : PropF V) (f : hyp A -> conc A), dd_hc (h1 f)
  | hc_impL : forall (A B C : PropF V) f g h, dd_hc (h0 (f : conc A)) ->
    dd_hc (h1 (g : hyp B -> conc C)) -> 
    dd_hc (h1 (h : hyp (Imp A B) -> conc C))
  | hc_impR : forall (A B : PropF V) (f : hyp A -> conc B) (g : conc (Imp A B)),
    dd_hc (h1 f) -> dd_hc (h0 g)
  | hc_andL : forall (A B C : PropF V) (f : hyp A -> hyp B -> conc C)
    (g : hyp (And A B) -> conc C), dd_hc (h2 f) -> dd_hc (h1 g)
  | hc_andR : forall (A B : PropF V) (f : conc A) (g : conc B)
    (h : conc (And A B)), dd_hc (h0 f) -> dd_hc (h0 g) -> dd_hc (h0 h)
  .

Inductive der_ord V : relationT (conc_gc V) :=
  | impLp1 : forall A B C ca bc hiab, 
    der_ord (gcI ca) (gcI (@impL V A B C ca bc hiab))
  | impLp2 : forall A B C ca bc hb hiab, 
    der_ord (gcI (bc hb)) (gcI (@impL V A B C ca bc hiab))
  | impRp : forall A B ab ha, 
    der_ord (gcI (ab ha)) (gcI (@impR V A B ab))
  | andRp1 : forall A B ca cb,
    der_ord (gcI ca) (gcI (@andR V A B ca cb))
  | andRp2 : forall A B ca cb,
    der_ord (gcI cb) (gcI (@andR V A B ca cb))
  | andLp : forall A B C abc ha hb haab,
    der_ord (gcI (abc ha hb)) (gcI (@andL V A B C abc haab))
  .

Definition lift X (R : relationT X) A (a : A) f g := R (f a) (g a).
Check (fun V => lift (@der_ord V)).
Check (fun X R A a => @lift X R A a : relationT (A -> X)).
Check (lift : forall X, relationT X -> forall A, A -> relationT (A -> X)).

Definition lift_all X (R : relationT X) A f g := forall a : A, R (f a) (g a).
Check (fun V => lift_all (@der_ord V)).
Check (fun V => lift_all (@der_ord V) : forall A, relationT (A -> conc_gc V)).

Inductive lift_some X (R : relationT X) A f g : Type :=
  | lsI : forall Hb : A, R (f Hb) (g Hb) -> @lift_some X R A f g.
Check (fun V => lift_some (@der_ord V)).
Check (fun V => lift_some (@der_ord V) : forall A, relationT (A -> conc_gc V)).

Print Implicit lift_all.
Print Implicit der_ord.

Inductive der_hc_ord V : (der_hc V) -> (der_hc V) -> Type :=
  | impLp1_hc : forall A B C ca bc, 
    der_hc_ord (h0 ca) (h1 (@impL V A B C ca bc))
  | impLp2_hc : forall A B C ca bc, 
    der_hc_ord (h1 bc) (h1 (@impL V A B C ca bc))
  | impRp_hc : forall A B ab, 
    der_hc_ord (h1 ab) (h0 (@impR V A B ab))
  | andRp1_hc : forall A B ca cb,
    der_hc_ord (h0 ca) (h0 (@andR V A B ca cb))
  | andRp2_hc : forall A B ca cb,
    der_hc_ord (h0 cb) (h0 (@andR V A B ca cb))
  | andLp_hc : forall A B C abc,
    der_hc_ord (h2 abc) (h1 (@andL V A B C abc))
  .

Lemma AccT_der_ord V (A : conc_gc V) : AccT (@der_ord V) A.
Proof. destruct A.
induction c ; apply AccT_intro ; intro y ; destruct y ;
intro do ; dependent destruction do ; (assumption || apply X).
Qed.

Lemma AccT_lift_der_ord V (B : PropF V) (Hb : hyp B) f :
  AccT (lift (@der_ord V) Hb) f.
Proof.  pose (AccT_der_ord (f Hb)).
remember (f Hb) as fHb.
clearbody a.  revert fHb a f HeqfHb.
epose (well_foundedT_induction' _ _).  exact y.  Unshelve.
intros b indl. simpl. simpl in indl.
intros f bfhb. subst. apply AccT_intro.
intros y lyf. unfold lift in lyf.
exact (indl _ lyf y eq_refl). Qed.

(* this is clearly not true if the domain type is empty
Lemma AccT_lift_all_der_ord V B f : 
  AccT (@lift_all _ (@der_ord V) (@hyp V B)) f.
  *)

(*
I don't think this will work either
Lemma AccT_lift_some_der_ord V B f : 
  AccT (@lift_some _ (@der_ord V) (@hyp V B)) f.
Proof.
apply AccT_intro. intros y lsyf.
destruct lsyf.
*)

(*
I don't think this approach will work, because for bc : hyp B -> conc C,
bc hb is a different object for different hb (potentially!)
Lemma AccT_der_hc_ord V A : AccT (@der_hc_ord V) A.
Proof. destruct A.
problem with this proof - inducts separately on cases of h0, h1, h2 - WRONG
induction c ; apply AccT_intro ; intro y ; destruct y ;
intro do ; dependent destruction do ; (assumption || apply X).
Qed.
*)

(* sample proofs *)
Lemma sample1 V A B : hyp (And A (Imp A B)) -> @conc V B.
Proof. apply andL. intro.  apply impL.
apply (init X).  apply init. Qed.

Lemma sample2 V A B : hyp (And (Imp A B) A) -> @conc V B.
Proof. apply andL. (* apply impL. fails, must switch args *)
intros. revert X. apply impL.
apply (init X0).  apply init. Qed.

Print Implicit init.
Print Implicit andR.

Definition iscad V (A C : PropF V) 
  (D: conc A) (E: hyp A -> conc C) (F : conc C) := True.

Print Implicit iscad.

Lemma initD V (A C : PropF V) Ha (E: hyp A -> conc C) :
  iscad (init Ha) E (E Ha).
Proof. exact I. Qed.

Lemma initE V (A : PropF V) (D : conc A) : @iscad V A A D (@init _ _) D.
Proof. exact I. Qed.

Lemma closed V (A C : PropF V) D E' : @iscad V A C D (fun _ => E') E'.
Proof. exact I. Qed.

Notation "B <- A" := (forall _ : A, B)
  (only parsing, at level 90, left associativity).

(* although the rules don't copy principal formulae into premises,
  E' here is sort of as though they do - see andC', impC' *)
Lemma andC V (A B C : PropF V) D1 D2 E' F1 F2 F : 
  @iscad _ (And A B) C (andR D1 D2) 
    (fun (Hab : hyp (And A B)) => andL (E' Hab) Hab) F
    <- (forall Ha Hb, @iscad V (And A B) C (andR D1 D2) 
      (fun Hab => E' Hab Ha Hb) (F1 Ha Hb))
    <- (forall Hb, @iscad V A C D1 (fun Ha => F1 Ha Hb) (F2 Hb))
    <- @iscad V B C D2 F2 F.
Proof. intros. exact I. Qed.

Lemma andC' V (A B C : PropF V) D1 D2 F1 F2 F : 
  @iscad _ (And A B) C (andR D1 D2) (andL F1) F
    <- (forall Hb, @iscad V A C D1 (fun Ha => F1 Ha Hb) (F2 Hb))
    <- @iscad V B C D2 F2 F.
Proof. intros. exact I. Qed.

Lemma impC V (A B C : PropF V) D' E1 E2 F1 F2 F3 F :
  @iscad V (Imp A B) _ (impR D')
     (fun Hab => impL (E1 Hab : conc A) (E2 Hab : hyp B -> conc C) Hab) F
    <- @iscad V (Imp A B) _ (impR D') E1 (F1 : conc A)
    <- (forall Hb : hyp B, @iscad V (Imp A B) _ (impR D')
      (fun Hab => E2 Hab Hb) (F2 Hb : conc C))
    <- @iscad V A _ F1 D' (F3 : conc B)
    <- @iscad V B _ F3 F2 F.
Proof. intros. exact I. Qed.

Lemma impC' V (A B C : PropF V) D' F1 F2 F3 F :
  @iscad V (Imp A B) _ (impR D') (impL (F1 : conc A) (F2 : hyp B -> conc C)) F
    <- @iscad V A _ F1 D' (F3 : conc B)
    <- @iscad V B _ F3 F2 F.
Proof. intros. exact I. Qed.

Lemma andLLC V (A B A1 B1 : PropF V) D' E F' (Hab : hyp (And A1 B1)) :
  @iscad V A B (andL D' Hab) E (andL F' Hab)
      <- (forall Ha Hb, @iscad V A B (D' Ha Hb) E (F' Ha Hb)).
Proof. intros. exact I. Qed.

Lemma impLLC V (A B A1 B1 : PropF V) D1 D2 E F2 (Hi : hyp (Imp A1 B1)) :
  @iscad V A B (impL D1 D2 Hi) E (impL D1 F2 Hi)
      <- (forall Hb, @iscad V A B (D2 Hb) E (F2 Hb)).
Proof. intros. exact I. Qed.

Lemma andRRC V A B C D E1 E2 F1 F2 :
  @iscad V A (And B C) D (fun Ha => andR (E1 Ha) (E2 Ha)) (andR F1 F2)
      <- iscad D E1 F1 <- iscad D E2 F2.
Proof. intros. exact I. Qed.

Lemma impRRC V A B C D E1 F1 :
  @iscad V A (Imp B C) D (fun Ha => impR (E1 Ha)) (impR F1)
      <- (forall H1, iscad D (fun Ha => E1 Ha H1) (F1 H1)).
Proof. intros. exact I. Qed.

Print Implicit andL.
Print Implicit impL.

Lemma andLRC V A B D A1 B1 E' F' (Hp : hyp (And A1 B1)) :
  @iscad V A B D (fun Ha => andL (E' Ha) Hp) (andL F' Hp)
      <- (forall H1 H2, iscad D (fun Ha => E' Ha H1 H2) (F' H1 H2)).
Proof. intros. exact I. Qed.

Lemma impLRC V A B D A1 B1 E1 E2 F1 F2 (Hi : hyp (Imp A1 B1)) :
  @iscad V A B D (fun Ha => impL (E1 Ha) (E2 Ha) Hi) (impL F1 F2 Hi)
      <- iscad D E1 F1
      <- (forall Hb, iscad D (fun Ha => E2 Ha Hb) (F2 Hb)).
Proof. intros. exact I. Qed.

Check fun V (A B C : PropF V) => hyp (And A B) -> conc C.

Definition cancut V (A C : PropF V) (D: conc A) (E: hyp A -> conc C) :=
  sigT (fun F : conc C => True).

Definition cancut_gc V (A C : PropF V) (D: conc_gc V) (E: hyp A -> conc_gc V) :=
  sigT (fun F : conc_gc V => conc_gc_concl F = C).

Lemma cancut_gcI V (A C : PropF V) (D: conc A) (E: hyp A -> conc C) :
  cancut D E -> cancut_gc C (gcI D) (fun ha => gcI (E ha)).
Proof. unfold cancut.  unfold cancut_gc. 
intro. cD.  exists (gcI X). reflexivity. Qed. 

Lemma cancut_gcD V (A C : PropF V) (D: conc A) (E: hyp A -> conc C) :
  cancut_gc C (gcI D) (fun ha => gcI (E ha)) -> cancut D E.
Proof. unfold cancut.  unfold cancut_gc.
intro. cD. destruct X. simpl in X0. subst. exists c. apply I. Qed.

(*
  conc_gc_concl D = A -> (forall ha : hyp A, conc_gc_concl (E ha) = C) ->

intros cc cda cec. destruct cc. exists (gcI x). reflexivity.
intros cd ce.  specialize (X eq_refl).
require X. intro. reflexivity.
cD. destruct X. simpl in X0. subst. exists c. apply I.
Qed. 
*)

(* can we formulate induction principle ?
Lemma cancut_ind V A C 
  forall A' C', isubfml A' A -> conc A' -> (hyp A' -> conc C')) -> 
  cancut (V : Set) (A C : PropF V), conc A -> (hyp A -> conc C).
  *)

Print Implicit well_foundedT_induction.
Print Implicit cancut.
Print Implicit cancut_gc.
Print Implicit cancut_gcI.
Print Implicit cancut_gcD.
Print Implicit AccT_der_ord.
Print Implicit well_foundedT_induction'.
Print Implicit lift.
Print Implicit AccT_lift_der_ord.
Print Implicit der_ord.

Lemma cut_adm_bc V B C (DAg : conc_gc V) (DACg : hyp B -> conc_gc V) Hb :
  (forall bc,
    (forall bc', lift (@der_ord V) Hb bc' bc -> cancut_gc C DAg bc') ->
    @cancut_gc V B C DAg bc) -> 
  cancut_gc C DAg DACg.
Proof. exact (well_foundedT_induction _ (AccT_lift_der_ord _ _)). Qed.

Print Implicit cut_adm_bc.

Definition use_wf_ldo V B C DAg DACg Hb :=
  @well_foundedT_induction _ _ (cancut_gc C DAg) DACg
  (@AccT_lift_der_ord V B Hb DACg).

(* problems doing proof of cut by induction on the derivation 
  cancut : conc A -> (hyp A -> conc C) -> Type 
  OK for left drivation, we have an ordering der_ord, on conc_gc
  (where conc_gc is conc without specifying the type of conclusion)
  but right derivation is of type (hyp A -> conc C),
  how to get suitable well founded ordering - see attempts above 
  what ordering do we need? look at steps in cut elimination
  eg andRRC, on the right derivation (for left premise) need
  E1 < (fun Ha => andR (E1 Ha) (E2 Ha))
  where forall Ha, we have E1 Ha < (fun Ha => andR (E1 Ha) (E2 Ha)) Ha
  for impRRC, need (fun Ha => E1 Ha H1) < (fun Ha => impR (E1 Ha))
  where, forall Ha, we have E1 Ha H1 < impR (E1 Ha)
  for andLRC, need (fun Ha => E' Ha H1 H2) < (fun Ha => andL (E' Ha) Hp)
  where, forall Ha, we have E' Ha H1 H2 < andL (E' Ha) Hp)
  for impLRC, need (fun Ha => E2 Ha Hb) < (fun Ha => impL (E1 Ha) (E2 Ha) Hi)
  where, forall Ha, we have E2 Ha Hb < impL (E1 Ha) (E2 Ha) Hi

  thus if we have an ordering such that if forall Ha, X Ha < Y Ha then X < Y
  this would be fine - and we have defined lift_all,
  but clearly AccT_lift_all_der_ord isn't true 
  (eg when the forall _ : _ is forall of an empty type)
  *)

(*
Lemma cut_adm V : forall A C DA DAC, @cancut V A C DA DAC.
Proof. intro A.
(* first, well-founded induction on A *)
pose (AccT_isubfml A). clearbody a. revert A a.
epose (well_foundedT_induction' _ _).  exact y.  Unshelve.
intros b subcf.
(* now have assumption that can do cut on smaller cut formulae *)
(* turn goal into one using cancut_gc *)
enough (forall C DAg DACg, @cancut_gc V b C DAg DACg).  
simpl. intros *. apply cancut_gcD. apply X.
(* well-founded induction on gcI DA *)
intro.  intro.
pose (AccT_der_ord DAg). clearbody a.  revert DAg a.
epose (well_foundedT_induction' _ _).  exact y.  Unshelve.
simpl. intros DAg lder. 
(* now have assumption that can do cut for smaller derivation on the left *)
intro.
What hyp do we need here:
forall DACg' : hyp b -> conc_gc V, such that 
forall hb, der_ord (DACg' hb) (der_ord (DACg hb), cancut ... DACg')
Is this enough?? need to look at reductions
Now have use_wf_ldo - what use of this?
Problem now - can't do a case analysis on DACg until we have Hb : hyp b
to apply DACg to it.
Maybe we should use something like dd_hc - trouble is, doing this we don't
get contraction, weakening and contexts automatically
*)

