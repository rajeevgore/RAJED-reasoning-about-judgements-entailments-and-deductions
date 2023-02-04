Add LoadPath "../general".
Require Export List.
Set Implicit Arguments.
Export ListNotations.

Delimit Scope My_scope with M.
Open Scope My_scope.

Parameter PropVars : Set.
Hypothesis Varseq_dec : forall x y:PropVars, {x = y} + {x <> y}.

(** * Definitions

definition of Propositional Formulas*)
Inductive PropF : Set :=
 | Var : PropVars -> PropF
 | Bot : PropF
 | Impl : PropF -> PropF -> PropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Impl A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.

(** Defined connectives *)
Notation "¬ A" := (A → ⊥) (at level 1)  : My_scope.
Notation "A ∧ B" := ((A → (B → ⊥)) → ⊥) (at level 15, right associativity) : My_scope.
Notation "A ∨ B" := ((A → ⊥) → B) (at level 15, right associativity) : My_scope.

(** Valuations are maps PropVars -> bool sending ⊥ to false*)
Fixpoint TrueQ v A : bool := match A with
 | # P   => v P
 | ⊥     => false
 | B → C => (negb (TrueQ v B)) || (TrueQ v C)
end.

(** Prove that the defined connectives are correct *)

Lemma def_neg_correct (A: PropF) :
  forall v, TrueQ v (¬ A) = negb (TrueQ v A).
Proof. intros. destruct A.
       simpl. rewrite Bool.orb_false_r. trivial.
       simpl. trivial.
       simpl. rewrite Bool.orb_false_r. trivial.
Qed.

Lemma def_or_correct (A B: PropF) :
  forall v, TrueQ v (A ∨ B) = orb (TrueQ v A) (TrueQ v B).
Proof. intros. simpl. repeat rewrite Bool.orb_false_r.
       rewrite Bool.negb_involutive.
       trivial.
Qed.

Lemma def_and_correct (A B: PropF) :
  forall v, TrueQ v (A ∧ B) = andb (TrueQ v A) (TrueQ v B).
Proof. intros. simpl. repeat rewrite Bool.orb_false_r.
       repeat rewrite Bool.negb_orb.
       repeat rewrite Bool.negb_involutive.
       reflexivity.
Qed.

(** * Gentzen's Sequent Calculus *)

Reserved Notation "Γ |- Δ" (at level 80).
Inductive LK : list PropF -> list PropF -> Prop :=
| LKId  : forall A Γ Δ, In A Γ  -> In A Δ  -> LK Γ Δ
| LKBot : forall Γ Δ,   In ⊥ Γ  -> LK Γ Δ
| LKImpL : forall A B Γ1 Γ2 Δ,
              LK (Γ1++B::Γ2) Δ   -> LK (Γ1++Γ2) (A::Δ)
           -> LK (Γ1++A→B::Γ2) Δ
| LKImpR : forall A B Γ Δ1 Δ2,
              LK (A::Γ) (Δ1++B::Δ2)
           -> LK Γ (Δ1++A→B::Δ2)
where "Γ |- Δ" := (LK (Γ) (Δ)) : My_scope.


Lemma weakening_appR_L:
  forall Γ Δ (D: Γ |- Δ), forall W, ((Γ ++ W) |- Δ).
Proof.
intros.
induction D.

apply (LKId A). rewrite in_app_iff. tauto. assumption.
apply LKBot. rewrite in_app_iff. tauto.

rewrite app_assoc_reverse. simpl.
apply LKImpL.
rewrite app_assoc_reverse in IHD1. simpl in IHD1. assumption.
rewrite app_assoc. assumption.

apply LKImpR.
simpl in IHD. assumption.
Qed.

Lemma weakening_appR_R:
  forall Γ Δ (D: Γ |- Δ), forall W, (Γ |- (Δ ++ W)).
Proof.
intros.
induction D.
apply (LKId A). assumption. rewrite in_app_iff. tauto.
apply LKBot. assumption.

apply LKImpL.
assumption.  simpl in IHD2. assumption.

rewrite app_assoc_reverse. simpl.
apply LKImpR.
rewrite app_assoc_reverse in IHD. simpl in IHD. assumption.
Qed.

(** Weakening by adding stuff on the left of the succedent is more
    complicated because of the form of the ImpL rule
    and weakening by adding stuff on the left of the antecedent is more
    complicated because of the form of the ImpR rule,
    but we changed ImpR to be of this form because the other form
    where premise is G1,A,G2 |- D1,B,D2 messes up adjacent exchange *)

Lemma cons_eq_app: forall (A : Type) (x y z : list A) (a : A),
  a :: x = y ++ z -> y = [] /\ z = a :: x \/
                         exists (y' : list A), y = a :: y' /\ x = y' ++ z.
Proof.
intros.
destruct y.
 simpl in H. subst. tauto.
 simpl in H. injection H. intros. right. subst. exists y. tauto.
Qed.

Lemma app_eq_app: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> exists (m : list A),
    w = y ++ m /\ z = m ++ x \/ y = w ++ m /\ x = m ++ z.
Proof.
 intro. intro.
 induction w.
    simpl. intros. exists y. rewrite H. tauto.

    intros. simpl in H.
    apply cons_eq_app in H.
    destruct H.  destruct H. rewrite H. simpl.
    exists (a :: w). rewrite H0. simpl. tauto.
    destruct H. destruct H.
    apply IHw in H0. destruct H0. destruct H0. destruct H0.
    rewrite H.  rewrite H0.  rewrite H1.  simpl.
    exists x1. tauto.
    destruct H0. rewrite H.  rewrite H0.  rewrite H1.  simpl.
    exists x1. tauto.
Qed.

Lemma weakening_R:
  forall Γ Δ (D: Γ |- Δ), forall Δ1 Δ2, (Δ = Δ1 ++ Δ2) ->
    forall W, (Γ |- (Δ1 ++ W ++ Δ2)).
Proof.
intro.  intro.  intro.
induction D.
intros.
apply (LKId A). assumption. rewrite in_app_iff. rewrite in_app_iff.
rewrite H1 in H0. rewrite in_app_iff in H0. tauto.
intros. apply LKBot. assumption.

intros. apply LKImpL.
exact (IHD1 Δ1 Δ2 H W).
intros.
lapply (IHD2 (A :: Δ1) Δ2).
simpl.  intro. apply H0.
rewrite H. simpl. trivial.

intros.
apply app_eq_app in H.
destruct H.  destruct H. destruct H. subst.
rewrite !app_assoc.
apply LKImpR.
rewrite !app_assoc_reverse.
apply IHD. apply app_assoc_reverse.
destruct H. rewrite H.
apply cons_eq_app in H0.
destruct H0.  destruct H0. subst.
rewrite app_nil_r.  rewrite app_assoc.
apply LKImpR.
rewrite app_assoc_reverse.
apply IHD. trivial.
destruct H0.  destruct H0. subst. rewrite app_assoc_reverse.
rewrite <- app_comm_cons.
apply LKImpR.  rewrite app_comm_cons.  rewrite app_assoc.
apply IHD. rewrite app_comm_cons. apply app_assoc.
Qed.

Check weakening_R.

Lemma weakening_L:
    forall Γ Δ (D: Γ |- Δ), forall Γ1 Γ2, (Γ = Γ1 ++ Γ2) ->
      forall W, ((Γ1 ++ W ++ Γ2) |- Δ).
Proof.
intro.  intro.  intro.
induction D.
intros.
apply (LKId A). rewrite !in_app_iff. subst.
rewrite in_app_iff in H. tauto. assumption.
intros. apply LKBot.  rewrite !in_app_iff. subst.
rewrite in_app_iff in H. tauto.

intros.
apply app_eq_app in H.
destruct H.  destruct H. destruct H. subst.
rewrite !app_assoc.
apply LKImpL.  rewrite !app_assoc_reverse.
apply IHD1. apply app_assoc_reverse.
rewrite !app_assoc_reverse.
apply IHD2. apply app_assoc_reverse.

destruct H. rewrite H.
apply cons_eq_app in H0.
destruct H0.  destruct H0. subst.
rewrite app_nil_r. rewrite app_assoc.
apply LKImpL.
rewrite app_assoc_reverse.
apply IHD1. trivial.
rewrite app_assoc_reverse.
apply IHD2. trivial.

destruct H0.  destruct H0. subst.
rewrite app_assoc_reverse.
rewrite <- app_comm_cons.
apply LKImpL.
rewrite app_comm_cons.
rewrite app_assoc.
apply IHD1. rewrite app_assoc_reverse.
simpl. trivial.
rewrite app_assoc.
apply IHD2. apply app_assoc.

intros.
apply LKImpR.
rewrite app_comm_cons.
apply IHD. rewrite H. apply app_comm_cons.
Qed.

Check weakening_L.

Lemma cons_single_app: forall T (A : T) L, A :: L = [A] ++ L.
Proof. simpl. trivial. Qed.

(**
Lemma cons_single_app: forall E (A : E) L, A :: L = [A] ++ L.
Proof. simpl. trivial. Qed.
 *)

Lemma exchange_L:
  forall Γ Δ (D: Γ |- Δ), forall G H Γ1 Γ2,
    (Γ = Γ1 ++ G :: H :: Γ2) -> ((Γ1 ++ H :: G :: Γ2) |- Δ).
Proof.
intro.  intro.  intro.
induction D.
intros.
apply (LKId A). rewrite in_app_iff. simpl. subst.
rewrite in_app_iff in H. simpl in H.
tauto. assumption.
intros. apply LKBot.
rewrite in_app_iff. simpl. subst.
rewrite in_app_iff in H. simpl in H.
tauto.

intros.
apply app_eq_app in H0.
destruct H0.  destruct H0. destruct H0.
apply cons_eq_app in H1.  destruct H1.  destruct H1.
injection H2. intros.  subst.

rewrite cons_single_app.  rewrite app_assoc.
rewrite app_nil_r in D1.
rewrite app_nil_r in D2.
apply LKImpL.
rewrite app_assoc_reverse.  rewrite <- cons_single_app.
apply IHD1. rewrite app_nil_r.  trivial.
rewrite app_assoc_reverse.  rewrite <- cons_single_app.  assumption.

destruct H1.  destruct H1.  subst.
apply cons_eq_app in H2.  destruct H2.  destruct H0.
injection H1. intros.  subst.
apply LKImpL.
apply IHD1.  rewrite app_assoc_reverse.  simpl. trivial.
rewrite app_assoc_reverse in D2.  simpl in D2.  assumption.

destruct H0.  destruct H0. subst.
rewrite !app_comm_cons. rewrite app_assoc.
apply LKImpL.
rewrite app_assoc_reverse.
rewrite <- !app_comm_cons.
apply IHD1.
rewrite app_assoc_reverse.
rewrite !app_comm_cons. trivial.
rewrite app_assoc_reverse. rewrite <- !app_comm_cons.
apply IHD2.
rewrite app_assoc_reverse.  rewrite !app_comm_cons. trivial.

destruct H0. subst.
apply cons_eq_app in H1.
destruct H1.  destruct H0.
injection H1. intros. subst.
rewrite app_nil_r.
rewrite cons_single_app.  rewrite app_assoc.
apply LKImpL. rewrite app_assoc_reverse. simpl.
apply IHD1. trivial.
rewrite app_assoc_reverse. simpl. assumption.

destruct H0.  destruct H0. subst.
rewrite app_assoc_reverse.  rewrite <- app_comm_cons.
apply LKImpL.
rewrite app_comm_cons.  rewrite app_assoc.
apply IHD1. rewrite app_assoc_reverse. simpl. trivial.
rewrite app_assoc.
apply IHD2. apply app_assoc.

intros. subst.
apply LKImpR. rewrite app_comm_cons.
apply IHD. apply app_comm_cons.
Qed.

Check exchange_L.

Lemma exchange_R:
  forall Γ Δ (D: Γ |- Δ), forall A B Δ1 Δ2,
    ( Δ = Δ1 ++ A :: B :: Δ2 ) -> ( Γ |- (Δ1 ++ B :: A :: Δ2) ).
Proof.
intro.  intro.  intro.
induction D.
intros.
apply (LKId A). assumption.
rewrite in_app_iff. simpl. subst.
rewrite in_app_iff in H0. simpl in H0.  tauto.
intros. apply LKBot. assumption.

intros.
apply LKImpL.
apply IHD1. assumption.
rewrite app_comm_cons.
apply IHD2. subst. simpl. trivial.

intros.
apply app_eq_app in H.
destruct H. destruct H. destruct H.
apply cons_eq_app in H0.
destruct H0. destruct H0.
injection H1. intros. subst.
rewrite cons_single_app.  rewrite app_assoc.
apply LKImpR. rewrite app_assoc_reverse. simpl.
apply IHD.  rewrite app_nil_r.  trivial.
destruct H0. destruct H0.
apply cons_eq_app in H1.
destruct H1. destruct H1.
injection H2. intros. subst.
apply LKImpR.
apply IHD.  rewrite app_assoc_reverse. simpl. trivial.
destruct H1. destruct H1. subst.
rewrite !app_comm_cons.  rewrite app_assoc.
apply LKImpR.
rewrite app_assoc_reverse.
rewrite <- !app_comm_cons.
apply IHD.  apply app_assoc_reverse.
destruct H.  apply cons_eq_app in H0.
destruct H0. destruct H0.
injection H1. intros. subst.
rewrite app_nil_r.
rewrite cons_single_app. rewrite app_assoc.
apply LKImpR.
rewrite app_assoc_reverse.  simpl.
apply IHD. trivial.
destruct H0. destruct H0. subst.
rewrite app_assoc_reverse.  rewrite <- app_comm_cons.
apply LKImpR.
rewrite app_comm_cons.  rewrite app_assoc.
apply IHD.
rewrite app_assoc_reverse.  rewrite <- app_comm_cons. trivial.
Qed.

Check exchange_R.

Lemma move_R_R: forall Γ A Δ3 Δ2 Δ1,
                ( Γ |- (Δ1 ++ A :: Δ2 ++ Δ3) ) ->
                ( Γ |- (Δ1 ++ Δ2 ++ A :: Δ3) ).
Proof.
intro. intro. intro. intro.
induction Δ2.
simpl. intros. assumption.
intros. rewrite cons_single_app.  rewrite !app_assoc.
rewrite app_assoc_reverse.
apply IHΔ2.
rewrite app_assoc_reverse.  simpl.
eapply exchange_R. eassumption.
rewrite <- app_comm_cons. trivial.
Qed.

Lemma move_L_R:
  forall Γ A Δ3 Δ2 Δ1,
    ( Γ |- (Δ1 ++ Δ2 ++ A :: Δ3) ) ->
    ( Γ |- (Δ1 ++ A :: Δ2 ++ Δ3)).
Proof.
intro.  intro.  intro. intro.
induction Δ2.
simpl. intros. assumption.
intros.
rewrite <- app_comm_cons.
eapply exchange_R. 2: reflexivity.
rewrite cons_single_app. rewrite app_assoc.
apply IHΔ2.
rewrite app_assoc_reverse.  simpl.  simpl in H.  assumption.
Qed.

Lemma move_R_L:
  forall Γ A Δ3 Δ2 Δ1,
    ( (Δ1 ++ A :: Δ2 ++ Δ3) |- Γ ) ->
    ( (Δ1 ++ Δ2 ++ A :: Δ3) |- Γ ).
Proof.
intro.  intro.  intro. intro.
induction Δ2.
simpl. intros. assumption.
intros. rewrite cons_single_app.  rewrite !app_assoc.
rewrite app_assoc_reverse.
apply IHΔ2.
rewrite app_assoc_reverse.  simpl.
eapply exchange_L. eassumption.
rewrite <- app_comm_cons. trivial.
Qed.

Lemma move_L_L:
  forall Γ A Δ3 Δ2 Δ1,
    ( (Δ1 ++ Δ2 ++ A :: Δ3) |- Γ ) ->
    ( (Δ1 ++ A :: Δ2 ++ Δ3) |- Γ ).
Proof.
intro.  intro.  intro. intro.
induction Δ2.
simpl. intros. assumption.
intros.
rewrite <- app_comm_cons.
eapply exchange_L. 2: reflexivity.
rewrite cons_single_app. rewrite app_assoc.
apply IHΔ2.
rewrite app_assoc_reverse.  simpl.  simpl in H.  assumption.
Qed.

(* These lemmas and Ltac are used to solve list equalities where bracketing 
   prevents the trivial tactic from being used *)

(** commented out by raj since they are tautologies 
Lemma list_app_eq_1:
  forall (L1 L2 : list PropF),
    L2 = L2 -> L1 ++ L2 = L1 ++ L2.
    Proof.
    intros. firstorder.
    Qed.

Lemma list_app_eq_2:
  forall (L1 L2 : list PropF),
    L2 = L2 -> L1 ++ L2 = L1 ++ L2.
    Proof.
    intros. firstorder.
    Qed.
 *)

Ltac list_solve := repeat
(** commented out by raj since they are tautologies 
try apply list_app_eq_1; try apply list_app_eq_2; 
 *)
try rewrite !app_comm_cons; try rewrite app_assoc_reverse;
match goal with
  | |- _ ++ (_) =>
(** commented out by raj since they are tautologies 
    try apply list_app_eq_1; try apply list_app_eq_1; 
 *)
    firstorder
      | _ => try rewrite app_assoc_reverse; try rewrite !app_comm_cons; firstorder
    end.


(* Implication left derives one sequent from two previously derived sequents
   so inversion is split into two lemmas, one for each of the sequents    *)

Lemma inv_ImpL1:
  forall Γ Δ (D: Γ |- Δ), forall Γ1 Γ2,
  forall E F,  Γ = Γ1 ++ E→F :: Γ2 ->  Γ1 ++ Γ2 |- E::Δ.
  Proof.
  intro. intro. intro.
  induction D.

  (** AXIOM *)
  intros. subst.
  rewrite in_app_iff in H.
  destruct H. apply (LKId A).
  firstorder. firstorder.

  rewrite -> cons_single_app in H.
  apply in_app_or in H. destruct H.
  simpl in H. destruct H. subst.
  apply in_split in H0.
  remember (E :: Δ) as Δ'.
  destruct H0. destruct H. subst.
  replace (Γ1 ++ Γ2 |- E :: x ++ E → F :: x0) with ((Γ1 ++ Γ2) |- (E :: x) ++ E → F :: x0).
  apply LKImpR.
  apply (LKId E). firstorder. firstorder. try list_solve.
  firstorder.

  apply (LKId A).
  firstorder. firstorder.

  (** BOT *)
  intros.
  apply LKBot.
  subst.   apply in_app_or in H. destruct H.
  firstorder. rewrite cons_single_app in H.
  apply in_app_or in H. destruct H.
  simpl in H. destruct H. discriminate. firstorder.
  firstorder.

  (** IMPL *)
  intros.
  apply app_eq_app in H.
  destruct H.
  destruct H.
  destruct H.
  apply cons_eq_app in H0. destruct H0. destruct H0.
  injection H1. intros. subst.
  rewrite app_nil_r in *.
  assumption.

  destruct H0. destruct H0. subst.
  cut ((Γ0 ++ x0 ++ A → B :: Γ2) = ((Γ0 ++ x0) ++ A → B :: Γ2)).
  intros. rewrite H. apply LKImpL.

  rewrite app_assoc_reverse.
  apply IHD1 with F.
  rewrite app_assoc_reverse. simpl. try list_solve.

  pose (move_L_R).
  replace (A :: E :: Δ) with ([] ++ A :: [E] ++ Δ).
(*  pose (g ((Γ0 ++ x0) ++ Γ2) A  Δ [E] []).
 *)
  pose (l ((Γ0 ++ x0) ++ Γ2) A  Δ [E] []).
  apply l0.
  replace ([] ++ [E] ++ A :: Δ) with (E :: A :: Δ).
  rewrite app_assoc_reverse.
  apply IHD2 with F.
  try list_solve. try list_solve. try list_solve. try list_solve.

  destruct H.
  apply cons_eq_app in H0. destruct H0. destruct H0.
  injection H1. intros. subst.
  rewrite app_nil_r.
  assumption.

  destruct H0. destruct H0. subst.
  replace ((Γ1 ++ A → B :: x0) ++ Γ3) with ((Γ1) ++ A → B :: x0 ++ Γ3).
  apply LKImpL.
  replace (Γ1 ++ B :: x0 ++ Γ3) with ((Γ1 ++ B :: x0) ++ Γ3).
  apply IHD1 with F.
  try list_solve. try list_solve.

  pose (move_L_R).
  replace (A :: E :: Δ) with ([] ++ A :: [E] ++ Δ).
  pose (l ((Γ1 ++ x0 ++ Γ3)) A  Δ [E] []).
  apply l0.
  replace ([] ++ [E] ++ A :: Δ) with (E :: A :: Δ).
  rewrite app_assoc.
  apply IHD2 with F.
  try list_solve. try list_solve. try list_solve. try list_solve.

  (** IMPR *)
  intros.
  replace (Γ1 ++ Γ2 |- E :: Δ1 ++ A → B :: Δ2) with ((Γ1 ++ Γ2) |- (E :: Δ1) ++ A → B :: Δ2).
  apply LKImpR.
  replace (A :: Γ1 ++ Γ2 |- (E :: Δ1) ++ B :: Δ2) with ((A :: Γ1) ++ Γ2 |- (E) :: Δ1 ++ B :: Δ2).
  apply IHD with F.
  simpl. subst.
  try list_solve. try list_solve. try list_solve.
  Qed.

Lemma inv_ImpL2:
  forall Γ Δ (D: Γ |- Δ), forall Γ1 Γ2,
  forall E F,  Γ = Γ1 ++ (E→F) :: Γ2 ->  (Γ1 ++ F :: Γ2) |- Δ.
  Proof.
  intro. intro. intro.
  induction D.

  (** AXIOM *)
  intros. subst.
  rewrite in_app_iff in H.
  destruct H. apply (LKId A).
  firstorder. firstorder.

  rewrite -> cons_single_app in H.
  apply in_app_or in H. destruct H.
  simpl in H. destruct H. subst.
  apply in_split in H0.
  remember (E :: Δ) as Δ'.
  destruct H0. destruct H. subst.
  pose (move_R_L).
  pose (l (x ++ E → F :: x0) F Γ2 Γ1 []).
  replace (Γ1) with ([] ++ Γ1).
  apply l0. simpl.
  pose LKImpR.
  pose (l1 E F (F::Γ1 ++ Γ2) x x0).
  apply l2. apply (LKId F). firstorder. firstorder.
  trivial.
  firstorder.
  apply (LKId A).
  firstorder. firstorder.

  (** BOT *)
  intros.
  apply LKBot.
  subst.   apply in_app_or in H. destruct H.
  firstorder. rewrite cons_single_app in H.
  apply in_app_or in H. destruct H.
  simpl in H. destruct H. discriminate. firstorder.
  firstorder.

  (** IMPL *)
  intros.
  apply app_eq_app in H.
  destruct H.
  destruct H.
  destruct H.
  apply cons_eq_app in H0. destruct H0. destruct H0.
  injection H1. intros. subst.
  rewrite app_nil_r in *.
  assumption.

  destruct H0. destruct H0. subst.
  replace (Γ0 ++ F :: x0 ++ A → B :: Γ2 ) with ((Γ0 ++ F :: x0) ++ A → B :: Γ2).
  apply LKImpL.

  replace ((Γ0 ++ F :: x0) ++ B :: Γ2) with ((Γ0) ++ F :: x0 ++ B :: Γ2).
  apply IHD1 with E.
  try list_solve. try list_solve.

  replace ((Γ0 ++ F :: x0) ++ Γ2) with ((Γ0) ++ F :: x0 ++ Γ2).
  apply IHD2 with E.
  try list_solve. try list_solve. try list_solve.

  destruct H.
  apply cons_eq_app in H0. destruct H0. destruct H0.
  injection H1. intros. subst. rewrite app_nil_r.
  assumption.

  destruct H0. destruct H0. subst.
  replace ((Γ1 ++ A → B :: x0) ++ F :: Γ3 ) with ((Γ1) ++ A → B :: x0 ++ F :: Γ3).
  apply LKImpL.

  replace (Γ1 ++ B :: x0 ++ F :: Γ3) with ((Γ1 ++ B :: x0) ++ F :: Γ3).
  apply IHD1 with E. try list_solve. try list_solve.

  replace (Γ1 ++ x0 ++ F :: Γ3) with ((Γ1 ++ x0) ++ F :: Γ3).
  apply IHD2 with E. try list_solve. try list_solve. try list_solve.

  (** IMPR *)
  intros.
  subst. apply LKImpR.
  replace (A :: Γ1 ++ F :: Γ2) with ((A :: Γ1) ++ F :: Γ2).
  apply IHD with E. try list_solve. try list_solve.
  Qed.

Lemma inv_ImpR:
  forall Γ Δ (D: Γ |- Δ), forall Δ1 Δ2,
  forall X Y , Δ = Δ1++X→Y::Δ2 ->  (X::Γ) |- (Δ1++Y::Δ2).
  Proof.
  intro. intro. intro.
  induction D.
  intros. subst.

  apply in_app_iff in H0.
  destruct H0.
  apply (LKId A). firstorder. firstorder.
  simpl in H0. destruct H0.
  subst. pose LKImpL.
  apply in_split in H. destruct H. destruct H. subst.
  pose (l X Y (X :: x) x0 (Δ1 ++ Y :: Δ2)).
  apply l0. apply (LKId Y). firstorder. firstorder.
  apply (LKId X). firstorder. firstorder.

  apply (LKId A). firstorder. firstorder.

  intros.
  apply LKBot. firstorder.

  intros.
  replace (X :: Γ1 ++ A → B :: Γ2 |- Δ1 ++ Y :: Δ2)
     with ((X :: Γ1) ++ A → B :: Γ2 |- Δ1 ++ Y :: Δ2).
  apply LKImpL.
  apply IHD1. assumption.

  replace ((X :: Γ1) ++ Γ2 |- A :: Δ1 ++ Y :: Δ2)
     with ((X :: Γ1) ++ Γ2 |- (A :: Δ1) ++ Y :: Δ2).
  apply IHD2. subst. try list_solve. try list_solve. try list_solve.

  intros.
  apply app_eq_app in H.
  destruct H.
  destruct H.
  destruct H.
  apply cons_eq_app in H0.
  destruct H0.   destruct H0.
  injection H1. intros.
  subst. rewrite app_nil_r in *.
  assumption.

  destruct H0. destruct H0. subst.
  replace (X :: Γ |- Δ0 ++ Y :: x0 ++ A → B :: Δ2)
     with (X :: Γ |- (Δ0 ++ Y :: x0) ++ A → B :: Δ2).
  apply LKImpR.
  pose (move_L_L).
  replace (A :: X :: Γ) with ([] ++ A :: [X] ++ Γ).
  pose (l ((Δ0 ++ Y :: x0) ++ B :: Δ2) A Γ [X] []).
  apply l0. simpl.
  replace ((Δ0 ++ Y :: x0) ++ B :: Δ2)
     with ((Δ0) ++ Y :: (x0 ++ B :: Δ2)).
  eapply IHD.
  try list_solve. try list_solve. try list_solve. try list_solve.

  destruct H. subst. apply cons_eq_app in H0.
  destruct H0. destruct H. subst. injection H0.
  intros. subst. rewrite app_nil_r.
  assumption.

  destruct H. destruct H.
  subst. replace (X :: Γ |- (Δ1 ++ A → B :: x0) ++ Y :: Δ3)
            with (X :: Γ |- (Δ1) ++ A → B :: x0 ++ Y :: Δ3).
  apply LKImpR.
    pose (move_L_L).
  replace (A :: X :: Γ) with ([] ++ A :: [X] ++ Γ).
  pose (l (Δ1 ++ B :: x0 ++ Y :: Δ3) A Γ [X] []).
  apply l0. simpl.
  replace (X :: A :: Γ |- Δ1 ++ B :: x0 ++ Y :: Δ3)
     with (X :: A :: Γ |- (Δ1 ++ B :: x0) ++ Y :: Δ3).
  apply IHD.
  try list_solve. try list_solve. try list_solve. try list_solve.
  Qed.


  (* Any proposition is either atomic (including bottom) or is an implication *)
  Lemma imp_or_atomic:
    forall X,
      (exists m n : PropF, X = m → n) \/ (forall m' n' : PropF, X <> m' → n').
    Proof.
    intros. induction X.
    right. intros. discriminate.
    right. intros. discriminate.
    left. exists X1. exists X2. reflexivity.
    Qed.

  Lemma contraction_atomic_r:
    forall Γ Δ  (D: Γ |- Δ) X,
      (forall p q, X <> p → q) ->
       forall Δ1 Δ2 Δ3, Δ = Δ1 ++ X :: Δ2 ++ X :: Δ3 -> Γ |- (Δ1 ++ X :: Δ2 ++ Δ3).
    intro. intro. intro.
    induction D.
    intros. apply (LKId A). assumption. subst.
    apply in_app_iff in H0. destruct H0.
    firstorder. destruct H0. subst. apply in_app_iff. right. firstorder .
    apply in_app_iff in H0. destruct H0. apply in_app_iff. right. firstorder .
    simpl in H0. destruct H0. subst. apply in_app_iff. right. firstorder .
    apply in_app_iff. right. firstorder .

    intros. apply LKBot. assumption.

    intros. induction X. apply LKImpL.
    apply IHD1. firstorder. assumption.
    replace (A :: Δ1 ++ # p :: Δ2 ++ Δ3) with ((A :: Δ1) ++ # p :: Δ2 ++ Δ3).
    apply IHD2. firstorder. rewrite H0. list_solve. list_solve.

    apply LKImpL.
    apply IHD1. firstorder. assumption.
    replace (A :: Δ1 ++ ⊥ :: Δ2 ++ Δ3) with ((A :: Δ1) ++ ⊥ :: Δ2 ++ Δ3).
    apply IHD2. firstorder. rewrite H0. list_solve. list_solve.
    pose (H X1 X2). firstorder.

    intros.

    apply app_eq_app in H0.
    destruct H0. destruct H0. destruct H0.
    apply cons_eq_app in H1.
    destruct H1. destruct H1.
    injection H2. intros. pose (H A B).
    rewrite H4 in n. firstorder.

    destruct H1. destruct H1. apply app_eq_app in H2.
    destruct H2. destruct H2. destruct H2.
    apply cons_eq_app in H3. destruct H3. destruct H3.
    injection H4. intros. pose (H A B).
    rewrite H6 in n. firstorder.

    destruct H3. destruct H3. subst.
    cut ((Δ0 ++ X :: x0) ++ B :: x2 ++ X :: Δ4 =
         Δ0 ++ X :: (x0 ++ B :: x2) ++ X :: Δ4). intro.
    pose (IHD X H Δ0 (x0 ++ B :: x2) Δ4 H0).
    replace (Δ0 ++ X :: (x0 ++ A → B :: x2) ++ Δ4)
       with ((Δ0 ++ X :: x0) ++ A → B :: x2 ++ Δ4).
    apply LKImpR.
    replace ((Δ0 ++ X :: x0) ++ B :: x2 ++ Δ4)
       with (Δ0 ++ X :: (x0 ++ B :: x2) ++ Δ4).
    assumption. list_solve. list_solve.  list_solve.

    destruct H2.
    apply cons_eq_app in H3.
    destruct H3. destruct H3.
    injection H4. intros. pose (H A B).
    rewrite H6 in n. firstorder.

    destruct H3. destruct H3. subst.
    replace ( Δ0 ++ X :: Δ3 ++ x2 ++ A → B :: Δ2)
       with ((Δ0 ++ X :: Δ3 ++ x2) ++ A → B :: Δ2).
    apply LKImpR.
    replace ((Δ0 ++ X :: Δ3 ++ x2) ++ B :: Δ2)
       with ((Δ0) ++ X :: Δ3 ++ x2 ++ B :: Δ2).
    apply IHD. assumption.

    list_solve. list_solve. list_solve. list_solve.

    apply cons_eq_app in H1. destruct H1. destruct H1.
    injection H2. intros. pose (H A B).
    rewrite H4 in n.
    firstorder.

    destruct H1. destruct H1. subst.
    replace ((Δ1 ++ A → B :: x0) ++ (X :: Δ3) ++ Δ4)
       with (Δ1 ++ A → B :: x0 ++ (X :: Δ3) ++ Δ4).
    apply LKImpR.
    replace (Δ1 ++ B :: x0 ++ (X :: Δ3) ++ Δ4)
       with ((Δ1 ++ B :: x0) ++ X :: Δ3 ++ Δ4).
    apply IHD. assumption.

    list_solve. list_solve. list_solve.
    Qed.

  Lemma contraction_atomic_l:
    forall Γ Δ  (D: LK Γ Δ) X, (forall p q, X <> p → q) -> forall Γ1 Γ2 Γ3, Γ = Γ1 ++ X :: Γ2 ++ X :: Γ3
        -> LK (Γ1 ++ X :: Γ2 ++ Γ3) Δ.

    intro. intro. intro. induction D.

    intros. subst. rewrite !in_app_iff in H. apply (LKId A).
    destruct H. firstorder. firstorder. rewrite <- H. firstorder.
    rewrite !in_app_iff in H.  destruct H. rewrite cons_single_app.
    rewrite in_app_iff. right.
    firstorder. firstorder. rewrite <- H. firstorder.
    rewrite in_app_iff. right. firstorder.
    firstorder.

    intros.
    subst. apply LKBot.   rewrite !in_app_iff in H.  destruct H.
    firstorder. firstorder. rewrite <- H. firstorder.
    rewrite !in_app_iff in H.  destruct H.
    rewrite in_app_iff. right.
    firstorder. firstorder. rewrite <- H. firstorder.
    rewrite in_app_iff. right.
    firstorder.

    intros.
    apply app_eq_app in H0.
    destruct H0. destruct H0. destruct H0.
    apply cons_eq_app in H1. destruct H1. destruct H1.
    injection H2. intros. pose (H A B). rewrite H4 in n. firstorder.

     destruct H1. destruct H1.
     apply app_eq_app in H2.
     destruct H2. destruct H2. destruct H2.
     apply cons_eq_app in H3. destruct H3. destruct H3.
     injection H4. intros. pose (H A B). rewrite H6 in n. firstorder.

     destruct H3. destruct H3. subst.
     replace (Γ0 ++ X :: (x0 ++ A → B :: x2) ++ Γ4)
        with ((Γ0 ++ X :: x0) ++ A → B :: x2 ++ Γ4).
     apply LKImpL.
     replace ((Γ0 ++ X :: x0) ++ B :: x2 ++ Γ4)
        with ((Γ0) ++ X :: (x0 ++ B :: x2) ++ Γ4).
     apply IHD1. assumption. try list_solve. try list_solve.
     replace ((Γ0 ++ X :: x0) ++ x2 ++ Γ4)
        with ((Γ0) ++ X :: (x0 ++ x2) ++ Γ4).
     apply IHD2. assumption. try list_solve. try list_solve. try list_solve.

     destruct H2. apply cons_eq_app in H3.
     destruct H3. destruct H3.
     injection H4. intros. pose (H A B). rewrite H6 in n. firstorder.

     destruct H3. destruct H3. subst.
     replace (Γ0 ++ X :: Γ3 ++ x2 ++ A → B :: Γ2)
        with ((Γ0 ++ X :: Γ3 ++ x2) ++ A → B :: Γ2).
     apply LKImpL.
     replace ((Γ0 ++ X :: Γ3 ++ x2) ++ B :: Γ2)
        with ((Γ0) ++ X :: (Γ3) ++ x2 ++ B :: Γ2).
     apply IHD1. assumption. try list_solve. try list_solve.
     try list_solve. try list_solve.
     replace ((Γ0 ++ X :: Γ3 ++ x2) ++ Γ2)
        with ((Γ0) ++ X :: (Γ3) ++ x2 ++ Γ2).
     apply IHD2. assumption. try list_solve. try list_solve.
     try list_solve.

     destruct H0. apply cons_eq_app in H1.
     destruct H1. destruct H1.
     injection H2. intros. pose (H A B). rewrite H4 in n. firstorder.
     destruct H1. destruct H1. subst.
     replace ((Γ1 ++ A → B :: x0) ++ X :: Γ3 ++ Γ4)
        with ((Γ1) ++ A → B :: x0 ++ X :: Γ3 ++ Γ4).
     apply LKImpL.
     replace (Γ1 ++ B :: x0 ++ X :: Γ3 ++ Γ4)
        with ((Γ1 ++ B :: x0) ++ X :: Γ3 ++ Γ4).
     apply IHD1. assumption. try list_solve. try list_solve.
     replace (Γ1 ++ x0 ++ X :: Γ3 ++ Γ4)
        with ((Γ1 ++ x0) ++ X :: Γ3 ++ Γ4).
     apply IHD2. assumption. try list_solve. try list_solve.
     try list_solve.

     intros.
     subst. apply LKImpR.
     replace (A :: Γ1 ++ X :: Γ2 ++ Γ3)
        with ((A :: Γ1) ++ X :: Γ2 ++ Γ3).
     apply IHD. assumption. try list_solve. try list_solve.
     Qed.

  (* is_sub_formula_of p q if q is a sub formula of p. It is written this way because
     it makes instances of is_sub_formula_of provable with the firstorder tactic. *)
Fixpoint  is_sub_formula_of p q:=
    match p with
      | # q' => False
      | Bot => False
      | p' → q' => q = p' \/ q = q'
      end.

Lemma contraction_helper:
    forall X, (forall X', is_sub_formula_of X X' ->
    (forall Γ Δ (D: LK Γ Δ), forall Γ1 Γ2 Γ3, Γ = Γ1 ++ X' :: Γ2 ++ X' :: Γ3
        -> LK (Γ1 ++ X' :: Γ2 ++ Γ3 ) Δ) /\
    (forall Γ Δ (D: LK Γ Δ), forall Δ1 Δ2 Δ3, Δ = Δ1 ++ X' :: Δ2 ++ X' :: Δ3
        -> LK Γ (Δ1 ++ X' :: Δ2 ++ Δ3))) ->
    ((forall Γ Δ (D: LK Γ Δ), forall Γ1 Γ2 Γ3, Γ = Γ1 ++ X :: Γ2 ++ X :: Γ3
        -> LK (Γ1 ++ X :: Γ2 ++ Γ3 ) Δ) /\
    (forall Γ Δ (D: LK Γ Δ), forall Δ1 Δ2 Δ3, Δ = Δ1 ++ X :: Δ2 ++ X :: Δ3
        -> LK Γ (Δ1 ++ X :: Δ2 ++ Δ3))).
    Proof.
    intros. split.
    intro. intro. intro. induction D.

    intros. subst.
    rewrite !in_app_iff in H0. apply (LKId A).
    destruct H0. firstorder. firstorder. rewrite <- H0. firstorder.
    rewrite !in_app_iff in H0.  destruct H0. rewrite cons_single_app.
    rewrite in_app_iff. right.
    firstorder. firstorder. rewrite <- H0. firstorder.
    rewrite in_app_iff. right. firstorder.
    firstorder.

    intros. subst.
  rewrite !in_app_iff in H0. apply (LKBot ).
    destruct H0. firstorder. firstorder. rewrite <- H0. firstorder.
    rewrite !in_app_iff in H0.  destruct H0. rewrite cons_single_app.
    rewrite in_app_iff. right.
    firstorder. firstorder. rewrite <- H0. firstorder.
    rewrite in_app_iff. right. firstorder.

    intros.
    pose LKImpL. pose (l A B Γ1 Γ2 Δ D1 D2).
    rewrite H0 in l0.
    pose (imp_or_atomic X). destruct o.
    destruct H1. destruct H1.
    subst. pose inv_ImpL2.
  cut ( Γ0 ++ x → x0 :: Γ3 ++ x → x0 :: Γ4 = Γ0 ++ x → x0 :: Γ3 ++ x → x0 :: Γ4). intro.
  pose (l1 (Γ0 ++ x → x0 :: Γ3 ++ x → x0 :: Γ4) Δ l0 Γ0 (Γ3 ++ x → x0 :: Γ4) x x0 H1).
  simpl in l2. cut (Γ0 ++ x0 :: Γ3 ++ x → x0 :: Γ4 = (Γ0 ++ x0 :: Γ3) ++ x → x0 :: Γ4). intro.
  pose (l1 (Γ0 ++ x0 :: Γ3 ++ x → x0 :: Γ4) Δ l2 (Γ0 ++ x0 :: Γ3) Γ4 x x0 H2).
  pose inv_ImpL1.
  pose (l4 (Γ0 ++ x → x0 :: Γ3 ++ x → x0 :: Γ4) Δ l0 Γ0 (Γ3 ++ x → x0 :: Γ4) x x0 H1).
  cut (Γ0 ++ Γ3 ++ x → x0 :: Γ4 = (Γ0 ++ Γ3) ++ x → x0 :: Γ4). intro.
  pose (l4 (Γ0 ++ Γ3 ++ x → x0 :: Γ4) (x :: Δ) l5 (Γ0 ++ Γ3) Γ4 x x0 H3).
  cut (is_sub_formula_of (x → x0) x0). intro.
  cut ((Γ0 ++ x0 :: Γ3) ++ x0 :: Γ4 = Γ0 ++ x0 :: Γ3 ++ x0 :: Γ4). intro.
  pose (H x0 H4). destruct a. simpl in l3.
  pose (H6 ((Γ0 ++ x0 :: Γ3) ++ x0 :: Γ4)  Δ l3 Γ0 Γ3 Γ4 H5).
  cut (is_sub_formula_of (x → x0) x). intro.
  pose (H x H8). destruct a. simpl in l6.
  cut (x :: x :: Δ = [] ++ x :: [] ++ x :: Δ ). intro.
  pose (H10 ((Γ0 ++ Γ3) ++ Γ4)  (x :: x :: Δ) l6   [] [] Δ H11).
  replace ([] ++ x :: [] ++ Δ) with (x :: Δ) in l8.
  replace ((Γ0 ++ Γ3) ++ Γ4) with (Γ0 ++ Γ3 ++ Γ4) in l8.
  pose (l x x0 Γ0 (Γ3 ++ Γ4)  Δ l7 l8). simpl in l9.
    assumption. firstorder. list_solve. list_solve.
    firstorder. list_solve. firstorder. list_solve.
    list_solve. list_solve.

    cut (X = Bot \/ exists p, X = # p). intros.

    pose LKImpL.
    pose (l A B Γ1 Γ2 Δ D1 D2).
    rewrite H0 in l2.
    destruct H2. subst.
    pose contraction_atomic_l. cut (Γ0 ++ ⊥ :: Γ3 ++ ⊥ :: Γ4 = Γ0 ++ ⊥ :: Γ3 ++ ⊥ :: Γ4). intro.
    pose (l3 (Γ0 ++ ⊥ :: Γ3 ++ ⊥ :: Γ4) Δ l0 Bot H1 Γ0 Γ3 Γ4 H2).
    assumption. trivial.

    destruct H2. subst.
    pose contraction_atomic_l. cut ( Γ0 ++ # x :: Γ3 ++ # x :: Γ4 =  Γ0 ++ # x :: Γ3 ++ # x :: Γ4). intro.
    pose (l3 ( Γ0 ++ # x :: Γ3 ++ # x :: Γ4) Δ l0 # x H1 Γ0 Γ3 Γ4 H2). assumption.
     trivial. induction X. right. exists p. trivial. left. trivial.
    destruct H1 with X1 X2. trivial.

    intros. apply LKImpR.
    replace (A :: Γ1 ++ X :: Γ2 ++ Γ3 )
       with ((A :: Γ1) ++ X :: Γ2 ++ Γ3 ).
    apply IHD . subst. list_solve. list_solve.

    intro. intro. intro.
    induction D.
      intros. subst. rewrite !in_app_iff in H1. apply (LKId A).
    destruct H1. firstorder. firstorder. destruct H1. firstorder.
    simpl in H1.  destruct H1. rewrite H1. firstorder.
    apply in_app_iff in H1. destruct H1. apply in_app_iff. right. firstorder.
    simpl in H1. destruct H1. subst. firstorder. apply in_app_iff. right. firstorder.

    intros. apply LKBot. assumption.

    intros.
    apply LKImpL. apply IHD1. assumption.
    replace (A :: Δ1 ++ X :: Δ2 ++ Δ3)
       with ((A :: Δ1) ++ X :: Δ2 ++ Δ3).
    apply IHD2. subst. list_solve. list_solve.

    intros.
    pose LKImpR.
    pose (l A B Γ Δ1 Δ2 D).
    rewrite H0 in l0.
    pose (imp_or_atomic X). destruct o.
    destruct H1. destruct H1.
    subst. pose (inv_ImpR).
    cut (Δ0 ++ x → x0 :: Δ3 ++ x → x0 :: Δ4 = Δ0 ++ x → x0 :: Δ3 ++ x → x0 :: Δ4). intro.
    pose (l1 Γ (Δ0 ++ x → x0 :: Δ3 ++ x → x0 :: Δ4) l0 Δ0 (Δ3 ++  x → x0 :: Δ4) x x0 H1).
    cut (Δ0 ++ x0 :: Δ3 ++ x → x0 :: Δ4 = (Δ0 ++ x0 :: Δ3) ++ x → x0 :: Δ4). intro.
    pose (l1 (x :: Γ) (Δ0 ++ x0 :: Δ3 ++ x → x0 :: Δ4) l2 (Δ0 ++ x0 :: Δ3) Δ4 x x0 H2).
    apply LKImpR. cut (is_sub_formula_of (x → x0) x). intro.
    pose (H x H3).  destruct a.
    cut (x :: x :: Γ = [] ++ x :: [] ++ x :: Γ). intro.
    pose (H4 (x :: x :: Γ) ((Δ0 ++ x0 :: Δ3) ++ x0 :: Δ4) l3 [] [] Γ H6).
    cut (is_sub_formula_of (x → x0) x0). intro. pose (H x0 H7).
    cut ((Δ0 ++ x0 :: Δ3) ++ x0 :: Δ4 = Δ0 ++ x0 :: Δ3 ++ x0 :: Δ4). intro.
    destruct a.
    pose (H10 ([] ++ x :: [] ++ Γ) ((Δ0 ++ x0 :: Δ3) ++ x0 :: Δ4) l4
           Δ0 Δ3 Δ4 H8).
    assumption. list_solve. firstorder. list_solve.
    firstorder. list_solve. list_solve.

    cut (X = Bot \/ exists p, X = # p). intros. destruct H2.
    pose LKImpR. pose (l1 A B Γ Δ1 Δ2 D).
    subst. firstorder. pose (contraction_atomic_r).
    cut (Δ0 ++ ⊥ :: Δ3 ++ ⊥ :: Δ4 = Δ0 ++ ⊥ :: Δ3 ++ ⊥ :: Δ4). intro.
    pose (l3 Γ (Δ0 ++ ⊥ :: Δ3 ++ ⊥ :: Δ4) l0 ⊥ H1 Δ0 Δ3 Δ4 H2).
    assumption. trivial.

    pose LKImpR. pose (l1 A B Γ Δ1 Δ2 D).
    subst. firstorder. pose (contraction_atomic_r). subst.
    cut (Δ0 ++ # x :: Δ3 ++ # x :: Δ4 = Δ0 ++ # x :: Δ3 ++ # x :: Δ4). intro.
    pose (l3 Γ (Δ0 ++ # x :: Δ3 ++ # x :: Δ4) l0 # x H1 Δ0 Δ3 Δ4 H2).
    assumption. trivial.

    induction X. right. exists p. trivial. left. trivial.
    pose (H1 X1 X2). firstorder.
    Qed.



  Theorem contraction:
    forall X,
      ((forall Γ Δ (D: LK Γ Δ), forall Γ1 Γ2 Γ3, Γ = Γ1 ++ X :: Γ2 ++ X :: Γ3
        -> LK (Γ1 ++ X :: Γ2 ++ Γ3 ) Δ) /\
    (forall Γ Δ (D: LK Γ Δ), forall Δ1 Δ2 Δ3, Δ = Δ1 ++ X :: Δ2 ++ X :: Δ3
        -> LK Γ (Δ1 ++ X :: Δ2 ++ Δ3))).
    Proof.
    intro.
    induction X.
    split. intros. subst.
    pose contraction_atomic_l.
    cut ((forall p0 q : PropF, # p <> p0 → q)). intro.
    cut ( Γ1 ++ # p :: Γ2 ++ # p :: Γ3 = Γ1 ++ # p :: Γ2 ++ # p :: Γ3). intro.
    pose (l (Γ1 ++ # p :: Γ2 ++ # p :: Γ3) Δ D (# p) H Γ1 Γ2 Γ3 H0). assumption.
    trivial. intros. discriminate.

    intros. subst.
    pose contraction_atomic_r.
    cut ((forall p0 q : PropF, # p <> p0 → q)). intro.
    cut (Δ1 ++ # p :: Δ2 ++ # p :: Δ3 = Δ1 ++ # p :: Δ2 ++ # p :: Δ3). intro.
    pose (l Γ (Δ1 ++ # p :: Δ2 ++ # p :: Δ3) D # p H Δ1 Δ2 Δ3 H0).
    assumption. trivial. discriminate.

    split. intros. apply LKBot. firstorder.
    intros. subst.
    pose contraction_atomic_r.
    cut ((forall p0 q : PropF, ⊥ <> p0 → q)). intro.
    cut (Δ1 ++ ⊥ :: Δ2 ++ ⊥ :: Δ3 = Δ1 ++ ⊥ :: Δ2 ++ ⊥ :: Δ3). intro.
    pose (l Γ (Δ1 ++ ⊥ :: Δ2 ++ ⊥ :: Δ3) D ⊥ H Δ1 Δ2 Δ3 H0).
    assumption. trivial. discriminate.

    split.
    intros. subst.
    pose (contraction_helper).
    cut (is_sub_formula_of (X1 → X2) X1). intro.
    pose (a (X1 → X2)).
    cut ((forall X' : PropF,
        is_sub_formula_of (X1 → X2) X' ->
        (forall Γ Δ : list PropF,
         Γ |- Δ ->
         forall Γ1 Γ2 Γ3 : list PropF,
         Γ = Γ1 ++ X' :: Γ2 ++ X' :: Γ3 -> Γ1 ++ X' :: Γ2 ++ Γ3 |- Δ) /\
        (forall Γ Δ : list PropF,
         Γ |- Δ ->
         forall Δ1 Δ2 Δ3 : list PropF,
         Δ = Δ1 ++ X' :: Δ2 ++ X' :: Δ3 -> Γ |- Δ1 ++ X' :: Δ2 ++ Δ3))).
    intro. pose (a0 H0). destruct a1.
    cut (Γ1 ++ X1 → X2 :: Γ2 ++ X1 → X2 :: Γ3 = Γ1 ++ X1 → X2 :: Γ2 ++ X1 → X2 :: Γ3). intro.
    pose (H1 (Γ1 ++ X1 → X2 :: Γ2 ++ X1 → X2 :: Γ3) Δ D Γ1 Γ2 Γ3 H3). assumption.
    trivial. intros. split.
    intros. simpl in H0.
    destruct H0. subst.
    destruct IHX1. cut (Γ0 ++ X1 :: Γ4 ++ X1 :: Γ5 = Γ0 ++ X1 :: Γ4 ++ X1 :: Γ5). intro.
    pose (H0 (Γ0 ++ X1 :: Γ4 ++ X1 :: Γ5) Δ0 H1 Γ0 Γ4 Γ5 H3). assumption.
    trivial.
    subst. destruct IHX2.
    cut (Γ0 ++ X2 :: Γ4 ++ X2 :: Γ5 = Γ0 ++ X2 :: Γ4 ++ X2 :: Γ5). intro.
    pose (H0 (Γ0 ++ X2 :: Γ4 ++ X2 :: Γ5) Δ0 H1 Γ0 Γ4 Γ5 H3). assumption.
    trivial.

    intros.
    subst.
    cut (X' = X1 \/ X' = X2).
    intro. destruct H2. subst. destruct IHX1.
    eapply H3 with (Δ1 ++ X1 :: Δ2 ++ X1 :: Δ3).
    assumption. trivial.
    subst. destruct IHX2.
    eapply H3 with (Δ1 ++ X2 :: Δ2 ++ X2 :: Δ3).
    assumption. trivial.
    firstorder.
    firstorder.

    intros. subst.
    cut ((forall X' : PropF,
      is_sub_formula_of (X1 → X2) X' ->
        (forall Γ Δ : list PropF,
         Γ |- Δ ->
         forall Γ1 Γ2 Γ3 : list PropF,
         Γ = Γ1 ++ X' :: Γ2 ++ X' :: Γ3 -> Γ1 ++ X' :: Γ2 ++ Γ3 |- Δ) /\
        (forall Γ Δ : list PropF,
         Γ |- Δ ->
         forall Δ1 Δ2 Δ3 : list PropF,
         Δ = Δ1 ++ X' :: Δ2 ++ X' :: Δ3 -> Γ |- Δ1 ++ X' :: Δ2 ++ Δ3))). intro.
    pose (contraction_helper (X1→ X2) H).
    destruct a.
    cut (Δ1 ++ X1 → X2 :: Δ2 ++ X1 → X2 :: Δ3 = Δ1 ++ X1 → X2 :: Δ2 ++ X1 → X2 :: Δ3). intro.
    pose (H1 Γ (Δ1 ++ X1 → X2 :: Δ2 ++ X1 → X2 :: Δ3) D Δ1 Δ2 Δ3 H2). assumption. trivial.

    intros. simpl in H.
    destruct H. subst. split.
    destruct IHX1. intros. subst.
    cut (Γ1 ++ X1 :: Γ2 ++ X1 :: Γ3 = Γ1 ++ X1 :: Γ2 ++ X1 :: Γ3). intro.
    pose (H (Γ1 ++ X1 :: Γ2 ++ X1 :: Γ3) Δ H1 Γ1 Γ2 Γ3 H2). assumption.
    trivial. intros.
    subst.  destruct IHX1.
    cut (Δ0 ++ X1 :: Δ4 ++ X1 :: Δ5 = Δ0 ++ X1 :: Δ4 ++ X1 :: Δ5). intro.
    pose (H1 Γ0 (Δ0 ++ X1 :: Δ4 ++ X1 :: Δ5) H Δ0 Δ4 Δ5 H2). assumption.
    trivial.

    split.
    intros. subst. destruct IHX2. eapply H with (Γ1 ++ X2 :: Γ2 ++ X2 :: Γ3).
    assumption. trivial.

    intros. subst. destruct IHX2. eapply H1 with (Δ0 ++ X2 :: Δ4 ++ X2 :: Δ5).
    assumption. trivial.
    Qed.


    Lemma cut_gax:
      forall (A A0 A1 : PropF) (L1 L2 : list PropF), In A0 L1 -> In A0 ([A] ++ L2)
          -> In A1 L2 -> In A1 ([A] ++ L1) -> exists B, In  B L1 /\ In  B L2.
    Proof.
    intros. apply in_app_iff in H0. inversion H0. apply in_app_iff in H2. inversion H2.
    simpl in H3. simpl in H4. inversion H3. inversion H4. rewrite -> H5 in H6. rewrite -> H6 in H.
    cut (In  A1 L1 /\ In  A1 L2). intro. exists A1. assumption. auto.
    firstorder. firstorder.
    cut (In  A1 L1 /\ In  A1 L2). intro. exists A1. assumption. auto.
    cut (In  A0 L1 /\ In  A0 L2). intro. exists A0. assumption. auto.
    Qed.

Theorem cut_elimination2:
forall  Γ1 Δ1 Γ2 Δ2 (D: LK Γ1 Δ1) (D1: LK Γ2 Δ2),
forall (A : PropF), Γ2 = [A] ++ Γ1 -> Δ1 = [A] ++ Δ2 -> Γ1 |- Δ2.
  intro. intro. intro. intro. intro. intro.
  induction D. induction D1.

  (* Axiom, Axiom *)
  intros. subst. pose cut_gax. pose (e A1 A A0 Γ Δ0 H H0 H2 H1).
  inversion e0. apply (LKId x). firstorder. firstorder.

  (* Axiom, Bot *)
  intros. subst. apply in_app_iff in H1. inversion H1. simpl in H2. firstorder.
  rewrite -> H0 in H1. rewrite -> H1 in H. apply LKBot. assumption.
  simpl in H0. apply (LKId A). assumption. assumption. rewrite -> H0 in H2. rewrite -> H2 in H.
  apply LKBot. assumption. apply LKBot. assumption. apply LKBot. assumption.

  (* Axiom, ImpL *)

  intros.
  subst.
  rewrite <- cons_single_app in H0.
  simpl in H0. destruct H0. subst.
  apply app_eq_app in H1. subst.

  destruct H1. destruct H0. destruct H0.
  subst.
  rewrite in_app_iff in H. destruct H. apply in_split in H.
  destruct H. destruct H. subst.  apply LKImpL.
  replace (([A] ++ x0 ++ A :: x1) ++ B :: Γ2)
  with ([] ++ A::x0 ++ A:: (x1 ++ B :: Γ2)) in D1_1.
  pose (contraction A). destruct a.
  cut ([] ++ A :: x0 ++ A :: x1 ++ B :: Γ2 =
  [] ++ A :: x0 ++ A :: x1 ++ B :: Γ2). intro.
  pose (H ([] ++ A :: x0 ++ A :: x1 ++ B :: Γ2) Δ0 D1_1 [] x0 (x1 ++ B :: Γ2) H1).
  replace ((x0 ++ A :: x1) ++ B :: Γ2) with ([] ++ x0 ++ A :: (x1 ++ B :: Γ2)).
  apply move_R_L. assumption. try list_solve. try list_solve. try list_solve.

  replace (([A] ++ x0 ++ A :: x1) ++ Γ2)
  with ([] ++ A::x0 ++ A:: (x1 ++ Γ2)) in D1_2.
  cut ([] ++ A :: x0 ++ A :: x1 ++ Γ2 =
  [] ++ A :: x0 ++ A :: x1 ++ Γ2). intro.
  pose (contraction A). destruct a.
  pose (H0 ([] ++ A :: x0 ++ A :: x1 ++ Γ2) (A0 :: Δ0) D1_2 [] x0 (x1 ++ Γ2) H).
  replace ((x0 ++ A :: x1) ++ Γ2) with ([] ++ x0 ++ A :: (x1 ++  Γ2)).
  apply move_R_L. assumption. try list_solve. try list_solve. try list_solve.

  simpl in H. destruct H. subst. pose LKImpL. pose (l A0 B ([A0 → B] ++ x) Γ2 Δ0 D1_1 D1_2).
  replace (([A0 → B] ++ x) ++ A0 → B :: Γ2)
  with ([] ++ A0 → B :: x ++ A0 → B :: Γ2) in l0.
  cut ([] ++ A0 → B :: x ++ A0 → B :: Γ2 = [] ++ A0 → B :: x ++ A0 → B :: Γ2). intro.
  pose (contraction (A0 → B)). destruct a.
  pose (H0 ( [] ++ A0 → B :: x ++ A0 → B :: Γ2) Δ0 l0 [] x Γ2 H).
  replace (x ++ A0 → B :: Γ2) with ([] ++ x ++ A0 → B :: Γ2).
  apply move_R_L. assumption.  try list_solve. try list_solve.  try list_solve.

  apply in_split in H.
  destruct H. destruct H. subst. pose LKImpL.
  pose (l A0 B ([A] ++ x) (x0 ++ A :: x1) Δ0 D1_1 D1_2).
  replace (([A] ++ x) ++ A0 → B :: x0 ++ A :: x1)
  with ([] ++ A :: (x ++ A0 → B :: x0) ++ A :: x1) in l0.
  cut ([] ++ A :: (x ++ A0 → B :: x0) ++ A :: x1 =
  [] ++ A :: (x ++ A0 → B :: x0) ++ A :: x1). intro.
  pose (contraction A). destruct a.
  pose (H0 ([] ++ A :: (x ++ A0 → B :: x0) ++ A :: x1) Δ0 l0 [] (x ++ A0 → B :: x0) x1 H).
  pose move_R_L. pose (l2 Δ0 A x1 (x ++ A0 → B :: x0) [] l1). simpl in l3.
  replace ((x ++ A0 → B :: x0) ++ A :: x1)
  with (x ++ A0 → B :: x0 ++ A :: x1) in l3.
  assumption.
  try list_solve. try list_solve. try list_solve.

  destruct H0. apply cons_eq_app in H1. destruct H1. destruct H1. subst.
  rewrite app_nil_r in H0. subst.
  simpl in H. destruct H. subst. pose LKImpL.
  pose (l A0 B [A0 → B] Γ2 Δ0 D1_1 D1_2).
  replace ([A0 → B] ++ A0 → B :: Γ2) with ([] ++ A0 → B :: [] ++ A0 → B :: Γ2) in l0.
  cut ([] ++ A0 → B :: [] ++ A0 → B :: Γ2 = [] ++ A0 → B :: [] ++ A0 → B :: Γ2). intro.
  pose (contraction (A0 → B)). destruct a.
  pose (H0 ([] ++ A0 → B :: [] ++ A0 → B :: Γ2) Δ0 l0 [] [] Γ2 H). simpl in l1.
  assumption. list_solve. list_solve.

  apply in_split in H. destruct H. destruct H. subst.
  replace (A0 → B :: x ++ A :: x0)
  with ([] ++ A0 → B :: (x ++ A :: x0)).
  apply LKImpL.
  cut ([] ++ A :: (B :: x) ++ A :: x0 = [] ++ A :: (B :: x) ++ A :: x0). intro.
  pose (contraction A). destruct a.
  pose (H0 ([] ++ A :: (B :: x) ++ A :: x0) Δ0 D1_1 [] (B :: x) x0 H).
  replace ([] ++ A :: (B :: x) ++ x0)
  with ([] ++ A :: B :: x ++ x0) in l.
  pose move_R_L. pose (l0 Δ0 A x0 (B :: x) [] l).
  assumption. list_solve. list_solve.

  pose (contraction A). destruct a.
  replace ([A] ++ B :: x ++ A :: x0 )
  with ([] ++ A :: (B :: x) ++ A :: x0 ).
  cut ([] ++ A :: x ++ A :: x0 = [] ++ A :: x ++ A :: x0). intro.
  replace ( [A] ++ x ++ A :: x0 )
  with ( [] ++ A :: x ++ A :: x0 ) in D1_2.
  pose (H ([] ++ A :: x ++ A :: x0) (A0 :: Δ0) D1_2 [] x x0 H1).
  apply move_R_L. assumption. list_solve. list_solve. list_solve.

  destruct H1. destruct H1.
  subst. pose LKImpL.
  pose (l A0 B Γ1  (x0 ++ Γ ) Δ0 D1_1 D1_2).
  replace (Γ1 ++ A0 → B :: x0 ++ Γ)
  with ((Γ1 ++ A0 → B :: x0) ++ Γ ) in l0.
  rewrite <- H0 in l0. apply in_split in H.
  destruct H. destruct H. subst.
  pose (contraction A). destruct a.
  replace ([A] ++ x ++ A :: x1)
  with ([] ++ A :: x ++ A :: x1) in l0.
  cut ([] ++ A :: x ++ A :: x1 = [] ++ A :: x ++ A :: x1). intro.
  pose (H ([] ++ A :: x ++ A :: x1) Δ0 l0 [] x x1 H2).
  replace (x ++ A :: x1) with ([] ++ x ++ A :: x1).
  apply move_R_L. assumption.
  list_solve. list_solve. list_solve. list_solve.
  
  apply (LKId A). assumption. assumption.

 (* Axiom, ImpR *)

  intros. subst.
  apply in_app_iff in H0.
  destruct H0. simpl in H0. destruct H0.
  subst. apply LKImpR.
  apply in_split in H. destruct H. destruct H.
  subst. pose (contraction A). destruct a.
  replace ( A0 :: [A] ++ x ++ A :: x0)
     with ( [A0] ++ A :: x ++ A :: x0) in D1.
  cut ([A0] ++ A :: x ++ A :: x0 = [A0] ++ A :: x ++ A :: x0). intro.
  pose (H ([A0] ++ A :: x ++ A :: x0) (Δ1 ++ B :: Δ2) D1 [A0] x x0 H1).
  replace (A0 :: x ++ A :: x0)
     with ([A0] ++ x ++ A :: x0).
  apply move_R_L. assumption.
  list_solve. list_solve. list_solve. firstorder.

  apply in_app_iff in H0. destruct H0.
  apply (LKId A). assumption. firstorder.
  apply (LKId A). assumption. firstorder. subst. firstorder.

  (* Bot *)

  intros.
  apply LKBot. firstorder. 

  induction D1. 
  (* Left, Axiom *)

  intros.
  subst.

  apply in_app_iff in H.
  destruct H. simpl in H. destruct H.
  subst. pose LKImpL.
  pose (l A B  Γ1 Γ0 ([A0] ++ Δ0) D2 D3).
  apply in_split in H0.
  destruct H0. destruct H.
  subst.
  pose (contraction A0). destruct a.
  replace ([A0] ++ x ++ A0 :: x0) with ([] ++ A0 :: x ++ A0 :: x0) in l.
  cut (([] ++ A0 :: x ++ A0 :: x0) = ([] ++ A0 :: x ++ A0 :: x0)). intro.
  pose (H0 (Γ1 ++ A → B :: Γ0) ([] ++ A0 :: x ++ A0 :: x0) l0 [] x x0 H1).
  replace (x ++ A0 :: x0) with ([] ++ x ++ A0 :: x0).
  apply move_R_R. assumption.
  list_solve. list_solve. list_solve. firstorder.

  apply (LKId A0).
  apply in_app_iff in H. destruct H.
  firstorder. firstorder.  subst. firstorder. 
  firstorder. 

  (* Left, Bot *)
  intros. subst. apply in_app_iff in H.
  destruct H. simpl in H. destruct H.
  subst. admit. firstorder.
  apply LKBot. assumption.

  (* Left, Left *)
  intros.
  eapply IHD1_1. intros. eapply IHD1.
  cut (A1 :: Γ1 ++ A→B :: Γ0 |- A1 :: Δ). intro.

   

  admit.

  (* Left Right *)
  admit.
Admitted.

End all_mod.

