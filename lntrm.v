
(* try non-adjacent move of a single formula, on the right-hand side,
  for system with princrule and seqrule *)

(* 
coqc gen.v
coqc dd.v
coqc List_lemmas.v
coqc lnt.v
coqc lntacs.v
*)

Require Import ssreflect.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.

Lemma gen_moveR: forall (V : Set) ns
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_moveR (nsrule (seqrule (@princrule V))) ns.

Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.  unfold nsext in H5.
unfold can_gen_moveR.  intros.
unfold nsext in H7.
(* cases of where the move occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ, Δ1 ++ Δ2 ++ Q :: Δ3) as seqe.

decompose [or] H7. 
{
clear H7.  cE.
(* case where the rule is applied in a sequent to the right
  of where the move takes place *)
remember (G0 ++ (seqe, d0) :: x) as Ge.
remember (map (nsext Ge H2 d) ps0) as pse.

apply derI with pse. subst pse. subst H6.
rewrite list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqGe.
apply NSctxt. assumption.

rewrite dersrec_forall.
intros q qin.  subst pse.  rewrite -> in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite -> Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_gen_moveR in c0.
unfold nsext. subst Ge. subst seqe.
rewrite <- list_rearr14.
eapply c0. 2:reflexivity.
unfold nsext. subst G. subst seq.
list_eq_assoc.
}

all : revgoals.
{ 
clear H7. cE.
(* now the case where the rule is applied in a sequent to the left
  of where the move takes place *)
remember (x ++ (seqe, d0) :: H6) as He.
remember (map (nsext G He d) ps0) as pse.

apply derI with pse. subst pse. subst G0.
rewrite <- list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqHe.
apply NSctxt. assumption.

rewrite dersrec_forall.
intros q qin.  subst pse.  rewrite -> in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite -> Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_gen_moveR in c0.
unfold nsext. subst He. subst seqe.
rewrite list_rearr14.

eapply c0. 2:reflexivity.
unfold nsext. subst H2. subst seq.
apply list_rearr14.
}

(* now case where move and rule application occur in the same sequent *)
cE. clear H7. injection H10 as.
inversion H3 as [? ? ? ? ? ? pr mse se].
unfold seqext in se.
subst.  clear H. clear H3.
destruct c0. unfold seqext in se.
injection se as sel ser.
subst.
(* do as much as possible for all rules at once *)
acacD'. (* gives 10 subgoals *)

{
(* sg 1 of 10 *)
stage1 pr.
(* normally need to rearrange *)
apply pr. (* solves one sg *)
stage2ds H1 qin1 qin3.  all : solve_eqs. }

(* sg 2 of 10 *)
all: cycle 1.
all: cycle 1.

(* sg 4 of 10 *)

(* problem here, Q between sel3 and sel5,
  but one of sel3 and sel5 must be empty due to princrule_R *)

{
pose pr as pr'.
apply princrule_R in pr'.
sD ; subst.
apply app_eq_nil in pr'. cD. subst.
simpl in pr.
simpl.
rewrite app_nil_r.

{
stage1 pr. (* will need to move Q around sel1 *)
rewrite app_assoc.
rewrite app_assoc.
rewrite app_assoc in pr.
rewrite list_rearr16'. DO THIS IN lntom
apply pr.
stage2ds H1 qin1 qin3.
2: list_assoc_r'.
2: simpl.
all: solve_eqs.
}

DONE TO HERE

{
apply app_eq_unit in pr'0.
sD ; subst ; simpl in pr ; simpl ;
  rewrite ?app_nil_r ; rewrite ?app_nil_r in pr.
{
stage1 pr. (* will need to move Q around sel1 *)
rewrite app_assoc.
rewrite list_rearr16.
apply pr.
stage2ds H1 qin1 qin3.
2: rewrite - list_rearr16'.
all: solve_eqs.
}

{
stage1 pr.
rewrite <- app_assoc.
simpl.
rewrite app_assoc.
apply pr.
stage2ds H1 qin1 qin3.
all: solve_eqs.
}
}
}
 
(* why does all : solve_eqs work?  see emails late Jan 2019 *)
{ stage12ds H1 qin1 qin3 pr l. all : solve_eqs. }
{ stage12ds H1 qin1 qin3 pr l. all : solve_eqs. }
{ stage12ds H1 qin1 qin3 pr sel. all : solve_eqs. }

(* subgoal has Q (formula to be moved) in principal formula *)
all: cycle 1.
all: cycle 1.

{ stage12ds H1 qin1 qin3 pr l. all : solve_eqs. }

(* four remaining subgoals have Q (formula to be moved) in principal formula *)
- {
subst. use_prR pr. stage1 pr. rewrite app_assoc. apply pr.
destruct pr ; simpl ; repeat (apply dlNil || apply dlCons).
use_cgmR H1. use_cgmR H1.
rewrite -> dersrec_forall in H0. apply H0. simpl. rewrite <- app_assoc. tauto.
}

- { subst. use_prR pr. stage1 pr. apply pr. unfold seqext in H0. exact H0. }

- {
subst. use_prR pr. stage1 pr. rewrite app_assoc. apply pr.
destruct pr ; simpl ; repeat (apply dlNil || apply dlCons).
use_cgmR H1. use_cgmR H1.
rewrite -> dersrec_forall in H0. apply H0. simpl. rewrite <- app_assoc. tauto.
}

- { subst. use_prR pr. stage1 pr. apply pr. unfold seqext in H0. exact H0. }

Qed.

Check gen_moveR.







