
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
{ nsright H7 G0 seqe d0 x c0 Ge HeqGe
  H2 d ps ps0 inps0 pse H6 H0 H H1 G seq. }
all : revgoals.
{ nsleft H7 G0 seqe d0 x c0 He HeqHe
  H2 d ps ps0 inps0 pse H6 H0 H H1 G seq. }


(* now case where move and rule application occur in the same sequent *)
cE. clear H7. injection H10 as.
inversion H3 as [? ? ? ? ? ? pr mse se].
unfold seqext in se.
subst.  clear H. clear H3.
destruct c0. 
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
use_prR pr.

{
stage1 pr. (* will need to move Q around sel1 *)
rewrite app_assoc.
rewrite app_assoc.
rewrite app_assoc in pr.
rewrite list_rearr16'. 
apply pr.
stage2ds H1 qin1 qin3.
2: list_assoc_r'.
2: simpl.
all: solve_eqs.
}

{
stage1 pr. (* will need to move Q around sel1 *)
rewrite list_rearr16'.
rewrite !app_assoc.
rewrite !app_assoc in pr.
apply pr.
stage2ds H1 qin1 qin3.
2: rewrite - list_rearr16'.
all: solve_eqs.
}

{
stage1 pr.
rewrite <- app_assoc.
simpl.
rewrite !app_assoc.
rewrite !app_assoc in pr.
apply pr.
stage2ds H1 qin1 qin3.
all: solve_eqs.
}
}
 
(* why does all : solve_eqs work?  see emails late Jan 2019 *)
{ stage12ds H1 qin1 qin3 pr l0. all : solve_eqs. }
{ stage12ds H1 qin1 qin3 pr l0. all : solve_eqs. }
{ stage12ds H1 qin1 qin3 pr ser. all : solve_eqs. }

(* subgoal has Q (formula to be moved) in principal formula *)
all: cycle 1.
all: cycle 1.

{ stage12ds H1 qin1 qin3 pr l0. all : solve_eqs. }

(* four remaining subgoals have Q (formula to be moved) in principal formula *)

- { mpv use_prR use_cgmR H1 H0 pr. }

- { subst. use_prR pr. stage1 pr. apply pr. unfold seqext in H0. exact H0. }

- { mpv use_prR use_cgmR H1 H0 pr. }

- { subst. use_prR pr. stage1 pr. apply pr. unfold seqext in H0. exact H0. }

Qed.

Check gen_moveR.







