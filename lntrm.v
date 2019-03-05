
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

(* proof using step lemma *)
Lemma gen_moveR_step_pr: forall V ps concl
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nsrule (seqrule (@princrule V)) ->
  gen_moveR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_moveR_step.
intros lreq nsr drs acm rs. subst.

inversion nsr as [? ? ? K ? sppc mnsp nsc].
unfold nsext in nsc.
unfold can_gen_moveR.   intros until 0. intros pp ss.
unfold nsext in pp.
(* cases of where the move occurs vs where the last rule applied *)
apply partition_2_2 in pp.
remember (Γ, Δ1 ++ Δ2 ++ Q :: Δ3) as seqe.

decompose [or] pp. 
{ nsright' pp G0 seqe d0 x c0 Ge HeqGe
  K d ps ps0 inps0 pse K0 drs nsr acm G seq rs. }
all : revgoals.
{ nsleft' pp G0 seqe d0 x c0 He HeqHe
  K d ps ps0 inps0 pse K0 drs nsr acm G seq rs. }


(* now case where move and rule application occur in the same sequent *)
cE. clear pp. injection H0 as.
inversion sppc as [? ? ? ? ? ? pr mse se].
unfold seqext in se.
subst.  clear nsr. clear sppc.
destruct c0. 
injection se as sel ser.
subst.
(* do as much as possible for all rules at once *)
acacD'. (* gives 10 subgoals *)

{
(* sg 1 of 10 *)
stage1' rs pr.
(* normally need to rearrange *)
apply pr. (* solves one sg *)
stage2ds acm qin1 qin3.  all : solve_eqs. }

(* sg 2 of 10 *)
all: cycle 1.
all: cycle 1.

(* sg 4 of 10 *)

(* problem here, Q between sel3 and sel5,
  but one of sel3 and sel5 must be empty due to princrule_R *)

{
use_prR pr.

{
stage1' rs pr. (* will need to move Q around sel1 *)
rewrite app_assoc.
rewrite app_assoc.
rewrite app_assoc in pr.
rewrite list_rearr16'. 
apply pr.
stage2ds acm qin1 qin3.
2: list_assoc_r'.
2: simpl.
all: solve_eqs.
}

{
stage1' rs pr. (* will need to move Q around sel1 *)
rewrite list_rearr16'.
rewrite !app_assoc.
rewrite !app_assoc in pr.
apply pr.
stage2ds acm qin1 qin3.
2: rewrite - list_rearr16'.
all: solve_eqs.
}

{
stage1' rs pr.
rewrite <- app_assoc.
simpl.
rewrite !app_assoc.
rewrite !app_assoc in pr.
apply pr.
stage2ds acm qin1 qin3.
all: solve_eqs.
}
}
 
(* why does all : solve_eqs work?  see emails late Jan 2019 *)
{ stage12ds' rs acm qin1 qin3 pr l0. all : solve_eqs. }
{ stage12ds' rs acm qin1 qin3 pr l0. all : solve_eqs. }
{ stage12ds' rs acm qin1 qin3 pr ser. all : solve_eqs. }

(* subgoal has Q (formula to be moved) in principal formula *)
all: cycle 1.
all: cycle 1.

{ stage12ds' rs acm qin1 qin3 pr l0. all : solve_eqs. }

(* four remaining subgoals have Q (formula to be moved) in principal formula *)

- { mpv' use_prR use_cgmR acm drs rs pr. }

- { subst. use_prR pr. stage1' rs pr. apply pr.
     unfold seqext in drs. exact drs. }

- { mpv' use_prR use_cgmR acm drs rs pr. }

- { subst. use_prR pr. stage1' rs pr. apply pr.
     unfold seqext in drs. exact drs. }

Qed.

Check gen_moveR_step_pr.

Lemma gen_moveR': forall (V : Set) ns
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_moveR (nsrule (seqrule (@princrule V))) ns.

Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.
subst.
pose gen_moveR_step_pr.
unfold gen_moveR_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g.
intros.  assumption.
Qed.

Check gen_moveR'.









