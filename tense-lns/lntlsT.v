Add LoadPath "../general".

(* proving the form of exchange where two adjacent lists are interchanged 
  for system with princrule and seqrule *)

Require Import ssreflect.
Require Import genT gen.
Require Import ddT.
Require Import List_lemmasT.
Require Import gen_tacs lntT.
Require Import lntacsT.


(** now the same thing for left context only **)

Lemma gen_swapL_step_loe_lc : forall V ps concl princrules
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  rules_L_oeT princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
apply can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2T in pp.

destruct c.
sD ; subst.
inversion ss. subst.
{ nsgen_swTT rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{inversion pp1. inversion ss. subst.
(* injection H0 as. subst. *)
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oeT in loe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD'T2 ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)

nsprsameLT princrules rs pr q qin inmps acm inps0 x0.
}

{ list_eq_nc. contradiction. }
Unshelve. all : solve_unshelved.
Qed.

Lemma gen_swapL_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros. eapply gen_swapL_step_loe_lc.
  apply princrule_pfc_L_oe'T. exact H. Qed.

Lemma gen_swapL_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule_pfc V))) (fun _ => False) ns),
  can_gen_swapL (nslcrule (seqrule (@princrule_pfc V))) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros until 0; intros H1 H2 H3. inversion H1. 
subst.
pose gen_swapL_step_pr_lc.
unfold gen_swapL_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.
