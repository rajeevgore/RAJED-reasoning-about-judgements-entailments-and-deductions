
(* proving the form of exchange where two adjacent lists are interchanged 
  for system with princrule and seqrule *)

Require Import ssreflect.
Require Import genT gen.
Require Import ddT.
Require Import List_lemmasT.
Require Import lntT.
Require Import lntacsT.

(** now the same thing for left context only **)

Lemma gen_swapR_step_roe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  rules_R_oeT princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros roe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nsext in nsc.
apply can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2T in pp.

destruct c.
sD ; subst.

{ nsgen_swT rs sppc (l, l0, d) (Γ, Δ', d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection ss as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst. clear sppc.
injection se as sel ser.
subst.

unfold rules_R_oeT in roe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD'T2 ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_ncT || (pose pr as Qpr ; apply roe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameRT princrules rs pr q qin inmps acm inps0 x0. 
}

{ list_eq_nc. contradiction. }
Unshelve. all : solve_unshelved.
Qed.

Lemma gen_swapR_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros. eapply gen_swapR_step_roe_lc.
  apply princrule_pfc_R_oe'T. exact H. Qed.

Lemma gen_swapR_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule_pfc V))) (fun _ => False) ns),
  can_gen_swapR (nslcrule (seqrule (@princrule_pfc V))) ns.

Proof. 
intros until 0. intros D.
eapply derrec_all_indT in D.
exact D. tauto.
intros H1 H2 H3 H4 H5. inversion H3. 
subst.
pose gen_swapR_step_pr_lc.
unfold gen_swapR_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.
