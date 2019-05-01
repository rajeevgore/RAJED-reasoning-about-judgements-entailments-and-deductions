
(* proving the form of exchange where two adjacent lists are interchanged 
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

(* proof using version of step lemma which is generic for rules *)
(* proof using swapped, don't need 20 separate cases!! *) 
Lemma gen_swapR_step_roe: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_R_oe princrules -> 
  last_rule = nsrule (seqrule princrules) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros roe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? K ? sppc mnsp nsc].
unfold nsext in nsc.
rewrite can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nsext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw nsr rs sppc (l, l0, d) (Γ, Δ', d0) acm inps0 swap. }
all : cycle 1.
{ nsgen_sw nsr rs sppc (l, l0, d) (Γ, Δ', d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
injection H0 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear nsr. clear sppc.
injection se as sel ser.
subst.

unfold rules_R_oe in roe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply roe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameR princrules rs pr q qin inmps acm inps0 x0. 

Qed.

Check gen_swapR_step_roe.

Lemma gen_swapR_step_pr: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nsrule (seqrule (@princrule V)) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros. eapply gen_swapR_step_roe. apply princrule_R_oe'. exact H. Qed.

Check gen_swapR_step_pr.

Lemma gen_swapR: forall {V : Set} ns
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_swapR (nsrule (seqrule (@princrule V))) ns.

Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_swapR_step_pr.
unfold gen_swapR_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

Check gen_swapR.

