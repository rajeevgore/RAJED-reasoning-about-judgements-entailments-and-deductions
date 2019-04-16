
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

(* proof using step lemma *)
Lemma gen_swapL_step_pr: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nsrule (seqrule (@princrule V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. subst.

inversion nsr as [? ? ? K ? sppc mnsp nsc].
unfold nsext in nsc.
unfold can_gen_swapL.   intros until 0. intros pp ss.
unfold nsext in pp.

apply partition_2_2 in pp.
remember (Γ1 ++ Γ3 ++ Γ2 ++ Γ4, Δ) as seqe.

decompose [or] pp. 

{ nsright pp G0 seqe d0 x Ge HeqGe
  K d ps ps0 inps0 pse K0 drs nsr acm G seq rs. }
all : revgoals.
{ nsleft pp G0 seqe d0 x He HeqHe
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
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply Idrule_L_oe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)).

(* need to do stage1 rs pr. to see what next,
  and stage12ds rs acm qin1 qin3 pr ...,
  then all : solve_eqs. to see what next *)

{ stage12ds rs acm qin1 qin3 pr sel3 ; solve_eqs ; 

....


{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc l) ; reflexivity.  }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc sel) ; reflexivity.  }

{ stage12altdsL rs drs acm qin1 qin3 pr. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ; 
rewrite (app_assoc l1) ; rewrite (app_assoc sel) ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc sel1) ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc l1) ; rewrite (app_assoc sel1) ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc l) ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc Φ1) ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ; reflexivity. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL rs drs acm qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc l1) ; rewrite (app_assoc Φ1) ; reflexivity. }

Qed.

Check gen_swapL_step_pr.

Lemma gen_swapL: forall {V : Set} ns
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_swapL (nsrule (seqrule (@princrule V))) ns.

Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_swapL_step_pr.
unfold gen_swapL_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

Check gen_swapL.

(* now the same thing for each rule individually *)
(*
Lemma gen_swapL_step_Id: 
Goal forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nsrule (seqrule (@Idrule V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. subst.

inversion nsr as [? ? ? K ? sppc mnsp nsc].
unfold nsext in nsc.
unfold can_gen_swapL.   intros until 0. intros pp ss.
unfold nsext in pp.

apply partition_2_2 in pp.
remember (Γ1 ++ Γ3 ++ Γ2 ++ Γ4, Δ) as seqe.

decompose [or] pp. 

{ nsright pp G0 seqe d0 x Ge HeqGe
  K d ps ps0 inps0 pse K0 drs nsr acm G seq rs. }
all : revgoals.
{ nsleft pp G0 seqe d0 x He HeqHe
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
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply Idrule_L_oe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)).

(* need to do stage1 rs pr. to see what next,
  and stage12ds rs acm qin1 qin3 pr ...,
  then all : solve_eqs. to see what next *)

*)
