
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

Lemma gen_swapL: forall (V : Set) ns
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_swapL (nsrule (seqrule (@princrule V))) ns.

Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.  unfold nsext in H5.
unfold can_gen_swapL.   intros until 0. intros pp ss.
unfold nsext in pp.
(* cases of where the swap occurs vs where the last rule applied *)
apply partition_2_2 in pp.
remember (Γ1 ++ Γ3 ++ Γ2 ++ Γ4, Δ) as seqe.

decompose [or] pp. 
{ nsright pp G0 seqe d0 x c0 Ge HeqGe
  H2 d ps ps0 inps0 pse H6 H0 H H1 G seq. }
all : revgoals.
{ nsleft pp G0 seqe d0 x c0 He HeqHe
  H2 d ps ps0 inps0 pse H6 H0 H H1 G seq. }

(* now case where move and rule application occur in the same sequent *)
cE. clear pp. injection H8 as.
inversion H3 as [? ? ? ? ? ? pr mse se].
unfold seqext in se.
subst.  clear H. clear H3.
destruct c0. 
injection se as sel ser.
subst.
(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply princrule_L_oe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)).

(* need to do stage1 pr. to see what next,
  then stage12ds H1 qin1 qin3 pr ...,
  then all : solve_eqs. to see what next *)

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc l) ; reflexivity.  }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc sel) ; reflexivity.  }

{ stage12altdsL H0 H1 qin1 qin3 pr. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ; 
rewrite (app_assoc l1) ; rewrite (app_assoc sel) ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc sel1) ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc l1) ; rewrite (app_assoc sel1) ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc l) ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc Φ1) ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ; reflexivity. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs. }

{ stage12altdsL H0 H1 qin1 qin3 pr ; solve_eqs ;
rewrite (app_assoc l1) ; rewrite (app_assoc Φ1) ; reflexivity. }

Qed.

(* 
}
{
stage1 pr.
Undo.
all : solve_eqs.
Undo 2.
*)

Check gen_swapL.







