
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
unfold can_gen_swapL.  intros.
unfold nsext in H7.
(* cases of where the swap occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ1 ++ Γ3 ++ Γ2 ++ Γ4, Δ) as seqe.

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
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply princrule_L_oe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)).

(* need to do stage1 pr. to see what next,
  then stage12ds H1 qin1 qin3 pr ...,
  then all : solve_eqs. to see what next *)
{ stage12ds H1 qin1 qin3 pr sel3 ; solve_eqs ;
rewrite (app_assoc l sel5) ; reflexivity.  }

{ stage12ds H1 qin1 qin3 pr sel1 ; solve_eqs ;
rewrite (app_assoc sel l) ; reflexivity.  }

{ stage12ds H1 qin1 qin3 pr sel5 ; solve_eqs.
apply eq_nnn_app. simpl. reflexivity. }

{ stage12ds H1 qin1 qin3 pr Γ3 ; solve_eqs ; reflexivity. }


(* 
{
stage1 pr.
Undo.
all : solve_eqs.
Undo 2.
*)

(* normally need to rearrange *)
apply pr. (* solves one sg *)
stage2ds H1 qin1 qin3.  all : solve_eqs. }

(* sg 2 of 10 *)
all: cycle 1.
all: cycle 1.

(* sg 4 of 10 *)

(* problem here, Q between sel3 and sel5,
  but one of sel3 and sel5 must be empty due to princrule_L *)

{
use_prL pr.

{
stage1 pr. (* will need to move Q around sel1 *)
rewrite app_assoc.
rewrite list_rearr16'.
apply pr.
stage2ds H1 qin1 qin3.
2: list_assoc_r'.
2: simpl.
all: solve_eqs.
}

{
stage1 pr. (* will need to move Q around sel1 *)
rewrite app_assoc.
rewrite list_rearr16'.
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
 
(* why does all : solve_eqs work?  see emails late Jan 2019 *)
{ stage12ds H1 qin1 qin3 pr l. all : solve_eqs. }
{ stage12ds H1 qin1 qin3 pr l. all : solve_eqs. }
{ stage12ds H1 qin1 qin3 pr sel. all : solve_eqs. }

(* subgoal has Q (formula to be moved) in principal formula *)
all: cycle 1.
all: cycle 1.

{ stage12ds H1 qin1 qin3 pr l. all : solve_eqs. }

(* four remaining subgoals have Q (formula to be moved) in principal formula *)
- { mpv use_prL use_cgmL H1 H0 pr. }

- { subst. use_prL pr. stage1 pr. apply pr. unfold seqext in H0. exact H0. }

- { mpv use_prL use_cgmL H1 H0 pr. }

- { subst. use_prL pr. stage1 pr. apply pr. unfold seqext in H0. exact H0. }

Qed.

Check gen_swapL.







