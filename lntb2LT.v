
(* box^2_L rules, as on paper 23/4/19, Fig 2 *)

Require Import ssreflect.
Require Import Omega.

Require Import genT.
Require Import ddT.
Require Import List_lemmasT.
Require Import lntT.
Require Import lntacsT.
Require Import lntmtacsT.

Set Implicit Arguments.

(* specific way of defining modal rules, for b2lrules,
  restricted to two sequents plus context, and one premise *) 
(* version in paper 23/4/19, Fig 2, \wbx_L^2, \bbx_L^2 *)
Inductive b2lrules (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
  | WBox2Ls : forall A d H1l H1r H2l H2r K1 K2, b2lrules 
      [[(pair (H1l ++ A :: H1r) K1, d) ]]
      [(pair (H1l ++ H1r) K1, d); 
        (pair (H2l ++ WBox A :: H2r) K2, bac)]
  | BBox2Ls : forall A d H1l H1r H2l H2r K1 K2, b2lrules 
      [[(pair (H1l ++ A :: H1r) K1, d) ]]
      [(pair (H1l ++ H1r) K1, d); 
        (pair (H2l ++ BBox A :: H2r) K2, fwd)].

Lemma gen_swapL_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. (* no clear drs. *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
apply can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* swap in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear swap. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H1). 
  * use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H3). 
  * use_acm2sT acm rs WBox2Ls list_assoc_l'. 
  * use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H). 
  }
+{ inversion_clear swap. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H1). 
  * use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H3). 
  * use_acm2sT acm rs BBox2Ls list_assoc_l'. 
  * use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H). 
  } }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_swTT rs sppc c (Γ', Δ, d) acm inps0 swap. }

(* here, swap in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H1). 
  ** use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H3). 
  ** use_acm2sT acm rs WBox2Ls list_assoc_l'. 
  ** use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst. 
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs WBox2Ls. }
}

(* BBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H1). 
  ** use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H3). 
  ** use_acm2sT acm rs BBox2Ls list_assoc_l'. 
  ** use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst. 
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs BBox2Ls. }
}
 }
 Unshelve. all : solve_unshelved.
Qed.

Lemma gen_swapR_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. (* no clear drs! *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
apply can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; 
  [> use_acm_sw_sepT acm rs swap WBox2Ls |
     use_acm_sw_sepT acm rs swap BBox2Ls ]. }
-{ nsgen_swTT rs sppc c (Γ, Δ', d) acm inps0 swap. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
* use_acm_sw_sepT acm rs swap WBox2Ls.
* use_drs rs drs WBox2Ls.
}
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
* use_acm_sw_sepT acm rs swap BBox2Ls.
* use_drs rs drs BBox2Ls.
}
}  
Unshelve. all : solve_unshelved.
Qed.
