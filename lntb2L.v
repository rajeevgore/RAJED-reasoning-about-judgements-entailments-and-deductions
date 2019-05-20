
(* box^2_L rules, as on paper 23/4/19, Fig 2 *)

Require Import ssreflect.
Require Import Omega.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.
Require Import lntls.
Require Import lntrs.
Require Import lntb1L.

Set Implicit Arguments.

(* specific way of defining modal rules, for b2lrules,
  restricted to two sequents plus context, and one premise *) 
(* version in paper 23/4/19, Fig 2, \wbx_L^2, \bbx_L^2 *)
Inductive b2lrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WBox2Ls : forall A d H1l H1r H2l H2r K1 K2, b2lrules 
      [[(pair (H1l ++ WBox A :: H1r) K1, d) ]]
      [(pair (H1l ++ H1r) K1, d); 
        (pair (H2l ++ WBox A :: H2r) K2, bac)]
  | BBox2Ls : forall A d H1l H1r H2l H2r K1 K2, b2lrules 
      [[(pair (H1l ++ BBox A :: H1r) K1, d) ]]
      [(pair (H1l ++ H1r) K1, d); 
        (pair (H2l ++ BBox A :: H2r) K2, bac)].

Lemma gen_swapL_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. (* no clear drs. *) subst.

inversion nsr as [? ? ? sppc mnsp nsc].
unfold nslclext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* swap in the first of the two sequents affected by the rule *)
-{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2s' acm rs WBox2Ls ltac: (assoc_mid H1). 
  * use_acm2s' acm rs WBox2Ls ltac: (assoc_mid H3). 
  * use_acm2s' acm rs WBox2Ls list_assoc_l'. 
  * use_acm2s' acm rs WBox2Ls ltac: (assoc_mid H). 
  }
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2s' acm rs BBox2Ls ltac: (assoc_mid H1). 
  * use_acm2s' acm rs BBox2Ls ltac: (assoc_mid H3). 
  * use_acm2s' acm rs BBox2Ls list_assoc_l'. 
  * use_acm2s' acm rs BBox2Ls ltac: (assoc_mid H). 
  } }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw nsr rs sppc c (Γ', Δ, d) acm inps0 swap. }

(* here, swap in either of the two sequents affected by the rule *)
-{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2s' acm rs WBox2Ls ltac: (assoc_mid H1). 
  ** use_acm2s' acm rs WBox2Ls ltac: (assoc_mid H3). 
  ** use_acm2s' acm rs WBox2Ls list_assoc_l'. 
  ** use_acm2s' acm rs WBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst. 
acacD' ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs WBox2Ls. }
*{ list_eq_nc. contradiction. }
}

(* BBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2s' acm rs BBox2Ls ltac: (assoc_mid H1). 
  ** use_acm2s' acm rs BBox2Ls ltac: (assoc_mid H3). 
  ** use_acm2s' acm rs BBox2Ls list_assoc_l'. 
  ** use_acm2s' acm rs BBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst. 
acacD' ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs BBox2Ls. }
*{ list_eq_nc. contradiction. }
}
}
Qed.

Check gen_swapL_step_b2L_lc.

Lemma gen_swapR_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. (* no clear drs! *) subst.

inversion nsr as [? ? ? sppc mnsp nsc].
unfold nslclext in nsc.
rewrite can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; 
  [> use_acm_sw_sep' acm rs swap WBox2Ls |
     use_acm_sw_sep' acm rs swap BBox2Ls ]. }
-{ nsgen_sw nsr rs sppc c (Γ, Δ', d) acm inps0 swap. }

-{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ use_acm_sw_sep' acm rs swap WBox2Ls. }
*{ use_drs rs drs WBox2Ls. }
*{ list_eq_nc. contradiction. }
}
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ use_acm_sw_sep' acm rs swap BBox2Ls. }
*{ use_drs rs drs BBox2Ls. }
*{ list_eq_nc. contradiction. }
}
}  

Qed.

Check gen_swapR_step_b2L_lc.
