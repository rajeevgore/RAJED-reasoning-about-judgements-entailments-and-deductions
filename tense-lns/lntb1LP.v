
(* try to adapt lntmr.v, which deals with diamond rules, to box rules *)

Require Import ssreflect.
Require Import Omega.

Require Import gen.
Require Import ddP.
Require Import List_lemmasP.
Require Import lntP.
Require Import lntacsP.
Require Import lntmtacsP.

Set Implicit Arguments.

(* specific way of defining modal rules, for b1lrules,
  restricted to two sequents plus context, and one premise *) 
(* version in paper 23/4/19, Fig 2, \wbx_L^1, \bbx_L^1 *)
Inductive b1lrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WBox1Ls : forall A d H1l H1r H2l H2r K1 K2, b1lrules 
      [[(pair (H1l ++ WBox A :: H1r) K1, d);
        (pair (H2l ++ A :: H2r) K2, fwd)]]
      [(pair (H1l ++ WBox A :: H1r) K1, d); 
        (pair (H2l ++ H2r) K2, fwd)]
  | BBox1Ls : forall A d H1l H1r H2l H2r K1 K2, b1lrules 
      [[(pair (H1l ++ BBox A :: H1r) K1, d);
        (pair (H2l ++ A :: H2r) K2, bac)]]
      [(pair (H1l ++ BBox A :: H1r) K1, d); 
        (pair (H2l ++ H2r) K2, bac)].

Lemma gen_swapL_step_b1L: forall V ps concl last_rule rules,
  last_rule = nslrule (@b1lrules V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? K sppc mnsp nsc]. clear nsr.
unfold nslext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 6 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-inversion sppc. (* solves first goal *)

(* swap in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs WBox1Ls. }
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs BBox1Ls. }
  }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw rs sppc c (Γ', Δ, d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw rs sppc pp (Γ', Δ, d) acm inps0 swap. }

(* here, swap in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs WBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s acm rs WBox1Ls ltac: (assoc_mid H1). }
{ use_acm2s acm rs WBox1Ls ltac: (assoc_mid H3). }
{ use_acm2s acm rs WBox1Ls list_assoc_l'. }
{ use_acm2s acm rs WBox1Ls ltac: (assoc_mid H). }
}
}

(* BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs BBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s acm rs BBox1Ls ltac: (assoc_mid H1). }
{ use_acm2s acm rs BBox1Ls ltac: (assoc_mid H3). }
{ use_acm2s acm rs BBox1Ls list_assoc_l'. }
{ use_acm2s acm rs BBox1Ls ltac: (assoc_mid H). }
}
}
}
(* another case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw rs sppc c (Γ', Δ, d) acm inps0 swap. }

Qed.

Check gen_swapL_step_b1L.

Lemma gen_swapR_step_b1L: forall V ps concl last_rule rules,
  last_rule = nslrule (@b1lrules V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? K sppc mnsp nsc]. clear nsr.
unfold nslext in nsc.
rewrite can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 6 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-inversion sppc. (* solves first goal *)

(* swap in the first of the two sequents affected by the rule *)
(* here the exchange is on the right and the rules operate on the left *)
-{ inversion sppc ; subst ; clear sppc ; (* 2 subgoals *)
   [> use_acm_sw_sep acm rs swap WBox1Ls |
     use_acm_sw_sep acm rs swap BBox1Ls ]. }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw rs sppc c (Γ, Δ', d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw rs sppc pp (Γ, Δ', d) acm inps0 swap. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
* use_acm_sw_sep acm rs swap WBox1Ls.
* use_acm_sw_sep acm rs swap WBox1Ls.
}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
* use_acm_sw_sep acm rs swap BBox1Ls.
* use_acm_sw_sep acm rs swap BBox1Ls.
}
}  

(* another case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw rs sppc c (Γ, Δ', d) acm inps0 swap. }

Qed.

Check gen_swapR_step_b1L.

(* for examples of how to combine these with other rules, 
  see lntmr.v, theorems gen_swapmsL and gen_swapmsR *)

(* interchange two sublists of list of formulae,
  no need to expand swap or the underlying rule *)

(** now want to do the same for left context only **)
Lemma gen_swapL_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* swap in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs WBox1Ls. }
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs BBox1Ls. }
  }

(* case of exchange in sequent to the left of where rule applied,
  also can use exchL2 rs sppc acm swap. *)
-{ nsgen_sw rs sppc c (Γ', Δ, d) acm inps0 swap. }

(* here, swap in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs WBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
use_acm2s acm rs WBox1Ls ltac: (assoc_mid H1).
use_acm2s acm rs WBox1Ls ltac: (assoc_mid H3).
use_acm2s acm rs WBox1Ls list_assoc_l'.
use_acm2s acm rs WBox1Ls ltac: (assoc_mid H).
}
}

(* BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs BBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
use_acm2s acm rs BBox1Ls ltac: (assoc_mid H1).
use_acm2s acm rs BBox1Ls ltac: (assoc_mid H3).
use_acm2s acm rs BBox1Ls list_assoc_l'.
use_acm2s acm rs BBox1Ls ltac: (assoc_mid H).
}
}
}
Qed.

Check gen_swapL_step_b1L_lc.

Lemma gen_swapR_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; [> 
  use_acm_sw_sep acm rs swap WBox1Ls |
  use_acm_sw_sep acm rs swap BBox1Ls ]. }
(* case of exchange in sequent to the left of where rule applied,
  also can use exchL2 rs sppc acm swap. *)
-{ nsgen_sw rs sppc c (Γ, Δ', d) acm inps0 swap. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
* use_acm_sw_sep acm rs swap WBox1Ls.
* use_acm_sw_sep acm rs swap WBox1Ls.
}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
* use_acm_sw_sep acm rs swap BBox1Ls.
* use_acm_sw_sep acm rs swap BBox1Ls.
}
}  

Qed.

Check gen_swapR_step_b1L_lc.

