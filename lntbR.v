
(* box_R rules, as on paper 23/4/19, Fig 2 *)

Require Import ssreflect.
Require Import Omega.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.
Require Import lntmtacs.

Set Implicit Arguments.

(* specific way of defining modal rules, for b2rrules,
  restricted to two sequents plus context, and one premise *) 
(* version in paper 23/4/19, Fig 2, \wbx_R^2, \bbx_R^2 *)
Inductive b2rrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WBox2Rs : forall A H1 K1l K1r, b2rrules 
      [[(pair H1 (K1l ++ WBox A :: K1r), fwd) ; (pair [] [A], fwd) ]]
      [(pair H1 (K1l ++ WBox A :: K1r), fwd)]
  | BBox2Rs : forall A H1 K1l K1r, b2rrules 
      [[(pair H1 (K1l ++ BBox A :: K1r), bac) ; (pair [] [A], bac) ]]
      [(pair H1 (K1l ++ BBox A :: K1r), bac)].

Lemma gen_swapL_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+ use_acm_os acm rs swap WBox2Rs.
+ use_acm_os acm rs swap BBox2Rs. }
(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw rs sppc c (Γ', Δ, d) acm inps0 swap. }
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
    * use_acm_os acm rs swap WBox2Rs.
    * { list_eq_nc. contradiction. }
    }
  +{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
    * use_acm_os acm rs swap BBox2Rs.
    * { list_eq_nc. contradiction. }
    }
  }
Qed.

Check gen_swapL_step_b2R_lc.

Lemma gen_swapR_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs WBox2Rs. }
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs BBox2Rs. }
  }
-{ nsgen_sw rs sppc c (Γ, Δ', d) acm inps0 swap. }
-{ inversion sppc ; subst ; clear sppc.  (* 2 subgoals *)
(* WBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1 acm rs WBox2Rs. }
*{ list_eq_nc. contradiction. }
}
(* BBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1 acm rs BBox2Rs. }
*{ list_eq_nc. contradiction. }
} }
Qed.

Check gen_swapR_step_b2R_lc.

(* now for the Box1R rules, which will be more difficult *)
Inductive b1rrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WBox1Rs : forall A d H1 H2 K1l K1r K2l K2r, b1rrules 
    [[(pair H1 (K1l ++ A :: K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac) ] ;
       [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac) ;
         (pair [] [A], fwd)] ]
      [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac)]
  | BBox1Rs : forall A d H1 H2 K1l K1r K2l K2r, b1rrules 
    [[(pair H1 (K1l ++ A :: K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd) ] ;
       [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd) ;
         (pair [] [A], bac)] ]
      [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd)].

(*
Lemma gen_swapL_step_b1R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1rrules V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
(* swapping in antecedent of first sequent in skeleton rule *)
+ use_acm_2 acm rs swap WBox1Rs.
+ use_acm_2 acm rs swap BBox1Rs. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
(* swapping to the left of first sequent in skeleton rule *)
+{
derIrs rs.
 list_assoc_l'.
 apply NSlclctxt'.
 apply WBox1Rs.
 ms_cgs acm.
 destruct acm as [acm1 acm2]
split.
list_assoc_r'.
eapply acm1. 
exact swap.
unfold nslclext.
list_assoc_r'.
reflexivity.
reflexivity.

list_assoc_r'.
eapply acm2. 
exact swap.
unfold nslclext.
list_assoc_r'.
reflexivity.
reflexivity.
}

 use_acm_os acm rs swap WBox1Rs.
+ use_acm_os acm rs swap BBox1Rs. }
(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw rs sppc c (Γ', Δ, d) acm inps0 swap. }
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
    * use_acm_os acm rs swap WBox1Rs.
    * { list_eq_nc. contradiction. }
    }
  +{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
    * use_acm_os acm rs swap BBox1Rs.
    * { list_eq_nc. contradiction. }
    }
  }
Qed.

Check gen_swapL_step_b2R_lc.
*)
