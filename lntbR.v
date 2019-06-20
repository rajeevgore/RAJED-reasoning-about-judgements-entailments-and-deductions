
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

acacDe ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+ use_acm_os acm rs swap WBox2Rs.
+ use_acm_os acm rs swap BBox2Rs. }
(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw rs sppc c (Γ', Δ, d) acm inps0 swap. }
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r ; (* 1 subgoal *)
    use_acm_os acm rs swap WBox2Rs.  }
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r ; (* 1 subgoal *)
    use_acm_os acm rs swap BBox2Rs.  }
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
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoal *)
  inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1 acm rs WBox2Rs. 
}
(* BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoal *)
  inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1 acm rs BBox2Rs. 
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
(* swapping in antecedent of first sequent in rule skeleton *)
+ use_acm_2 acm rs swap WBox1Rs.
+ use_acm_2 acm rs swap BBox1Rs. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
(* swapping to the left of the sequents in rule skeleton *)
+ use_acm_2_ass acm rs swap WBox1Rs.
+ use_acm_2_ass acm rs swap BBox1Rs. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
* use_acm_2 acm rs swap WBox1Rs.
(* swapping in antecedent of second sequent in rule skeleton *)
* use_acm_2_snd acm rs swap WBox1Rs.
}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
* use_acm_2 acm rs swap BBox1Rs.
(* swapping in antecedent of second sequent in rule skeleton *)
* use_acm_2_snd acm rs swap BBox1Rs.
} }
  
Qed.

Check gen_swapL_step_b1R_lc.

Lemma gen_swapR_step_b1R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1rrules V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals, WBox and BBox *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
* use_acm_2_sw acm rs swap ltac: (assoc_mid H1) WBox1Rs.
* use_acm_2_sw acm rs swap ltac: (assoc_mid H4) WBox1Rs.
* use_acm_2_sw acm rs swap list_assoc_l' WBox1Rs.
* use_acm_2_sw acm rs swap ltac: (assoc_mid H) WBox1Rs.
}
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
* use_acm_2_sw acm rs swap ltac: (assoc_mid H1) BBox1Rs.
* use_acm_2_sw acm rs swap ltac: (assoc_mid H4) BBox1Rs.
* use_acm_2_sw acm rs swap list_assoc_l' BBox1Rs.
* use_acm_2_sw acm rs swap ltac: (assoc_mid H) BBox1Rs.
} 
}
(* case of exchange in sequent to the left of where rule applied,
  no need to expand sppc - check where else this may hold *) 
- exchL2 rs sppc acm swap. 

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals, WBox and BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swap in first sequent in rule skeleton *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
** use_acm_2_sw acm rs swap ltac: (assoc_mid H3) WBox1Rs.
** use_acm_2_sw acm rs swap ltac: (assoc_mid H5) WBox1Rs.
** use_acm_2_sw acm rs swap list_assoc_l' WBox1Rs.
** use_acm_2_sw acm rs swap ltac: (assoc_mid H) WBox1Rs.
}
(* swap in second sequent in rule skeleton *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm_2_sw'' acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
    ltac: (rewrite list_rearr16') ltac: (rewrite - list_rearr16') WBox1Rs. }

}

+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swap in first sequent in rule skeleton *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
** use_acm_2_sw acm rs swap ltac: (assoc_mid H3) BBox1Rs.
** use_acm_2_sw acm rs swap ltac: (assoc_mid H5) BBox1Rs.
** use_acm_2_sw acm rs swap list_assoc_l' BBox1Rs.
** use_acm_2_sw acm rs swap ltac: (assoc_mid H) BBox1Rs.
}
(* swap in second sequent in rule skeleton *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm_2_sw'' acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
    ltac: (rewrite list_rearr16') ltac: (rewrite - list_rearr16') BBox1Rs. }

}
}
Qed.

Check gen_swapR_step_b1R_lc.

