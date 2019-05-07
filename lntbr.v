
(* try to adapt lntmr.v, which deals with diamond rules, to box rules *)

Require Import ssreflect.
Require Import Omega.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.
Require Import lntls.
Require Import lntrs.

Set Implicit Arguments.

(* specific way of defining modal rules, for bsrules,
  restricted to two sequents plus context, and one premise *) 
Inductive bsrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WBoxLs : forall A d H1l H1r H2l H2r K1 K2, bsrules 
      [[(pair (H1l ++ WBox A :: H1r) K1, d);
        (pair (H2l ++ A :: H2r) K2, fwd)]]
      [(pair (H1l ++ WBox A :: H1r) K1, d); 
        (pair (H2l ++ H2r) K2, fwd)]
  | BBoxLs : forall A d H1l H1r H2l H2r K1 K2, bsrules 
      [[(pair (H1l ++ BBox A :: H1r) K1, d);
        (pair (H2l ++ A :: H2r) K2, bac)]]
      [(pair (H1l ++ BBox A :: H1r) K1, d); 
        (pair (H2l ++ H2r) K2, bac)].

(* corresponding diamond rules, not used now *)
Inductive dsrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WDiaRs : forall A d G1 G2 H1l H1r H2l H2r, dsrules 
      [[(pair G1 (H1l ++ WDia A :: H1r), d);
        (pair G2 (H2l ++ A :: H2r), fwd)]]
      [(pair G1 (H1l ++ WDia A :: H1r), d); 
        (pair G2 (H2l ++ H2r), fwd)]
  | BDiaRs : forall A d G1 G2 H1l H1r H2l H2r, dsrules 
      [[(pair G1 (H1l ++ BDia A :: H1r), d);
        (pair G2 (H2l ++ A :: H2r), bac)]]
      [(pair G1 (H1l ++ BDia A :: H1r), d); 
        (pair G2 (H2l ++ H2r), bac)].

Ltac ms_cgs acm := 
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_swapL_def' in acm ;
rewrite -> ?can_gen_swapR_def' in acm ;
unfold nslext.

(* where exchange is in the first of two sequents of the modal rule *)
Ltac use_acm1 acm rs := 
(* interchange two sublists of list of formulae *)
derIrs rs ; [> 
apply NSlctxt2 ;
assoc_single_mid ;
apply WBoxLs || apply BBoxLs || apply WDiaRs || apply BDiaRs |
ms_cgs acm ;
list_assoc_r' ; simpl ; eapply acm ] ; [> | 
  unfold nslext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; 
swap_tac.

(* where swapping is in second sequent of modal rule,
  in which conclusion has no principal formula *)
Ltac use_acm2s acm rs rw :=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 ;
rw ; (* rewrite so as to identify two parts of context *)
apply WBoxLs || apply BBoxLs || apply WDiaRs || apply BDiaRs |
ms_cgs acm ;
list_assoc_r' ; simpl ;
rewrite list_rearr22 ; eapply acm ] ; [> | 
  unfold nslext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; swap_tac.

Lemma gen_swapL_step_bsr: forall V ps concl last_rule rules,
  last_rule = nslrule (@bsrules V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? K sppc mnsp nsc].
unfold nslext in nsc.
rewrite can_gen_swapL_def'.  intros until 0. intros swap pp ss.
unfold nslext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 6 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-inversion sppc. (* solves first goal *)

(* swap in the first of the two sequents affected by the rule *)
-{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs. }
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs. }
  }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw nsr rs sppc c (Γ', Δ, d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw nsr rs sppc pp (Γ', Δ, d) acm inps0 swap. }

(* here, swap in either of the two sequents affected by the rule *)
-{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s acm rs ltac: (assoc_mid H1). }
{ use_acm2s acm rs ltac: (assoc_mid H3). }
{ use_acm2s acm rs list_assoc_l'. }
{ use_acm2s acm rs ltac: (assoc_mid H). }
}

*{ apply eq_sym in H4. list_eq_nc. contradiction. }
}

(* BBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s acm rs ltac: (assoc_mid H1). }
{ use_acm2s acm rs ltac: (assoc_mid H3). }
{ use_acm2s acm rs list_assoc_l'. }
{ use_acm2s acm rs ltac: (assoc_mid H). }
}

*{ apply eq_sym in H4. list_eq_nc. contradiction. }
}
}
(* another case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw nsr rs sppc c (Γ', Δ, d) acm inps0 swap. }

Qed.

Check gen_swapL_step_bsr.

Ltac use_acm_sw_sep acm rs swap :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 ;
apply WBoxLs || apply BBoxLs || apply WDiaRs || apply BDiaRs |
ms_cgs acm ;
eapply acm in swap ] ;
[> (rewrite - list_rearr21 ; eapply swap) || 
  (list_assoc_r' ; simpl ; eapply swap) |
  unfold nslext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ].

Lemma gen_swapR_step_bsr: forall V ps concl last_rule rules,
  last_rule = nslrule (@bsrules V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? K sppc mnsp nsc].
unfold nslext in nsc.
rewrite can_gen_swapR_def'.  intros until 0. intros swap pp ss.
unfold nslext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 6 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-inversion sppc. (* solves first goal *)

(* swap in the first of the two sequents affected by the rule *)
(* here the exchange is on the right and the rules operate on the left *)
-{ clear nsr.  inversion sppc ; subst ; clear sppc ; (* 2 subgoals *)
  use_acm_sw_sep acm rs swap. }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw nsr rs sppc c (Γ, Δ', d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw nsr rs sppc pp (Γ, Δ', d) acm inps0 swap. }

-{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ use_acm_sw_sep acm rs swap. }
*{ use_acm_sw_sep acm rs swap. }
*{ apply eq_sym in H4. list_eq_nc. contradiction. }
}
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ use_acm_sw_sep acm rs swap. }
*{ use_acm_sw_sep acm rs swap. }
*{ apply eq_sym in H4. list_eq_nc. contradiction. }
}
}  

(* another case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw nsr rs sppc c (Γ, Δ', d) acm inps0 swap. }

Qed.

Check gen_swapR_step_bsr.

(* for examples of how to combine these with other rules, 
  see lntmr.v, theorems gen_swapmsL and gen_swapmsR *)
