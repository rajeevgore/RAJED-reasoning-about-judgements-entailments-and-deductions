
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

Ltac use_acmL acm rsub rs := 
(* interchange two sublists of list of formulae *)
eapply derI ; [> unfold rsub in rs ; apply rs ; clear rs ;
rewrite list_rearr20 ;  apply NSlctxt' ;
assoc_single_mid ;
(apply WBoxLs || apply BBoxLs) |
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_swapL_def' in acm ;
rewrite -> ?can_gen_swapR_def' in acm ;
unfold nslext ; list_assoc_r' ; simpl ;
eapply derrec_same_nsL ] ; 
[> eapply acm ; [> | apply nslext2_def | reflexivity ] | reflexivity ] ; 
swap_tac.

Ltac use_acm2s acm rsub rs rw :=
eapply derI ; [> unfold rsub in rs ; apply rs ; clear rs ; 
rewrite list_rearr21 ;  apply NSlctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
(apply WBoxLs || apply BBoxLs) |
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_swapL_def' in acm ;
rewrite -> ?can_gen_swapR_def' in acm ;
unfold nslext ; list_assoc_r' ; simpl ;
rewrite list_rearr22 ; eapply acm ] ;
[> | rewrite list_rearr21 ; apply nslext_def | reflexivity ] ; swap_tac.

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
  use_acmL acm rsub rs. }
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acmL acm rsub rs. }
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
  use_acmL acm rsub rs. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s acm rsub rs ltac: (assoc_mid H1). }
{ use_acm2s acm rsub rs ltac: (assoc_mid H3). }
{ use_acm2s acm rsub rs list_assoc_l'. }
{ use_acm2s acm rsub rs ltac: (assoc_mid H). }
}

*{ apply eq_sym in H4. list_eq_nc. contradiction. }
}

(* BBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acmL acm rsub rs. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s acm rsub rs ltac: (assoc_mid H1). }
{ use_acm2s acm rsub rs ltac: (assoc_mid H3). }
{ use_acm2s acm rsub rs list_assoc_l'. }
{ use_acm2s acm rsub rs ltac: (assoc_mid H). }
}

*{ apply eq_sym in H4. list_eq_nc. contradiction. }
}
}
(* another case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw nsr rs sppc c (Γ', Δ, d) acm inps0 swap. }

Qed.

Check gen_swapL_step_bsr.

(* can we improve on having two different tactics use_acmR and use_acmR2 ? *)
(* can we adapt use_acmL to do for use_acmR as well ? *)
Ltac use_acmR acm rsub rs swap :=
(* interchange two sublists of list of formulae *)
eapply derI ; [> unfold rsub in rs ; apply rs ; clear rs ;
rewrite list_rearr20 ; apply NSlctxt' ;
(apply WBoxLs || apply BBoxLs) |
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_swapL_def' in acm ;
rewrite -> ?can_gen_swapR_def' in acm ;
unfold nslext ; list_assoc_r' ; simpl ; eapply acm ] ;
[> exact swap | apply nslext2_def | reflexivity ].

Ltac use_acmR2 acm rsub rs swap :=
(* interchange two sublists of list of formulae *)
eapply derI ; [> unfold rsub in rs ; apply rs ; clear rs ;
list_assoc_r' ; simpl ;
rewrite list_rearr20 ; apply NSlctxt' ;
(apply WBoxLs || apply BBoxLs) |
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_swapL_def' in acm ;
rewrite -> ?can_gen_swapR_def' in acm ;
unfold nslext ; rewrite - list_rearr21 ; eapply acm ] ;
[> exact swap | rewrite list_rearr21 ; apply nslext2_def | reflexivity ].

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

inversion sppc. (* solves first goal *)

all : cycle 1.

(* case of exchange in sequent to the left of where rule applied *)
{ nsgen_sw nsr rs sppc c (Γ, Δ', d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
{ nsgen_sw nsr rs sppc pp (Γ, Δ', d) acm inps0 swap. }

all : cycle 1.

(* another case of exchange in sequent to the right of where rule applied *)
{ nsgen_sw nsr rs sppc c (Γ, Δ', d) acm inps0 swap. }

(* swap in the first of the two sequents affected by the rule *)
(* here the exchange is on the right and the rules operate on the left *)
{ clear nsr.  inversion sppc ; subst ; clear sppc ; (* 2 subgoals *)
  use_acmR acm rsub rs swap. }

{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
{ use_acmR acm rsub rs swap. }
{ use_acmR2 acm rsub rs swap. }
{ apply eq_sym in H4. list_eq_nc. contradiction. }
}
{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
{ use_acmR acm rsub rs swap. }
{ use_acmR2 acm rsub rs swap. }
{ apply eq_sym in H4. list_eq_nc. contradiction. }
}
}  
Qed.

Check gen_swapR_step_bsr.

