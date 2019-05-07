
(* modal rules *)

Require Import ssreflect.
Require Import Omega.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.
Require Import lntls.
Require Import lntrs.
Require Import lntbr.

Set Implicit Arguments.

(* diamond rules, as in an earlier version of the system *)

Inductive drules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WDiaR : forall A d, drules [[(pair [] [WDia A], d); (pair [] [A], fwd)]]
      [(pair [] [WDia A], d); (pair [] [], fwd)]
  | BDiaR : forall A d, drules [[(pair [] [BDia A], d); (pair [] [A], bac)]]
      [(pair [] [WDia A], d); (pair [] [], bac)].
      
Lemma drules_conc_ne: forall V ps,  drules (V:=V) ps [] -> False.
Proof.  intros. inversion H. Qed.

(* try more specific way of defining modal rules, for drules,
  restricted to two sequents plus context, and one premise 
Inductive dsrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  gives WDiaRs and DiaRs, now in lntbr.v
  *)

Inductive pdsrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | Psrules : forall ps c,
    nsrule (seqrule (@princrule V)) ps c -> pdsrules ps c
  | Dsrules : forall ps c,
    nslrule (@dsrules V) ps c -> pdsrules ps c.

(* for diamond rules, exchange on left, on 1st sequent *)
Ltac dia1l' rs acm rw1 rw2 := 
  eapply derI ; [> unfold rsub in rs ; apply rs ; rw1 ;  
  apply NSlctxt' ; (apply WDiaRs || apply BDiaRs) | 
  rewrite dersrec_single ;  rewrite -> Forall_map_single in acm ;
  unfold can_gen_swapL in acm ;  unfold nslext ;
  list_assoc_r ; simpl ; rw2 ;
  eapply acm ; [> | reflexivity ] ; clear acm ;
  unfold nslext ; list_assoc_r' ; simpl ; reflexivity]. 
  
Ltac dia1l sppc rs acm := subst ; clear sppc ;
  dia1l' rs acm ltac: (rewrite app_comm_cons) idtac.
  
Lemma gen_swapL_step_dsr: forall V ps concl last_rule rules,
  last_rule = nslrule (@dsrules V) ->
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
(* here the exchange is on the right and the rules operate on the left *)
-{ clear nsr.  inversion sppc ; subst ; clear sppc ; (* 2 subgoals *)
  use_acm_sw_sep acm rs swap. }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw nsr rs sppc c (Γ', Δ, d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw nsr rs sppc pp (Γ', Δ, d) acm inps0 swap. }

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
-{ nsgen_sw nsr rs sppc c (Γ', Δ, d) acm inps0 swap. }

Qed.

Check gen_swapL_step_dsr.


(* including first modal rules, in the specific (dsrules) form *)
Lemma gen_swapmsL: forall (V : Set) ns
  (D : derrec (@pdsrules V) (fun _ => False) ns),
    can_gen_swapL (@pdsrules V) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_swapL_step_pr.
unfold gen_swapL_step in g.
eapply g.  reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros. apply Psrules.  assumption.
subst.
pose gen_swapL_step_dsr.
unfold gen_swapL_step in g.
eapply g.  reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros. apply Dsrules.  assumption.
Qed.

Check gen_swapmsL.

(*
Lemma gen_swapL_step_dr: forall V ps concl last_rule rules,
  last_rule = nslrule (seqlrule (@drules V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. subst.

inversion nsr as [? ? ? K sppc mnsp nsc].
unfold nslext in nsc.
unfold can_gen_swapL.   intros until 0. intros pp ss.
unfold nslext in pp.

remember (Γ1 ++ Γ3 ++ Γ2 ++ Γ4, Δ) as seqe.
acacD' ; subst. (* 6 subgoals, the various locs where the exchange might be
  relative to where the rule is active *)
apply sdne in sppc. contradiction.

all: rewrite -> ?app_nil_r in *.

all : cycle 1.

(* I think this will be too complicated, 
  don't use seqlrule, but write rules explicitly 
  using the fact that drules rules have exactly two sequents 
  and one premise *)

*)
Ltac use_acm acm rsub rs drs trans_tm := 
(* interchange two sublists of list of formulae *)
clear drs ;
eapply derI ; [> unfold rsub in rs ; apply rs ;
rewrite list_rearr20 ;  apply NSlctxt' ;
assoc_single_mid ;
(apply WDiaRs || apply BDiaRs) |
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
unfold can_gen_swapR in acm ; 
unfold nslext ; list_assoc_r' ; simpl ;
eapply derrec_same_nsR ] ; [> 
eapply acm ; [> apply nslext2_def |] ; 
eapply (@eq_trans _ _ trans_tm) ;
[> list_eq_assoc | reflexivity] | list_eq_assoc].

Ltac use_drs acm rsub rs rtac drs :=  
(*  use WDiaRs rule directly from drs *)
  clear acm ;
  eapply derI ; [> unfold rsub in rs ; apply rs ;
  rewrite list_rearr20 ;
  apply NSlctxt' ;
  rtac ; (* rewrite using associativity if needed *)
  (apply WDiaRs || apply BDiaRs) |
  exact drs ].

Ltac use_acm2 acm rsub rs drs rw trans_tm := 
(* interchange two sublists of list of formulae *)
clear drs ;
eapply derI ; [> unfold rsub in rs ; apply rs ;
rewrite list_rearr21 ;  apply NSlctxt' ;
rw ; 
(apply WDiaRs || apply BDiaRs) |
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
unfold can_gen_swapR in acm ; 
unfold nslext ; list_assoc_r' ; simpl ;
rewrite list_rearr22 ;
eapply derrec_same_nsR ] ; [> 
eapply acm ; [> apply nslext2_def' |] ; 
eapply (@eq_trans _ _ trans_tm) ;
[> list_eq_assoc | reflexivity] | list_eq_assoc ].

Lemma gen_swapR_step_dsr: forall V ps concl last_rule rules,
  last_rule = nslrule (@dsrules V) ->
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
-{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs. }
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs. }
  }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw nsr rs sppc c (Γ, Δ', d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw nsr rs sppc pp (Γ, Δ', d) acm inps0 swap. }

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
-{ nsgen_sw nsr rs sppc c (Γ, Δ', d) acm inps0 swap. }

Qed.

Check gen_swapR_step_dsr.


(* including first modal rules, in the specific (dsrules) form *)
Lemma gen_swapmsR: forall (V : Set) ns
  (D : derrec (@pdsrules V) (fun _ => False) ns),
    can_gen_swapR (@pdsrules V) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_swapR_step_pr.
unfold gen_swapR_step in g.
eapply g.  reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros. apply Psrules.  assumption.
subst.
pose gen_swapR_step_dsr.
unfold gen_swapR_step in g.
eapply g.  reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros. apply Dsrules.  assumption.
Qed.

Check gen_swapmsR.

