Add LoadPath "../general".

(* modal rules *)

Require Import ssreflect.
Require Import Omega.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.
Require Import lntmtacs.
Require Import lntls.
Require Import lntrs.

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
  restricted to two sequents plus context, and one premise *)
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

Inductive pdsrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | Psrules : forall ps c,
    nsrule (seqrule (@princrule V)) ps c -> pdsrules ps c
  | Dsrules : forall ps c,
    nslrule (@dsrules V) ps c -> pdsrules ps c.

Lemma gen_swapL_step_dsr: forall V ps concl last_rule rules,
  last_rule = nslrule (@dsrules V) ->
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
(* here the exchange is on the right and the rules operate on the left *)
-{ inversion sppc ; subst ; clear sppc ; (* 2 subgoals *)
   [> use_acm_sw_sep acm rs swap WDiaRs |
     use_acm_sw_sep acm rs swap BDiaRs ]. }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw rs sppc c (Γ', Δ, d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw rs sppc pp (Γ', Δ, d) acm inps0 swap. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep acm rs swap WDiaRs. }
*{ use_acm_sw_sep acm rs swap WDiaRs. }
}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep acm rs swap BDiaRs. }
*{ use_acm_sw_sep acm rs swap BDiaRs. }
}
}

(* another case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw rs sppc c (Γ', Δ, d) acm inps0 swap. }

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

inversion nsr as [? ? ? K sppc mnsp nsc]. clear nsr.
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

Lemma gen_swapR_step_dsr: forall V ps concl last_rule rules,
  last_rule = nslrule (@dsrules V) ->
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
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs WDiaRs. }
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs BDiaRs. }
  }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw rs sppc c (Γ, Δ', d) acm inps0 swap. }
(* case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw rs sppc pp (Γ, Δ', d) acm inps0 swap. }

(* here, swap in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WDia *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs WDiaRs. }
(* swapping in second sequent of principal rule *)
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s acm rs WDiaRs ltac: (assoc_mid H1). }
{ use_acm2s acm rs WDiaRs ltac: (assoc_mid H3). }
{ use_acm2s acm rs WDiaRs list_assoc_l'. }
{ use_acm2s acm rs WDiaRs ltac: (assoc_mid H). }
} 
}

(* BDia *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1 acm rs BDiaRs. }
(* swapping in second sequent of principal rule *)
*{
inversion_clear swap. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s acm rs BDiaRs ltac: (assoc_mid H1). }
{ use_acm2s acm rs BDiaRs ltac: (assoc_mid H3). }
{ use_acm2s acm rs BDiaRs list_assoc_l'. }
{ use_acm2s acm rs BDiaRs ltac: (assoc_mid H). }
}
}
}
(* another case of exchange in sequent to the right of where rule applied *)
-{ nsgen_sw rs sppc c (Γ, Δ', d) acm inps0 swap. }

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

