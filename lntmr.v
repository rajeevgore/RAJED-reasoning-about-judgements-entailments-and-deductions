
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

Set Implicit Arguments.

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
intros lreq nsr drs acm rs. subst.

inversion nsr as [? ? ? K sppc mnsp nsc].
unfold nslext in nsc.
unfold can_gen_swapL.   intros until 0. intros pp ss.
unfold nslext in pp. subst.

remember (Γ1 ++ Γ3 ++ Γ2 ++ Γ4, Δ) as seqe.
acacD' ; subst. (* 6 subgoals, the various locs where the exchange might be
  relative to where the rule is active *)
inversion sppc. (* solves first goal *)

all: rewrite -> ?app_nil_r in *.
all : cycle 1.

(* case of exchange in sequent to the left of where rule applied *)
{ nsgen drs nsr rs c sppc q qin acm inps0 list_assoc_r list_assoc_r'.  }
(* case of exchange in sequent to the right of where rule applied *)
{ nsgen drs nsr rs pp sppc q qin acm inps0 
  ltac: (rewrite app_assoc) ltac: (rewrite app_assoc). }
all : cycle 1.
(* another case of exchange in sequent to the right of where rule applied *)

{ nsgen drs nsr rs c sppc q qin acm inps0 
  ltac: (rewrite app_assoc ; rewrite (app_assoc _ pp1))
  ltac: (rewrite - !app_assoc). }

(* now have two cases where one of the sequents involved in the rule is 
  where the exchange takes place, they should be easy as the exchange
  is on the left and the rules operate on the right *)
clear nsr.  inversion sppc.

{ dia1l sppc rs acm. } (* for WDia *)
{ dia1l sppc rs acm. } (* for BDia *)

(* now where exchange is in the right one of the two sequents in the rule *)
clear nsr.  inversion sppc. 

{
subst. clear sppc.  acacD'. (* 3 subgoals resulting *)

+ { subst.  rewrite ?app_nil_r. 
  dia1l' rs acm ltac: (rewrite app_comm_cons) idtac. }

+ { subst. simpl.  rewrite list_rearr19.
 dia1l' rs acm idtac ltac: (rewrite (list_rearr16' G)). }

+ { subst. simpl.  apply eq_sym in H4. list_eq_nc. contradiction. }
}

{
clear sppc.  acacD'. (* 3 subgoals *)

+ { subst. rewrite ?app_nil_r. 
  dia1l' rs acm ltac: (rewrite app_comm_cons) idtac. }

+ { subst. simpl.  rewrite list_rearr19.
 dia1l' rs acm idtac ltac: (rewrite (list_rearr16' G)). }

+ { subst. simpl.  apply eq_sym in H4. list_eq_nc. contradiction. }
}

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
intros lreq nsr drs acm rs. subst.

inversion nsr as [? ? ? K sppc mnsp nsc].
unfold nslext in nsc.
unfold can_gen_swapR.   intros until 0. intros pp ss.
unfold nslext in pp. subst.

remember (Γ, Δ1 ++ Δ3 ++ Δ2 ++ Δ4) as seqe.
acacD' ; subst. (* 6 subgoals, the various locs where the exchange might be
  relative to where the rule is active *)
inversion sppc. (* solves first goal *)

all: rewrite -> ?app_nil_r in *.
all : cycle 1.

(* case of exchange in sequent to the left of where rule applied *)
{ nsgen drs nsr rs c sppc q qin acm inps0 list_assoc_r list_assoc_r'.  }
(* case of exchange in sequent to the right of where rule applied *)
{ nsgen drs nsr rs pp sppc q qin acm inps0 
  ltac: (rewrite app_assoc) ltac: (rewrite app_assoc). }
all : cycle 1.
(* another case of exchange in sequent to the right of where rule applied *) 
{ nsgen drs nsr rs c sppc q qin acm inps0 
  ltac: (rewrite app_assoc ; rewrite (app_assoc _ pp1))
  ltac: (rewrite - !app_assoc). }

(* now have two cases where one of the sequents involved in the rule is where
  the exchange takes place, they will be harder than exchange on the left *)
  
{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 10 subgoals resulting *)
{ use_drs acm rsub rs list_assoc_l' drs. }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ H2 ++ (WDia A :: H5) ++ Δ4). }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ (H2 ++ WDia A :: H4) ++ Δ3 ++ Δ4). }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ Δ2 ++ H1 ++ WDia A :: H1r). }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ Δ2 ++ (H1 ++ WDia A :: H6) ++ Δ4). }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ Δ2 ++ Δ3 ++ H4 ++ WDia A :: H1r). }
{ use_drs acm rsub rs idtac drs. }
{ use_drs acm rsub rs idtac drs. }
{ use_acm acm rsub rs drs (Γ, H1l ++ (WDia A :: H3) ++ Δ3 ++ Δ4). }
{ use_acm acm rsub rs drs (Γ, (H1l ++ WDia A :: H1) ++ Δ2 ++ Δ3 ++ Δ4). }
}

{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 10 subgoals resulting *)
{ use_drs acm rsub rs list_assoc_l' drs. }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ H2 ++ (BDia A :: H5) ++ Δ4). }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ (H2 ++ BDia A :: H4) ++ Δ3 ++ Δ4). }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ Δ2 ++ H1 ++ BDia A :: H1r). }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ Δ2 ++ (H1 ++ BDia A :: H6) ++ Δ4). }
{ use_acm acm rsub rs drs (Γ, Δ1 ++ Δ2 ++ Δ3 ++ H4 ++ BDia A :: H1r). }
{ use_drs acm rsub rs idtac drs. }
{ use_drs acm rsub rs idtac drs. }
{ use_acm acm rsub rs drs (Γ, H1l ++ (BDia A :: H3) ++ Δ3 ++ Δ4). }
{ use_acm acm rsub rs drs (Γ, (H1l ++ BDia A :: H1) ++ Δ2 ++ Δ3 ++ Δ4). }
}
}

{ clear nsr.  inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 15 subgoals resulting *)
{ use_drs acm rsub rs idtac drs. }
{ use_drs acm rsub rs idtac drs. }
{ use_acm acm rsub rs drs (G1, H1l ++ (WDia A :: H6) ++ Δ3 ++ Δ4). }
{ use_acm acm rsub rs drs (G1, (H1l ++ WDia A :: H5) ++ Δ2 ++ Δ3 ++ Δ4). }
{ use_drs acm rsub rs list_assoc_l' drs. }
{ use_acm acm rsub rs drs (G1, Δ1 ++ H2 ++ (WDia A :: H8) ++ Δ4). }
{ use_acm acm rsub rs drs (G1, Δ1 ++ (H2 ++ WDia A :: H7) ++ Δ3 ++ Δ4). }
{ use_acm acm rsub rs drs (G1, Δ1 ++ Δ2 ++ H5 ++ WDia A :: H1r). }
{ use_acm acm rsub rs drs (G1, Δ1 ++ Δ2 ++ (H5 ++ WDia A :: H9) ++ Δ4). }
{ use_acm acm rsub rs drs (G1, Δ1 ++ Δ2 ++ Δ3 ++ H7 ++ WDia A :: H1r). }
(* now instances of exchange in second sequent of the rule *)

{ use_acm2 acm rsub rs drs list_assoc_r'
  (G2, (H2l ++ A :: H4) ++ Δ2 ++ Δ3 ++ Δ4). }

{ use_acm2 acm rsub rs drs ltac: (assoc_mid H7)
  (G2, Δ1 ++ (H4 ++ A :: H7) ++ Δ3 ++ Δ4). }

{ use_acm2 acm rsub rs drs ltac: (assoc_mid H9)
  (G2, Δ1 ++ Δ2 ++ (H7 ++ A :: H9) ++ Δ4). }

{ use_acm2 acm rsub rs drs list_assoc_l' 
  (G2, Δ1 ++ Δ2 ++ Δ3 ++ (H9 ++ A :: H2r)). }

{ apply eq_sym in H4. list_eq_nc. contradiction. }
}

{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 15 subgoals resulting *)
{ use_drs acm rsub rs idtac drs. }
{ use_drs acm rsub rs idtac drs. }
{ use_acm acm rsub rs drs (G1, H1l ++ (BDia A :: H6) ++ Δ3 ++ Δ4). }
{ use_acm acm rsub rs drs (G1, (H1l ++ BDia A :: H5) ++ Δ2 ++ Δ3 ++ Δ4). }
{ use_drs acm rsub rs list_assoc_l' drs. }
{ use_acm acm rsub rs drs (G1, Δ1 ++ H2 ++ (BDia A :: H8) ++ Δ4). }
{ use_acm acm rsub rs drs (G1, Δ1 ++ (H2 ++ BDia A :: H7) ++ Δ3 ++ Δ4). }
{ use_acm acm rsub rs drs (G1, Δ1 ++ Δ2 ++ H5 ++ BDia A :: H1r). }
{ use_acm acm rsub rs drs (G1, Δ1 ++ Δ2 ++ (H5 ++ BDia A :: H9) ++ Δ4). }
{ use_acm acm rsub rs drs (G1, Δ1 ++ Δ2 ++ Δ3 ++ H7 ++ BDia A :: H1r). }
(* now instances of exchange in second sequent of the rule *)

{ use_acm2 acm rsub rs drs list_assoc_r'
  (G2, (H2l ++ A :: H4) ++ Δ2 ++ Δ3 ++ Δ4). }

{ use_acm2 acm rsub rs drs ltac: (assoc_mid H7)
  (G2, Δ1 ++ (H4 ++ A :: H7) ++ Δ3 ++ Δ4). }

{ use_acm2 acm rsub rs drs ltac: (assoc_mid H9)
  (G2, Δ1 ++ Δ2 ++ (H7 ++ A :: H9) ++ Δ4). }

{ use_acm2 acm rsub rs drs list_assoc_l' 
  (G2, Δ1 ++ Δ2 ++ Δ3 ++ (H9 ++ A :: H2r)). }

{ apply eq_sym in H4. list_eq_nc. contradiction. }
}
}
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

