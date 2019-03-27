
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

(* context of a nested sequent *)
Definition nslext W (G H seqs : list W) := G ++ seqs ++ H.

Lemma nslext_def: forall W G H seqs, @nslext W G H seqs = G ++ seqs ++ H.
Proof.  unfold nslext. reflexivity.  Qed.

Inductive nslrule W (sr : rls (list W)) : rls (list W) :=
  | NSlctxt : forall ps c G H, sr ps c ->
    nslrule sr (map (nslext G H) ps) (nslext G H c).

Inductive is_map2 U V W :
  (U -> V -> W) -> list U -> list V -> list W -> Prop :=
  | map2_nil : forall f, is_map2 f [] [] []
  | map2_cons : forall f u us v vs ws, is_map2 f us vs ws -> 
    is_map2 f (u :: us) (v :: vs) (f u v :: ws).

Lemma is_map2_lens: forall X Y Z (f : X -> Y -> Z) ws us vs, 
  is_map2 f us vs ws -> length ws = length us /\ length ws = length vs.
Proof. induction ws ; intros ; inversion H. tauto.
  subst. apply IHws in H4. simpl. 
  destruct H4. split. rewrite H0. reflexivity.
  rewrite H1. reflexivity. Qed.

(* seqlrule_s pss cs qss ds means that the nth member of cs and 
  of each member of pss is extended, per seqrule_s, to become
  the nth member of ds and of each member of qss *)
Inductive seqlrule_s (W : Set) : 
  list (list (rel (list W) * dir)) -> list (rel (list W) * dir) ->
  rls (list (rel (list W) * dir)) := 
  | Slcons : forall ps pss pss' c cs qs qss qss' d ds bf, 
    seqrule_s (map fst ps) c (map fst qs) d ->
    seqlrule_s pss cs qss ds ->  
    map snd ps = map snd qs ->
    is_map2 cons ps pss pss' -> 
    is_map2 cons qs qss qss' -> 
    seqlrule_s pss' ((c, bf) :: cs) qss' ((d, bf) :: ds).

(* same number of premises before and after extension *)
Lemma seqrule_s_nprems: forall W pss qss cs ds, 
  @seqlrule_s W pss cs qss ds -> length pss = length qss.
Proof.  intros ; inversion H ; subst. 
  pose (arg_cong (@length dir) H2). rewrite -> !map_length in e.
  apply is_map2_lens in H3.  apply is_map2_lens in H4.
  destruct H3.  destruct H4.  rewrite H3 H4 e. reflexivity. Qed.

(* same number of sequents in conclusion before and after extension *)
Lemma seqrule_s_conc_len: forall W cs ds pss qss, 
  @seqlrule_s W pss cs qss ds -> length cs = length ds.
Proof.  induction cs ; intros ; inversion H.
  subst. simpl. apply IHcs in H3. rewrite H3. reflexivity. Qed.

Lemma in_is_map2: forall A B C (f : A -> B -> C) zs xs ys z,
  is_map2 f xs ys zs -> In z zs ->
  exists x y, In x xs /\ In y ys /\ z = f x y.
Proof.  induction zs ; intros.
  apply in_nil in H0. contradiction.
  apply in_inv in H0. sD.
  subst.  inversion H. subst. eexists.  eexists.
  split.  eapply in_eq.  split.  eapply in_eq.  reflexivity.
  inversion H. subst.
  eapply IHzs in H5. cD. eexists.  eexists.
  split. apply in_cons.  eassumption.
  split. apply in_cons.  eassumption. eassumption.  
  assumption. Qed.

(* same number of sequents in each premise as in conclusion 
  (both before and after extension) *)
Lemma seqrule_s_pcb_len: forall W pss qss cs ds, 
  @seqlrule_s W pss cs qss ds -> forall ps, In ps pss -> length ps = length cs.
Proof. intros until 0. intro.  induction H. intros.
  eapply in_is_map2 in H2.
  2 : eassumption. cD. subst. simpl.
  apply IHseqlrule_s in H7. rewrite H7. reflexivity. Qed.

Inductive seqlrule (W : Set) (sr : rls (list (rel (list W) * dir))) :
  rls (list (rel (list W) * dir)) :=  
  | Slrule : forall pss cs qss ds, seqlrule_s pss cs qss ds -> sr pss cs ->
    seqlrule sr qss ds.

Inductive drules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WDiaR : forall A d, drules [[(pair [] [WDia A], d); (pair [] [A], fwd)]]
      [(pair [] [WDia A], d); (pair [] [], fwd)]
  | BDiaR : forall A d, drules [[(pair [] [BDia A], d); (pair [] [A], bac)]]
      [(pair [] [WDia A], d); (pair [] [], bac)].
      
Check (fun V => nslrule (seqlrule (@drules V))).

Lemma drules_conc_ne: forall V ps,  drules (V:=V) ps [] -> False.
Proof.  intros. inversion H. Qed.

Inductive pdrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | Prules : forall ps c,
    nsrule (seqrule (@princrule V)) ps c -> pdrules ps c
  | Drules : forall ps c,
    nslrule (seqlrule (@drules V)) ps c -> pdrules ps c.

Axiom gen_swapL_step_dr_ax: forall V ps concl last_rule rules,
  last_rule = nslrule (seqlrule (@drules V)) ->
  gen_swapL_step last_rule rules ps concl.

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

(* including first modal rules *)
Lemma gen_swapmL: forall (V : Set) ns
  (D : derrec (@pdrules V) (fun _ => False) ns),
    can_gen_swapL (@pdrules V) ns.
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
intros. apply Prules.  assumption.
subst.
pose gen_swapL_step_dr_ax.
unfold gen_swapL_step in g.
eapply g.  reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros. apply Drules.  assumption.
Qed.

Lemma sdne: forall V ps, seqlrule (drules (V:=V)) ps [] -> False.
Proof. intros.  inversion H. subst.
inversion H1 ; subst ;
apply seqrule_s_conc_len in H0 ; simpl in H0 ; omega. Qed.

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
{
clear drs nsr.
eapply derI.  unfold rsub in rs. apply rs.
assoc_mid c.
rewrite <- nslext_def.
apply NSlctxt. exact sppc.
rewrite dersrec_forall.
intros q qin.
rewrite -> in_map_iff in qin.
cE.
subst q.
rewrite -> Forall_forall in acm.
rename_last inps0.  eapply in_map in inps0.  pose (acm _ inps0) as acmps.
unfold can_gen_swapL in acmps.
unfold nslext.
list_assoc_r.
eapply acmps.
unfold nslext.
list_assoc_r'.
reflexivity.
reflexivity.
}
(* case of exchange in sequent to the right of where rule applied *)
{
clear drs nsr.
eapply derI.  unfold rsub in rs. apply rs.
assoc_mid pp.
rewrite <- nslext_def.
apply NSlctxt. exact sppc.
rewrite dersrec_forall.
intros q qin.
rewrite -> in_map_iff in qin.
cE.
subst q.
rewrite -> Forall_forall in acm.
rename_last inps0.  eapply in_map in inps0.  pose (acm _ inps0) as acmps.
unfold can_gen_swapL in acmps.
unfold nslext.
rewrite app_assoc.
eapply acmps.
unfold nslext.
rewrite app_assoc.
reflexivity.
reflexivity.
}
all : cycle 1.
(* another case of exchange in sequent to the right of where rule applied *)
{
clear drs nsr.
eapply derI.  unfold rsub in rs. apply rs.
assoc_mid c.
rewrite <- nslext_def.
apply NSlctxt. exact sppc.
rewrite dersrec_forall.
intros q qin.
rewrite -> in_map_iff in qin.
cE.
subst q.
rewrite -> Forall_forall in acm.
rename_last inps0.  eapply in_map in inps0.  pose (acm _ inps0) as acmps.
unfold can_gen_swapL in acmps.
unfold nslext.
rewrite app_assoc.
rewrite (app_assoc _ pp1).
eapply acmps.
unfold nslext.
rewrite - !app_assoc.
reflexivity.
reflexivity.
}

(* now have two cases where one of the sequents involved in the rule is 
  where the exchange takes place, they should be easy as the exchange
  is on the left and the rules operate on the right *)
clear nsr. 
inversion sppc.

{
subst. clear sppc.
eapply derI.  unfold rsub in rs. apply rs.
rewrite app_comm_cons.  rewrite <- (nslext_def G0).
apply NSlctxt. apply WDiaRs.
rewrite dersrec_single.

rewrite -> Forall_map_single in acm.
unfold can_gen_swapL in acm.
unfold nslext.
list_assoc_r. simpl.
eapply acm ; clear acm.
unfold nslext. list_assoc_r'. simpl. reflexivity. reflexivity.
}

(* now similar to above for BDia *)
{
subst. clear sppc.
eapply derI.  unfold rsub in rs. apply rs.
rewrite app_comm_cons.  rewrite <- (nslext_def G0).
apply NSlctxt. apply BDiaRs.
rewrite dersrec_single. 

rewrite -> Forall_map_single in acm.
unfold can_gen_swapL in acm.
unfold nslext.
list_assoc_r. simpl.
eapply acm ; clear acm.
unfold nslext. list_assoc_r'. simpl. reflexivity. reflexivity.
}

(* now where exchange is in the right one of the two sequents in the rule *)
clear nsr.
inversion sppc. 

subst. clear sppc.
(* at this point we seem to have two possibilities,
  one of which we have already done *)
acacD'. (* 4 subgoals *)

{
subst.
rewrite ?app_nil_r.

(* from here, same as above *)
eapply derI.  unfold rsub in rs. apply rs.
rewrite app_comm_cons.  rewrite <- (nslext_def G).
apply NSlctxt. apply WDiaRs.
rewrite dersrec_single. 

rewrite -> Forall_map_single in acm.
unfold can_gen_swapL in acm.
unfold nslext.
list_assoc_r. simpl.
eapply acm ; clear acm.
unfold nslext. list_assoc_r'. simpl. reflexivity. reflexivity.
}

{
subst. simpl.
rewrite list_rearr19.
eapply derI.  unfold rsub in rs. apply rs.
rewrite <- (nslext_def G).
apply NSlctxt. apply WDiaRs.
rewrite dersrec_single.

rewrite -> Forall_map_single in acm.
unfold can_gen_swapL in acm.
unfold nslext.
list_assoc_r. simpl.
rewrite (list_rearr16' G).
eapply acm ; clear acm.
unfold nslext. list_assoc_r'. simpl. reflexivity. reflexivity.
}

subst. simpl.
apply eq_sym in H4. list_eq_nc. contradiction.

clear sppc.
acacD'. (* 3 subgoals *)

{
subst. rewrite ?app_nil_r. 
eapply derI.  unfold rsub in rs. apply rs.
rewrite app_comm_cons.  rewrite <- (nslext_def G).
apply NSlctxt. apply BDiaRs.
rewrite dersrec_single.

rewrite -> Forall_map_single in acm.
unfold can_gen_swapL in acm.
unfold nslext.
list_assoc_r. simpl.
eapply acm ; clear acm.
unfold nslext. list_assoc_r'. simpl. reflexivity. reflexivity.
}

{
subst. simpl.
rewrite list_rearr19.
eapply derI.  unfold rsub in rs. apply rs.
rewrite <- (nslext_def G).
apply NSlctxt. apply BDiaRs.
rewrite dersrec_single.

rewrite -> Forall_map_single in acm.
unfold can_gen_swapL in acm.
unfold nslext.
list_assoc_r. simpl.
rewrite (list_rearr16' G).
eapply acm ; clear acm.
unfold nslext. list_assoc_r'. simpl. reflexivity. reflexivity.
}
subst. simpl.
apply eq_sym in H4. list_eq_nc. contradiction.

Qed.

Check gen_swapL_step_dsr.

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

