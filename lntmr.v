
(* modal rules *)

Require Import ssreflect.

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

(* same number of sequents in each premise as in conclusion 
  (both before and after extension) *)
Lemma seqrule_s_pcb_len: forall W pss qss cs ds ps, 
  @seqlrule_s W pss cs qss ds -> In ps pss -> length ps = length cs.
Proof.  induction pss ; intros.
  simpl in H0. tauto.
  apply in_inv in H0. destruct H0.
  TBC


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

rewrite -> app_nil_r in *.
simpl in *.

(* use acm *)


{ nsright pp G0 seqe d0 x c0 Ge HeqGe
  K d ps ps0 inps0 pse K0 drs nsr acm G seq rs. }
all : revgoals.
{ nsleft pp G0 seqe d0 x c0 He HeqHe
  K d ps ps0 inps0 pse K0 drs nsr acm G seq rs. }

(* now case where move and rule application occur in the same sequent *)
cE. clear pp. injection H0 as.
inversion sppc as [? ? ? ? ? ? pr mse se].
unfold seqext in se.
subst.  clear nsr. clear sppc.
destruct c0.
injection se as sel ser.
subst.
(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply princrule_L_oe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)).
*)



