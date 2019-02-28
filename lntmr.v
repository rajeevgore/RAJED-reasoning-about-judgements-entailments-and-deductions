
(* modal rules *)

Require Import ssreflect.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.

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
  | map2_cons : forall f u us v vs ws, is_map2 f us vs ws -> 
    is_map2 f (u :: us) (v :: vs) (f u v :: ws).

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

Definition rsub U V f g := forall (u : U) (v : V), f u v -> g u v.

Inductive pdrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | Prules : forall ps c,
    nsrule (seqrule (@princrule V)) ps c -> pdrules ps c
  | Drules : forall ps c,
    nslrule (seqlrule (@drules V)) ps c -> pdrules ps c.

Definition gen_swapL_step (V : Set)
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  Forall (can_gen_swapL rules) ps -> rsub last_rule rules -> 
  can_gen_swapL rules concl.

Axiom gen_swapL_step_pr: forall V ps concl, gen_swapL_step 
  (nsrule (seqrule (@princrule V))) (@pdrules V) ps concl.

Axiom gen_swapL_step_dr: forall V ps concl, gen_swapL_step 
  (nslrule (seqlrule (@drules V))) (@pdrules V) ps concl.

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
eapply g. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros. apply Prules.  assumption.
subst.
pose gen_swapL_step_dr.
unfold gen_swapL_step in g.
eapply g. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros. apply Drules.  assumption.
Qed.


Lemma can_gen_swapL_mono: forall (V : Set)
  (rulesa rulesb : rls (list (rel (list (PropF V)) * dir))) ns,
  rsub rulesa rulesb ->
  can_gen_swapL rulesa ns -> can_gen_swapL rulesb ns.
Proof.  unfold can_gen_swapL.  intros. 
eapply H in H1.
eapply derrec_rmono in X. exact X. exact H1. exact H2. Qed.


(*
Lemma gen_swapL_step_pr': forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rsub last_rule rules -> last_rule = nsrule (seqrule (@princrule V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.  intros.  unfold gen_swapL_step. intros. subst.
eapply can_gen_swapL_mono in X0. exact X0.
inversion H0. unfold nsext in H5.
unfold can_gen_swapL.  intros.
unfold nsext in H7.
(* cases of where the swap occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ1 ++ Γ3 ++ Γ2 ++ Γ4, Δ) as seqe.

decompose [or] H7.
(* this fails *)
{ nsright H7 G0 seqe d0 x c0 Ge HeqGe
  H d ps ps0 inps0 pse H6 H1 H0 H2 G seq. }
all : revgoals.
{ nsleft H7 G0 seqe d0 x c0 He HeqHe
  H2 d ps ps0 inps0 pse H6 H0 H H1 G seq. }




*)
