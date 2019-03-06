
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


