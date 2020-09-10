
(* stuff to do with seqlrule, and ths modal diamond rules defined using it,
  now not used *)

Require Import ssreflect.
Require Import Omega.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.
Require Import lntls.
Require Import lntrs.
Require Import lntmr.

Set Implicit Arguments.

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
Lemma seqlrule_s_conc_len: forall W cs ds pss qss,
  @seqlrule_s W pss cs qss ds -> length cs = length ds.
Proof.  induction cs ; intros ; inversion H.
  subst. simpl. apply IHcs in H3. rewrite H3. reflexivity. Qed.

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

Inductive pdrules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | Prules : forall ps c,
    nsrule (seqrule (@princrule V)) ps c -> pdrules ps c
  | Drules : forall ps c,
    nslrule (seqlrule (@drules V)) ps c -> pdrules ps c.

Axiom gen_swapL_step_dr_ax: forall V ps concl last_rule rules,
  last_rule = nslrule (seqlrule (@drules V)) ->
  gen_swapL_step last_rule rules ps concl.

(* including first modal rules, in the general (using seqlrule) form *)
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

Check gen_swapmL.

Lemma sdne: forall V ps, seqlrule (drules (V:=V)) ps [] -> False.
Proof. intros.  inversion H. subst.
inversion H1 ; subst ;
apply seqlrule_s_conc_len in H0 ; simpl in H0 ; omega. Qed.



