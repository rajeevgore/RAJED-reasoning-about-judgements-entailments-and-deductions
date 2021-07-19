
(* linear logic phase semantics *)

Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT.
Require Import fmlsext lldefs.

Definition comm_monoid M m e := 
  (forall (x y z : M), m (m x y) z = m x (m y z)) /\
  (forall (x y : M), m x y = m y x) /\
  (forall (x : M), m x e = x) /\
  (forall (x : M), m e x = x).

(*
Section Phase_Space. (* fix a single phase space *)
Variable M : Type.
Variable m : M -> M -> M.
Variable e : M.
Variable bot : M -> Prop.
Hypothesis cmM : comm_monoid m e.
*)
Parameter M : Type.
Parameter m : M -> M -> M.
Parameter e : M.
Parameter bot : M -> Prop.
Axiom cmM : comm_monoid m e.

Definition lolli_sem (X Y : M -> Prop) u := forall (v : M), X v -> Y (m u v).
Definition dual_sem X := lolli_sem X bot.
Print Implicit lolli_sem.

Lemma dual_dual_sem (X : M -> Prop) u : X u -> dual_sem (dual_sem X) u.
Proof. unfold dual_sem.  unfold lolli_sem.  intros.
pose cmM as cmM'.  unfold comm_monoid in cmM'. destruct cmM'.
destruct H2.  rewrite H2. apply H0. exact H. Qed.

Lemma dual_anti (X Y : M -> Prop) : (forall u, X u -> Y u) ->
  forall v, dual_sem Y v -> dual_sem X v.
Proof. unfold dual_sem.  unfold lolli_sem. intros xy v yv w xw.
exact (yv _ (xy _ xw)). Qed.

Lemma dd_mono (X Y : M -> Prop) : (forall u, X u -> Y u) ->
  forall v, dual_sem (dual_sem X) v -> dual_sem (dual_sem Y) v.
Proof. intros xy.  exact (dual_anti _ (dual_anti _ xy)). Qed.

Lemma ddd_iff (X : M -> Prop) v :
  dual_sem (dual_sem (dual_sem X)) v <-> dual_sem X v.
Proof. split. apply dual_anti. apply dual_dual_sem. apply dual_dual_sem. Qed.

Inductive prods (X Y : M -> Prop) : M -> Prop :=
  | prodI : forall x y : M, X x -> Y y -> prods X Y (m x y).

Lemma prods_mono (X X' Y Y' : M -> Prop) : (forall u, X u -> X' u) ->
  (forall u, Y u -> Y' u) -> (forall u, prods X Y u -> prods X' Y' u).
Proof. intros xx yy u pxy. destruct pxy.
exact (prodI _ _ _ _ (xx _ H) (yy _ H0)). Qed.
 
Definition tens_sem X Y := dual_sem (dual_sem (prods X Y)).
Definition par_sem X Y := dual_sem (tens_sem (dual_sem X) (dual_sem Y)).

Inductive idems : M -> Prop := 
  | idemsI : forall x : M, m x x = x -> idems x.

Definition idem1 x := (m x x = x) /\ dual_sem (dual_sem (eq e)) x.

Fixpoint sem {V : Set} (sv : V -> M -> Prop) f := match f with 
  | Var v => sv v
  | DVar v => dual_sem (sv v)
  | Bot _ => bot
  | One _ => dual_sem (dual_sem (eq e))
  | Zero _ => dual_sem (dual_sem (fun _ => empty))
  | Top _ => fun _ => True
  | tens A B => tens_sem (sem sv A) (sem sv B)
  | par A B => par_sem (sem sv A) (sem sv B) 
  | plus A B => dual_sem (dual_sem (fun x => sem sv A x \/ sem sv B x))
  | wth A B => (fun x => sem sv A x /\ sem sv B x) 
  | Bang f => dual_sem (dual_sem (fun x => sem sv f x /\ idem1 x))
  | Query f => dual_sem (fun x => dual_sem (sem sv f) x /\ idem1 x)
  end.

Definition fact X := forall u, dual_sem (dual_sem X) u -> X u.

Lemma fact_dual X : fact (dual_sem X).
Proof. unfold fact. apply dual_anti. apply dual_dual_sem. Qed.

(* dual_sem o dual_sem is a closure operator and facts are the closed sets *)
Lemma facts_int X Y : fact X -> fact Y -> fact (fun u => X u /\ Y u).
unfold fact. intros fx fy u fxy. split.
- apply fx.  eapply dd_mono. 2: exact fxy. firstorder.
- apply fy.  eapply dd_mono. 2: exact fxy. firstorder. Qed.

Lemma dual_sem_1 : forall u, iff (dual_sem (eq e) u) (bot u).
Proof. unfold dual_sem. unfold lolli_sem.
pose cmM as cmM'.  unfold comm_monoid in cmM'. destruct cmM'.
destruct H0. destruct H1.
intro u. split.
- intro bm. specialize (bm _ eq_refl).  rewrite H1 in bm. exact bm.
- intros bu v ev. subst v. rewrite H1. exact bu. Qed.

Lemma dual_sem_bot : dual_sem bot e.
Proof. unfold dual_sem. unfold lolli_sem.  intros v bv.
pose cmM as cmM'.  unfold comm_monoid in cmM'. destruct cmM'.
destruct H0. destruct H1.
rewrite H2. exact bv. Qed.

Lemma dual_sem_empty u : dual_sem (fun _ : M => empty) u.
Proof. unfold dual_sem. unfold lolli_sem.  intros v em. destruct em. Qed.

Lemma fact_bot : fact bot.
Proof. unfold fact. intro.  rewrite - dual_sem_1.
apply dual_anti. intros v ev. subst v. exact dual_sem_bot. Qed.

(* semantics of all formula interpretations are facts *)
Lemma fact_sem {V} A sv : (forall v, fact (sv v)) -> fact (@sem V sv A).
Proof. intros fv.  induction A ; simpl ; try (apply fact_dual).
apply fv. apply fact_bot.  unfold fact. tauto.
exact (facts_int IHA1 IHA2). Qed.

Lemma dual_sem_or X Y v : 
  dual_sem (fun u => X u \/ Y u) v <-> dual_sem X v /\ dual_sem Y v.
Proof. unfold dual_sem. unfold lolli_sem. repeat split.
firstorder.  firstorder.  firstorder. Qed.

(* this does NOT hold Lemma dual_sem_and X Y v : 
  dual_sem (fun u => X u /\ Y u) v <-> dual_sem X v \/ dual_sem Y v. *)

Lemma sub_dual_inv (X Y : M -> Prop) :
  (forall v, X v -> dual_sem Y v) -> (forall v, Y v -> dual_sem X v).
Proof. intros xdy v yv.  apply (dual_anti _ xdy).
exact (dual_dual_sem _ yv). Qed.

Lemma dual_sub_inv (X Y : M -> Prop) : fact X ->
  (forall v, dual_sem X v -> Y v) -> (forall v, dual_sem Y v -> X v).
Proof. intros fx dxy v dy. apply fx. revert v dy.
apply sub_dual_inv.  intros v dxv.
exact (dual_dual_sem _ (dxy v dxv)). Qed.

(*
Lemma ddp_comm X Y u : dual_sem (dual_sem (prods X Y)) u ->
  prods (dual_sem (dual_sem X)) (dual_sem (dual_sem Y)) u.
argument: 
lolli_sem X (lolli_sem Y Z) equals
lolli_sem (prods X Y) Z
so fact Y -> fact (lolli_sem X Y)
so ???
NB prods of facts probably not a fact, otherwise defn of
sem of times redundant
*)

(* need to show correspondence between dual of formula and
  dual_sem (used in semantics definitions) *)
Lemma sem_dual_fwd {V} sv A : (forall v, fact (sv v)) -> 
  forall u, (sem sv (@dual V A) u) -> (dual_sem (sem sv A) u). 
Proof. intros fsv. induction A ; simpl ; intros u.
- tauto.
- apply dual_dual_sem.
- apply dual_anti.  intro. rewrite dual_sem_1. tauto.
- apply dual_anti.   intros. apply dual_sem_empty.
- intro bu. apply dual_dual_sem. rewrite dual_sem_1. exact bu.
- intro tr. apply dual_dual_sem. apply dual_sem_empty.
- unfold par_sem. unfold tens_sem. rewrite !ddd_iff.  apply dual_anti. 
  exact (prods_mono _ _ (sub_dual_inv _ IHA1) (sub_dual_inv _ IHA2)).
- apply dual_anti. intros v ss.  rewrite dual_sem_or. split.
+ apply (dual_anti _ IHA1). apply dual_dual_sem. exact (proj1 ss).
+ apply (dual_anti _ IHA2). apply dual_dual_sem. exact (proj2 ss).
- unfold par_sem. unfold tens_sem. rewrite ddd_iff. apply dd_mono.
  intros v pr. inversion pr.  exact (prodI _ _ _ _ (IHA1 _ H) (IHA2 _ H0)).
- rewrite ddd_iff. rewrite dual_sem_or. firstorder.
- rewrite ddd_iff. apply dual_anti. intros v sai.  destruct sai. split.
  apply (dual_anti _ IHA). apply dual_dual_sem. exact H. exact H0.
- apply dd_mono. firstorder. Qed.

Print Implicit sub_dual_inv.
Print Implicit prods_mono.
Print Implicit fact_sem.

Lemma sem_dual_bwd {V} sv A : (forall v, fact (sv v)) -> 
  forall u, (dual_sem (sem sv A) u) -> (sem sv (@dual V A) u). 
Proof. intros fsv. induction A ; simpl ; intros u.
- tauto.
- exact (fsv v u).
- apply dual_anti. intro. rewrite dual_sem_1. tauto.
- apply dual_anti. tauto.
- rewrite ddd_iff. rewrite dual_sem_1. tauto.
- tauto.
- unfold par_sem. unfold tens_sem.  rewrite !ddd_iff.  apply dual_anti. 
pose (dual_sub_inv (fact_sem _ _ fsv) IHA1) as dsd1.
pose (dual_sub_inv (fact_sem _ _ fsv) IHA2) as dsd2.
exact (prods_mono _ _ dsd1 dsd2).
- apply dual_anti.  intro v. rewrite dual_sem_or.
pose (dual_sub_inv (fact_sem _ _ fsv) IHA1) as dsd1.
pose (dual_sub_inv (fact_sem _ _ fsv) IHA2) as dsd2.  firstorder.
- unfold par_sem. unfold tens_sem.  rewrite ddd_iff.  apply dd_mono. 
exact (prods_mono _ _ IHA1 IHA2).
- rewrite ddd_iff. rewrite dual_sem_or. firstorder.
- rewrite ddd_iff. apply dual_anti.
pose (dual_sub_inv (fact_sem _ _ fsv) IHA) as dsd. firstorder.
- apply dd_mono. firstorder. Qed.

(*
End Phase_Space.
*)

