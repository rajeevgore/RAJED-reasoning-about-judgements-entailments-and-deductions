(* linear logic phase semantics - version with non-deteministic monoid *)

Set Implicit Arguments.

From Coq Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality. 
(* for functional_extensionality *)
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.Classical_Prop. (* for classic *)
Print ClassicalFacts.prop_degeneracy. Print ClassicalFacts.prop_extensionality.
Print ClassicalFacts.excluded_middle. Print Classical_Prop.classic.
Axiom ax_prop_ext : ClassicalFacts.prop_extensionality.
Check FunctionalExtensionality.forall_extensionality. (* and P, S *)

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT.
Require Import lldefs fmlsext.

Lemma iff_app_eq A P Q : (forall x : A, P x <-> Q x) -> P = Q.
Proof. intro ipq. apply FunctionalExtensionality.functional_extensionality.
intro x. apply ax_prop_ext. apply ipq. Qed.

Print Assumptions iff_app_eq.

(* 3-way merges, two different ways, equivalent *)
Inductive merge3L M (m : M -> M -> M -> Prop) x y z r : Prop :=
  | merge3LI : forall xy, m x y xy -> m xy z r -> merge3L m x y z r.
Inductive merge3R M (m : M -> M -> M -> Prop) x y z r : Prop :=
  | merge3RI : forall yz, m y z yz -> m x yz r -> merge3R m x y z r.

Definition comm_monoid_nd M (m : M -> M -> M -> Prop) e := 
  (forall x y z r, merge3L m x y z r <-> merge3R m x y z r) /\
  (forall (x y r : M), m x y r <-> m y x r) /\
  (forall (x y : M), m x e y <-> x = y) /\
  (forall (x y : M), m e x y <-> x = y).

Definition cmass M m e (cm : @comm_monoid_nd M m e) := proj1 cm.
Definition cmcomm M m e (cm : @comm_monoid_nd M m e) := proj1 (proj2 cm).
Definition cmride M m e (cm : @comm_monoid_nd M m e) := proj1 (proj2(proj2 cm)).
Definition cmlide M m e (cm : @comm_monoid_nd M m e) := proj2 (proj2(proj2 cm)).
Definition cmrid M m e cm x := proj2 (@cmride M m e cm x x) eq_refl. 
Definition cmlid M m e cm x := proj2 (@cmlide M m e cm x x) eq_refl. 
Check cmass.  Check cmcomm.  Check cmrid.  Check cmlid.

(*
*)
Section Phase_Space. (* fix a single phase space *)
Variable M : Type.
Variable m : M -> M -> M -> Prop.
Variable e : M.
Variable bot : M -> Prop.
Hypothesis cmM : comm_monoid_nd m e.

Check (cmass cmM). Check (cmcomm cmM). Check (cmrid cmM). Check (cmlid cmM).

Definition lolli_sem (X Y : M -> Prop) u :=
  forall (v w : M), X v -> m u v w -> Y w.
Definition dual_sem X := lolli_sem X bot.
Print Implicit lolli_sem.

(** dual_sem lemmas **)

(* note - one less implicit arg than before *)
Lemma dual_dual_sem (X : M -> Prop) u : X u -> dual_sem (dual_sem X) u.
Proof. unfold dual_sem. unfold lolli_sem. intros.
apply (H0 _ _ H).  rewrite (cmcomm cmM). exact H1. Qed.

Lemma dual_anti (X Y : M -> Prop) : (forall u, X u -> Y u) ->
  forall v, dual_sem Y v -> dual_sem X v.
Proof. unfold dual_sem.  unfold lolli_sem. intros xy v yv u w xu.
exact (yv _ _ (xy _ xu)). Qed.

Lemma dd_mono (X Y : M -> Prop) : (forall u, X u -> Y u) ->
  forall v, dual_sem (dual_sem X) v -> dual_sem (dual_sem Y) v.
Proof. intros xy.  exact (dual_anti _ (dual_anti _ xy)). Qed.

Lemma ddd_iff (X : M -> Prop) v :
  dual_sem (dual_sem (dual_sem X)) v <-> dual_sem X v.
Proof. split. apply dual_anti. apply dual_dual_sem. apply dual_dual_sem. Qed.

Lemma ddd_iff' (X : M -> Prop) : 
  dual_sem (dual_sem (dual_sem X)) = dual_sem X.
apply FunctionalExtensionality.functional_extensionality.
intro y.  apply ax_prop_ext.  apply ddd_iff. Qed.

Lemma ds_ds_ds (X Y : M -> Prop) : (forall u, X u -> dual_sem Y u) -> 
  (forall u, dual_sem (dual_sem X) u -> dual_sem Y u).
Proof. intros xdy u ddx.  eapply dd_mono in xdy.
rewrite -> ddd_iff in xdy. exact xdy. exact ddx. Qed.

Inductive prods (X Y : M -> Prop) : M -> Prop :=
  | prodI : forall x y z : M, X x -> Y y -> m x y z -> prods X Y z.

Lemma prods_mono (X X' Y Y' : M -> Prop) : (forall u, X u -> X' u) ->
  (forall u, Y u -> Y' u) -> (forall u, prods X Y u -> prods X' Y' u).
Proof. intros xx yy u pxy. destruct pxy.
exact (prodI _ _ (xx _ H) (yy _ H0) H1). Qed.
 
Definition tens_sem X Y := dual_sem (dual_sem (prods X Y)).
Definition par_sem X Y := dual_sem (tens_sem (dual_sem X) (dual_sem Y)).

Inductive idems : M -> Prop := | idemsI : forall x : M, m x x x -> idems x.

Definition idem1 x := (m x x x) /\ dual_sem (dual_sem (eq e)) x.
(* try idemd as alternative to idem1 *)
Definition Jc x := tens_sem (eq x) (eq x) x.
Definition Jw x := dual_sem (dual_sem (eq e)) x.
(* these clauses say you can contract, and weaken, anything in J *)
Definition J x := Jc x /\ Jw x.

Variable K : M -> Prop.

Lemma tens_sem_mono (X X' Y Y' : M -> Prop) : (forall u, X u -> X' u) ->
  (forall u, Y u -> Y' u) -> (forall u, tens_sem X Y u -> tens_sem X' Y' u).
Proof. unfold tens_sem. intros xx yy. apply dd_mono. 
apply (prods_mono _ _ xx yy). Qed.

Lemma par_sem_mono (X X' Y Y' : M -> Prop) : (forall u, X u -> X' u) ->
  (forall u, Y u -> Y' u) -> (forall u, par_sem X Y u -> par_sem X' Y' u).
Proof. unfold par_sem. intros xx yy. apply dual_anti.
apply tens_sem_mono ; apply dual_anti ; assumption. Qed.

Definition par_sem_mono' X X' Y Y' u pxy xx yy :=
  @par_sem_mono X X' Y Y' xx yy u pxy.

Lemma lolli_sem_mono (X X' Y Y' : M -> Prop) : (forall u, X' u -> X u) ->
  (forall u, Y u -> Y' u) -> (forall u, lolli_sem X Y u -> lolli_sem X' Y' u).
Proof. unfold lolli_sem. intros xx yy u xy v w xv muvw. 
exact (yy _ (xy _ _ (xx _ xv) muvw)). Qed.

Definition lolli_sem_mono' X X' Y Y' u pxy xx yy :=
  @lolli_sem_mono X X' Y Y' xx yy u pxy.

Definition query_sem X := dual_sem (fun x => dual_sem X x /\ K x).
Definition bang_sem X := dual_sem (dual_sem (fun x => X x /\ K x)).
Definition bang_query X :
  dual_sem (query_sem X) = bang_sem (dual_sem X) := eq_refl.

Lemma query_sem_mono (X X' : M -> Prop) :
  (forall u, X u -> X' u) -> (forall u, query_sem X u -> query_sem X' u).
Proof. intros xx. apply dual_anti.  intros u dxk. cD. split. 
revert dxk.  apply (dual_anti _ xx). exact dxk0. Qed.

Lemma bang_sem_mono (X X' : M -> Prop) :
  (forall u, X u -> X' u) -> (forall u, bang_sem X u -> bang_sem X' u).
Proof. intros xx. apply dd_mono. firstorder. Qed.

Variable V : Set.
Variable sv : V -> M -> Prop. (* semantics of variables *)

Fixpoint sem f := match f with 
  | Var v => sv v
  | DVar v => dual_sem (sv v)
  | Bot _ => bot
  | One _ => dual_sem (dual_sem (eq e))
  | Zero _ => dual_sem (dual_sem (fun _ => empty))
  | Top _ => fun _ => True
  | tens A B => tens_sem (sem A) (sem B)
  | par A B => par_sem (sem A) (sem B) 
  | plus A B => dual_sem (dual_sem (fun x => sem A x \/ sem B x))
  | wth A B => (fun x => sem A x /\ sem B x) 
  | Bang f => bang_sem (sem f)
  | Query f => query_sem (sem f)
  end.

Print Implicit sem.

(* semantics of list of formula is sem of their par *)
Definition seml fs := fold_right par_sem bot (map sem fs).
(* note useful lemmas
  fold_left_rev_right fold_right_app fold_symmetric fold_left_app,
  need to prove more using assoc and comm and identity of par_sem *)

Lemma seml_alt fs : seml fs = sem (fold_right (@par V) (@Bot V) fs).
Proof. induction fs. reflexivity.
unfold seml. simpl. apply f_equal. exact IHfs. Qed.

(** fact lemmas  **)

(* fact and factd are equivalent *)
Definition fact X := forall u, dual_sem (dual_sem X) u -> X u.
Inductive factd : (M -> Prop) -> Prop := 
  | factdI : forall X, factd (dual_sem X).

Lemma fact_dual X : fact (dual_sem X).
Proof. unfold fact. apply dual_anti. apply dual_dual_sem. Qed.

Lemma fact_int X Y : fact X -> fact Y -> fact (fun u => X u /\ Y u).
Proof. unfold fact. intros dx dy u ddc. split.
- apply dx. revert u ddc. apply dd_mono. tauto.
- apply dy. revert u ddc. apply dd_mono. tauto. Qed.

Lemma fact_tens X Y : fact (tens_sem X Y).  Proof. apply fact_dual. Qed.

(*
Lemma fact_J : fact J.
Proof. apply fact_int.
- unfold tens_sem. unfold fact. intros u. (* doesn't work *)
*)

(* can do without these (with a lot of extra effort),
  in fact, for specific semantics used in completeness proof,
  not clear that they are true
Axiom fact_J : fact J. (* can we prove this? *)
Axiom fact_K : fact K. (* can we prove this? *)
  *)

Lemma fact_dd_eq X : fact X -> dual_sem (dual_sem X) = X.
Proof. intro fx. apply iff_app_eq. intro x. split.
apply fx. apply dual_dual_sem. Qed.

Lemma factd_imp Y : factd Y -> fact Y. 
Proof. intro fdy. destruct fdy. apply fact_dual. Qed.

(* doesn't work unless Y = dual_sem (dual_sem Y) *)
Lemma fact_imp_d Y : fact Y -> factd Y.
Proof. intro fy.  rewrite - (fact_dd_eq fy).  apply factdI. Qed.

Definition factd_iff X := conj (@fact_imp_d X) (@factd_imp X).

Lemma ds_ds_fact (X Y : M -> Prop) : fact Y ->
  (forall u, X u -> Y u) -> (forall u, dual_sem (dual_sem X) u -> Y u).
Proof. intros fy ddxy u xu. rewrite - (fact_dd_eq fy).
exact (dd_mono ddxy xu). Qed.

Lemma lolli_eq (Z : M -> Prop) u w :
  (forall x, m w u x -> Z x) = lolli_sem (eq u) Z w.
Proof. unfold lolli_sem. apply ax_prop_ext.
split ; intros. subst. exact (H _ H1).  exact (H _ _ eq_refl H0). Qed.

(* don't know if these will be what we want *)
(* actually want this
Lemma fact_comx' Z u w : fact Z -> fact (fun v : M => m v u w -> Z w).
*)

Lemma fact_com_lem Y Z u v : 
  (forall x, m v u x -> lolli_sem Y Z x) <-> lolli_sem (prods (eq u) Y) Z v.
Proof.  unfold lolli_sem.  split.
- intros yz uy w uyw mvyw.  destruct uyw. subst.
pose (merge3RI _ _ _ _ _ _ H1 mvyw).
apply (cmass cmM) in m0. destruct m0.
exact (yz _ H _ _ H0 H2).
- intros pz x mvux y w yw me.
pose (merge3LI _ _ _ _ _ _ mvux me).
apply (cmass cmM) in m0. destruct m0.
exact (pz _ _ (prodI _ _ eq_refl yw H) H0).
Qed.

Lemma fact_com_lem' Y u : 
  (fun v => forall x, m v u x -> dual_sem Y x) = dual_sem (prods (eq u) Y).
Proof. apply iff_app_eq. intro x.  apply fact_com_lem.  Qed.

Lemma fact_com Z u : fact (fun v => forall x, m v u x -> dual_sem Z x).
Proof. rewrite fact_com_lem'. apply fact_dual. Qed.

Lemma fact_com' Z u : fact Z -> fact (fun v => forall x, m v u x -> Z x).
Proof. intro fz. destruct (fact_imp_d fz). apply fact_com. Qed.

(* actually want this in proof of uncurry_sem_lem 
we could get these if m u v w -> Z w implies forall w, m u v w -> Z w
which would normally be true in our situation, where
m u v w and m u v w' imply w and w' are the same multiset,
and where Z comes from some list of formula being derivable,
when Z is invariant under rearrangements of its arguments
Lemma fact_comcx' Z u w : fact Z -> fact (fun v : M => m u v w -> Z w).
Lemma fact_comx' Z u w : fact Z -> fact (fun v : M => m v u w -> Z w).
Proof. intro fz. unfold fact.
*)

Lemma fact_comc' Z u : fact Z -> fact (fun v => forall x, m u v x -> Z x).
Proof. intro fz. eapply fact_com' in fz.  apply (eq_rect _ _ fz).
apply FunctionalExtensionality.functional_extensionality.
intro x.  apply FunctionalExtensionality.forall_extensionalityP.
intro y.  apply ax_prop_ext.  rewrite (cmcomm cmM u x). reflexivity. Qed.

(* dual_sem o dual_sem is a closure operator and facts are the closed sets *)
Lemma facts_int X Y : fact X -> fact Y -> fact (fun u => X u /\ Y u).
unfold fact. intros fx fy u fxy. split.
- apply fx.  eapply dd_mono. 2: exact fxy. firstorder.
- apply fy.  eapply dd_mono. 2: exact fxy. firstorder. Qed.

Lemma lolli_sem_eq_sw u v X : (lolli_sem (eq v) X u) -> (lolli_sem (eq u) X v).
Proof. unfold lolli_sem. intros vu v' w uv' me. subst.
apply (vu _ _ eq_refl).  apply (cmcomm cmM). exact me. Qed.

Definition lolli_sem_eq_iff u v X :=
conj (@lolli_sem_eq_sw u v X) (@lolli_sem_eq_sw v u X) : iff _ _.

Lemma dual_sem_eq x v : dual_sem (eq v) x <-> dual_sem (eq x) v.
Proof. apply lolli_sem_eq_iff. Qed.

Lemma lolli_sem_e X Y : lolli_sem X Y e <-> (forall x, X x -> Y x).
Proof. unfold lolli_sem. split.
- intros eqv x xx. apply (eqv _ _ xx). apply (cmlid cmM).
- intros xy v w xv mevw.  apply (cmlide cmM) in mevw.
subst. exact (xy _ xv).  Qed.

Lemma lolli_sem_1 X u : iff (lolli_sem (eq e) X u) (X u).
Proof. rewrite lolli_sem_eq_iff. rewrite lolli_sem_e.  split.
firstorder. intros. subst. assumption. Qed.

Lemma lolli_sem_1_eq X : (lolli_sem (eq e) X) = X.
Proof. apply iff_app_eq. apply lolli_sem_1. Qed.

Lemma dual_sem_1 : forall u, iff (dual_sem (eq e) u) (bot u).
Proof. apply lolli_sem_1. Qed.

Lemma dual_sem_1_eq : (dual_sem (eq e)) = bot.
Proof. apply iff_app_eq. apply dual_sem_1. Qed.

Lemma lolli_same_sound X : lolli_sem X X e.
Proof. apply lolli_sem_e. firstorder. Qed.

Lemma dual_sem_bot : dual_sem bot e.
Proof. unfold dual_sem. apply lolli_same_sound. Qed.

Lemma dual_sem_empty u : dual_sem (fun _ : M => empty) u.
Proof. unfold dual_sem. unfold lolli_sem.  
intros v w em muvw. destruct em. Qed.

Lemma fact_bot : fact bot.
Proof. unfold fact. intro.  rewrite - dual_sem_1.
apply dual_anti. intros v ev. subst v. exact dual_sem_bot. Qed.

Hypothesis fsv : forall v, fact (sv v).

(* semantics of all formula interpretations are facts *)
Lemma fact_sem A : fact (sem A).
Proof.  induction A ; simpl ; try (apply fact_dual).
apply fsv. apply fact_bot.  unfold fact. tauto.
exact (facts_int IHA1 IHA2). Qed.

Lemma fact_seml As : fact (seml As).
Proof. rewrite seml_alt. apply fact_sem. Qed.

Lemma dual_sem_or X Y v : 
  dual_sem (fun u => X u \/ Y u) v <-> dual_sem X v /\ dual_sem Y v.
Proof. unfold dual_sem. unfold lolli_sem. repeat split.
firstorder.  firstorder.  firstorder. Qed.

Lemma dual_sem_or' X Y : 
  dual_sem (fun u => X u \/ Y u) = (fun v => dual_sem X v /\ dual_sem Y v).
Proof. apply iff_app_eq.  intro x.  apply dual_sem_or. Qed.

Lemma dsao k A z : fact k -> dual_sem 
  (fun x => dual_sem A x /\ k x) z ->
 dual_sem (dual_sem 
   (fun y => A y \/ dual_sem k y)) z.
Proof.  intro fk.  apply dual_anti. intro u.  rewrite dual_sem_or. 
intro. destruct H. split. exact H. exact (fk _ H0). Qed.
  
(* this does NOT hold Lemma dual_sem_and X Y v : 
  dual_sem (fun u => X u /\ Y u) v <-> dual_sem X v \/ dual_sem Y v. *)

Lemma sub_dual_inv (X Y : M -> Prop) :
  (forall v, X v -> dual_sem Y v) -> (forall v, Y v -> dual_sem X v).
Proof. intros xdy v yv.  apply (dual_anti _ xdy).
exact (dual_dual_sem yv). Qed.

Lemma sub_inv_dual (X Y : M -> Prop) : fact X -> 
  (forall v, dual_sem X v -> dual_sem Y v) -> (forall v, Y v -> X v).
Proof. intros fx dxy v yv.  exact (fx _ (sub_dual_inv _ dxy yv)).  Qed.

Lemma dual_sub_inv (X Y : M -> Prop) : fact X ->
  (forall v, dual_sem X v -> Y v) -> (forall v, dual_sem Y v -> X v).
Proof. intros fx dxy v dy. apply fx. revert v dy.
apply sub_dual_inv.  intros v dxv.
exact (dual_dual_sem (dxy v dxv)). Qed.

Lemma bot_o x v : (forall y, m v x y -> bot y) <-> dual_sem (eq x) v.
Proof. unfold dual_sem. unfold lolli_sem.  
split ; intros ; subst ; firstorder. Qed.

Lemma prods_comm X Y u : prods X Y u -> prods Y X u.
Proof. intro pxy. destruct pxy.
rewrite -> (cmcomm cmM) in H1.  exact (prodI _ _ H0 H H1). Qed.

Lemma prods_comm_eq X Y : prods X Y = prods Y X.
Proof. apply iff_app_eq. split ; apply prods_comm. Qed.

Lemma tens_comm X Y u : tens_sem X Y u -> tens_sem Y X u.
Proof. unfold tens_sem.  rewrite (prods_comm_eq X Y). tauto. Qed.

Lemma tens_comm_eq X Y : tens_sem X Y = tens_sem Y X.
Proof. apply iff_app_eq. split ; apply tens_comm. Qed.

Lemma par_comm X Y u : par_sem X Y u -> par_sem Y X u.
Proof. unfold par_sem.  apply dual_anti.
intro. rewrite tens_comm_eq. tauto. Qed.

Lemma par_comm_eq X Y : par_sem X Y = par_sem Y X.
Proof. apply iff_app_eq. split ; apply par_comm. Qed.

(** curry and uncurry of lolli, tens_sem, prods **)

Lemma curry_prods_sem X Y Z u : 
  lolli_sem (prods X Y) Z u -> lolli_sem X (lolli_sem Y Z) u.
Proof. unfold lolli_sem.  intros unc * xv m1 * yv m2.
pose (merge3LI _ _ _ _ _ _ m1 m2) as m3eq.
apply (cmass cmM) in m3eq. destruct m3eq.
revert H0. apply unc.  exact (prodI _ _ xv yv H). Qed.

Lemma curry_sem X Y Z u : 
  lolli_sem (tens_sem X Y) Z u -> lolli_sem X (lolli_sem Y Z) u.
Proof. intro lt. apply curry_prods_sem.
unfold lolli_sem.  unfold lolli_sem in lt.
intros * pxy. apply lt. unfold tens_sem. exact (dual_dual_sem pxy). Qed.

Lemma curry_sem_bot X Y u : 
  dual_sem (tens_sem X Y) u -> lolli_sem X (dual_sem Y) u.
Proof. unfold dual_sem. apply curry_sem. Qed.

Lemma curry_bot_prods X Y u : 
  dual_sem (prods X Y) u -> lolli_sem X (dual_sem Y) u.
Proof. intro dpxy. apply curry_sem_bot.
unfold tens_sem. rewrite ddd_iff. exact dpxy. Qed.

(* difficult to do this for tens instead of prods? easier if Z is bot *)
Lemma uncurry_prods_sem X Y Z u : 
  lolli_sem X (lolli_sem Y Z) u -> lolli_sem (prods X Y) Z u.
Proof. unfold lolli_sem.  intros cur * ddp me.  destruct ddp.
pose (merge3RI _ _ _ _ _ _ H1 me) as m3eq.
apply (cmass cmM) in m3eq. destruct m3eq.
exact (cur _ _ H H2 _ _ H0 H3). Qed.

Lemma uncurry_bot_prods X Y u :
  lolli_sem X (dual_sem Y) u -> dual_sem (prods X Y) u.
Proof. apply uncurry_prods_sem. Qed.

Lemma uncurry_sem_bot X Y u : 
  lolli_sem X (dual_sem Y) u -> dual_sem (tens_sem X Y) u.
Proof. unfold tens_sem. rewrite ddd_iff. apply uncurry_bot_prods. Qed.

(* THESE FAIL for the non-deterministic monoid
Lemma uncurry_sem_lem X Y Z u : fact Z ->
  lolli_sem (prods X Y) Z u -> lolli_sem (tens_sem X Y) Z u.
Proof.  unfold lolli_sem. unfold tens_sem.  intros fz cur.
intros v w.  revert v.
epose (@ds_ds_fact (prods X Y) (fun v => m u v w -> Z w)).  apply z.
2: exact (fun v => cur v w).
need something a bit different, see at fact_comc' above
exact (ds_ds_fact (fact_comc' fz) cur). Qed.

BUT THE OTHERS FOLLOWING SUCCEED *)

Definition curry_prods_sem_eqv X Y Z u : iff _ _ :=
  conj (@curry_prods_sem X Y Z u) (@uncurry_prods_sem X Y Z u).
Definition curry_sem_bot_eqv X Y u : iff _ _ :=
  conj (@curry_sem_bot X Y u) (@uncurry_sem_bot X Y u).
Definition curry_bot_prods_eqv X Y u : iff _ _ :=
  conj (@curry_bot_prods X Y u) (@uncurry_bot_prods X Y u).

Lemma fact_lolli_dual X Z : fact (lolli_sem X (dual_sem Z)).
Proof. unfold fact. intros u ddld.  apply curry_sem_bot.
(* this fails pose (dd_mono (@uncurry_sem_bot _ _) _ ddld). *)
epose (dd_mono (@uncurry_sem_bot _ _)).  specialize (d _ ddld).
rewrite -> ddd_iff in d. exact d. Qed.

Lemma fact_lolli X Y : fact Y -> fact (lolli_sem X Y).
Proof. intro fy. destruct (fact_imp_d fy). apply fact_lolli_dual. Qed.

Print Implicit dd_mono.
Print Implicit uncurry_sem_bot.

(* this gives tens_assoc one way *)
Lemma tens_assoc_lem X Y Z u : dual_sem (tens_sem (tens_sem X Y) Z) u ->
  dual_sem (tens_sem X (tens_sem Y Z)) u.
Proof. intros dt.  pose (curry_sem (curry_sem_bot dt)) as l.
apply uncurry_sem_bot.
apply (lolli_sem_mono' _ _ l). tauto. apply uncurry_sem_bot. Qed.

Lemma tens_assoc X Y Z u : 
  (tens_sem X (tens_sem Y Z)) u -> (tens_sem (tens_sem X Y) Z) u.
Proof. pose (@dual_anti _ _ (@tens_assoc_lem X Y Z) u).
rewrite -> !(fact_dd_eq (@fact_tens _ _)) in d. exact d. Qed.

Lemma par_assocr X Y Z u : 
  (par_sem (par_sem X Y) Z) u -> (par_sem X (par_sem Y Z)) u.
Proof. unfold par_sem.  rewrite  !(fact_dd_eq (@fact_tens _ _)).
apply dual_anti. intro v. apply tens_assoc. Qed.

(* and with obvious commutativity of tens, tens_assoc one way 
  gives you tens_assoc the other way, and tens_assoc gives par_assoc *)

Print Implicit tens_comm_eq.

(* with deterministic monoid, we proved tens_assocr_lem using uncurry_sem,
  now we do it the other way around *)
Lemma tens_assocr_lem X Y Z u : dual_sem (tens_sem X (tens_sem Y Z)) u ->
  dual_sem (tens_sem (tens_sem X Y) Z) u.
Proof. rewrite !(tens_comm_eq X).  rewrite !(tens_comm_eq _ Z).
apply tens_assoc_lem. Qed.

Lemma uncurry_sem X Y Z u : fact Z ->
  lolli_sem X (lolli_sem Y Z) u -> lolli_sem (tens_sem X Y) Z u.
Proof. intros fz lxyz.  apply fact_imp_d in fz. destruct fz as [Z'].
apply curry_sem_bot.  apply tens_assocr_lem.  apply uncurry_sem_bot.
apply (lolli_sem_mono' _ _ lxyz). tauto.  apply uncurry_sem_bot. Qed.

Definition curry_sem_eqv X Y Z fz u : iff _ _ :=
  conj (@curry_sem X Y Z u) (@uncurry_sem X Y Z u fz).

(* proving tens_assocr_lem using uncurry_sem *)
Lemma tens_assocr_lem' X Y Z u : dual_sem (tens_sem X (tens_sem Y Z)) u ->
  dual_sem (tens_sem (tens_sem X Y) Z) u.
Proof. intros dt.  apply uncurry_sem_bot.
apply uncurry_sem. apply fact_dual.
apply (lolli_sem_mono' _ _ (curry_sem_bot dt)).  tauto.
apply curry_sem_bot. Qed.

Lemma tens_assocr X Y Z u : 
  (tens_sem (tens_sem X Y) Z) u -> (tens_sem X (tens_sem Y Z)) u.
Proof. pose (@dual_anti _ _ (@tens_assocr_lem X Y Z) u).
rewrite -> !(fact_dd_eq (@fact_tens _ _)) in d. exact d. Qed.

Print Implicit fact_seml.

Lemma par_assoc X Y Z u : 
  (par_sem X (par_sem Y Z)) u -> (par_sem (par_sem X Y) Z) u.
Proof. unfold par_sem.  rewrite  !(fact_dd_eq (@fact_tens _ _)).
apply dual_anti. intro v. apply tens_assocr. Qed.

Lemma par_assoc_eq X Y Z : 
  (par_sem X (par_sem Y Z)) = (par_sem (par_sem X Y) Z).
Proof. apply iff_app_eq. split. apply par_assoc. apply par_assocr. Qed.

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
Lemma sem_dual_fwd A : forall u, (sem (@dual V A) u) -> (dual_sem (sem A) u). 
Proof. induction A ; simpl ; intros u.
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
  intros v pr. inversion pr.  exact (prodI _ _ (IHA1 _ H) (IHA2 _ H0) H1).
- rewrite ddd_iff. rewrite dual_sem_or. firstorder.
- rewrite ddd_iff. apply dual_anti. intros v sai.  destruct sai. split.
  apply (dual_anti _ IHA). apply dual_dual_sem. exact H. exact H0.
- apply dd_mono. firstorder. Qed.

Print Implicit sub_dual_inv.
Print Implicit prods_mono.

Lemma sem_dual_bwd A : forall u, (dual_sem (sem A) u) -> (sem (@dual V A) u). 
Proof. induction A ; simpl ; intros u.
- tauto.
- apply fsv.
- apply dual_anti. intro. rewrite dual_sem_1. tauto.
- apply dual_anti. tauto.
- rewrite ddd_iff. rewrite dual_sem_1. tauto.
- tauto.
- unfold par_sem. unfold tens_sem.  rewrite !ddd_iff.  apply dual_anti. 
pose (dual_sub_inv (fact_sem _) IHA1) as dsd1.
pose (dual_sub_inv (fact_sem _) IHA2) as dsd2.
exact (prods_mono _ _ dsd1 dsd2).
- apply dual_anti.  intro v. rewrite dual_sem_or.
pose (dual_sub_inv (fact_sem _) IHA1) as dsd1.
pose (dual_sub_inv (fact_sem _) IHA2) as dsd2.  firstorder.
- unfold par_sem. unfold tens_sem.  rewrite ddd_iff.  apply dd_mono. 
exact (prods_mono _ _ IHA1 IHA2).
- rewrite ddd_iff. rewrite dual_sem_or. firstorder.
- rewrite ddd_iff. apply dual_anti.
pose (dual_sub_inv (fact_sem _) IHA) as dsd. firstorder.
- apply dd_mono. firstorder. Qed.

Lemma sem_dual A : forall u, (sem (@dual V A) u) <-> (dual_sem (sem A) u).
Proof. intros u. split.
apply (sem_dual_fwd _).  apply (sem_dual_bwd _). Qed.

Definition sem_dual_eq A := iff_app_eq _ _ (sem_dual A).

Print Implicit merge3LI.
Print Implicit prodI.
Print Implicit ds_ds_fact.

Lemma sem_lolli A B u :
  sem (@lolli V A B) u <-> lolli_sem (sem A) (sem B) u.
Proof. unfold lolli. simpl. unfold par_sem.
rewrite curry_sem_bot_eqv.  unfold lolli_sem.
pose sem_dual.  clearbody i.  split.
- intros dd * sa muvw. specialize (dd v w).  rewrite <- i in dd.
rewrite dual_dual in dd.
exact (fact_sem B (dd sa muvw)).
- intros sabm * dda muvw.  rewrite <- i in dda. 
rewrite dual_dual in dda. 
exact (dual_dual_sem (sabm _ _ dda muvw)). Qed.

(* note, all the binary semantic definitions are commutative *)
(* not obvious that they are all associative *)

Lemma prods_lolli X Y u : prods (lolli_sem X Y) X u -> Y u.
Proof. intro pl. inversion pl. unfold lolli_sem in H.
exact (H _ _ H0 H1). Qed.

Lemma tens_lolli X Y u : fact Y -> tens_sem (lolli_sem X Y) X u -> Y u.
Proof.  unfold tens_sem.  intros fy tlxy.
apply fy. revert tlxy. apply dd_mono. intro. apply prods_lolli. Qed.

Definition tens_lolli' X Y fy u := @tens_lolli X Y u fy.

Lemma dual_sem_e X : dual_sem X e <-> (forall x, X x -> bot x).
Proof. unfold dual_sem. apply lolli_sem_e. Qed.

Lemma par_sem_e_bwd (X Y : M -> Prop) :
  (forall x, X x -> Y x) -> par_sem (dual_sem X) Y e.
Proof. intro xy. unfold par_sem.  unfold tens_sem. rewrite ddd_iff.
rewrite curry_bot_prods_eqv.  rewrite lolli_sem_e.
exact (dd_mono xy). Qed.

Lemma par_sem_bwd (X Y : M -> Prop) u : 
  lolli_sem (dual_sem X) Y u -> par_sem X Y u.
Proof. unfold lolli_sem. intros xy.
unfold par_sem.  unfold tens_sem. rewrite ddd_iff.
rewrite curry_bot_prods_eqv.  unfold lolli_sem.
intros * ddxv muvw.  exact (dual_dual_sem (xy _ _ ddxv muvw)). Qed.

Lemma par_sem_bwd' (X Y : M -> Prop) u : fact X -> 
  lolli_sem X Y u -> par_sem (dual_sem X) Y u.
Proof. intros fx lxy.  apply par_sem_bwd.  revert u lxy.
apply lolli_sem_mono.  exact fx. tauto. Qed.

Lemma par_sem_fwd (X Y : M -> Prop) u : fact Y -> 
  par_sem (dual_sem X) Y u -> lolli_sem X Y u.
Proof. intros fy.  unfold par_sem.  unfold tens_sem. rewrite ddd_iff.
rewrite curry_bot_prods_eqv.  unfold lolli_sem.
intros ddxy * xv muvw.  
exact (fy _ (ddxy _ _ (dual_dual_sem xv) muvw)). Qed.

Lemma par_sem_fwd' (X Y : M -> Prop) u : fact Y -> 
  par_sem X Y u -> lolli_sem (dual_sem X) Y u.
Proof. intros fy pxy. apply (par_sem_fwd fy).
eapply (par_sem_mono (@dual_dual_sem _)). 2: apply pxy. tauto. Qed.

Definition par_sem_dual_eqv X Y fx fy u : iff _ _ :=
  conj (@par_sem_fwd X Y u fy) (@par_sem_bwd' X Y u fx). 
Definition par_sem_eqv X Y fy u : iff _ _ :=
  conj (@par_sem_fwd' X Y u fy) (@par_sem_bwd X Y u). 
  
Lemma par_sem_e_fwd (X Y : M -> Prop) : fact Y -> 
  par_sem (dual_sem X) Y e -> (forall x, X x -> Y x).
Proof. intros fy pd. rewrite - lolli_sem_e.  exact (par_sem_fwd fy pd). Qed.
 
Lemma par_sem_bot Y u : fact Y -> par_sem bot Y u -> Y u.
Proof. intros fy pby.  apply (par_sem_fwd' fy) in pby. 
exact (pby e u dual_sem_bot (cmrid cmM _)).  Qed.

Lemma par_sem_botc Y u : fact Y -> par_sem Y bot u -> Y u.
Proof. intros fy pby.  apply (par_sem_fwd' fact_bot) in pby. 
exact (fy _ pby).  Qed.

Lemma par_sem_botic Y u : fact Y -> Y u -> par_sem Y bot u.
Proof. intros fy yu.  apply par_sem_bwd. eapply dd_mono.
intros. exact H. exact (dual_dual_sem yu). Qed.

Lemma par_sem_botc_eq Y : fact Y -> par_sem Y bot = Y.
Proof. intro fy. apply iff_app_eq. intro x. split. 
apply (par_sem_botc fy).  apply (par_sem_botic fy).  Qed.

Definition par_sem_boti Y u fy yu := par_comm (@par_sem_botic Y u fy yu).

(** seml **)

Lemma seml_app' l l' : 
  seml (l ++ l') = fold_right par_sem (seml l') (map sem l).
Proof. unfold seml. rewrite map_app. apply fold_right_app. Qed.

Lemma seml_app_lem l s : fact s -> 
  fold_right par_sem s (map sem l) = par_sem (seml l) s.
Proof. intro fs. induction l ; unfold seml ; simpl.
- apply iff_app_eq.  intro x.  split.
apply (par_sem_boti fs).  apply (par_sem_bot fs).
- rewrite - par_assoc_eq.  apply f_equal. exact IHl. Qed.

Lemma seml_app l l' : 
  seml (l ++ l') = par_sem (seml l) (seml l').
Proof. rewrite seml_app'.
apply seml_app_lem. exact (fact_seml _).  Qed.

Lemma seml_nil : seml [] = bot.  Proof. reflexivity. Qed.

Lemma seml_cons A As : seml (A :: As) = par_sem (sem A) (seml As).
Proof. reflexivity. Qed.

Lemma seml_single A : seml [A] = sem A.
Proof. unfold seml. simpl.
apply par_sem_botc_eq. exact (fact_sem _). Qed.

Lemma seml_merge xs ys zs :
  merge xs ys zs -> seml zs = par_sem (seml xs) (seml ys).
Proof. intro mrg. induction mrg.
- rewrite !seml_cons. rewrite IHmrg. apply par_assoc_eq.
- rewrite !seml_cons. rewrite IHmrg. rewrite !par_assoc_eq.
  rewrite (par_comm_eq (sem y)). reflexivity.
- unfold seml. simpl.  rewrite (par_sem_botc_eq fact_bot). reflexivity. Qed.

Print Implicit par_sem_botc_eq.
Print Implicit fact_sem.

(** lolli combinators **)

Lemma lolli_C (X Y Z : M -> Prop) u :
  lolli_sem X (lolli_sem Y Z) u -> lolli_sem Y (lolli_sem X Z) u.
Proof. unfold lolli_sem.  intros xyz * yv me * xw mw.
pose (merge3LI _ _ _ _ _ _ me mw) as m3eq.
apply (cmass cmM) in m3eq. destruct m3eq.
rewrite -> (cmcomm cmM) in H.
pose (merge3RI _ _ _ _ _ _ H H0) as m3eq.
apply (cmass cmM) in m3eq. destruct m3eq.
exact (xyz _ _ xw H1 _ _ yv H2). Qed.

Definition lolli_C' (X Y Z : M -> Prop) := 
  (proj2 (@lolli_sem_e _ _) (@lolli_C X Y Z)).

Lemma lolli_dual_inv X Y u : 
  lolli_sem X (dual_sem Y) u -> lolli_sem Y (dual_sem X) u.
Proof. apply lolli_C. Qed.

Lemma lolli_B (X Y Z : M -> Prop) u w z :
  lolli_sem Y Z u -> lolli_sem X Y w -> m u w z -> lolli_sem X Z z.
Proof. unfold lolli_sem. intros yz xy me * xv mc.
pose (merge3LI _ _ _ _ _ _ me mc) as m3eq.
apply (cmass cmM) in m3eq. destruct m3eq.
exact (yz _ _ (xy _ _ xv H) H0). Qed.

Lemma lolli_B' (X Y Z : M -> Prop) :
  lolli_sem (lolli_sem Y Z) (lolli_sem (lolli_sem X Y) (lolli_sem X Z)) e.
Proof. apply lolli_sem_e.  intros x lyz.
intros v w. exact (lolli_B lyz). Qed.

(* this is what DLW calls cl_stability *)
Lemma prod_ddL X Y z : prods (dual_sem (dual_sem X)) Y z -> tens_sem X Y z.
Proof. apply lolli_sem_e.  apply uncurry_prods_sem.
apply lolli_sem_e. 
apply (ds_ds_fact (fact_lolli (@fact_dual _))).
intros u xu v w yv me.  apply dual_dual_sem.
exact (prodI _ _ xu yv me). Qed.

Lemma prod_ddR X Y z : prods Y (dual_sem (dual_sem X)) z -> tens_sem Y X z.
Proof. rewrite prods_comm_eq. rewrite tens_comm_eq. apply prod_ddL. Qed.

Lemma prod_dd X Y z : 
  prods (dual_sem (dual_sem X)) (dual_sem (dual_sem Y)) z -> tens_sem X Y z.
Proof. intro pxy. apply prod_ddL in pxy.
revert pxy. eapply ds_ds_ds.
intros u pxdy. exact (prod_ddR pxdy). Qed.

(** soundness - in semantics, true means set contains e,
  for semantics of list of formulae, imagine them joined by par **)

Lemma id_sound' X : par_sem X (dual_sem X) e.
Proof. apply par_sem_bwd. apply lolli_same_sound. Qed.

Lemma id_sound X : par_sem (dual_sem X) X e.
Proof. apply par_comm. apply id_sound'. Qed.

Lemma one_sound : sem (One V) e.
Proof. simpl. apply dual_dual_sem. reflexivity. Qed.

Lemma top_ctxt_sound X : par_sem X (sem (Top V)) e.
Proof. apply par_sem_bwd.  rewrite lolli_sem_e. simpl. tauto. Qed.

Lemma bot_ctxt_sound (X : M -> Prop) : 
  X e -> par_sem X (sem (Bot V)) e.
Proof. intro xe. apply par_sem_bwd.  rewrite lolli_sem_e. simpl.
intro x. unfold dual_sem. unfold lolli_sem.
intro xb.  exact (xb _ _ xe (cmrid cmM _)).  Qed.

(* this should be true as par_sem is commutative, but
  similar proof fails, so par_sem_bwd must not be an equivalence
Lemma bot_ctxt_sound' (X : M -> Prop) : 
  X e -> par_sem (sem (Bot V)) X e.
  *)

Lemma plusL_sem A B u : sem A u -> sem (@plus V A B) u.
Proof. intro sa. simpl. apply dual_dual_sem. exact (or_introl sa). Qed.

Lemma plusL_ctxt_sound (X : M -> Prop) A B u : 
  par_sem X (sem A) u -> par_sem X (sem (@plus V A B)) u.
Proof. apply par_sem_mono. tauto. apply plusL_sem. Qed.

Lemma plusR_sem A B u : sem B u -> sem (@plus V A B) u.
Proof. intro sa. simpl. apply dual_dual_sem. exact (or_intror sa). Qed.

Lemma plusR_ctxt_sound (X : M -> Prop) A B u : 
  par_sem X (sem B) u -> par_sem X (sem (@plus V A B)) u.
Proof. apply par_sem_mono. tauto. apply plusR_sem. Qed.

Lemma wth_ctxt_sound (X : M -> Prop) A B u : par_sem X (sem A) u ->
  par_sem X (sem B) u -> par_sem X (sem (@wth V A B)) u.
Proof. intros sa sb.
apply par_sem_bwd. unfold lolli_sem.
pose (par_sem_fwd' (fact_sem _) sa) as la.
pose (par_sem_fwd' (fact_sem _) sb) as lb.
unfold lolli_sem in la.  unfold lolli_sem in lb.
intros * dxv muvw. simpl.  
exact (conj (la v w dxv muvw) (lb v w dxv muvw)). Qed.

Lemma tens_mrg_sound X Y A B : par_sem X (sem A) e ->
  par_sem Y (sem B) e -> par_sem (par_sem X Y) (sem (@tens V A B)) e.
Proof. intros sxa syb.
apply par_sem_e_bwd.  intros v txy.
pose (par_sem_fwd' (fact_sem _) sxa) as lxa.
pose (par_sem_fwd' (fact_sem _) syb) as lyb.
unfold lolli_sem in lxa.  unfold lolli_sem in lyb.
revert txy. apply tens_sem_mono ; intros u dsu.
- exact (lxa u u dsu (cmlid cmM _)).
- exact (lyb u u dsu (cmlid cmM _)).  Qed.

Hypothesis KsubJ : forall x, K x -> J x.
Hypothesis KsubJc : forall x, K x -> Jc x.
Hypothesis KsubJw : forall x, K x -> Jw x.
Hypothesis Kidem : forall x, tens_sem K K x -> K x.
Hypothesis Kidemp : forall x, prods K K x -> K x.
Hypothesis Ke : dual_sem (dual_sem K) e.
(* not needed
Hypothesis Kid : forall x, dual_sem (dual_sem (eq e)) x -> K x.
*)
(* note, at this point DLW has
  e in cl K, ie dual_sem (dual_sem K) e
  equiv dual_sem (dual_sem (eq e)) x -> dual_sem (dual_sem K) x
  which is a weaker condition,
  and maybe Kidem should be prods K K x -> K x,
  bacause tens_sem K K x -> K x isn't true(?) in the pr_sem semantics *)
(* something wrong here, since we have 
  J x = dual_sem (dual_sem (eq e)) x /\ ... -> K x -> J x 
  where did I get this definition of Kid ?? *)

(* don't otherwise need Kid
Lemma fact_K : fact K.
Proof. unfold fact. intros u ddk. apply Kid.
apply (dd_mono KsubJw) in ddk.  unfold Jw in ddk.
revert ddk. apply ds_ds_ds. easy. Qed.
*)

Lemma query_sound (X : M -> Prop) u : X u -> query_sem X u.
Proof. apply sub_dual_inv.
intros v c. destruct c. exact H. Qed.

Lemma query_ctxt_sound X Y u : 
  par_sem X Y u -> par_sem X (query_sem Y) u.
Proof. apply par_sem_mono. tauto. apply query_sound. Qed.

Lemma bang_sound' (X : M -> Prop) u : K u -> X u -> bang_sem X u.
Proof. intros idu xu. unfold bang_sem.
apply dual_dual_sem. tauto. Qed.

Print Implicit par_sem_eqv.
Print Implicit fact_dual.

Lemma bang_ctxt_sound_alt (X Y : M -> Prop) : 
  lolli_sem (bang_sem X) Y e -> lolli_sem (bang_sem X) (bang_sem Y) e.
Proof. rewrite !lolli_sem_e.  intros bxy x.
apply ds_ds_ds.  intros u xku. destruct xku.
pose (bxy _ (bang_sound' _ H0 H)).
apply dual_dual_sem.  easy. Qed.

(* try to prove this without using fact_K - no luck,
  but proved commutative version below 
Lemma bang_ctxt_sound (X Y : M -> Prop) : fact Y -> 
  par_sem (query_sem X) Y e -> par_sem (query_sem X) (bang_sem Y) e.
Proof.  intros fy.
rewrite (fun X => par_sem_eqv X fy).
rewrite (fun X => @par_sem_eqv X (bang_sem Y) (@fact_dual _)).
rewrite !lolli_sem_e.
intros dqy x dq.
apply bang_sound'.
unfold dual_sem in dq.
unfold lolli_sem in dq.
unfold query_sem in dq.
(* this would be easy if K were a fact *)
admit.
exact (dqy _ dq).
Admitted.
*)

Print Implicit par_sem_eqv.
Print Implicit sub_dual_inv.

(* try the commutative version *)
Lemma bang_ctxt_sound (X Y : M -> Prop) : fact Y -> 
  par_sem Y (query_sem X) e -> par_sem (bang_sem Y) (query_sem X) e.
Proof.  intros fy.
pose (fun X Z => @par_sem_eqv X _ (@fact_dual Z)).
rewrite !i.  rewrite !lolli_sem_e.
intros dyxk x.  apply dual_anti.
intros u cdk.  unfold bang_sem.
pose (fy _ (sub_dual_inv (dual_sem Y) dyxk cdk)).
apply dual_dual_sem.  exact (conj y (proj2 cdk)).
Qed.

(* this proof uses fact_K, see proof of commutative version above 
Lemma bang_ctxt_sound (X Y : M -> Prop) : fact Y -> 
  par_sem (query_sem X) Y e -> par_sem (query_sem X) (bang_sem Y) e.
Proof. unfold query_sem.
intros fy qxy.
apply par_sem_bwd'.
apply fact_int. apply fact_dual. apply fact_K.
apply (par_sem_fwd fy) in qxy.
rewrite lolli_sem_e.  rewrite -> lolli_sem_e in qxy.
intros x dsi.  exact (bang_sound' _ (proj2 dsi) (qxy _ dsi)).  Qed.
*)

Print Implicit par_sem_fwd.

Lemma K_lolli_refl Y x : fact Y -> K x -> lolli_sem Y Y x.
Proof. intros fy kx.
pose (KsubJw kx) as jx.  unfold Jw in jx.  
apply (fact_lolli fy). clearbody jx. revert jx.  apply dd_mono.
intros. subst u. apply lolli_same_sound. Qed.

Lemma ddK_lolli_refl Y x : fact Y -> dual_sem (dual_sem K) x -> lolli_sem Y Y x.
Proof. intros fy ddkx.
apply (fact_lolli fy). revert ddkx.  apply dd_mono.
intro u. exact (K_lolli_refl fy). Qed.

Lemma K_e_lem Y x : fact Y -> Y e -> K x -> Y x.
Proof. intros fy ye kx.  apply (K_lolli_refl fy kx ye (cmrid cmM _)). Qed.

Lemma ddK_e_lem Y x : fact Y -> Y e -> dual_sem (dual_sem K) x -> Y x.
Proof. intros fy ye kx.  apply (ddK_lolli_refl fy kx ye (cmrid cmM _)). Qed.

(* found a proof of this not requiring fact_K *)
Lemma wk_ctxt_sound (X Y : M -> Prop) : fact Y -> 
  Y e -> par_sem (query_sem X) Y e.
Proof. intros fy ye. rewrite (fun X => par_sem_eqv X fy).
rewrite lolli_sem_e.  intros x dq.
unfold dual_sem in dq.
apply (ddK_e_lem fy ye).
revert x dq. apply dd_mono. easy. Qed.

(* this proof involves fact_K 
Lemma wk_ctxt_sound (X Y : M -> Prop) : fact Y -> 
  Y e -> par_sem (query_sem X) Y e.
Proof. intros fy ye.  apply par_sem_bwd'.
apply fact_int. apply fact_dual. apply fact_K.
rewrite lolli_sem_e.  
intros. apply K_e_lem ; tauto. Qed.
*)

(* actually use these now, not wk_ctxt_sound *)
Lemma wk_lolli_lem (X : M -> Prop) : lolli_sem (bang_sem X) (dual_sem bot) e.
Proof. apply lolli_sem_e. unfold bang_sem. apply ds_ds_ds.
intros u xui. destruct xui.
pose (KsubJw H0) as ju. unfold Jw in ju. clearbody ju.
revert ju. apply dual_anti. intros.
apply dual_sem_1. exact H1. Qed.

Lemma wk_lolli_lemd (X : M -> Prop) : lolli_sem bot (query_sem X) e.
Proof. apply lolli_sem_e.  intros x bx v w mbk me.
pose (KsubJw (proj2 mbk)) as ju. unfold Jw in ju.  clearbody ju.
rewrite dual_sem_1_eq in ju.
apply (ju _ _ bx).  apply (cmcomm cmM). exact me. Qed.

Lemma ctr_lolli_lem (X : M -> Prop) : 
  lolli_sem (bang_sem X) (tens_sem (bang_sem X) (bang_sem X)) e.
Proof. apply lolli_sem_e. unfold bang_sem. apply ds_ds_ds.
intros u xui. destruct xui.
pose (KsubJc H0) as ju. unfold Jc in ju.  clearbody ju.
revert ju. apply tens_sem_mono ; intros ; subst ; 
  apply dual_dual_sem ; split ; assumption. Qed.

(* dualizing ctr_lolli_lem is harder than the original!! *)
Lemma ctr_lolli_lemd (X : M -> Prop) : 
  lolli_sem (par_sem (query_sem X) (query_sem X)) (query_sem X) e.
Proof. apply lolli_sem_e.  unfold par_sem.
apply dual_anti.  unfold query_sem.
pose (@ctr_lolli_lem (dual_sem X)).
pose (proj1 (lolli_sem_e _ _) l).
intros u diu.  exact (t u (dual_dual_sem diu)). Qed.

Lemma ctr_lolli_sound (X Y : M -> Prop) : 
  lolli_sem (tens_sem (bang_sem X) (bang_sem X)) Y e ->
  lolli_sem (bang_sem X) Y e.
Proof. rewrite !lolli_sem_e.
intros ty x bx. apply ty.
revert x bx.  apply lolli_sem_e. apply ctr_lolli_lem. Qed.

Print Implicit ctr_lolli_lem.
Print Implicit lolli_sem_e.
Print Implicit dual_sub_inv.

(* soundness of rules *)
Lemma merge_tens_sound ps c :
  merge_ctxtg Tensrule ps c -> ForallT (fun p => seml p e) ps -> seml c e.
Proof. intros m0 pss.
destruct m0.  destruct m0.  inversion t. subst.
rewrite !seml_app.
rewrite (par_comm_eq _ (seml cr)).  apply par_assocr.
rewrite seml_single.
inversion pss. inversion H2. clear pss H2 H6. subst.
rewrite seml_app in H1.  rewrite seml_app in H5.
rewrite seml_cons in H1.  rewrite seml_cons in H5.
rewrite (par_comm_eq (sem _)) in H1.
rewrite (par_comm_eq (sem _)) in H5.
rewrite par_assoc_eq in H5.  rewrite par_assoc_eq in H1.
pose (tens_mrg_sound H1 H5). clearbody p. revert p.
apply iffD1.  apply fun_cong.  apply fun_cong. apply f_equal.
rewrite (seml_merge m0).  rewrite (seml_merge m1).
rewrite !par_assoc_eq. apply fun_cong. apply f_equal.
rewrite - !par_assoc_eq. apply f_equal. apply par_comm_eq. Qed.

Lemma seml_fe Φ1 Φ2 As : seml (fmlsext Φ1 Φ2 As) e <->
  (forall x : M, dual_sem (par_sem (seml Φ1) (seml Φ2)) x -> seml As x).
Proof. unfold fmlsext. rewrite !seml_app.
  rewrite - (par_comm_eq (seml Φ2)).  rewrite (par_assoc_eq).
  rewrite (par_sem_eqv _ (fact_seml _) e). 
  apply lolli_sem_e. Qed.

Lemma llprinc_sound ps c :
  fmlsruleg llprinc ps c -> ForallT (fun p => seml p e) ps -> seml c e.
Proof. intros f pss. destruct f. destruct l.
- (* Parrule *) destruct p. inversion pss. clear pss H2. subst.
  revert H1. unfold fmlsext. rewrite !seml_app.
  rewrite !seml_cons.  rewrite (par_assoc_eq (sem A)). easy.
- (* Wthrule *) destruct w.  inversion pss. inversion H2.
  clear pss H2 H6. subst. revert H1 H5.
  rewrite !seml_fe. rewrite !seml_single. 
  intros sa sb x dp.  exact (conj (sa x dp) (sb x dp)). 

- (* PlusLrule *) destruct p. inversion pss. clear pss H2. subst.
  revert H1.  rewrite !seml_fe. rewrite !seml_single. 
  intros sa x dp.  pose (sa _ dp). simpl.
  rewrite dual_sem_or'. clearbody s. revert s.
  apply sub_dual_inv. easy.

- (* PlusRrule *) destruct p. inversion pss. clear pss H2. subst.
  revert H1.  rewrite !seml_fe. rewrite !seml_single. 
  intros sa x dp.  pose (sa _ dp). simpl.
  rewrite dual_sem_or'. clearbody s. revert s.
  apply sub_dual_inv. easy.

- (* Toprule *) destruct t.
  rewrite !seml_fe. rewrite !seml_single. simpl. easy.

- (* Botrule *) destruct b. inversion pss.  clear pss H2. subst.
  revert H1. rewrite !seml_fe. rewrite seml_single. rewrite !seml_nil.
  easy. Qed.

Lemma mall_sound ps c :
  mall_rules ps c -> ForallT (fun p => seml p e) ps -> seml c e.
Proof. intros mpc pss.  destruct mpc.
- (* llprinc *) exact (llprinc_sound f pss).
- (* Tensrule *) exact (merge_tens_sound m0 pss).
- (* Onerule *) destruct o. unfold seml. simpl.
  apply par_sem_e_bwd. intro. rewrite dual_sem_1. easy.
- (* Id *) destruct i.  unfold seml. simpl.
  apply par_sem_bwd. rewrite lolli_sem_e. 
  intros. exact (par_sem_botic (@fact_dual _) H).
- (* Idd *) destruct i.  unfold seml. simpl.
  apply par_sem_bwd. rewrite lolli_sem_e.  intros.
  apply (par_sem_botic (@fsv v)).  exact (@fsv v x H).
Qed.

Print Implicit par_sem_botic.
Print Implicit wk_ctxt_sound.

Lemma dda_splitL A B u :
  dual_sem (dual_sem (fun x => A x /\ B x)) u -> dual_sem (dual_sem A) u.
Proof. apply dd_mono. easy. Qed.

Lemma dda_splitR A B u :
  dual_sem (dual_sem (fun x => A x /\ B x)) u -> dual_sem (dual_sem B) u.
Proof. apply dd_mono. easy. Qed.

Lemma par_qq A B : par_sem (query_sem A) (query_sem B) =
  query_sem (fun x => A x \/ B x).
Proof. apply iff_app_eq. intro. split ; apply sub_dual_inv ; intros.
- cD. apply dual_dual_sem.

pose (KsubJc H0) as ju. unfold Jc in ju.  clearbody ju.
revert ju.  apply dual_sem_or in H. cD.

apply tens_sem_mono ; intros ; subst ; rewrite bang_query ;
  apply bang_sound' ; assumption.

- revert H. apply sub_dual_inv. intro.
unfold query_sem. rewrite dual_sem_or'.
rewrite ddd_iff. apply sub_dual_inv.
intros w pdd. apply prod_dd in pdd. 
revert pdd. apply dd_mono.
intros u pab.  destruct pab. cD.
pose (Kidemp (prodI _ _ H3 H2 H1)).
pose H1.  rewrite -> (cmcomm cmM) in m0.
pose (K_lolli_refl (@fact_dual _) H2 H m0) as daz.
pose (K_lolli_refl (@fact_dual _) H3 H0 H1) as dbz.
repeat split ; assumption. Qed.

(*
NB got this far without using non-invertible apply 
pose (dda_splitL _ H) as dda.  pose (dda_splitL _ H0) as ddb.
pose (dda_splitR _ H) as ddkx.  pose (dda_splitR _ H0) as ddky.
rewrite -> ddd_iff in dda.  rewrite -> ddd_iff in ddb.
pose H1.  rewrite -> (cmcomm cmM) in m0.
pose (ddK_lolli_refl (@fact_dual _) ddky dda m0) as daz.
pose (ddK_lolli_refl (@fact_dual _) ddkx ddb H1) as dbz.
(* now for K *)
pose (prodI _ _ ddkx ddky H1).
want prods K K z (tens_sem K K z will do)
this is cl_stability of DLW 

pose (ddK_lolli_refl fact_bot ddkx) as lbbx.
pose (ddK_lolli_refl fact_bot ddky) as lbby.
pose (lolli_B lbbx lbby H1) as lbbz.
*)

(* 
Lemma par_qq A B : par_sem (query_sem A) (query_sem B) =
  query_sem (fun x => A x \/ B x).
Proof. apply iff_app_eq. intro. split ; apply sub_dual_inv ; intros.
- cD. apply dual_dual_sem.

pose (KsubJc H0) as ju. unfold Jc in ju.  clearbody ju.
revert ju.  apply dual_sem_or in H. cD.

apply tens_sem_mono ; intros ; subst ; rewrite bang_query ;
  apply bang_sound' ; assumption.

- revert H. apply dd_mono. intros u H.  split.
+ rewrite !bang_query in H.  unfold bang_sem in H.
destruct H.  apply dual_sem_or.  split.
++ eapply dd_mono in H. 2: intros u dk ; exact (proj1 dk).
rewrite -> ddd_iff in H.
eapply dd_mono in H0. 2: intros u dk ; exact (proj2 dk).
eapply (ddK_lolli_refl (@fact_dual _)) in H0.
apply (H0 _ _ H). apply (cmcomm cmM). exact H1.
++ eapply dd_mono in H. 2: intros u dk ; exact (proj2 dk).
eapply dd_mono in H0. 2: intros u dk ; exact (proj1 dk).
rewrite -> ddd_iff in H0.
eapply (ddK_lolli_refl (@fact_dual _)) in H.
apply (H _ _ H0 H1).
 
+ rewrite !bang_query in H.  destruct H.
apply Kidemp.  eapply prodI. 3: eassumption.
(* at this point need fact_K - how to fix?? *)
unfold bang_sem in H. revert H.  apply (ds_ds_fact fact_K). easy.
unfold bang_sem in H0. revert H0.  apply (ds_ds_fact fact_K). easy.
Qed.
*)

Lemma query_dd A : query_sem (dual_sem (dual_sem A)) = query_sem A.
Proof. unfold query_sem.  apply f_equal.
apply iff_app_eq. intro. rewrite ddd_iff. reflexivity. Qed.

(* this one more likely than query_seml_eqv to be right *)
Lemma query_seml_eqv_plus fs :
  seml (map (@Query V) fs) = query_sem (sem (fold_right (@plus V) (Zero V) fs)).
Proof. unfold seml. induction fs ; simpl.
- unfold query_sem. 
apply iff_app_eq.
intro. split.

+ apply sub_dual_inv. intros v ddk.
rewrite -> ddd_iff in ddk. cD.
pose (KsubJw ddk0) as ju. unfold Jw in ju. 
rewrite -> dual_sem_1_eq in ju. exact ju.
+ rewrite - dual_sem_1_eq. apply sub_dual_inv. intros. subst v.
apply (@dd_mono K).  intros u ku.  rewrite ddd_iff. split. 
intros v w em. destruct em. exact ku. exact Ke.

- simpl. rewrite IHfs. rewrite par_qq.
rewrite query_dd. reflexivity. Qed.

(* case of Bangrule - very difficult to get this proof right *)
Lemma bang_sound_lem ps c (f : fmlsrulegq (Query (V:=V)) Bangrule ps c)
  (pss : ForallT (fun p => seml p e) ps) : seml c e.
Proof. destruct f. destruct b. subst.
inversion pss. clear pss H2. subst.
revert H1.  rewrite !seml_fe. rewrite !seml_single. 
rewrite - !lolli_sem_e.  rewrite - !seml_app.  rewrite - !map_app.
rewrite !query_seml_eqv_plus.  apply bang_ctxt_sound_alt.  Qed.

Lemma maell_sound ps c : 
  maell_rules ps c -> ForallT (fun p => seml p e) ps -> seml c e.
Proof. intros mpc pss.  destruct mpc.
- (* mall_rules *) exact (mall_sound m0 pss).
- (* weakening *) destruct f. destruct w. 
  inversion pss. clear pss H2. subst. revert H1.
  rewrite !seml_fe. intros sa x dp.  pose (sa _ dp). 
  rewrite seml_single. simpl. 
  clearbody s. clear dp. revert x s.
  rewrite - lolli_sem_e. rewrite seml_nil.
  apply wk_lolli_lemd.
- (* contraction *) destruct f. destruct c0. 
  inversion pss. clear pss H2. subst. revert H1.
  rewrite !seml_fe. intros sa x dp.  pose (sa _ dp). 
  clearbody s. clear dp sa. revert x s.
  rewrite seml_cons.  rewrite !seml_single. simpl. 
  rewrite - lolli_sem_e. apply ctr_lolli_lemd.
- (* Queryrule *) destruct f. destruct q.
  inversion pss. clear pss H2. subst.
  revert H1.  rewrite !seml_fe. rewrite !seml_single. 
  intros sa x dp.  pose (sa _ dp). simpl.  apply (query_sound s).
- (* Bangrule *) exact (bang_sound_lem f pss). Qed.

Lemma der_maell_sound : 
  forall c, derrec maell_rules emptyT c -> seml c e.
Proof. apply derrec_all_rect. intros. destruct H.
intros ps c mr dm.  exact (maell_sound mr). Qed.

(* cut_sound - assume first tens rule is applied *)
Lemma cut_sound X Y : fact Y -> par_sem (tens_sem (dual_sem X) X) Y e -> Y e.
Proof. intros fy pt. apply (par_sem_bot fy).
apply (par_sem_mono' pt (tens_lolli' fact_bot)). tauto. Qed.

(*
*)
End Phase_Space.
