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
Require Import gen genT.
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

Inductive idems : M -> Prop := | idemsI : forall x : M, m x x x -> idems x.

Definition idem1 x := (m x x x) /\ dual_sem (dual_sem (eq e)) x.
(* try idemd as alternative to idem1 *)
Definition idemd x := tens_sem (eq x) (eq x) x /\ dual_sem (dual_sem (eq e)) x.

Definition query_sem X := dual_sem (fun x => dual_sem X x /\ idemd x).
Definition bang_sem X := dual_sem (dual_sem (fun x => X x /\ idemd x)).
Definition bang_query X :
  dual_sem (query_sem X) = bang_sem (dual_sem X) := eq_refl.

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
  | Bang f => bang_sem (sem sv f)
  | Query f => query_sem (sem sv f)
  end.

(* semantics of list of formula is sem of their par *)
Definition seml {V} sv fs := fold_right par_sem bot (map (@sem V sv) fs).
(* note useful lemmas
  fold_left_rev_right fold_right_app fold_symmetric fold_left_app,
  need to prove more using assoc and comm and identity of par_sem *)

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

Axiom fact_idemd : fact idemd. (* can we prove this? *)

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

Lemma lolli_sem_1 X : forall u, iff (lolli_sem (eq e) X u) (X u).
Proof. unfold lolli_sem.
intro u. split.
- intro bm. apply (bm _ _ eq_refl).  apply (cmrid cmM).
- intros bu v w ev. subst v.  rewrite (cmride cmM). 
intro uw. subst. exact bu. Qed.

Lemma lolli_sem_1_eq X : (lolli_sem (eq e) X) = X.
Proof. apply iff_app_eq. apply lolli_sem_1. Qed.

Lemma dual_sem_1 : forall u, iff (dual_sem (eq e) u) (bot u).
Proof. apply lolli_sem_1. Qed.

Lemma dual_sem_1_eq : (dual_sem (eq e)) = bot.
Proof. apply iff_app_eq. apply dual_sem_1. Qed.

Lemma lolli_sem_e X Y : lolli_sem X Y e <-> (forall x, X x -> Y x).
Proof. unfold lolli_sem. split.
- intros eqv x xx. apply (eqv _ _ xx). apply (cmlid cmM).
- intros xy v w xv mevw.  apply (cmlide cmM) in mevw.
subst. exact (xy _ xv).  Qed.

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

Lemma par_assoc X Y Z u : 
  (par_sem X (par_sem Y Z)) u -> (par_sem (par_sem X Y) Z) u.
Proof. unfold par_sem.  rewrite  !(fact_dd_eq (@fact_tens _ _)).
apply dual_anti. intro v. apply tens_assocr. Qed.

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
  intros v pr. inversion pr.  exact (prodI _ _ (IHA1 _ H) (IHA2 _ H0) H1).
- rewrite ddd_iff. rewrite dual_sem_or. firstorder.
- rewrite ddd_iff. apply dual_anti. intros v sai.  destruct sai. split.
  apply (dual_anti _ IHA). apply dual_dual_sem. exact H. exact H0.
- apply dd_mono. firstorder. Qed.

Print Implicit sub_dual_inv.
Print Implicit prods_mono.

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

Lemma sem_dual {V} sv A : (forall v, fact (sv v)) -> 
  forall u, (sem sv (@dual V A) u) <-> (dual_sem (sem sv A) u).
Proof. intros fsv u. split.
apply (sem_dual_fwd _ _ fsv).  apply (sem_dual_bwd _ _ fsv). Qed.

Print Implicit merge3LI.
Print Implicit prodI.
Print Implicit ds_ds_fact.

Lemma sem_lolli {V} A B sv u : (forall v, fact (sv v)) ->
  sem sv (@lolli V A B) u <-> lolli_sem (sem sv A) (sem sv B) u.
Proof. intro fsv. unfold lolli. simpl. unfold par_sem.
rewrite curry_sem_bot_eqv.  unfold lolli_sem.
pose (fun A => sem_dual _ A fsv).  clearbody i.  split.
- intros dd * sa muvw. specialize (dd v w).  rewrite <- i in dd.
rewrite dual_dual in dd.
exact (fact_sem B sv fsv (dd sa muvw)).
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

Lemma dual_sem_eq_e v : dual_sem (eq e) v <-> bot v.
Proof. unfold dual_sem. unfold lolli_sem. 
split. intro. exact (H e v eq_refl (cmrid cmM _)).
intros bv v0 w ev mvw. subst. apply (cmride cmM) in mvw.
subst. exact bv. Qed.

Lemma dual_sem_eq_e' : dual_sem (eq e) = bot.
Proof. apply iff_app_eq. intro x. apply dual_sem_eq_e. Qed.

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

(* soundness - in semantics, true means set contains e,
  for semantics of list of formulae, imagine them joined by par *)
Lemma id_sound' X : par_sem X (dual_sem X) e.
Proof. apply par_sem_bwd. apply lolli_same_sound. Qed.

Lemma id_sound X : par_sem (dual_sem X) X e.
Proof. apply par_comm. apply id_sound'. Qed.

Lemma one_sound V sv : sem sv (One V) e.
Proof. simpl. apply dual_dual_sem. reflexivity. Qed.

Lemma top_ctxt_sound V sv X : par_sem X (sem sv (Top V)) e.
Proof. apply par_sem_bwd.  rewrite lolli_sem_e. simpl. tauto. Qed.

Lemma bot_ctxt_sound V sv (X : M -> Prop) : 
  X e -> par_sem X (sem sv (Bot V)) e.
Proof. intro xe. apply par_sem_bwd.  rewrite lolli_sem_e. simpl.
intro x. unfold dual_sem. unfold lolli_sem.
intro xb.  exact (xb _ _ xe (cmrid cmM _)).  Qed.

(* this should be true as par_sem is commutative, but
  similar proof fails, so par_sem_bwd must not be an equivalence
Lemma bot_ctxt_sound' V sv (X : M -> Prop) : 
  X e -> par_sem (sem sv (Bot V)) X e.
  *)

Lemma plusL_sem V sv A B u : sem sv A u -> sem sv (@plus V A B) u.
Proof. intro sa. simpl. apply dual_dual_sem. exact (or_introl sa). Qed.

Lemma plusL_ctxt_sound V sv (X : M -> Prop) A B u : 
  par_sem X (sem sv A) u -> par_sem X (sem sv (@plus V A B)) u.
Proof. apply par_sem_mono. tauto. apply plusL_sem. Qed.

Lemma plusR_sem V sv A B u : sem sv B u -> sem sv (@plus V A B) u.
Proof. intro sa. simpl. apply dual_dual_sem. exact (or_intror sa). Qed.

Lemma plusR_ctxt_sound V sv (X : M -> Prop) A B u : 
  par_sem X (sem sv B) u -> par_sem X (sem sv (@plus V A B)) u.
Proof. apply par_sem_mono. tauto. apply plusR_sem. Qed.

Lemma wth_ctxt_sound V sv (X : M -> Prop) A B u :
  (forall v, fact (sv v)) -> par_sem X (sem sv A) u ->
  par_sem X (sem sv B) u -> par_sem X (sem sv (@wth V A B)) u.
Proof. intros fsv sa sb.
apply par_sem_bwd. unfold lolli_sem.
pose (par_sem_fwd' (fact_sem _ _ fsv) sa) as la.
pose (par_sem_fwd' (fact_sem _ _ fsv) sb) as lb.
unfold lolli_sem in la.  unfold lolli_sem in lb.
intros * dxv muvw. simpl.  
exact (conj (la v w dxv muvw) (lb v w dxv muvw)). Qed.

Lemma tens_mrg_sound V sv X Y A B :
  (forall v, fact (sv v)) -> par_sem X (sem sv A) e ->
  par_sem Y (sem sv B) e -> par_sem (par_sem X Y) (sem sv (@tens V A B)) e.
Proof. intros fsv sxa syb.
apply par_sem_e_bwd.  intros v txy.
pose (par_sem_fwd' (fact_sem _ _ fsv) sxa) as lxa.
pose (par_sem_fwd' (fact_sem _ _ fsv) syb) as lyb.
unfold lolli_sem in lxa.  unfold lolli_sem in lyb.
revert txy. apply tens_sem_mono ; intros u dsu.
- exact (lxa u u dsu (cmlid cmM _)).
- exact (lyb u u dsu (cmlid cmM _)).  Qed.

Lemma par_sem_bot Y u : fact Y -> par_sem bot Y u -> Y u.
Proof. intros fy pby.  apply (par_sem_fwd' fy) in pby. 
exact (pby e u dual_sem_bot (cmrid cmM _)).  Qed.

Lemma query_sound (X : M -> Prop) u : X u -> query_sem X u.
Proof. apply sub_dual_inv.
intros v c. destruct c. exact H. Qed.

Lemma query_ctxt_sound X Y u : 
  par_sem X Y u -> par_sem X (query_sem Y) u.
Proof. apply par_sem_mono. tauto. apply query_sound. Qed.

Lemma bang_sound (X : M -> Prop) : X e -> bang_sem X e.
Proof. unfold bang_sem. rewrite dual_sem_e. intro sa.
intros u. unfold dual_sem. unfold lolli_sem. unfold idemd.
intros dsi. specialize (dsi e u). require dsi.
apply (conj sa).  split ; apply dual_dual_sem.
eapply prodI ; try reflexivity.  apply (cmlid cmM _). trivial.
exact (dsi (cmrid cmM _)). Qed.

Lemma bang_sound' (X : M -> Prop) u : idemd u -> X u -> bang_sem X u.
Proof. intros idu xu. unfold bang_sem.
apply dual_dual_sem. tauto. Qed.

Lemma bang_ctxt_sound (X Y : M -> Prop) : fact Y -> 
  par_sem (query_sem X) Y e -> par_sem (query_sem X) (bang_sem Y) e.
Proof. unfold query_sem.
intros fy qxy.
apply par_sem_bwd'.
apply fact_int. apply fact_dual. apply fact_idemd.
apply (par_sem_fwd fy) in qxy.
rewrite lolli_sem_e.  rewrite -> lolli_sem_e in qxy.
intros x dsi.  exact (bang_sound' _ (proj2 dsi) (qxy _ dsi)).  Qed.

Print Implicit par_sem_fwd.

Lemma wk_ctxt_sound (X Y : M -> Prop) : fact Y -> 
  Y e -> par_sem (query_sem X) Y e.
Proof. intros fy ye.  apply par_sem_bwd'.
apply fact_int. apply fact_dual. apply fact_idemd.
rewrite lolli_sem_e.  intro x.  unfold idemd.
rewrite dual_sem_eq_e'.
apply factd_iff in fy. destruct fy.  intro cc.  eapply lolli_B.
exact (proj2 (proj2 cc)).  exact ye.  exact (cmrid cmM _). Qed.

Lemma ctr_lolli_lem (X : M -> Prop) : 
  lolli_sem (bang_sem X) (tens_sem (bang_sem X) (bang_sem X)) e.
Proof. apply lolli_sem_e. unfold bang_sem. apply ds_ds_ds.
intros u xui. destruct xui. pose H0. destruct i. revert H1. apply dd_mono.
apply prods_mono ; intros ; subst ; apply dual_dual_sem ; exact (conj H H0).
Qed.

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
(* this might be difficult, need to prove inductively
  that as par_sem is assoc and commutative, need to just use
  par_sem context (principal formula) 
Lemma maell_sound {V} sv ps c : (forall v, fact (sv v)) ->
  @maell_rules V ps c -> ForallT (fun p => seml sv p e) ps -> seml sv c e.
Proof. intros fsv mpc pss.
destruct mpc.
- (* mall_rules *) admit.
- (* weakening *) destruct f. destruct w. sfs.
  unfold seml.
  rewrite map_app.
  rewrite fold_right_app.
*)

(* cut_sound - assume first tens rule is applied *)
Lemma cut_sound X Y : fact Y -> par_sem (tens_sem (dual_sem X) X) Y e -> Y e.
Proof. intros fy pt. apply (par_sem_bot fy).
apply (par_sem_mono' pt (tens_lolli' fact_bot)). tauto. Qed.

(*
*)
End Phase_Space.