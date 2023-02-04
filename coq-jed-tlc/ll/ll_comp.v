
(* completeness of linear logic calculus using phase semantics *)

Set Implicit Arguments.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT swappedT rtcT.
Require Import fmlsext lldefs ll_exch ll_camq ll_semnd.

From Coq Require Import ssreflect.

(* the monoid used for completeness, lists of formulae *)

Definition FLM {V} := list (LLfml V).
(* m is app, e is [] *)
(*
Print Implicit comm_monoid_nd.
Print Implicit merge.
Print Implicit nil.
Print Implicit tens_sem.
Print tens_sem.
Print Implicit der_ll.
Print Implicit dual_sem.
Print Implicit prb.
Print Implicit sem.
Print Implicit fact.
*)

Definition mergeP {T} X Y Z := inhabited (@merge T X Y Z).

(* problem, lists do not form a comm_monoid,
  need to use equivalence classes - at deductive or semantic level? 
  or use non-deterministic monoid, as in ll_semnd.v *)
Lemma comm_monoid_nd_list X : comm_monoid_nd (@mergeP X) [].
Proof. unfold comm_monoid_nd. 
repeat apply conj ; intros ; apply conj ;
try (apply inhabited_ind ; intro ; apply inhabits).
- intro m. destruct m.  destruct H.  destruct H0.
destruct (merge_assoc X1 X0). 
exact (merge3RI _ _ _ _ _ _ (inhabits m0) (inhabits m)).
- intro m. destruct m.  destruct H.  destruct H0.
destruct (merge_assoc (merge_sym X1) (merge_sym X0)). 
exact (merge3LI _ _ _ _ _ _ (inhabits (merge_sym m0)) (inhabits (merge_sym m))).
- exact (merge_sym X0).
- exact (merge_sym X0).
- apply inhabited_ind. apply merge_RnilE. 
- intro. subst. apply inhabits. apply merge_Rnil.
- apply inhabited_ind. apply merge_LnilE. 
- intro. subst. apply inhabits. apply merge_Lnil. Qed.


(* the Girard paper defines the set of members of the monoid 
  corresponding to a formula in terms of provability, which makes
  the completeness argument easy, but you need to show that this
  definition is consistent with the definitions of the semantic operations
  (corresponding to the formula connectives) *)

(* the K of DLW needs to be a parameter of the semantics,
which we choose to be the set of lists of query formulae 
(for DLW, banged formulae)
so soundness requires certain things like cl K ∅ and K ∘ K ⊆ K.
and completeness requires K is lists of query formulae *)

(* call this the provability semantics *)

Definition der_ll V A G := inhabited (derrec (@maell_rules V) emptyT (A :: G)).
Definition der_ll_l V As G := 
  inhabited (derrec (@maell_rules V) emptyT (As ++ G)).
Definition pr_sv {V} v G := 
  inhabited (derrec maell_rules emptyT (@Var V v :: G)).
Definition prb {V} G := inhabited (derrec (@maell_rules V) emptyT G).

(* K = lists of query formulae *)
(* I think this won't work but instead choose K to be the 
  set of lists of formula which you can always weaken in 
Inductive K {V} : list (LLfml V) -> Prop := 
  | K_I : forall G, K (map (@Query V) G). 

Problem: if K is lists of Query formulae then 
Kid doubtful (is says that formula lists that can always be weakened in 
are in K ; don't seem to need it
if K is lists of formulae which you can always weaken in,
then how do you know they can always be contracted (KsubJc)
*)
Inductive K {V} : list (LLfml V) -> Prop := 
  | K_I : forall G, K (map (@Query V) G). 
(*
Definition K {V} := 
  @dual_sem (list (LLfml V)) mergeP prb (dual_sem mergeP prb (eq [])).
  *)
Definition Kd {V} := 
  @dual_sem (list (LLfml V)) mergeP prb (dual_sem mergeP prb (eq [])).

Print Implicit maell_sound. 
Print Implicit sem.
Print Implicit pr_sv.
Print Implicit der_ll.
Print Implicit fact_sem.
Print Implicit prods.
Print Implicit comm_monoid_nd_list.

Lemma Ke {V} : dual_sem mergeP prb (dual_sem mergeP prb (@K V)) [].
Proof. apply (dual_dual_sem (comm_monoid_nd_list _)).
apply (K_I []). Qed.

Lemma Kidemp {V} x : prods mergeP K K x -> @K V x.
Proof. intro pmkk.  destruct pmkk. destruct H1. 
destruct H.  destruct H0. 
apply ll_lems.merge_map_exM in H1. cD.
subst. apply K_I. Qed.

Lemma Kdidem V x : @prods (list (LLfml V)) mergeP Kd Kd x -> Kd x.
Proof. intro pmkk.  destruct pmkk. destruct H1.  revert H H0.
unfold Kd. rewrite !(dual_sem_1_eq _ (comm_monoid_nd_list _)).
unfold dual_sem.  unfold lolli_sem.
intros mx my v w pv mz. destruct mz.
pose (merge_assoc H H1). cD. clear H H1.
eapply mx. 2: apply (inhabits s0).
eapply my. 2: apply (inhabits s1). exact pv. Qed.

(* Jw means, for the pr semantics, that weakening by x is admissible *)
Lemma Jw_pr {V} x : Jw mergeP [] prb x <-> (forall v w, 
  inhabited (derrec maell_rules emptyT v) -> mergeP x v w -> 
  inhabited (derrec (@maell_rules V) emptyT w)).
Proof. unfold Jw.  rewrite (dual_sem_1_eq _ (comm_monoid_nd_list _)).
(* unfold prb. unfold dual_sem. unfold lolli_sem. *) reflexivity. Qed.

Lemma KsubJw {V} x : @K V x -> Jw mergeP [] prb x.
Proof. unfold Jw. intro kx.  destruct kx.
rewrite (dual_sem_1_eq _ (comm_monoid_nd_list _)).
intros v w pv me. revert pv. unfold prb. 
destruct me.
pose (merges_swapped (merge_simple_app _ _) H).
apply inhabited_mono. intro dv. 
eapply exch_maell_rtc. 2: apply c.
clear H c.  induction G. exact dv.
eapply derI.  eapply wk_maellI.
eapply (OSgctxt_eq _ _ _ []). apply wkrule_I.
simpl. reflexivity. reflexivity.
sfs. apply (dersrec_singleI IHG). Qed.

(* meaning of dual_sem mergeP prb (@K V), etc *)
Lemma dK_pr {V} : dual_sem mergeP prb (@K V) = prb.
Proof. apply iff_app_eq. intro.  split ; intros.
apply (H []). apply (K_I []). apply inhabits. apply merge_Rnil.
intros v w kv me.  apply KsubJw in kv.
(* unfold Jw in kv.  unfold dual_sem in kv.  unfold lolli_sem in kv. *)
revert me.  rewrite (cmcomm (comm_monoid_nd_list _)).
apply kv.  intros v0 w0 ve me.  subst.  destruct me.
apply merge_RnilE in H0. subst. exact H. Qed.

Lemma ddK_pr {V} : dual_sem mergeP prb (dual_sem mergeP prb (@K V)) =
  Jw mergeP [] prb.
Proof. apply iff_app_eq. intro. unfold Jw.
rewrite (dual_sem_1_eq _ (comm_monoid_nd_list _)).
rewrite dK_pr. reflexivity. Qed.

Print Implicit Jw.
Print Implicit Jc.
Check ll_lems.merge_doubles_via_der.
Print Implicit merge_doubles.
Print Implicit prodI.
Check prodI.

(* Jc means, for the pr semantics, that whenever v, 
  merged in any way with two copies of x, is provable,
  then v, merged in any way with one copy of x, is provable *)
Lemma Jc_pr {V} x : Jc mergeP (@prb V) x <-> (forall u xu,
  (forall xx xxu, mergeP x x xx -> mergeP u xx xxu -> 
  inhabited (derrec maell_rules emptyT xxu)) -> 
  mergeP x u xu -> inhabited (derrec (@maell_rules V) emptyT xu)).
Proof. unfold Jc.  unfold tens_sem.  rewrite prods_eq_eq. reflexivity. Qed.

Lemma KsubJc {V} x : @K V x -> Jc mergeP prb x.
Proof. unfold Jc.  intros kx v w pxx me.
specialize (pxx (doubles x)).  destruct me.  destruct kx.
pose (ll_lems.merge_doubles_via_der (rules := ctrqrules) (merge_sym H)).
require s.
{ intros q inqx. apply InT_mapE in inqx. cD. subst.
intros a b cq.  exact (ctrqrules_I cq). }
cD. require (pxx s). { eapply prodI.
reflexivity. reflexivity. apply inhabits. apply merge_doubles. }
destruct (pxx (inhabits s0)).  apply inhabits.
apply (derl_derrec_trans (derl_mono ctrq_maell s1)).
apply (dersrec_singleI X). Qed.

(*
Lemma KdsubJ V x : @Kd V x -> J mergeP [] prb x.
Proof. unfold J. intro kdx. split. 2: exact kdx.
unfold tens_sem.
*)

(* a condition of semantics generally (forall v : V, fact m bot (sv v)) *)
(*
note lemmas from ll_semnd.v
Lemma dual_sem_1 : forall u, iff (dual_sem (eq e) u) (bot u).
Lemma dual_sem_bot : dual_sem bot e.
Lemma fact_bot : fact bot.
Check dual_sem_1.
Check dual_sem_bot.
Check fact_bot.
*)

Lemma pr_sv_sem V v : @pr_sv V v = @der_ll V (Var v).
Proof. reflexivity. Qed.

(* fact_der_ll follows easily from this *)
Lemma fact_der_ll_l V As : fact mergeP prb (@der_ll_l V As).
Proof. unfold fact.  unfold dual_sem.  unfold lolli_sem.    intros.
specialize (H As).  apply H.
2: apply inhabits. 2: apply merge_simple_appr.
intros.  destruct H0.  destruct H1.  apply inhabits. clear H.
pose (merges_swapped (merge_simple_app _ _) H0).
apply (exch_maell_rtc X c). Qed.

Lemma fact_der_ll V A : fact mergeP prb (@der_ll V A).
Proof. unfold fact.  unfold dual_sem.  unfold lolli_sem.    intros.
specialize (H [A]).  apply H.
2: apply inhabits. 2: apply merge_simple_appr.
intros.  destruct H0.  destruct H1.  apply inhabits.
apply merge_singleL in H0.  cD.  subst.  apply (exch_maell X).
swap_tac_Rc. Qed.

Lemma fact_pr_sv {V} v : fact mergeP prb (@pr_sv V v).
Proof. apply fact_der_ll. Qed.

Lemma der_ll_dual V A G : 
  dual_sem mergeP prb (der_ll A) G -> der_ll (@dual V A) G.
Proof. unfold dual_sem. unfold lolli_sem.  unfold der_ll.
intros lav. specialize (lav [dual A]).  unfold prb in lav.
apply lav.  apply inhabits. apply maell_id.
apply inhabits. apply merge_simple_appr. Qed.

(* this one requires cut rule
Lemma dual_der_ll V A G : 
  der_ll (@dual V A) G -> dual_sem mergeP prb (der_ll A) G.
Proof. unfold dual_sem. unfold lolli_sem.  unfold der_ll.
intros idag v w iav mgvw. unfold prb.
destruct idag.  destruct iav.  destruct mgvw.  apply inhabits.
destruct (fst (cut_adm_maell_Q A X0 X)). Qed.
*)

(* sem_dual instantiated to pr *)
Definition sem_dual_pr {V} A := @sem_dual _ _ _ prb (comm_monoid_nd_list _)
  K V pr_sv fact_pr_sv A.
Definition sem_dual_pr_eq {V} A := iff_app_eq _ _ (@sem_dual_pr V A).

Definition dual_anti_pr {V} := @dual_anti _ mergeP (@prb V).
Definition dd_mono_pr {V} := @dd_mono _ mergeP (@prb V).
Definition ddd_iff_pr {V} := 
  @ddd_iff _ mergeP [] (@prb V) (comm_monoid_nd_list _).
Definition fact_dd_eq_pr {V} :=
  @fact_dd_eq _ mergeP [] (@prb V) (comm_monoid_nd_list _).
Definition dd_der_ll_eq {V} A := fact_dd_eq_pr (@fact_der_ll V A).
Definition par_sem_mono_pr {V} := @par_sem_mono _ mergeP (@prb V).
Definition tens_sem_mono_pr {V} := @tens_sem_mono _ mergeP (@prb V).
Print Implicit ds_ds_fact.
Definition ds_ds_fact_pr {V} A X := @ds_ds_fact _ mergeP [] (@prb V)
  (comm_monoid_nd_list _) X _ (@fact_der_ll V A).
Definition dual_sub_inv_pr {V} A Y := @dual_sub_inv _ mergeP [] (@prb V)
  (comm_monoid_nd_list _) _ Y (@fact_der_ll V A).

Print Implicit dual_sub_inv.

Lemma mergeP_same T x : mergeP x x x -> x = (@nil T).
Proof. intro mps. destruct mps. exact (merge_eqL X). Qed.

Lemma mergeP_same_eq T x : mergeP x x x <-> x = (@nil T).
Proof. split. apply mergeP_same. 
intro. subst. apply inhabits. apply merge_Lnil. Qed.

(* now we need to show that the semantics defined using pr_sv
  corresponds to der_ll (at least, for completeness, one way) *)
Lemma sem_pr_tens V (sema semb : _ -> Prop) A B
  (IHAa : forall X, sema X -> der_ll A X)
  (IHAb : forall X, semb X -> der_ll B X) X :
  tens_sem mergeP prb sema semb X -> der_ll (@tens V A B) X.
Proof. intros ts.
pose (tens_sem_mono_pr IHAa IHAb ts).  clearbody t.
revert t.  unfold tens_sem.  apply ds_ds_fact_pr.
intros u p12.  destruct p12.
destruct H.  destruct H0.  destruct H1. apply inhabits.
unfold der_ll in *.
eapply derI. apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] [] x y). apply Tensrule_I.
apply merge_nil. apply H.  reflexivity. 
exact (dlCons X0 (dersrec_singleI X1)). Qed.

Lemma spp_lem V A v w : der_ll A v -> mergeP [A] v w -> @prb V w.
Proof.  unfold der_ll.  unfold prb.
intros dav me. destruct dav. destruct me. apply inhabits.
apply merge_singleL in H. cD. subst.
apply (exch_maell X). swap_tac_Rc. Qed.

Lemma sppl_lem V As v w : der_ll_l As v -> mergeP As v w -> @prb V w.
Proof.  unfold der_ll.  unfold prb.
intros dav me. destruct dav. destruct me. apply inhabits.
pose (merges_swapped (merge_simple_app _ _) H).
exact (exch_maell_rtc X c). Qed.

Lemma der_ll_prb V A w : der_ll A w <-> @prb V (A :: w).
Proof. reflexivity. Qed.

Lemma sem_pr_par_l V (sema semb : _ -> Prop) A Bs
  (IHAa : forall X, sema X -> der_ll A X)
  (IHAb : forall X, semb X -> der_ll_l Bs X) X :
  par_sem mergeP (@prb V) sema semb X -> der_ll_l (A :: Bs) X.
Proof. intro pab.  pose (par_sem_mono_pr IHAa IHAb pab).
unfold par_sem in p.  unfold tens_sem in p.
rewrite -> ddd_iff_pr in p.
clear IHAa IHAb pab.
unfold dual_sem in p.  unfold lolli_sem in p.
specialize (p (A :: Bs) ((A :: Bs) ++ X)).
require p.  eapply prodI.  apply spp_lem.  apply sppl_lem.
apply inhabits.  apply merge_simple_app.
require p.  apply inhabits.  apply merge_simple_appr.
unfold prb in p. unfold der_ll_l. exact p. Qed.

Print Implicit sem_pr_par_l.

Lemma sem_pr_par V (sema semb : _ -> Prop) A B
  (IHAa : forall X, sema X -> der_ll A X)
  (IHAb : forall X, semb X -> der_ll B X) X :
  par_sem mergeP prb sema semb X -> der_ll (@par V A B) X.
Proof. intro pab.  pose (sem_pr_par_l (Bs := [B]) IHAa IHAb pab).
destruct d. apply inhabits. clear IHAa IHAb pab.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Par_p.  eapply Parrule_I. reflexivity. reflexivity.
exact (dersrec_singleI X0). Qed.

Lemma sem_pr_bang V (sema : _ -> Prop) A
  (IHA : forall X, sema X -> der_ll A X) X :
  bang_sem mergeP prb K sema X -> der_ll (@Bang V A) X.
Proof. apply ds_ds_fact_pr.
intros u si. destruct si. specialize (IHA _ H).
destruct H0. destruct IHA. apply inhabits.
eapply derI.  eapply bang_maellI. eapply (fmlsrulegq_I _ _ []).
eapply Bangrule_I. reflexivity. reflexivity. reflexivity. reflexivity.
exact (dersrec_singleI X0). Qed.

Lemma der_ll_query V A u : der_ll A u -> der_ll (@Query V A) u.
Proof. unfold der_ll. intro ia. destruct ia. apply inhabits.
eapply derI.  eapply query_maellI.  eapply (OSgctxt_eq _ _ _ []).
eapply Queryrule_I. reflexivity. reflexivity.
exact (dersrec_singleI X). Qed.

Definition dsol W bot := dual_sem_or bot (comm_monoid_nd_list W).
Definition dsaol W bot := @dsao _ _ _ bot (comm_monoid_nd_list W).

Lemma ds_mrg_query V A : dual_sem mergeP prb (der_ll A) [@Query V A].
Proof. intros v w psav mqvw.
apply der_ll_query in psav.
destruct psav.  destruct mqvw.  apply inhabits.
apply merge_singleL in H. cD. subst.
apply (exch_maell X). swap_tac_Rc. Qed.

(* this is a sort of monotonicity of query *)
(* found, with much effort, a proof of this not requiring fact_K *)
(* previous proof of sem_pr_query involving fact_K used dual_sem_or *)
Lemma sem_pr_query V (sema : _ -> Prop) A 
  (IHA : forall X, sema X -> der_ll A X) X :
  query_sem mergeP prb K sema X -> der_ll (@Query V A) X.
Proof. intro ddi. 
pose (query_sem_mono IHA ddi).
clearbody q.  clear IHA ddi.
(* unfold query_sem in q.  unfold dual_sem in q.  unfold lolli_sem in q. 
pose (q [Query A] (Query A :: X)).  unfold der_ll.  unfold prb in p.  *)
apply (q [Query A] (Query A :: X)).  split.
- apply ds_mrg_query.
- apply (K_I [A]).
- apply inhabits. apply merge_simple_appr.
Qed.

Print Implicit query_sem_mono.
Print Implicit lolli_sem_mono.
Print Implicit dual_sem_or.
Print Implicit dd_mono.
Print Implicit dd_mono_pr.
Print Implicit dual_anti.
Print Implicit dual_anti_pr.
Print Implicit fact_pr_sv.
Print Implicit dual_sem_1_eq.
Print Implicit ds_ds_fact_pr.
Print Implicit fact_der_ll.
Print Implicit fact_dd_eq.
Print Implicit fact_dd_eq_pr.
Print Implicit comm_monoid_nd_list.
Print Implicit par_sem_mono.
Print Implicit par_sem_mono_pr.
Check (ds_ds_fact (comm_monoid_nd_list _)).
Check (fact_dd_eq_pr (@fact_der_ll _ _)).
Print Implicit dd_der_ll_eq.
Print Implicit prodI.
Print Implicit dual_sub_inv_pr.

(* completeness re this particular semantics *)
Lemma sem_pr V A X : sem mergeP [] prb K pr_sv A X -> @der_ll V A X.
Proof. revert X. induction A ; simpl.
- unfold pr_sv. unfold der_ll. tauto.
- unfold dual_sem. unfold der_ll. unfold lolli_sem.
unfold pr_sv. unfold prb. intros.
specialize (H [DVar v]). apply H.
2: apply inhabits. 2: apply merge_simple_appr.
apply inhabits. pose (maell_id (Var v)).  simpl in d. exact d.
- unfold prb. unfold der_ll.
intro. apply inhabited_ind.  intro. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Bot_p.  eapply Botrule_I. reflexivity. reflexivity.
apply dersrec_singleI. exact X0.
- unfold der_ll. intros. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Top_p.  eapply Toprule_I. reflexivity. reflexivity. apply dlNil.
- rewrite (dual_sem_1_eq (@prb V) (comm_monoid_nd_list _)).
unfold der_ll. unfold dual_sem. unfold lolli_sem.
intros X pmb. specialize (pmb [One V] (One V :: X)).
unfold prb in pmb. apply pmb.
2: apply inhabits. 2: apply merge_simple_appr.
apply inhabits. eapply derI. apply one_maellI. apply Onerule_I. apply dlNil.
- intros X dde. unfold dual_sem in dde. unfold lolli_sem in dde.
unfold der_ll. unfold prb in dde. apply (dde [Zero V]).
2: apply inhabits. 2: apply merge_simple_appr. tauto.

- (* tens *) apply sem_pr_tens ; assumption.

- (* wth *) intros X sw. 
specialize (IHA1 _ (proj1 sw)).  specialize (IHA2 _ (proj2 sw)).
clear sw. unfold der_ll in *.
destruct IHA1.  destruct IHA2.  apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Wth_p.  eapply Wthrule_I. reflexivity. reflexivity.
exact (dlCons X0 (dersrec_singleI X1)).

- (* par *) apply sem_pr_par ; assumption. 

- (* plus *) apply ds_ds_fact_pr.
intros u ddo.  destruct ddo.
+ specialize (IHA1 _ H). clear IHA2 H.  destruct IHA1. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply PlusL_p.  eapply PlusLrule_I. reflexivity. reflexivity.
exact (dersrec_singleI X).
+ specialize (IHA2 _ H). clear IHA1 H.  destruct IHA2. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply PlusR_p.  eapply PlusRrule_I. reflexivity. reflexivity.
exact (dersrec_singleI X).
 
- (* Bang *) apply sem_pr_bang ; assumption.
- (* Query *) apply sem_pr_query ; assumption.
Qed.

Lemma seml_pr V As : forall X,
  seml mergeP [] prb K pr_sv As X -> @der_ll_l V As X.
Proof. induction As. 
- rewrite seml_nil. unfold der_ll_l. unfold prb. easy.
- rewrite seml_alt. intro X. simpl. apply sem_pr_par_l.
apply sem_pr.  rewrite - seml_alt. exact IHAs. Qed.

Print Implicit sem_pr_par_l.
Print Implicit dual_sem_bot.
Print Implicit dual_sem_1_eq.
Print Implicit comm_monoid_nd_list.
Print Implicit maell_sound.
Print Implicit cut_sound.
Print Implicit fact_der_ll.
Print Implicit fact_sem.

Definition maell_sound_pr V :=
  @maell_sound _ mergeP [] prb (comm_monoid_nd_list _)
  K V pr_sv fact_pr_sv KsubJc KsubJw Kidemp Ke.

Definition der_maell_sound_pr V :=
  @der_maell_sound _ mergeP [] prb (comm_monoid_nd_list _)
  K V pr_sv fact_pr_sv KsubJc KsubJw Kidemp Ke.

Check maell_sound_pr.  Check der_maell_sound_pr.

Definition cut_sound_pr V X Y := 
  @cut_sound _ mergeP [] (@prb V) (comm_monoid_nd_list _)
  K X _ (@fact_der_ll _ Y). 

Definition cut_sound_pr_l V X Y := 
  @cut_sound _ mergeP [] (@prb V) (comm_monoid_nd_list _)
  K X _ (@fact_der_ll_l _ Y). 

Check cut_sound_pr.  Check cut_sound_pr_l.

(* from here to completeness: and to cut-admissibility *)
Check sem_pr.
(* cut_sound - assume first tens rule is applied *)
Check cut_sound.
Check maell_sound_pr. 

Print Implicit seml_pr.
Print Implicit cut_sound_pr_l.

Theorem cut_adm_maell_sem {V} (A : LLfml V) cl cr c :
  derrec maell_rules emptyT (dual A :: cl) ->
  derrec maell_rules emptyT (A :: cr) ->
  merge cl cr c -> inhabited (derrec maell_rules emptyT c).
Proof. intros dl dr me. 
(* first use tens rule since cut_sound assumes that done *)
assert (derrec maell_rules emptyT (tens (dual A) A :: c)).
eapply derI. apply tens_maellI.
eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] []). apply Tensrule_I.
apply merge_nil. exact me.  reflexivity. simpl.
apply (dlCons dl). apply (dersrec_singleI dr). clear dl dr.
apply der_maell_sound_pr in X.
rewrite seml_cons in X. simpl in X.  rewrite sem_dual_pr_eq in X.
epose (par_sem_mono' X). require p. intros u t. exact t.
pose (cut_sound_pr_l (p (seml_pr _))).
unfold der_ll_l in d.  rewrite -> app_nil_r in d. exact d. Qed.

Check cut_adm_maell_sem.


