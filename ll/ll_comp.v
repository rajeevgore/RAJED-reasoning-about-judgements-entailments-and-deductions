
(* completeness of linear logic calculus using phase semantics *)

Set Implicit Arguments.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT swappedT.
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
Print Implicit pr_sem.
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

Definition pr_sem V A G := inhabited (derrec (@maell_rules V) emptyT (A :: G)).
Definition pr_seml V As G := 
  inhabited (derrec (@maell_rules V) emptyT (As ++ G)).
Definition pr_sv {V} v G := 
  inhabited (derrec maell_rules emptyT (@Var V v :: G)).
Definition prb {V} G := inhabited (derrec (@maell_rules V) emptyT G).
(* K = lists of query formulae *)
Inductive K {V} : list (LLfml V) -> Prop := 
  | K_I : forall G, K (map (@Query V) G). 

Print Implicit sem.
Print Implicit pr_sv.
Print Implicit pr_sem.

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

Lemma pr_sv_sem V v : @pr_sv V v = @pr_sem V (Var v).
Proof. reflexivity. Qed.

(* do we need this result? note, fact_pr_sem follows easily from it
Lemma fact_pr_seml V As : fact mergeP prb (@pr_seml V As).
Proof. unfold fact.  unfold dual_sem.  unfold lolli_sem.    intros.
specialize (H As).  apply H.
2: apply inhabits. 2: apply merge_simple_appr.
intros.  destruct H0.  destruct H1.  apply inhabits.
(* need result here, two different merges is transitive closure of swapped *)
*)

Lemma fact_pr_sem V A : fact mergeP prb (@pr_sem V A).
Proof. unfold fact.  unfold dual_sem.  unfold lolli_sem.    intros.
specialize (H [A]).  apply H.
2: apply inhabits. 2: apply merge_simple_appr.
intros.  destruct H0.  destruct H1.  apply inhabits.
apply merge_singleL in H0.  cD.  subst.  apply (exch_maell X).
swap_tac_Rc. Qed.

Lemma fact_pr_sv {V} v : fact mergeP prb (@pr_sv V v).
Proof. apply fact_pr_sem. Qed.

Lemma pr_sem_dual V A G : 
  dual_sem mergeP prb (pr_sem A) G -> pr_sem (@dual V A) G.
Proof. unfold dual_sem. unfold lolli_sem.  unfold pr_sem.
intros lav. specialize (lav [dual A]).  unfold prb in lav.
apply lav.  apply inhabits. apply maell_id.
apply inhabits. apply merge_simple_appr. Qed.

(* this one requires cut rule
Lemma dual_pr_sem V A G : 
  pr_sem (@dual V A) G -> dual_sem mergeP prb (pr_sem A) G.
Proof. unfold dual_sem. unfold lolli_sem.  unfold pr_sem.
intros idag v w iav mgvw. unfold prb.
destruct idag.  destruct iav.  destruct mgvw.  apply inhabits.
destruct (fst (cut_adm_maell_Q A X0 X)). Qed.
*)

(* sem_dual instantiated to pr *)
Definition sem_dual_pr {V} A := @sem_dual _ _ _ prb (comm_monoid_nd_list _)
  K V pr_sv A fact_pr_sv.
Definition sem_dual_pr_eq {V} A := iff_app_eq _ _ (@sem_dual_pr V A).

Definition dual_anti_pr {V} := @dual_anti _ mergeP (@prb V).
Definition dd_mono_pr {V} := @dd_mono _ mergeP (@prb V).
Definition ddd_iff_pr {V} := 
  @ddd_iff _ mergeP [] (@prb V) (comm_monoid_nd_list _).
Definition fact_dd_eq_pr {V} :=
  @fact_dd_eq _ mergeP [] (@prb V) (comm_monoid_nd_list _).
Definition dd_pr_sem_eq {V} A := fact_dd_eq_pr (@fact_pr_sem V A).
Definition par_sem_mono_pr {V} := @par_sem_mono _ mergeP (@prb V).
Definition tens_sem_mono_pr {V} := @tens_sem_mono _ mergeP (@prb V).
Print Implicit ds_ds_fact.
Definition ds_ds_fact_pr {V} A X := @ds_ds_fact _ mergeP [] (@prb V)
  (comm_monoid_nd_list _) X _ (@fact_pr_sem V A).
Definition dual_sub_inv_pr {V} A Y := @dual_sub_inv _ mergeP [] (@prb V)
  (comm_monoid_nd_list _) _ Y (@fact_pr_sem V A).

Print Implicit dual_sub_inv.

Lemma mergeP_same T x : mergeP x x x -> x = (@nil T).
Proof. intro mps. destruct mps. exact (merge_eqL X). Qed.

Lemma mergeP_same_eq T x : mergeP x x x <-> x = (@nil T).
Proof. split. apply mergeP_same. 
intro. subst. apply inhabits. apply merge_Lnil. Qed.

Lemma bang_sem_lem3 V sema x : x = ([] : list (LLfml V)) -> 
  dual_sem mergeP prb sema [] ->
    dual_sem mergeP prb sema x /\ mergeP x x x /\
    dual_sem mergeP prb (dual_sem mergeP prb (eq [])) x.
Proof. intros xe sip. rewrite mergeP_same_eq. subst.
pose (comm_monoid_nd_list (LLfml V)) as cm.
rewrite (dual_sem_1_eq _ cm).
split. apply sip. split. reflexivity. exact (dual_sem_bot prb cm). Qed.

Lemma bang_sem_lem'' V sema x : x = ([] : list (LLfml V)) -> 
  (forall u : list (LLfml V), (sema u : Prop) -> prb u) -> 
    dual_sem mergeP prb sema x /\ mergeP x x x /\
    dual_sem mergeP prb (dual_sem mergeP prb (eq [])) x.
Proof. intros xe sip. rewrite mergeP_same_eq. subst.
pose (comm_monoid_nd_list (LLfml V)) as cm.
rewrite (dual_sem_1_eq _ cm). rewrite (dual_sem_e prb cm).
split. apply sip. split. reflexivity. exact (dual_sem_bot prb cm). Qed.

Lemma bang_sem_lem' V A x : x = ([] : list (LLfml V)) -> 
  (forall u : list (LLfml V), sem mergeP [] prb K pr_sv A u -> prb u) -> 
    dual_sem mergeP prb (sem mergeP [] prb K pr_sv A) x /\ mergeP x x x /\
    dual_sem mergeP prb (dual_sem mergeP prb (eq [])) x.
Proof. intros xe sip. rewrite mergeP_same_eq. subst.
pose (comm_monoid_nd_list (LLfml V)) as cm.
rewrite (dual_sem_1_eq _ cm). rewrite (dual_sem_e prb cm).
split. apply sip. split. reflexivity. exact (dual_sem_bot prb cm). Qed.

Lemma bang_sem_lem V A x : (forall u : list (LLfml V),
  sem mergeP [] prb K pr_sv A u -> prb u) -> 
  comm_monoid_nd mergeP ([] : list (LLfml V)) -> x = [] -> 
    dual_sem mergeP prb (sem mergeP [] prb K pr_sv A) x /\ mergeP x x x /\
    dual_sem mergeP prb (dual_sem mergeP prb (eq [])) x.
Proof. intros sip cm xe. rewrite mergeP_same_eq. subst.
rewrite (dual_sem_1_eq _ cm). rewrite (dual_sem_e prb cm).
split. apply sip. split. reflexivity. exact (dual_sem_bot prb cm). Qed.

(* now we need to show that the semantics defined using pr_sv
  corresponds to pr_sem (at least, for completeness, one way) *)
Lemma sem_pr_tens V (sema semb : _ -> Prop) A B
  (IHAa : forall X, sema X -> pr_sem A X)
  (IHAb : forall X, semb X -> pr_sem B X) X :
  tens_sem mergeP prb sema semb X -> pr_sem (@tens V A B) X.
Proof. intros ts.
pose (tens_sem_mono_pr IHAa IHAb ts).  clearbody t.
revert t.  unfold tens_sem.  apply ds_ds_fact_pr.
intros u p12.  destruct p12.
destruct H.  destruct H0.  destruct H1. apply inhabits.
unfold pr_sem in *.
eapply derI. apply tens_maellI.  eapply merge_ctxtgI. eapply eq_rect.
eapply (@merge_ctxtI _ _ _ _ [] [] x y). apply Tensrule_I.
apply merge_nil. apply H.  reflexivity. 
exact (dlCons X0 (dersrec_singleI X1)). Qed.

Lemma spp_lem V A v w : pr_sem A v -> mergeP [A] v w -> @prb V w.
Proof.  unfold pr_sem.  unfold prb.
intros dav me. destruct dav. destruct me. apply inhabits.
apply merge_singleL in H. cD. subst.
apply (exch_maell X). swap_tac_Rc. Qed.

Lemma pr_sem_prb V A w : pr_sem A w <-> @prb V (A :: w).
Proof. reflexivity. Qed.

Lemma sem_pr_par V (sema semb : _ -> Prop) A B
  (IHAa : forall X, sema X -> pr_sem A X)
  (IHAb : forall X, semb X -> pr_sem B X) X :
  par_sem mergeP prb sema semb X -> pr_sem (@par V A B) X.
Proof. intro pab.  pose (par_sem_mono_pr IHAa IHAb pab).
unfold par_sem in p.  unfold tens_sem in p.
rewrite -> ddd_iff_pr in p.
clear IHAa IHAb pab.
unfold dual_sem in p.  unfold lolli_sem in p.
specialize (p [A ; B] ([A ; B] ++ X)).
require p.  eapply prodI.  apply spp_lem.  apply spp_lem.
apply inhabits.  apply merge_simple_app.
require p.  apply inhabits.  apply merge_simple_appr.
unfold prb in p. unfold pr_sem. destruct p. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Par_p.  eapply Parrule_I. reflexivity. reflexivity.
exact (dersrec_singleI X0). Qed.

Lemma sem_pr_bang V (sema : _ -> Prop) A
  (IHA : forall X, sema X -> pr_sem A X) X :
  bang_sem mergeP prb K sema X -> pr_sem (@Bang V A) X.
Proof. apply ds_ds_fact_pr.
intros u si. destruct si. specialize (IHA _ H).
destruct H0. destruct IHA. apply inhabits.
eapply derI.  eapply bang_maellI. eapply (fmlsrulegq_I _ _ []).
eapply Bangrule_I. reflexivity. reflexivity. reflexivity. reflexivity.
exact (dersrec_singleI X0). Qed.

Lemma pr_sem_query V A u : pr_sem A u -> pr_sem (@Query V A) u.
Proof. unfold pr_sem. intro ia. destruct ia. apply inhabits.
eapply derI.  eapply query_maellI.  eapply (OSgctxt_eq _ _ _ []).
eapply Queryrule_I. reflexivity. reflexivity.
exact (dersrec_singleI X). Qed.

Definition dsol W bot := dual_sem_or bot (comm_monoid_nd_list W).
Definition dsaol W bot := @dsao _ _ _ bot (comm_monoid_nd_list W).

(* this is a sort of monotonicity of query *)
Lemma sem_pr_query V (sema : _ -> Prop) A 
  (IHA : forall X, sema X -> pr_sem A X) X :
  query_sem mergeP prb K sema X -> pr_sem (@Query V A) X.
Proof. intro ddi.  unfold query_sem in ddi.
apply dsaol in ddi.  apply fact_pr_sem.
revert X ddi. intro. apply dd_mono. intros u sds. destruct sds.
specialize (IHA u H). exact (pr_sem_query IHA).

apply (H [Query A] _ (K_I [A])).
apply inhabits.  apply merge_simple_appr.
apply fact_K.  Qed.

(*
Print Implicit lolli_sem_mono.
Print Implicit dual_sem_or.
Print Implicit dd_mono.
Print Implicit dd_mono_pr.
Print Implicit dual_anti.
Print Implicit dual_anti_pr.
Print Implicit fact_pr_sv.
Print Implicit dual_sem_1_eq.
Print Implicit ds_ds_fact_pr.
Print Implicit fact_pr_sem.
Print Implicit fact_dd_eq.
Print Implicit fact_dd_eq_pr.
Print Implicit comm_monoid_nd_list.
Print Implicit par_sem_mono.
Print Implicit par_sem_mono_pr.
Check (ds_ds_fact (comm_monoid_nd_list _)).
Check (fact_dd_eq_pr (@fact_pr_sem _ _)).
Print Implicit dd_pr_sem_eq.
Print Implicit prodI.
Print Implicit dual_sub_inv_pr.
*)

(* completeness re this particular semantics *)
Lemma sem_pr V A X : sem mergeP [] prb K pr_sv A X -> @pr_sem V A X.
Proof. revert X. induction A ; simpl.
- unfold pr_sv. unfold pr_sem. tauto.
- unfold dual_sem. unfold pr_sem. unfold lolli_sem.
unfold pr_sv. unfold prb. intros.
specialize (H [DVar v]). apply H.
2: apply inhabits. 2: apply merge_simple_appr.
apply inhabits. pose (maell_id (Var v)).  simpl in d. exact d.
- unfold prb. unfold pr_sem.
intro. apply inhabited_ind.  intro. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Bot_p.  eapply Botrule_I. reflexivity. reflexivity.
apply dersrec_singleI. exact X0.
- unfold pr_sem. intros. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Top_p.  eapply Toprule_I. reflexivity. reflexivity. apply dlNil.
- rewrite (dual_sem_1_eq (@prb V) (comm_monoid_nd_list _)).
unfold pr_sem. unfold dual_sem. unfold lolli_sem.
intros X pmb. specialize (pmb [One V] (One V :: X)).
unfold prb in pmb. apply pmb.
2: apply inhabits. 2: apply merge_simple_appr.
apply inhabits. eapply derI. apply one_maellI. apply Onerule_I. apply dlNil.
- intros X dde. unfold dual_sem in dde. unfold lolli_sem in dde.
unfold pr_sem. unfold prb in dde. apply (dde [Zero V]).
2: apply inhabits. 2: apply merge_simple_appr. tauto.

- (* tens *) apply sem_pr_tens ; assumption.

- (* wth *) intros X sw. 
specialize (IHA1 _ (proj1 sw)).  specialize (IHA2 _ (proj2 sw)).
clear sw. unfold pr_sem in *.
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

Print Implicit dual_sem_bot.
Print Implicit dual_sem_1_eq.
Print Implicit comm_monoid_nd_list.

(* from here to completeness: and to cut-admissibility
Check sem_pr.
(* cut_sound - assume first tens rule is applied *)
Check cut_sound.
Check maell_sound. (* not yet proved *)
*)
