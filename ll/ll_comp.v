
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

(* call this the provability semantics *)

Definition pr_sem V A G := inhabited (derrec (@maell_rules V) emptyT (A :: G)).
Definition pr_seml V As G := 
  inhabited (derrec (@maell_rules V) emptyT (As ++ G)).
Definition pr_sv {V} v G := 
  inhabited (derrec maell_rules emptyT (@Var V v :: G)).
Definition prb {V} G := inhabited (derrec (@maell_rules V) emptyT G).

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

Lemma fact_pr_sv V v : fact mergeP prb (@pr_sv V v).
Proof. apply fact_pr_sem. Qed.

(*
Lemma pr_sem_tens V A B G : 
  (tens_sem (@app _) csb (pr_sem A) (pr_sem B)) G -> pr_sem (@tens V A B) G.
Proof. unfold tens_sem. unfold pr_sem.
*)

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

Print Implicit dual_sem_1_eq.

(* now we need to show that the semantics defined using pr_sv
  corresponds to pr_sem (at least, for completeness, one way) *)
(*
Lemma sem_pr V A X : sem mergeP [] prb pr_sv A X -> @pr_sem V A X.
Proof. induction A ; simpl.
- unfold pr_sv. unfold pr_sem. tauto.
- unfold dual_sem. unfold pr_sem. unfold lolli_sem.
unfold pr_sv. unfold prb. intro.
specialize (H [DVar v]). apply H.
2: apply inhabits. 2: apply merge_simple_appr.
apply inhabits. pose (maell_id (Var v)).  simpl in d. exact d.
- unfold prb. unfold pr_sem. apply inhabited_ind. intro. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Bot_p.  eapply Botrule_I. reflexivity. reflexivity.
apply dersrec_singleI. exact X0.
- unfold pr_sem. intro. apply inhabits.
eapply derI.  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []).
apply Top_p.  eapply Toprule_I. reflexivity. reflexivity. apply dlNil.
- rewrite (dual_sem_1_eq (@prb V) (comm_monoid_nd_list _)).
unfold pr_sem. unfold dual_sem. unfold lolli_sem.
intro pmb. specialize (pmb [One V] (One V :: X)).
unfold prb in pmb. apply pmb.
2: apply inhabits. 2: apply merge_simple_appr.
apply inhabits. eapply derI. apply one_maellI. apply Onerule_I. apply dlNil.
- intro dde. unfold dual_sem in dde. unfold lolli_sem in dde.
unfold pr_sem. unfold prb in dde. apply (dde [Zero V]).
2: apply inhabits. 2: apply merge_simple_appr. tauto.
- TBC
*)



