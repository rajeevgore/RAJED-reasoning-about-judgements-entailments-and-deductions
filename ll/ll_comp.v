
(* completeness of linear logic calculus using phase semantics *)

Set Implicit Arguments.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT swappedT.
Require Import fmlsext lldefs ll_exch ll_camq ll_sem.

From Coq Require Import ssreflect.

(* the monoid used for completeness, lists of formulae *)

Definition FLM {V} := list (LLfml V).
(* m is app, e is [] *)
(*
Print Implicit comm_monoid.
Print Implicit app.
Print Implicit nil.
Print Implicit tens_sem.
Print tens_sem.
Print Implicit pr_sem.
Print Implicit dual_sem.
Print Implicit prb.
Print Implicit sem.
Print Implicit fact.
*)

(* problem, lists do not form a comm_monoid,
  need to use equivalence classes - at deductive or semantic level? 
Lemma comm_monoid_list X : comm_monoid (@app X) [].
*)

(* the Girard paper defines the set of members of the monoid 
  corresponding to a formula in terms of provability, which makes
  the completeness argument easy, but you need to show that this
  definition is consistent with the definitions of the semantic operations
  (corresponding to the formula connectives) *)

(* call this the provability semantics *)

Definition pr_sem V A G := inhabited (derrec (@maell_rules V) emptyT (A :: G)).
Definition pr_seml V As G := 
  inhabited (derrec (@maell_rules V) emptyT (As ++ G)).
Definition prb {V} G := inhabited (derrec (@maell_rules V) emptyT G).

(*
Lemma pr_sem_tens V A B G : 
  (tens_sem (@app _) csb (pr_sem A) (pr_sem B)) G -> pr_sem (@tens V A B) G.
Proof. unfold tens_sem. unfold pr_sem.
*)

(*
Lemma fact_cs V A : fact (@app _) prb (@pr_sem V A).
*)

Lemma pr_sem_dual V A G : 
  dual_sem (@app _) prb (pr_sem A) G -> pr_sem (@dual V A) G.
Proof. unfold dual_sem. unfold lolli_sem.  unfold pr_sem.
intros lav. specialize (lav [dual A]).  unfold prb in lav.
require lav. apply inhabits. apply maell_id.
destruct lav.  apply inhabits.
apply (exch_maell X). swap_tac_Rc. Qed.

(* this one requires cut rule *)
Lemma dual_pr_sem V A G : 
  pr_sem (@dual V A) G -> dual_sem (@app _) prb (pr_sem A) G.
Proof. unfold dual_sem. unfold lolli_sem.  unfold pr_sem.
intros idag v iav. unfold prb.
destruct idag.  destruct iav.  apply inhabits.
destruct (fst (cut_adm_maell_Q A X0 X)).
eapply (d _ _ _ eq_refl eq_refl). apply merge_simple_appr. Qed.





  

