
(* try non-adjacent exchange, for system with princrule and seqrule *)

Require Import dd.
Require Import lnt.
Require Import List_lemmas.

Definition can_gen_exchL {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ1 Γ2 Γ3 (A B : PropF V) Δ,
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ A :: Γ2 ++ B :: Γ3) Δ ->
  derrec rules (fun _ => False) 
    (G ++ (pair (Γ1 ++ B :: Γ2 ++ A :: Γ3) Δ, d) :: H).

Ltac stage1 pr := 
subst ;
rewrite ?app_nil_r in * ;
eapply derI ; [
rewrite <- nsext_def ; apply NSctxt ;
eapply Sctxt in pr ;
unfold seqext in pr ;
simpl in pr | idtac ].

Ltac stage2 H1 qin1 qin3 := 
rewrite dersrec_all ;  rewrite Forall_forall ;
intros q qin ; rewrite in_map_iff in qin ; cD ;
rename_last qin1 ;
rewrite in_map_iff in qin1 ; cD ;
rename_last qin3 ;
destruct qin1 ; subst ;
rewrite Forall_forall in H1 ;
eapply in_map in qin3 ;
eapply in_map in qin3 ;
apply H1 in qin3 ;
unfold can_gen_exchL in qin3 ;
unfold nsext.

Ltac stage3 qin3 l l1 := 
eapply qin3 ; [ apply nsext_def |
rewrite seqext_def ; [ list_eq_assoc | apply (l,l1) ] ].

Lemma gen_exchL: forall (V : Set) ns
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_exchL (nsrule (seqrule (@princrule V))) ns.

Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.  unfold nsext in H5.
unfold can_gen_exchL.  intros.
unfold nsext in H7.
(* cases of where the exchange occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ1 ++ B :: Γ2 ++ A :: Γ3, Δ) as seqe.

decompose [or] H7. clear H7.  cE.
(* case where the rule is applied in a sequent to the right
  of where the exchange takes place *)
remember (G0 ++ (seqe, d0) :: x) as Ge.
remember (map (nsext Ge H2 d) ps0) as pse.

apply derI with pse. subst pse. subst H6.
rewrite list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqGe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_gen_exchL in c0.
unfold nsext. subst Ge. subst seqe.
rewrite <- list_rearr14.
eapply c0. 2:reflexivity.
unfold nsext. subst G. subst seq.
list_eq_assoc.

all : revgoals. clear H7. cE.
(* now the case where the rule is applied in a sequent to the left
  of where the exchange takes place *)
remember (x ++ (seqe, d0) :: H6) as He.
remember (map (nsext G He d) ps0) as pse.

apply derI with pse. subst pse. subst G0.
rewrite <- list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqHe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchL in c0.
unfold nsext. subst He. subst seqe.
rewrite list_rearr14.

eapply c0. 2:reflexivity.
unfold nsext. subst H2. subst seq.
apply list_rearr14.

(* now case where exchange and rule application occur in the same sequent *)
cE. clear H7. injection H10 as.
inversion H3 as [? ? ? ? ? ? pr mse se].
unfold seqext in se.
subst.  clear H. clear H3.
destruct c0. unfold seqext in se.
injection se as sel ser.
subst.
(* do as much as possible for all rules at once *)
acacD'. (* gives 15 subgoals *)

(* sg 1 of 15 *)
stage1 pr.

apply pr. (* solves one sg *)

stage2 H1 qin1 qin3.
rewrite (app_assoc Γ1). (* need to do this more generally *)
stage3 qin3 l l1.

(* sg 2-4 of 15 *)
(* A is principal formula *)
all: cycle 1.
all: cycle 1.
all: cycle 1.

(* sg 5 of 15 *)
stage1 pr.

(* need to get Φ1 ++ sel3 ++ Φ2 *)
repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
repeat (apply pr || rewrite list_rearr16 || rewrite list_rearr15).

stage2 H1 qin1 qin3.

rewrite <- !app_assoc. (* need to do this more generally *)
simpl.
rewrite app_assoc.
stage3 qin3 l l1.

(* B is principal formula *)
all: cycle 1.

(* sg 7 of 15 *)
stage1 pr.

(* need to get Φ1 ++ sel3 ++ Φ2 *)
repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
repeat (apply pr || rewrite list_rearr16 || rewrite list_rearr15).

stage2 H1 qin1 qin3.

rewrite <- !app_assoc. (* need to do this more generally *)
simpl.
rewrite app_assoc.
rewrite app_assoc.
stage3 qin3 l l1.

(* sg 8 of 15 *)
(* l = [] *)
stage1 pr.

rewrite app_comm_cons.
rewrite app_assoc.
apply pr.

stage2 H1 qin1 qin3.

rewrite <- !app_assoc. (* need to do this more generally *)
rewrite <- !app_comm_cons. (* need to do this more generally *)
rewrite app_assoc.
stage3 qin3 l l1.

(* B principal formula *)
all: cycle 1.

(* sg 10 of 15 *)
stage1 pr.

repeat (rewrite !app_assoc || rewrite !app_comm_cons).

rewrite <- (app_assoc _ l). (* need to do this more generally *)
rewrite <- (app_assoc _ l0). (* need to do this more generally *)
apply pr. 

stage2 H1 qin1 qin3.

rewrite <- !app_assoc. (* need to do this more generally *)
rewrite <- !app_comm_cons. (* need to do this more generally *)
stage3 qin3 l l1.

(* sg 11 of 15 *)
stage1 pr.

rewrite <- !app_assoc. (* need to do this more generally *)
apply pr. 

stage2 H1 qin1 qin3.

rewrite (app_assoc _ l). (* need to do this more generally *)
stage3 qin3 l l1.

(* A in principal formula *)
all: cycle 1.
all: cycle 1.
all: cycle 1.

(* sg 15 of 15 *)
subst.
rewrite ?app_nil_r in *.
eapply derI.
rewrite <- nsext_def. apply NSctxt.

eapply Sctxt in pr.
unfold seqext in pr.
simpl in pr.

rewrite <- !app_assoc. (* need to do this more generally *)
apply pr. 

stage2 H1 qin1 qin3.

rewrite !app_assoc. (* need to do this more generally *)
rewrite  <- (app_assoc _ l1). (* need to do this more generally *)
stage3 qin3 l l1.

(* now the cases where the principal formula contains A or B *)
all: apply princrule_L in pr.

sE.
subst.
discriminate.
subst.
injection sel3 as.
subst.
simpl.
rewrite ?app_nil_r in *.



