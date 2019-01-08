
(* try non-adjacent move of a single formula,
  for system with princrule and seqrule *)

Require Import gen.
Require Import dd.
Require Import lnt.
Require Import List_lemmas.

Definition can_gen_moveL {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ1 Γ2 Γ3 (Q : PropF V) Δ,
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ Q :: Γ2 ++ Γ3) Δ ->
  derrec rules (fun _ => False) 
    (G ++ (pair (Γ1 ++ Γ2 ++ Q :: Γ3) Δ, d) :: H).

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
unfold can_gen_moveL in qin3 ;
unfold nsext.

Ltac stage3 qin3 l l1 := 
eapply qin3 ; [ apply nsext_def |
rewrite seqext_def ; [ list_eq_assoc | apply (l,l1) ] ].

Lemma gen_moveL: forall (V : Set) ns
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_moveL (nsrule (seqrule (@princrule V))) ns.

Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.  unfold nsext in H5.
unfold can_gen_moveL.  intros.
unfold nsext in H7.
(* cases of where the move occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ1 ++ Γ2 ++ Q :: Γ3, Δ) as seqe.

decompose [or] H7. clear H7.  cE.
(* case where the rule is applied in a sequent to the right
  of where the move takes place *)
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
unfold can_gen_moveL in c0.
unfold nsext. subst Ge. subst seqe.
rewrite <- list_rearr14.
eapply c0. 2:reflexivity.
unfold nsext. subst G. subst seq.
list_eq_assoc.

all : revgoals. clear H7. cE.
(* now the case where the rule is applied in a sequent to the left
  of where the move takes place *)
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
unfold can_gen_moveL in c0.
unfold nsext. subst He. subst seqe.
rewrite list_rearr14.

eapply c0. 2:reflexivity.
unfold nsext. subst H2. subst seq.
apply list_rearr14.

(* now case where move and rule application occur in the same sequent *)
cE. clear H7. injection H10 as.
inversion H3 as [? ? ? ? ? ? pr mse se].
unfold seqext in se.
subst.  clear H. clear H3.
destruct c0. unfold seqext in se.
injection se as sel ser.
subst.
(* do as much as possible for all rules at once *)
acacD'. (* gives 10 subgoals *)

(* sg 1 of 10 *)
stage1 pr.
(* normally need to rearrange *)
apply pr. (* solves one sg *)

stage2 H1 qin1 qin3.
eapply derrec_same.
eapply qin3.
apply nsext_def.
unfold seqext.
f_equal.
apply app_assoc. (* need to generalise this *)
list_eq_assoc.

(* sg 2 of 10 *)
all: cycle 1.
all: cycle 1.

(* sg 4 of 10 *)

(* problem here, Q between sel3 and sel5,
  but one of sel3 and sel5 must be empty due to princrule_L *)

pose pr as pr'.
apply princrule_L in pr'.
sD ; subst.
apply app_eq_nil in pr'. cD. subst.
simpl in pr.
simpl.
rewrite app_nil_r.

stage1 pr. (* will need to move Q around sel1 *)

rewrite app_assoc.
rewrite list_rearr16.
apply pr.
stage2 H1 qin1 qin3.
rewrite <- app_assoc.
simpl.
rewrite <- app_assoc.
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.

apply app_eq_unit in pr'0.
sD ; subst.
simpl in pr. simpl.
rewrite app_nil_r.
stage1 pr. (* will need to move Q around sel1 *)
rewrite app_assoc.
rewrite list_rearr16.
apply pr.
stage2 H1 qin1 qin3.
rewrite <- app_assoc.
simpl.
rewrite <- app_assoc.
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.

rewrite app_nil_r in pr.
simpl.
stage1 pr.
rewrite <- app_assoc.
simpl.
rewrite app_assoc.
apply pr.
stage2 H1 qin1 qin3.
rewrite <- app_assoc.
rewrite (app_assoc _ l).
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.
 
stage1 pr.
(* need to rearrange appends to get ... ++ l ++ ... *)
rewrite <- !app_assoc.
rewrite app_assoc.
apply pr.
stage2 H1 qin1 qin3.
(*
pose (qin3 G H6 _ _ Γ1 (sel1 ++ l1 ++ sel5)).
*)
(*
eapply derrec_same.
eapply qin3.
apply nsext_def.
unfold seqext.
the above would work if we could rewrite without instantiating *)
assert ((Γ1 ++ sel1) ++ l1 ++ sel5 ++ Q :: Γ3 = 
  Γ1 ++ (sel1 ++ l1 ++ sel5) ++ Q :: Γ3).
list_eq_assoc.
rewrite H.
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.

stage1 pr.
(* just need to get l in the middle *)
rewrite app_assoc.
rewrite app_comm_cons.
rewrite app_assoc.
apply pr.
stage2 H1 qin1 qin3.
repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons).
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.

stage1 pr.
rewrite <- !app_assoc.
apply pr.
stage2 H1 qin1 qin3.
rewrite app_assoc.
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.

(* subgoal has Q (formula to be moved) in principal formula *)
all: cycle 1.
all: cycle 1.

stage1 pr.
rewrite <- !app_assoc.
apply pr.
stage2 H1 qin1 qin3.
rewrite !app_assoc.
(* why doesn't this work?
rewrite app_assoc in qin3. *)
rewrite <- (app_assoc _ Γ2).
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.

(* four remaining subgoals have Q (formula to be moved) in principal formula *)

pose pr as Qpr.
apply princrule_L in Qpr.
sD.
subst.
discriminate.
subst.
injection Qpr0 as.
subst.
simpl.
rewrite ?app_nil_r in *.

stage1 pr.
rewrite app_assoc.
apply pr.
(* doesn't work, need to use the ps1 in the goal here is that
  given by princrule ps1 ([Qpr], l0)
stage2 H1 qin1 qin3. *)
destruct pr. (* case pr. or elim pr. don't put value of ps1 into premises *)
simpl.
intros.
rewrite dersrec_all.
apply Forall_nil.
simpl.
intros.
rewrite dersrec_all.
rewrite Forall_forall.
intros.
apply in_inv in H.
sD.
subst.

rewrite Forall_forall in H1 ;
simpl in H1.
rewrite or_false in H1.

Lemma all_eq_imp: forall (T : Type) (y : T) (z : T -> Prop),
  (forall (x : T), y = x \/ False -> z x) <-> z y.
Proof. firstorder. subst.  assumption. Qed.

eapply in_inv in H1.

eapply in_map in qin3 ;
eapply in_map in qin3 ;
apply H1 in qin3 ;
unfold can_gen_moveL in qin3 ;
unfold nsext.




