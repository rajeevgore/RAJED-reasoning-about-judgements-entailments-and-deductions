
(* try non-adjacent move of a single formula,
  for system with princrule and seqrule *)

(* 
coqc gen.v
coqc dd.v
coqc List_lemmas.v
coqc lnt.v
*)

Require Import ssreflect.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.

Ltac list_eq_nc := 
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_single in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.

Ltac sD_list_eq := repeat (cD' || list_eq_nc || sDx).

Ltac assoc_mid l := 
  list_assoc_r ;
  rewrite ?app_comm_cons ;
  repeat ((rewrite <- (app_assoc _ l _) ; fail 1) || rewrite app_assoc) ;
  rewrite <- (app_assoc _ l _).

Definition app_assoc_cons A l m (x : A) xs := app_assoc l m (x :: xs).

(* in ssreflect *)
Ltac list_assoc_l' := repeat (rewrite !app_assoc || rewrite !app_comm_cons).
Ltac list_assoc_r' :=
  repeat (rewrite - !app_assoc || rewrite - !app_comm_cons).

Ltac assoc_single_mid :=
  list_assoc_r' ; 
  rewrite ?app_assoc_cons.

(* test of assoc_mid
Lemma x : forall T (a b c d e f g : list T) (x y z : T),
  a ++ x :: b ++ c ++ y :: d ++ e ++ z :: f = g.
intros.
assoc_mid b. (* doesn't work *)
assoc_mid c.
assoc_mid d. (* doesn't work *)
assoc_mid e.
*)

Ltac use_prL pr := 
  pose pr as Qpr ;
  apply princrule_L in Qpr ;
  sD_list_eq ;
  subst ;
  simpl ;
  simpl in pr ;
  rewrite -> ?app_nil_r in * ;
  rewrite ?app_nil_r.

Lemma all_eq_imp: forall (T : Type) (y : T) (z : T -> Prop),
(forall (x : T), y = x \/ False -> z x) <-> z y.
Proof. firstorder. subst.  assumption. Qed.

Definition can_gen_moveL {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ1 Γ2 Γ3 (Q : PropF V) Δ,
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ Q :: Γ2 ++ Γ3) Δ ->
  derrec rules (fun _ => False) 
    (G ++ (pair (Γ1 ++ Γ2 ++ Q :: Γ3) Δ, d) :: H).

Ltac use_cgmL H1 := 
  rewrite -> Forall_forall in H1 ;
  simpl in H1 ;
  specialize_full H1 ;
  [ | unfold can_gen_moveL in H1 ; unfold nsext ;
    rewrite <- app_assoc ;
    eapply H1 ; reflexivity ] ;
  unfold nsext ; tauto.

Ltac stage1 pr := 
subst ;
rewrite -> ?app_nil_r in * ;
eapply derI ; [
rewrite <- nsext_def ; apply NSctxt ;
eapply Sctxt in pr ;
unfold seqext in pr ;
simpl in pr | idtac ].

Ltac stage2 H1 qin1 qin3 := 
rewrite dersrec_forall ;
intros q qin ; rewrite -> in_map_iff in qin ; cD ;
rename_last qin1 ;
rewrite -> in_map_iff in qin1 ; cD ;
rename_last qin3 ;
destruct qin1 ; subst ;
rewrite -> Forall_forall in H1 ;
eapply in_map in qin3 ;
eapply in_map in qin3 ;
apply H1 in qin3 ;
unfold can_gen_moveL in qin3 ;
unfold nsext.

Ltac stage3 qin3 l l1 := 
eapply qin3 ; [ apply nsext_def |
rewrite seqext_def ; list_eq_assoc ].

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

rewrite dersrec_forall.
intros q qin.  subst pse.  rewrite -> in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite -> Forall_forall in H1.
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

rewrite dersrec_forall.
intros q qin.  subst pse.  rewrite -> in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite -> Forall_forall in H1.
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

{
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
}

(* sg 2 of 10 *)
all: cycle 1.
all: cycle 1.

(* sg 4 of 10 *)

(* problem here, Q between sel3 and sel5,
  but one of sel3 and sel5 must be empty due to princrule_L *)

{
pose pr as pr'.
apply princrule_L in pr'.
sD ; subst.
apply app_eq_nil in pr'. cD. subst.
simpl in pr.
simpl.
rewrite app_nil_r.

{
stage1 pr. (* will need to move Q around sel1 *)

rewrite app_assoc.
rewrite list_rearr16.
apply pr.
stage2 H1 qin1 qin3.
rewrite <- app_assoc.
simpl.
rewrite <- app_assoc.
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.
}

apply app_eq_unit in pr'0.
sD ; subst.
{
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
}

{
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
}
}
 
{
stage1 pr.
(* need to rearrange appends to get ... ++ l ++ ... *)
assoc_mid l.
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
}

{
stage1 pr.
(* just need to get l in the middle *)
assoc_mid l.
apply pr.
stage2 H1 qin1 qin3.
(*
specialize_full qin3.
apply nsext_def.
unfold seqext.
all : cycle 1.
eapply derrec_same.
exact qin3.  
f_equal.  f_equal.
all : repeat (apply pair_eqI).
all : try reflexivity.
all : assoc_single_mid.
2: reflexivity.
list_eq_assoc.
but our reasoning more generally would depend on recognising single variables
*)

repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons).
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.
}

{
stage1 pr.
rewrite <- !app_assoc.
apply pr.
stage2 H1 qin1 qin3.
rewrite app_assoc.
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.
}

(* subgoal has Q (formula to be moved) in principal formula *)
all: cycle 1.
all: cycle 1.

{
stage1 pr.
rewrite <- !app_assoc.
apply pr.
stage2 H1 qin1 qin3.
rewrite !app_assoc.
rewrite <- (app_assoc _ Γ2).
eapply qin3.  apply nsext_def.  unfold seqext.  list_eq_assoc.
}

(* four remaining subgoals have Q (formula to be moved) in principal formula *)
- {
subst. use_prL pr. stage1 pr. rewrite app_assoc. apply pr.
destruct pr ; simpl ; repeat (apply dlNil || apply dlCons).
use_cgmL H1. use_cgmL H1.
rewrite -> dersrec_forall in H0. apply H0. simpl. rewrite <- app_assoc. tauto.
}

- { subst. use_prL pr. stage1 pr. apply pr. unfold seqext in H0. exact H0.  }

- {
subst. use_prL pr. stage1 pr. rewrite app_assoc. apply pr.
destruct pr ; simpl ; repeat (apply dlNil || apply dlCons).
use_cgmL H1. use_cgmL H1.
rewrite -> dersrec_forall in H0. apply H0. simpl. rewrite <- app_assoc. tauto.
}

- { subst. use_prL pr. stage1 pr. apply pr. unfold seqext in H0. exact H0.  }

Qed.

Check gen_moveL.







