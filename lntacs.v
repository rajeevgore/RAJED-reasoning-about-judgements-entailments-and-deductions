
(* tactics etc for lntom *)

Require Import ssreflect.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.

Lemma midI: forall T (a b c d : list T) x,
  a = c -> b = d -> a ++ x :: b = c ++ x :: d.
Proof. intros. subst. reflexivity. Qed.

Lemma appI: forall T (a b c d : list T),
  a = b -> c = d -> a ++ c = b ++ d.
Proof. intros. subst. reflexivity. Qed.

Lemma apprI: forall T (a b c : list T),
  a = b -> a ++ c = b ++ c.
Proof. intros. subst. reflexivity. Qed.

Lemma if_eq_rev_eq: forall {T} (a b : list T),
  a = b -> (rev a = rev b).
Proof. intros. subst. reflexivity. Qed.

Lemma if_rev_eq: forall {T} (a b : list T),
  (rev a = rev b) -> a = b.
Proof. intros. 
pose (if_eq_rev_eq (rev a) (rev b) H).
rewrite -> !rev_involutive in e.
exact e.
Qed.

Lemma appl_cong: forall {T} (a b c : list T),
  (c ++ a = c ++ b) <-> (a = b).
Proof.  intros. unfold iff. apply conj ; intro.  
  induction c. simpl in H. exact H.
  simpl in H. inversion H. tauto.
  intros. subst. reflexivity. Qed.

Lemma appr_cong: forall {T} (a b c : list T),
  (a ++ c = b ++ c) <-> (a = b).
Proof.  intros. unfold iff. apply conj ; intro.  
pose (if_eq_rev_eq (a ++ c) (b ++ c) H).
rewrite -> !rev_app_distr in e.
rewrite -> appl_cong in e.
apply if_rev_eq in e.  exact e.
subst. reflexivity.  Qed.

Lemma app_eq_nil_iff: forall {A} (l l' : list A), 
  l ++ l' = [] <-> l = [] /\ l' = [].
Proof. intros. unfold iff. split ; intros.
  destruct l ; simpl in H ; [ tauto | discriminate]. 
  destruct H. subst. simpl. tauto. Qed.

Lemma applI: forall {T} (a b c : list T),
  a = b -> c ++ a = c ++ b.
Proof. intros. subst. reflexivity. Qed.

Ltac list_eq_nc := 
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
     | [ H : _ ++ _ = [_] |- _ ] => apply app_eq_unit in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_single in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.

Ltac sD_list_eq := repeat (cD' || list_eq_nc || sDx).

Definition app_assoc_cons A l m (x : A) xs := app_assoc l m (x :: xs).

(* in ssreflect *)
Ltac list_assoc_l' := repeat (rewrite !app_assoc || rewrite !app_comm_cons).
Ltac list_assoc_r' :=
  repeat (rewrite - !app_assoc || rewrite - !app_comm_cons).

Ltac assoc_mid l := 
  list_assoc_r' ;
  rewrite ?app_comm_cons ;
  repeat ((rewrite - (app_assoc _ l _) ; fail 1) || rewrite app_assoc) ;
  rewrite - (app_assoc _ l _).

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

Ltac use_prX princrule_X pr := 
  pose pr as Qpr ;
  apply princrule_X in Qpr ;
  repeat (sD_list_eq ; subst ; simpl ; simpl in pr ;
  rewrite -> ?app_nil_r in * ; rewrite ?app_nil_r).

Ltac use_prL pr := use_prX princrule_L pr.
Ltac use_prR pr := use_prX princrule_R pr.

Ltac check_app_app :=
  match goal with
    | [ |- _ ++ _ = _ ++ _ ] => idtac
    end.

Lemma nsI: forall T (G H : list T) (x y : T),
  x = y -> G ++ x :: H = G ++ y :: H.
Proof. intros. subst. reflexivity. Qed.

Lemma all_eq_imp: forall (T : Type) (y : T) (z : T -> Prop),
(forall (x : T), y = x \/ False -> z x) <-> z y.
Proof. firstorder. subst.  assumption. Qed.

Definition can_gen_moveL {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ1 Γ2 Γ3 (Q : PropF V) Δ,
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ Q :: Γ2 ++ Γ3) Δ ->
  derrec rules (fun _ => False) 
    (G ++ (pair (Γ1 ++ Γ2 ++ Q :: Γ3) Δ, d) :: H).

Definition can_gen_moveR {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Δ1 Δ2 Δ3 (Q : PropF V) Γ,
  ns = G ++ (seq, d) :: H -> seq = pair Γ (Δ1 ++ Q :: Δ2 ++ Δ3) ->
  derrec rules (fun _ => False) 
    (G ++ (pair Γ (Δ1 ++ Δ2 ++ Q :: Δ3), d) :: H).

Ltac use_cgm cgmX H1 := 
  rewrite -> Forall_forall in H1 ;
  simpl in H1 ;
  specialize_full H1 ;
  [ | unfold cgmX in H1 ; unfold nsext ;
    rewrite <- app_assoc ;
    eapply H1 ; reflexivity ] ;
  unfold nsext ; tauto.

Ltac use_cgmL H1 := use_cgm can_gen_moveL H1.
Ltac use_cgmR H1 := use_cgm can_gen_moveR H1.

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

Ltac stage2ds H1 qin1 qin3 := 
  stage2 H1 qin1 qin3 ; eapply derrec_same ; [
    eapply qin3 ; [ apply nsext_def | unfold seqext ] | ].

Ltac srs pr := eapply seqrule_same ; [ exact pr |
  apply pair_eqI ; try reflexivity ]. 

Ltac amt l0 := eapply eq_trans ; [> assoc_mid l0 .. ] ; [> reflexivity ..].
  
Ltac stage12ds H1 qin1 qin3 pr l0 := 
  stage1 pr ; [ srs pr ; amt l0 | stage2ds H1 qin1 qin3 ].

Ltac app_cancel := 
  (list_assoc_l' ; rewrite ?appr_cong ;
  list_assoc_r' ; rewrite ?appl_cong).

Ltac solve_eqs := 
  prgt 33 ;
  repeat clear_one ;
  try (apply nsI) ;
  repeat (apply pair_eqI) ;
  try refl_ni ;
  assoc_single_mid ;
  try (apply midI) ;
  try (first [check_app_app | reflexivity]) ;
  repeat app_cancel ;
  try (first [check_app_app | reflexivity]) ;
  try refl_ni ;
  prgt 44.

(* tactic for when principal formula to be moved *)
Ltac mpv use_prL use_cgmL H1 H0 pr := 
  subst ; use_prL pr ; stage1 pr ; [ 
  rewrite !app_assoc ; rewrite !app_assoc in pr ; apply pr |
  destruct pr ; simpl ; repeat (apply dlNil || apply dlCons) ;
  try (use_cgmL H1) ;
  rewrite -> dersrec_forall in H0 ; apply H0 ; simpl ;
  rewrite <- app_assoc ;  tauto ].

