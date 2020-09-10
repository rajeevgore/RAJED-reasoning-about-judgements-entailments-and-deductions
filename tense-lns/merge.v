Require Import List.
Export ListNotations.

Require Import gen_tacs lntT List_lemmasT.
Require Import existsT.
Require Import contractedT.
Require Import Coq.Classes.CRelationClasses.
Require Import structural_equivalence.

Ltac clear_useless :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         | [H : [?a] = [?a] |- _] => clear H
         | [H : ?a :: ?b = ?a :: ?b |- _] => clear H
         | [H1 : ?a, H2 : ?a |- _] => clear H2
         end.

Ltac inv_singleton :=
    repeat ( match goal with
       | [ H : ?a :: [] = ?c :: ?d |- _ ] => inversion H; subst
       | [ H : ?a :: ?b = ?c :: [] |- _ ] => inversion H; subst
       | [ H : ?a :: ?b = ?c :: ?d |- _ ] => inversion H; subst
       | [ H : ((?a,?b) = ?c) |- _ ] => inversion H; subst
       | [ H : ?c = (?a,?b) |- _ ] => inversion H; subst
             end; clear_useless).

Inductive merge {V : Set} :  (list (rel (list (PropF V)) * dir)) ->  (list (rel (list (PropF V)) * dir)) ->  (list (rel (list (PropF V)) * dir)) -> Type :=
| merge_nilL ns1 ns2 ns3 : ns1 = [] -> ns3 = ns2 -> merge ns1 ns2 ns3
| merge_nilR ns1 ns2 ns3 : ns2 = [] -> ns3 = ns1 -> merge ns1 ns2 ns3
| merge_step Γ Δ Σ Π d ns1 ns2 ns3 ns4 ns5 ns6 seq1 seq2 seq3 :
    seq1 = (Γ,Δ,d) -> seq2 = (Σ,Π,d) -> seq3 = (Γ++Σ,Δ++Π,d) ->
    merge ns1 ns2 ns3 ->
    ns4 = seq1 :: ns1 -> ns5 = seq2 :: ns2 -> ns6 = seq3 :: ns3 ->
    merge ns4 ns5 ns6.

Lemma merge_existence {V : Set} : forall n1 n2,
      struct_equiv_weak n1 n2 ->
      existsT2 n3, @merge V n1 n2 n3.
Proof.
  induction n1; intros n2  Hequiv.
  inversion Hequiv. subst. inversion H0; subst.
  simpl in *. subst. exists nil. econstructor; reflexivity.
  discriminate.
  subst. inversion H0. subst. simpl in *.
  exists ns3. econstructor 1; reflexivity.
  discriminate.

  destruct n2. exists (a :: n1). econstructor 2; reflexivity.
  destruct a as [ [Γ1 Δ1] d1].
  destruct p as [ [Γ2 Δ2] d2].
  pose proof (struct_equiv_weak_d _ _ _ _ _ _ Hequiv). subst.
  eapply struct_equiv_weak_cons in Hequiv.
  eapply IHn1 in Hequiv. destruct Hequiv as [n3 Hn3].
  exists ((Γ1 ++ Γ2, Δ1 ++ Δ2, d2) :: n3).
  econstructor 3; try reflexivity. assumption.
Qed.

Lemma merge_consL : forall {V : Set} l l2 a b c,
    @merge V (a :: l) [b] (c :: l2) ->
    l = l2.
Proof.
  intros until 0; intros Hm.
  inversion Hm; try discriminate;
    inv_singleton; try reflexivity.
  inversion X; try discriminate;
  subst; reflexivity.
Qed.  


Lemma merge_consR : forall {V : Set} l l2 a b c,
    @merge V [b] (a :: l) (c :: l2) ->
    l = l2.
Proof.
  intros until 0; intros Hm.
  inversion Hm; try discriminate;
    inv_singleton; try reflexivity.
  inversion X; try discriminate;
  subst; reflexivity.
Qed.  

Lemma merge_unique {V : Set} : forall n1 n2 n3 n4,
    struct_equiv_weak n1 n2 ->
    merge n1 n2 n3 -> @merge V n1 n2 n4 -> n3 = n4.
Proof.
  induction n1; intros n2 n3 n4 Hs Hm1 Hm2.
  inversion Hm1; subst; inversion Hm2; subst;
    try reflexivity; try discriminate.

  inversion Hm1; inversion Hm2; subst; try discriminate; try reflexivity;
    inv_singleton; try reflexivity.

  all : try solve [inversion X; subst; try reflexivity; try discriminate].

  eapply IHn1 in X; [ | | exact X0].
  subst. reflexivity.
  eapply struct_equiv_weak_cons. exact Hs.
Qed.

Lemma merge_struct_equiv_weak : forall {V : Set} G1 G2 G3,
  merge G1 G2 G3 ->
  @struct_equiv_weak V G1 G2.
Proof.
  induction G1; intros G2 G3 H.
  + inversion H; try discriminate.
    econstructor 2. erewrite app_nil_l. reflexivity. econstructor.
    econstructor 2. erewrite app_nil_l. reflexivity. econstructor.    
  + inversion H; try discriminate.
  -{ inversion H0.
     subst. econstructor 1.
     erewrite app_nil_l. reflexivity.    
     econstructor.
   }
  -{ subst. inv_singleton.
     eapply struct_equiv_weak_cons_rev.
     eapply IHG1. eassumption.
   }
Qed.

Lemma merge_nil : forall {V : Set} ns,
    @merge V [] [] ns -> ns = [].
Proof.
  induction ns; intros Hm. auto.
  inversion Hm; try discriminate.
Qed.

Lemma merge_ex_str : forall {V : Set} G1 G2,
    struct_equiv_str G1 G2 -> existsT2 G3, @merge V G1 G2 G3.
Proof.
  induction G1; intros G2 Hs.
  inversion Hs. exists []. constructor; reflexivity.
  discriminate.
  inversion Hs; try discriminate.
  inv_singleton. eapply IHG1 in H1.
  destruct H1 as [G3 H1].
  eexists ( (Γ1 ++ Γ2, Δ1 ++ Δ2, d) :: G3).
  econstructor 3; try reflexivity. assumption.
Qed.

Lemma merge_appLR : forall {V : Set} G1 G2 G3 G,
    merge G1 G2 G3 ->
    length G1 = length G2 ->
    @merge V (G1 ++ G) G2 (G3 ++ G).
Proof.
  induction G1; intros until 0; intros Hm Hl.
  +{ destruct G2. inversion Hm; try discriminate.
     subst. simpl. econstructor 2; reflexivity.
     subst. simpl. econstructor 2; reflexivity.
     discriminate.
   }
  +{ destruct G2. discriminate.
     simpl in Hl. inversion Hl as [Hl'].
     simpl. destruct G3. inversion Hm; discriminate.

     simpl. inversion Hm; try discriminate.
     subst. inv_singleton.
     eapply IHG1 in X.
     econstructor 3; try reflexivity.
     eassumption. assumption.
   }
Qed.

Lemma merge_appRR : forall {V : Set} G1 G2 G3 G,
    merge G1 G2 G3 ->
    length G1 = length G2 ->
    @merge V (G1) (G2 ++ G) (G3 ++ G).
Proof.
  induction G1; intros until 0; intros Hm Hl.
  +{ destruct G2. inversion Hm; try discriminate.
     subst. simpl. econstructor 1; reflexivity.
     subst. simpl. econstructor 1; reflexivity.
     discriminate.
   }
  +{ destruct G2. discriminate.
     simpl in Hl. inversion Hl as [Hl'].
     simpl. destruct G3. inversion Hm; discriminate.

     simpl. inversion Hm; try discriminate.
     subst. inv_singleton.
     eapply IHG1 in X.
     econstructor 3; try reflexivity.
     eassumption. assumption.
   }
Qed.

Lemma merge_ex : forall {V : Set} G1 G2,
    struct_equiv_weak G1 G2 -> existsT2 G3, @merge V G1 G2 G3.
Proof.
  intros until 0; intros Hs.
  inversion Hs; subst;
  pose proof H0 as H0';
  eapply struct_equiv_str_length in H0';
  eapply merge_ex_str in H0;
  destruct H0 as [G3 H0];
  exists (G3 ++ ns3).

  eapply merge_appLR; assumption.
  eapply merge_appRR; assumption.
Qed.

Lemma merge_contracted_nseq : forall {V : Set} G H,
  @merge V G G H ->
  contracted_nseq H G.
Proof.
  induction G; intros H Hm.
  eapply merge_nil in Hm. subst. econstructor.
  inversion Hm; try discriminate.
  inv_singleton.
  econstructor. eapply contracted_seq_double.
  apply IHG. assumption.
Qed.
