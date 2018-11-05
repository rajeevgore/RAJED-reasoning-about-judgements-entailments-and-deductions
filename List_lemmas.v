Require Import List.
Import ListNotations.

Ltac app_assoc_solve G := rewrite <- (app_assoc G); reflexivity.
Ltac app_assoc_solve2 G H := rewrite <- (app_assoc G); simpl;
                             rewrite <- (app_assoc H); reflexivity.
Ltac eapp_assoc_solve2 G H := erewrite <- (app_assoc G); simpl;
                             erewrite <- (app_assoc H); reflexivity.
Ltac app_assoc_hyp G H := rewrite <- (app_assoc G) in H.
Ltac app_assoc_hyp_inv G H := rewrite <- (app_assoc G) in H; apply app_inv_head in H.

Lemma partition_2_2 : forall {A : Type} (l1 l2 l3 l4 : list A) a b,
l1 ++ a :: l2 = l3 ++ b :: l4 ->
  (exists l5, l1 = l3 ++ b :: l5 /\ l4 = l5 ++ a :: l2) \/
  (l3 = l1 /\ a = b /\ l2 = l4) \/
  (exists l5, l3 = l1 ++ a :: l5 /\ l2 = l5 ++ b :: l4).
Proof.
  induction l1; intros l2 l3 l4 b c H.
  - simpl in *. destruct l3.
    right. left. simpl in *. inversion H.
    subst. apply conj. reflexivity. apply conj; reflexivity.
    simpl in H. inversion H as [[H2 H3]].
    subst. right. right. exists l3.  apply conj; reflexivity.
    
  - destruct l3. simpl in *. inversion H as [[H2 H3]].
    subst. left. exists l1.  apply conj; reflexivity.
    simpl in H. inversion H as [[H2 H3]]. subst.
    apply IHl1 in H3. destruct H3 as [[l5 [H4 H5]] | [[H4 H5] | [l5 [H4 H5]]]];
                        subst.
    + left. exists l5. simpl.  apply conj; reflexivity. 
    + right. left.  apply conj. reflexivity.  assumption. 
    + right. right. exists l5. apply conj; reflexivity.
Qed.

Lemma partition_3_2 : forall {A : Type}  (Γ Δ : list A) G' H' Γ1 Δ1 Γ2 Δ2 G H J,
    G ++ (Γ1, Δ1) :: H ++ (Γ2, Δ2) :: J = G' ++ (Γ, Δ) :: H' ->
    (exists l, G = G' ++ (Γ,Δ) :: l /\ H' = l ++ (Γ1, Δ1) :: H ++ (Γ2, Δ2) :: J) \/
    (G' = G /\ Γ1 = Γ /\ Δ1 = Δ /\ H' =  H ++ (Γ2, Δ2) :: J) \/
    (exists l1 l2, G' = G ++ (Γ1, Δ1) :: l1 /\
                   H = l1 ++ (Γ, Δ) :: l2 /\
                   H' = l2 ++ (Γ2, Δ2) :: J) \/
    (G' = G ++ (Γ1,Δ1) :: H /\ Γ2 = Γ /\ Δ2 = Δ /\ J = H' ) \/
    (exists l, G' = G ++ (Γ1, Δ1) :: H ++ (Γ2, Δ2) :: l /\
               J = l++ (Γ, Δ) ::H').
Proof.
  intros A l1 m1 G' H' l2 m2 l3 m3 G H J.
  revert G J H l1 m1 G' H' l2 m2 l3 m3.
  induction G; intros J H l1 m1 G' H' l2 m2 l3 m3 H2.
  - simpl in *. destruct G'.
    right. left. simpl in H2. inversion H2. 
    repeat apply conj; reflexivity.
    simpl in H2. inversion H2 as [[H3 H4]].
    right. right. edestruct  (partition_2_2 _ _ _ _ _ _ H4) as [H0 | [[H0 H5] | H0]].
    + left. destruct H0 as [l5 [H0' HH]]. subst. exists G', l5.
      repeat apply conj; try reflexivity. 
    + right. left. subst. inversion H2 as [H3]. apply app_inv_head in H3.
      inversion H3.
      repeat apply conj; reflexivity.
    + right. right. destruct H0 as [l5 [H0' H5]]. exists l5.
      subst.  inversion H2. app_assoc_hyp_inv H H1. simpl in H1.
      inversion H1.
      repeat apply conj; reflexivity.
  -  simpl in *. destruct G'. simpl in *. left.
     inversion H2 as [[H3 H4]].
     exists G. 
     repeat apply conj; reflexivity.
     simpl in H2. inversion H2 as [[H3 H4]].
     apply IHG in H4.
     destruct H4 as [ [ll [HH1 HH2]] | 
                      [[HH1 [HH2 [HH3]]] | 
                       [ [ll1 [ll2 [HH1 [HH2 HH3]]]] | 
                         [[HH1 [HH2 [HH3 HH4]]] | [ll [HH1 HH2]]]]]]; subst.
     + left. exists ll. 
       repeat apply conj; reflexivity.
     + right. left.  
       repeat apply conj; reflexivity.
     + right. right. left. exists ll1. exists ll2. 
       repeat apply conj; reflexivity.
     + right. right. right. left. 
       repeat apply conj; reflexivity.
     + right. right. right. right. exists ll. 
       repeat apply conj; reflexivity.

Unshelve.    
all : try assumption.
Qed.

Lemma app_cons_single : forall {A : Type} (l1 l2 : list A) a,
  l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  induction l1; intros. reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.

Lemma partition_2_3 : forall {A : Type} (l1 l2 l3 l4 : list A) a b,
    l1 ++ a :: b :: l2 = l3 ++ l4 ->
    (l3 = l1 /\ l4 = a :: b :: l2) \/
    (exists l5, l1 = l3 ++ l5 /\ l4 = l5 ++ a :: b :: l2) \/
    (l3 = l1 ++ [a] /\ l4 = b :: l2) \/
    (l3 = l1 ++ [a;b] /\ l4 = l2) \/
    (exists l5, l3 = l1 ++ [a;b] ++ l5 /\ l2 = l5 ++ l4).
Proof.
  induction l1; intros until 0; intros H.
  - destruct l3. left.  auto. 
    right.
    simpl in *. inversion H as [[H1 H2]]. subst.
    destruct l3. simpl in *. subst.
    right. left.  auto. 
    simpl in H2. inversion H2 as [[H1 H3]].
    subst. right. right. right. exists l3. auto. 
    
  - simpl in *. destruct l3. right. left. 
    exists (a::l1). auto.
    simpl in *. inversion H as [[H1 H2]].  subst.
    apply IHl1 in H2. 
    destruct H2 as [ [H3 H4] | [[l5 [H3 H4]] | [ [H3 H4] | [ [H3 H4] | [l5 [ H4 H5]]]]]];
      subst.
    + left. auto. 
    + inversion H as [H2]. app_assoc_hyp_inv l3 H2. subst. right. left.
      exists l5. auto. 
    + inversion H as [H2]. rewrite <- app_assoc in H2.
      apply app_inv_head in H2. simpl in H2. inversion H2 as [H3].
      subst. right. right. left. apply conj; reflexivity.
    + inversion H as [H2]. app_assoc_hyp_inv l1 H2. simpl in H2.
      inversion H2 as [H3]. subst. right. right. right. left.
      apply conj; reflexivity.
    + subst. right. right. right. right. inversion H as [H2].
      app_assoc_hyp_inv l1 H2. simpl in *. inversion H2. subst.
      exists l5.  apply conj; reflexivity.
Qed.