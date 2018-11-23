Require Import List Omega.
Import ListNotations.

Ltac app_assoc_solve G := rewrite <- (app_assoc G); reflexivity.
Ltac app_assoc_solve2 G H := rewrite <- (app_assoc G); simpl;
                             rewrite <- (app_assoc H); reflexivity.
Ltac eapp_assoc_solve2 G H := erewrite <- (app_assoc G); simpl;
                             erewrite <- (app_assoc H); reflexivity.
Ltac app_assoc_hyp G H := rewrite <- (app_assoc G) in H.
Ltac app_assoc_hyp_inv G H := rewrite <- (app_assoc G) in H; apply app_inv_head in H.

Ltac list_assoc_l := repeat (rewrite !app_assoc || rewrite !app_comm_cons).
Ltac list_assoc_r := 
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons).
Ltac list_eq_assoc := list_assoc_r ; reflexivity.

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

Lemma subst_dep : forall (T : Type) (G1 G2 : T) P (P2 : forall (G : T), P G  -> nat)  (D1 : P G1),
    G1 = G2  ->
    exists (D2 : P G2), P2 G1 D1 = P2 G2 D2.
Proof.
  intros T G1 G2 P P2 D1 Heq.
  generalize dependent D1. subst.
  intros D1. exists D1. reflexivity.
Qed.

Ltac finish_ht_admis_ex1 := simpl; apply le_n_S;  assumption.
Ltac finish_ht_admis_ex2 := simpl; apply le_n_S;
                            eapply (Nat.le_trans _ _ _ _ _);
                            assumption.
Ltac find_trans_solve :=      match goal with
               | [ H1 : ?n1 <= ?n2, H2 : ?n2 <= ?n3 |- ?n1 <= ?n3] =>
                 apply (Nat.le_trans n1 n2 n3 H1 H2) end.
Ltac finish_ht_admis_ex3 :=  simpl; apply le_n_S; find_trans_solve.
Ltac ap_part_2_2 P1 l5 P3 P4 P5 :=
  apply partition_2_2 in P1;
  destruct P1 as [ [l5 [P3 P4]] | [ [P3 [P4 P5]] |  [l5 [P3 P4]]]].

Ltac ap_part_2_3 P5 l5 P55 := apply partition_2_3 in P5;
    destruct P5 as [ [P5 PP5] | [ [l5 [P5 PP5]]
                                | [[P5 PP5] | [[P5 PP5] | [l5 [P5 PP5]]]]]].

Lemma list_rearr1 : forall {A : Type} (a : A) G0 l5 H,
      (G0 ++ a :: l5 ++ H) =
           (((G0 ++ [a]) ++ l5) ++  H).
Proof.
  intros.     rewrite app_cons_single.
  rewrite app_assoc. reflexivity.
Qed.

Lemma list_rearr2 : forall {A : Type} (a : A) G0 l5 H,
  ((G0 ++ [a]) ++ l5) ++ H =  G0 ++ a :: l5 ++ H.
Proof. intros. do 2 rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr4 : forall {T1 T2 T3 : Type} G (A B E : T1) (Δ : list T2)
                           Γ1 Γ2 (δ : T3) H,
    G ++ (Γ1 ++ E :: A :: B :: Γ2, Δ, δ) :: H =
    G ++ ((Γ1 ++ [E]) ++ A :: B :: Γ2, Δ, δ) :: H.
Proof. intros. rewrite <- app_assoc.  reflexivity. Qed.

Lemma list_rearr5 : forall {T1 T2 T3 : Type} G (E B : T1)
                           Γ1 Γ2 (Δ : list T2) (δ : T3) H,
    G ++ ((Γ1 ++ [E]) ++ B :: Γ2, Δ, δ) :: H =
    G ++ (Γ1 ++ E :: B :: Γ2, Δ, δ) :: H.
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr6 : forall {T1 T2 T3 : Type} (E : T1) G l5 Γ3 Γ2
                           (Δ : list T2) (δ : T3) H,
    G ++ (Γ3 ++ E :: l5 ++ Γ2, Δ, δ) :: H =
    G ++ (((Γ3 ++ [E]) ++ l5) ++ Γ2, Δ, δ) :: H.
Proof. intros. rewrite (app_cons_single Γ3).
       rewrite (app_assoc _ l5). reflexivity.
Qed.

Lemma list_rearr7 : forall {T1 T2 T3 : Type} G (E : T1) l5 Γ3 Γ2
                           (Δ : list T2) (δ : T3) H,
G ++ (((Γ3 ++ [E]) ++ l5) ++ Γ2, Δ, δ) :: H =
      G ++ (Γ3 ++ E :: l5 ++ Γ2, Δ, δ) :: H.
Proof. intros.  do 2 rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr8 : forall {T1 T2 T3 : Type} G Γ1 Γ2 (A B : T1)
                           (Δ : list T2) (δ : T3) H,
 G ++ ((Γ1 ++ [A; B]) ++ Γ2, Δ, δ) :: H =
      G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H.
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr9 : forall {T1 T2 T3 : Type} G Γ1 Γ2 (A B : T1)
                           (Δ : list T2) (δ : T3) H,
G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H =
G ++ (((Γ1 ++ [B]) ++ [A]) ++ Γ2, Δ, δ) :: H.
Proof. intros.   rewrite (app_cons_single _ _ B);
  rewrite (app_cons_single _ _ A). reflexivity.
Qed.

Lemma list_rearr10 : forall {T1 T2 T3 : Type} G Γ1 Γ4 (A B : T1) l5
                           (Δ : list T2) (δ : T3) H,
G ++ ((Γ1 ++ [A; B] ++ l5) ++ Γ4, Δ, δ) :: H =
       G ++ (Γ1 ++ A :: B :: l5 ++ Γ4, Δ, δ) :: H.
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma list_rearr11 : forall {T1 T2 T3 : Type} G Γ1 Γ4 (A B : T1) l5
                           (Δ : list T2) (δ : T3) H,
G ++ (Γ1 ++ B :: A :: l5 ++ Γ4, Δ, δ) :: H =
      G ++ ((((Γ1 ++ [B]) ++ [A]) ++ l5) ++ Γ4, Δ, δ) :: H.
Proof.
  intros. rewrite (app_cons_single _ _ B).
  rewrite (app_cons_single _ _ A).
  rewrite (app_assoc _ l5). reflexivity.
Qed.

Lemma list_rearr13 : forall {T : Type} a (G l5 H : list T),
     G ++ a :: l5 ++ H = (G ++ a :: l5) ++ H.
Proof.
  intros. rewrite app_comm_cons. rewrite app_assoc.
  reflexivity. Qed.

Lemma list_rearr14 : forall {T : Type} a b (F G H : list T),
  F ++ a :: (G ++ b :: H) = (F ++ a :: G) ++ b :: H.
Proof.
  intros. rewrite app_comm_cons. rewrite app_assoc.
  reflexivity. Qed.

Lemma list_rearr15 : forall {T Xt : Type} (F G H : list T) (X : Xt),
  (F ++ (G ++ H), X) = ((F ++ G) ++ H, X).
Proof.  intros. rewrite app_assoc.  reflexivity. Qed.

Lemma list_rearr15_R : forall {T Xt : Type} (F G H : list T) (X : Xt),
  (X, F ++ (G ++ H)) = (X, (F ++ G) ++ H).
Proof.  intros. rewrite app_assoc.  reflexivity. Qed.

Lemma list_rearr16' : forall {T : Type} (F G : list T) (a : T),
  F ++ (a :: G) = (F ++ [a]) ++ G.
Proof.  intros. rewrite <- app_assoc. simpl.  reflexivity. Qed.

Lemma list_rearr16 : forall {T Xt : Type} (F G : list T) (a : T) (X : Xt),
  (F ++ (a :: G), X) = ((F ++ [a]) ++ G, X).
Proof.  intros. rewrite <- app_assoc. simpl.  reflexivity. Qed.

Lemma list_rearr16_R : forall {T Xt : Type} (F G : list T) (a : T) (X : Xt),
  (X, F ++ (a :: G)) = (X, (F ++ [a]) ++ G).
Proof.  intros. rewrite <- app_assoc. simpl.  reflexivity. Qed.

Lemma list_rearr17_R : forall {T1 T2 : Type} (Φ : T2) Δ1 (B A : T1) eqr3 U Ψ2,
(Φ, Δ1 ++ B :: A :: eqr3 ++ U :: Ψ2) =
(Φ, (Δ1 ++ B :: A :: eqr3) ++ U :: Ψ2).
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma cons_eq_app: forall (A : Type) (x y z : list A) (a : A),
  a :: x = y ++ z -> y = [] /\ z = a :: x \/
  exists (y' : list A), y = a :: y' /\ x = y' ++ z.
Proof.
intros.
destruct y. simpl in H. subst. tauto.
simpl in H.
injection H.
intros. right. subst.
exists y. tauto.
Qed.

Definition app_eq_cons (A : Type) (x y z : list A) (a : A) p :=
  @cons_eq_app A x y z a (eq_sym p).

Lemma app_eq_app: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> exists (m : list A),
    w = y ++ m /\ z = m ++ x \/ y = w ++ m /\ x = m ++ z.
Proof.
intro. intro.
induction w.
simpl. intros.
exists y. rewrite H. tauto.
intros. simpl in H.
apply cons_eq_app in H.
destruct H.  destruct H.  rewrite H. simpl.
exists (a :: w).  rewrite H0. simpl. tauto.
destruct H.  destruct H.
apply IHw in H0.  destruct H0.  destruct H0. destruct H0.
rewrite H.  rewrite H0.  rewrite H1.  simpl.
exists x1. tauto.
destruct H0.
rewrite H.  rewrite H0.  rewrite H1.  simpl.
exists x1. tauto.
Qed.




