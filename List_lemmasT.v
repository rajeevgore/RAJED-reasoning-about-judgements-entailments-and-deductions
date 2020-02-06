Require Import List Omega.
Import ListNotations.
Set Implicit Arguments.

Require Import existsT.
Require Import genT gen.


Open Scope type_scope.

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
Ltac list_app_nil := repeat (rewrite !app_nil_l || rewrite !app_nil_r).
Ltac list_assoc_l_simp := repeat
  (rewrite !app_assoc || rewrite !app_comm_cons || list_app_nil).
Ltac list_assoc_r_simp := repeat
  (rewrite <- !app_assoc || rewrite <- !app_comm_cons || list_app_nil).
Ltac list_assoc_l_simp' := repeat
  (rewrite !app_assoc || rewrite !app_comm_cons || rewrite !app_nil_l
  || rewrite !app_nil_r).
Ltac list_assoc_r_simp' := repeat
  (rewrite <- !app_assoc || rewrite <- !app_comm_cons || rewrite !app_nil_l
  || rewrite !app_nil_r).
Ltac list_eq_assoc := list_assoc_r ; reflexivity.

Lemma if_eq_rev_eq: forall {T} (a b : list T),
  a = b -> (rev a = rev b).
Proof. intros. subst. reflexivity. Qed.

Lemma if_rev_eq: forall {T} (a b : list T),
  (rev a = rev b) -> a = b.
Proof. intros. 
pose (@if_eq_rev_eq T (rev a) (rev b) H).
rewrite -> !rev_involutive in e.
exact e.
Qed.

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

Lemma partition_2_2T : forall {A : Type} (l1 l2 l3 l4 : list A) a b,
l1 ++ a :: l2 = l3 ++ b :: l4 ->
  (existsT2 l5, (l1 = l3 ++ b :: l5) * (l4 = l5 ++ a :: l2)) +
  (((l3 = l1)* (a = b) * (l2 = l4)) +
  (existsT l5, (l3 = l1 ++ a :: l5) * (l2 = l5 ++ b :: l4))).
Proof.
  induction l1; intros l2 l3 l4 b c H.
  - simpl in *. destruct l3.
    right. left. simpl in *. inversion H.
    subst. repeat split. 
    simpl in H. inversion H as [[H2 H3]].
    subst. right. right. exists l3.  repeat split. 
    
  - destruct l3. simpl in *. inversion H as [[H2 H3]].
    subst. left. exists l1.  repeat split. 
    simpl in H. inversion H as [[H2 H3]]. subst.
    apply IHl1 in H3. destruct H3 as [[l5 [H4 H5]] | [[[H4 H5]] | [l5 [H4 H5]]]];
                        subst.
    + left. exists l5. simpl.  repeat split. 
    + right. left.  repeat split. 
    + right. right. exists l5. repeat split. 
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

Lemma eq_app_canc1 : forall {A : Type} (l1 l2 l2': list A),
  (l1 ++ l2 = l1 ++ l2') <-> (l2 = l2').
Proof. intros.  unfold iff. split ; intros.
  induction l1. simpl in H. exact H.
  eapply IHl1. simpl in H. inversion H. reflexivity.
  subst. reflexivity. Qed.

Lemma eq_app_canc2 : forall {A : Type} (l1 l1' l2: list A),
  (l1 ++ l2 = l1' ++ l2) <-> (l1 = l1').
Proof. intros.  unfold iff. split ; intros.
  apply if_eq_rev_eq in H.
  rewrite -> !rev_app_distr in H.
  rewrite -> eq_app_canc1 in H.
  apply if_rev_eq in H. exact H.
  subst. reflexivity. Qed.

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

(* not sure if we ever need this *)
Lemma list_rearr18 : forall {T : Type} (F G H : list T) (a : T),
  (F ++ G ++ a :: H) = (F ++ G) ++ a :: H.
Proof.  intros. apply app_assoc. Qed.

Lemma list_rearr19 : forall {T : Type} (F G H : list T) (a : T),
  (F ++ G) ++ a :: H = F ++ (G ++ [a]) ++ H.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma list_rearr20 : forall {T : Type} (F G : list T) (a b : T),
  F ++ a :: b :: G = F ++ [a ; b] ++ G.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma list_rearr21 : forall {T : Type} (F G : list T) (a b : T),
  (F ++ [a]) ++ b :: G = F ++ [a ; b] ++ G.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma list_rearr22 : forall {T : Type} (F G : list T) (a b : T),
  F ++ a :: b :: G = (F ++ [a]) ++ b :: G.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

Lemma list_rearr23 : forall {T : Type} (b a : T) (F G : list T),
  a :: F ++ b :: G = (a :: F) ++ b :: G.
Proof.  intros. list_assoc_r. simpl. reflexivity. Qed.

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

Lemma cons_eq_appT: forall (A : Type) (x y z : list A) (a : A),
  a :: x = y ++ z -> sum ((y = []) * (z = a :: x)) 
  (sigT (fun y' : list A => prod (y = a :: y') (x = y' ++ z))).
Proof.
intros.
destruct y. simpl in H. subst. tauto.
simpl in H.
injection H.
intros. right. subst.
exists y. tauto.
Qed.

Lemma cons_eq_appT2: forall (A : Type) (x y z : list A) (a : A),
    a :: x = y ++ z ->
    ((y = []) * (z = a :: x)) +
  existsT2 (y' : list A), (y = a :: y') * (x = y' ++ z).
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

Definition app_eq_consT2 (A : Type) (x y z : list A) (a : A) p :=
  @cons_eq_appT2 A x y z a (eq_sym p).

Lemma app_eq_nilT : forall (A : Type) (l l' : list A),
    l ++ l' = [] -> (l = []) * (l' = []).
Proof.  destruct l; intros l' H. tauto. discriminate. Qed.

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

Lemma app_eq_appT: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> sigT (fun m : list A =>
    sum ((w = y ++ m) * (z = m ++ x)) ((y = w ++ m) * (x = m ++ z))).
Proof.  intro. intro.  induction w.
simpl. intros.
exists y. rewrite H. tauto.
intros. simpl in H.
apply cons_eq_appT in H.
destruct H.  destruct p.  subst. simpl.
exists (a :: w). simpl.  tauto.
destruct s.  destruct p.
apply IHw in e0.  destruct e0. 
destruct s ; destruct p ; subst ; simpl ; exists x1 ; tauto.
Qed.

Lemma app_eq_appT2: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> existsT2 (m : list A),
    ((w = y ++ m) * (z = m ++ x)) + ((y = w ++ m) * (x = m ++ z)).
Proof.
  induction w; intros until 0; intros H; simpl in *.
  subst. exists y. right. tauto.
  apply cons_eq_appT2 in H. destruct H as [[H1 H2]| [l [? H3]]]; subst.
  exists (a :: w). tauto.
  eapply IHw in H3. destruct H3 as [l2 [[H3 H4] | [H3 H4]]]; subst.
  exists l2. tauto.
  exists l2. tauto.
Qed.

Definition app_eq_consT (A : Type) (x y z : list A) (a : A) p :=
  @cons_eq_appT A x y z a (eq_sym p).

Lemma list_eq_nil: forall (A : Type) (x y : list A) (u : A),
  x ++ u :: y = [] -> False.
Proof.  intros.  apply app_eq_nil in H.  cD.  discriminate.  Qed.

Lemma app_eq_unitT :
  forall {A : Type} (x y:list A) (a:A),
    x ++ y = [a] -> ((x = []) * (y = [a])) + ((x = [a]) * (y = [])).
Proof.
  intros until 0; intros H.
  destruct x. auto.
  simpl in *. inversion H. subst. right.
  rewrite H2. apply app_eq_nilT in H2. destruct H2 as [H2a H2b].
  subst. auto.
Qed.

Definition nil_eq_list A x y u p := @list_eq_nil A x y u (eq_sym p).
Definition nil_eq_app A u v p := @app_eq_nil A u v (eq_sym p).
Definition nil_eq_appT A u v p := @app_eq_nilT A u v (eq_sym p).
Definition unit_eq_app A x y a p := @app_eq_unit A x y a (eq_sym p).
Definition unit_eq_appT A x y a p := @app_eq_unitT A x y a (eq_sym p).

Lemma list_eq_single: forall (A : Type) (x y : list A) (u v : A),
  x ++ u :: y = [v] -> x = [] /\ y = [] /\ u = v.
Proof.  intros.  apply app_eq_cons in H.  sD.  injection H0 as.  subst.  tauto.
        apply app_cons_not_nil in H1.  contradiction.  Qed.

Lemma list_eq_singleT: forall (A : Type) (x y : list A) (u v : A),
  x ++ u :: y = [v] -> prod (x = []) (prod (y = []) (u = v)).
Proof.  intros.  apply app_eq_consT in H.  sD.  injection H0 as.  subst.  tauto.
  apply nil_eq_appT in H1. cD. discriminate H2. Qed.

Lemma list_eq_singleT_nobrac: forall (A : Type) (x y : list A) (u v : A),
  x ++ u :: y = [v] -> (x = []) * (y = []) * (u = v).
Proof.  intros.  apply app_eq_consT2 in H. sD.  injection H0 as.  subst.  tauto.
  apply app_cons_not_nil in H1.  contradiction.  Qed.

Definition single_eq_list A x y u v p := @list_eq_single A x y u v (eq_sym p).
Definition single_eq_listT A x y u v p := @list_eq_singleT A x y u v (eq_sym p).
Definition single_eq_listT_nobrac A x y u v p := @list_eq_singleT_nobrac A x y u v (eq_sym p).

Lemma nnn_app_eq: forall {A : Type} (x : list A), [] ++ [] ++ [] ++ x = x.
Proof.  intros.  simpl. reflexivity. Qed.

Definition eq_nnn_app {A : Type} (x : list A) := eq_sym (nnn_app_eq x).


(* Caitlin added from here for weakening. *)

Lemma cons_singleton : forall {A : Type} (l : list A) a,
    a :: l = [a] ++ l.
Proof. induction l; intros b; firstorder. Qed.

Ltac list_cons_singleton a := repeat rewrite (cons_singleton _ a).
Ltac tac_cons_singleton_arg a l :=
    match l with
    | nil => idtac
    | _ => rewrite (cons_singleton l a)
    end.

Ltac tac_cons_singleton :=
  repeat
  match goal with
   | [ |- context [?a :: ?l]] => progress (tac_cons_singleton_arg a l)
  end.

(* Caitlin added from here for contraction. *)

Ltac rem_nil_goal := repeat rewrite app_nil_l; repeat rewrite app_nil_r.
Ltac rem_nil_hyp_arg H := repeat rewrite app_nil_l in H; repeat rewrite app_nil_r in H.
Ltac rem_nil_hyp :=
  match goal with
  | [ H : context[ [] ++ ?A ] |- _ ] => rem_nil_hyp_arg H
  | [ H : context[ ?A ++ [] ] |- _ ] => rem_nil_hyp_arg H
  | _ => idtac
  end.

Ltac rem_nil := rem_nil_hyp; rem_nil_goal.

Ltac list_assoc_r_single :=
  list_assoc_r; tac_cons_singleton; rem_nil.

Ltac app_bracket_middle_arg l :=
  repeat match l with
         | ?l1 ++ ?l2 ++ ?l3 ++ ?l4 => rewrite (app_assoc l2)
         end.

Ltac add_empty_hyp_L l H :=  rewrite <- (app_nil_l l) in H.
Ltac add_empty_goal_L l :=  rewrite <- (app_nil_l l).
Ltac add_empty_hyp_R l H :=  rewrite <- (app_nil_r l) in H.
Ltac add_empty_goal_R l :=  rewrite <- (app_nil_r l).
Ltac rem_empty_hyp_L l H :=  rewrite (app_nil_l l) in H.
Ltac rem_empty_goal_L l :=  rewrite (app_nil_l l).
Ltac rem_empty_hyp_R l H :=  rewrite (app_nil_r l) in H.
Ltac rem_empty_goal_R l :=  rewrite (app_nil_r l).

Ltac breakdown :=
  repeat (
      repeat (match goal with
              | [ H : ?A ++ ?B = ?x ++ ?y |- _ ] => apply app_eq_app in H; sE; subst
              end) ;
      repeat (match goal with
              | [H2 : [?a] = ?A ++ ?B |- _ ] => apply unit_eq_app in H2; sE; subst
              end));
  repeat try rewrite app_nil_r; repeat try rewrite app_nil_l;
  repeat (match goal with
          | [ H3 : context[ ?x ++ [] ] |- _ ] => rewrite (app_nil_r x) in H3
          end);
  repeat (match goal with
          | [ H3 : context[ [] ++ ?x ] |- _ ] => rewrite (app_nil_l x) in H3
          end).

Ltac tac_cons_singleton_arg_hyp H a l :=
    match l with
    | nil => idtac
    | _ => rewrite (cons_singleton l a) in H
    end.

Ltac tac_cons_singleton_hyp H :=
  repeat
  match goal with
  | [ H : context [?a :: ?l] |- _] => progress (tac_cons_singleton_arg_hyp H a nil ||
                                                tac_cons_singleton_arg_hyp H a l)
  end.

Ltac list_assoc_r_s_arg H :=
  tac_cons_singleton_hyp H; repeat rewrite <- !app_assoc in H.


Ltac list_assoc_r_arg H :=
  repeat (rewrite <- !app_assoc in H || rewrite <- !app_comm_cons in H).
Ltac list_assoc_l'_arg H := repeat (rewrite !app_assoc in H || rewrite !app_comm_cons in H).
Ltac list_assoc_l'_arg_conc H := list_assoc_l; list_assoc_l'_arg H.
Ltac list_assoc_r_arg_conc H := list_assoc_r; list_assoc_r_arg H.


Ltac list_assoc_r_singleton_hyp H :=
  list_assoc_r_arg H; tac_cons_singleton_hyp H.

Ltac list_assoc_r_singleton_hyp2 H :=
  list_assoc_r_s_arg H.

Definition non_empty {A : Type} (l : list A) :=
  match l with
  | nil => False
  | _ => True
  end.

Ltac check_app_head l1 l2 :=
  match l1 with
  | l2 ++ ?l3 => idtac
  | _ => fail
  end.

Ltac check_app_tail l1 l2 :=
  match l1 with
  | ?l3 ++ l2 => idtac
  | _ => fail
  end.

Ltac clear_useless :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         | [H : [?a] = [?a] |- _] => clear H
         | [H : ?a :: ?b = ?a :: ?b |- _] => clear H
         | [H1 : ?a, H2 : ?a |- _] => clear H2
         end.

(*
Lemma testing_clear_useless : forall (a b c : nat) (l1 l2 l3 : list nat),
    a::l1 = b::l2 ->
    [b] = [c] ->
    c = a ->
    l2 = l2 ->
    [l2] = [l2] ->
    True.
Proof.  
  clear_useless.
Admitted.
 *)

Ltac inv_singleton :=
    repeat ( match goal with
       | [ H : ?a :: [] = ?c :: ?d |- _ ] => inversion H; subst
       | [ H : ?a :: ?b = ?c :: [] |- _ ] => inversion H; subst
       | [ H : ?a :: ?b = ?c :: ?d |- _ ] => inversion H; subst
       | [ H : ((?a,?b) = ?c) |- _ ] => inversion H; subst
       | [ H : ?c = (?a,?b) |- _ ] => inversion H; subst
             end; clear_useless).

Ltac inversion_cons :=
  repeat match goal with
         | [ H : ?a :: ?l1 = ?b :: ?l2 |- _] => inversion H; subst; clear_useless
         end.
