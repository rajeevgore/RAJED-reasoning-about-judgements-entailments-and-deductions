Require Import List.
Require Import Lia.
Export ListNotations.

Require Import gen_tacs lntT List_lemmasT.
Require Import gen genT.
Require Import lntacsT.
Require Import existsT.
Require Import contractedT weakenedT.
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

Lemma merge_str_length : forall {V : Set} G1 G2 G3,
    struct_equiv_str G1 G2 -> @merge V G1 G2 G3 -> length G3 = length G1.
Proof.
  induction G1; intros G2 G3 Hs Hm.
  inversion Hs; subst; inversion Hm;
    subst; try reflexivity; discriminate.
  inversion Hs; try discriminate.
  subst. inv_singleton.
  inversion Hm; try discriminate.
  inv_singleton.
  simpl. erewrite IHG1.
  reflexivity. eassumption. eassumption.
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

Lemma merge_merge_contractedR : forall {V} G1 G2 G3 G4,
    merge G1 G2 G3 ->
    @merge V G3 G2 G4 ->
    contracted_nseq G4 G3.
Proof.
  induction G1; intros until 0; intros Hm1 Hm2.
  inversion Hm1. subst. inversion Hm2; subst.
  econstructor. econstructor.
  inversion_cons. 
  inversion Hm2; try discriminate.
  repeat inversion_cons.
  econstructor. eapply contracted_seq_double.
  eapply merge_contracted_nseq. eassumption.
  subst. inversion Hm2. subst. econstructor.
  subst. econstructor.
  discriminate. discriminate.

  inversion Hm1. discriminate. subst.
  inversion Hm2. discriminate.
  subst. eapply contracted_nseq_refl.
  discriminate.
  subst. inversion_cons. 
  inversion Hm2.  discriminate. discriminate.
  subst. repeat inversion_cons. 
  econstructor.

  eapply cont_seq_stepL; [ | eapply cont_seq_baseR]; econstructor.
  list_assoc_r. eapply contracted_multi_L.
  eapply contracted_multi_double.
  list_assoc_r. eapply contracted_multi_L.
  eapply contracted_multi_double.
  eapply IHG1. eassumption. eassumption.
Qed.



Lemma merge_weakened_nseqL : forall {V : Set} G H GH,
    struct_equiv_str G H ->
    @merge V G H GH ->
  weakened_nseq G GH.
Proof.
  induction G; intros H GH Hs Hm.
  inversion Hm; subst.
  inversion Hs; subst. econstructor. discriminate.
  econstructor. discriminate.

  inversion Hm. discriminate.
  subst. inversion Hs. discriminate.
  subst. inversion H3. subst.
  clear_useless.
  inversion Hs. inversion H. inversion H0. subst.
  clear_useless.
  econstructor.

  eapply weak_seq_baseLR.
  econstructor.
  eapply weak_multi_step.
  eapply weak_appL.
  econstructor.
  eapply weak_seqR. 
  eapply weak_multi_step.
  eapply weak_appL.
  econstructor.
  eapply IHG. eassumption. eassumption. 
Qed.

Lemma merge_weakened_nseqR : forall {V : Set} G H GH,
    struct_equiv_str G H ->
    @merge V G H GH ->
  weakened_nseq H GH.
Proof.
  intros V G H; revert G.
  induction H; intros G GH Hs Hm.
  inversion Hm; subst.
  inversion Hs; subst. econstructor. discriminate.
  inversion Hs. 
  econstructor. discriminate. discriminate.

  inversion Hm. subst.
  inversion Hs; discriminate. discriminate.
  subst. inversion H4. subst.
  clear_useless.
  econstructor.
  eapply weak_seq_baseLR.
  econstructor.
  eapply weak_multi_step.
  eapply weak_appR.
  econstructor.
  econstructor.
  eapply weak_multi_step.
  eapply weak_appR.
  econstructor.
  eapply IHlist.
  inversion Hs. subst. inversion H. inversion H0.
  subst. eapply H1. assumption.
Qed.

Inductive leT (n : nat) : nat -> Type :=
  leT_n : leT n n
| leT_S : forall m : nat, leT n m -> leT n (S m).

Lemma leT_0_m : forall m, leT 0 m.
Proof.
  induction m. econstructor.
  econstructor. assumption.
Qed.

Lemma leT_S_S: forall n m, leT (S n) (S m) -> leT n m.
Proof.
  intros n m; revert n.
  induction m; intros n H.
  inversion H. econstructor.
  subst. inversion H1.
  inversion H. econstructor.
  subst.
  econstructor. eapply IHm.
  assumption.
Qed.

Lemma leT_length : forall {T : Type} (l1 l2 : list T),
  leT (length l1) (length l2) ->
  existsT2 la lb, (l2 = la ++ lb) *
                  (length la = length l1).
Proof.
  induction l1; intros l2 Hl.
  simpl in *. exists nil, l2.
  firstorder.
  simpl in Hl. destruct l2.
  inversion Hl.
  simpl in Hl.
  eapply leT_S_S in Hl.
  eapply IHl1 in Hl.
  destruct Hl as [la [lb [H1 H2]]].
  subst.
  simpl. exists (t :: la), lb.
  simpl. firstorder.
Qed.

Lemma merge_ex_leT : forall {T : Set} G H GH,
@merge T G H GH ->
leT (length G) (length H) ->
existsT2 H1 H2 GH1, (H = H1 ++ H2) *
           (struct_equiv_str G H1) *
           (merge G H1 GH1) *
           (GH = GH1 ++ H2). 
Proof.
  intros until 0; intros Hm Hl.
  remember G as GG. remember H as HH. remember GH as GGHH.
  revert G H GH Hl HeqGG HeqHH HeqGGHH.
  induction Hm; intros; subst.
  exists nil. exists GH. exists nil.
  repeat split. econstructor. econstructor. reflexivity. reflexivity.
  subst. exists nil, nil, nil.
  simpl in Hl. destruct GH. repeat split. econstructor.
  econstructor. reflexivity. reflexivity.
  simpl in Hl. inversion Hl.

  simpl in *. eapply leT_S_S in Hl.
(*   destruct (leT_length _ _ Hl) as [la [lb [Hlab Hlab2]]]. *)
  eapply IHHm in Hl. destruct Hl as [HH1 [HH2 [GGHH1 pf]]].
  do 3 destruct pf as [pf ?].
  subst.
  exists ((Σ, Π, d) :: HH1).  
  eexists.
  exists ((Γ ++ Σ, Δ ++ Π, d) :: GGHH1).
  repeat split.
  econstructor. reflexivity. reflexivity.
  assumption.
  eapply merge_step; try reflexivity.
  eassumption.
  all : reflexivity.
Qed.


Lemma  merge_app : forall {V : Set} l1 l2 l3 l4 l5 l6,
    length l1 = length l3 ->
    @merge V l1 l3 l5 ->
    merge l2 l4 l6 ->
    merge (l1 ++ l2) (l3 ++ l4) (l5 ++ l6).
Proof.
  induction l1; intros until 0; intros Hl Hm1 Hm2.
  destruct l3; [|discriminate].
  inversion Hm1; subst; try assumption; discriminate.

  destruct l3. discriminate.
  inversion Hm1; try discriminate.
  subst. inv_singleton.
  simpl. econstructor 3; try reflexivity.
  eapply IHl1. simpl in *. lia. assumption. assumption.
Qed.

Lemma merge_app_rev : forall {V : Set} l1 l2 l3 l4 l5 l6,
    length l1 = length l3 ->
    length l1 = length l5 ->
    merge (l1 ++ l2) (l3 ++ l4) (l5 ++ l6) ->
    (merge l1 l3 l5) * (@merge V l2 l4 l6).
Proof.
  induction l1; intros until 0; intros Hl1 Hl2 Hm.
  destruct l3; destruct l5; try discriminate.
  simpl in *. split. econstructor; reflexivity. assumption.

  destruct l3; destruct l5; try discriminate.
  simpl in *. inversion Hm; try discriminate.
  subst.
  inv_singleton_str.
  edestruct IHl1.
  inversion Hl1 as [Hl1']. eapply Hl1'.
  inversion Hl2 as [Hl2']. eapply Hl2'.
  eassumption.
  split. eapply merge_step; try reflexivity.
  all : eassumption.
Qed.

Lemma merge_app_struct_equiv_strR : forall {V : Set} G H1 seq GHseq,
    merge G (H1 ++ [seq]) GHseq ->
    struct_equiv_str G (H1 ++ [seq]) ->
    existsT2 G2 seq2 GH seq3,
  (G = G2 ++ [seq2]) * (GHseq = GH ++ [seq3]) *
  (@merge V G2 H1 GH) * (struct_equiv_str G2 H1).
Proof.
  intros until 0; intros Hm Hs.
  destruct (list_nil_or_tail_singleton G); subst.
  inversion Hs; destruct H1; discriminate.
  sD. subst.
  destruct (list_nil_or_tail_singleton GHseq). subst.
  inversion Hm; destruct H1; discriminate.
  sD. subst.
  pose proof (struct_equiv_str_length _ _ Hs) as Hsl.
  repeat rewrite app_length in Hsl. simpl in Hsl.
  repeat rewrite PeanoNat.Nat.add_1_r in Hsl.
  inversion Hsl.
  eapply merge_app_rev in Hm.
  destruct Hm as [Hm1 Hm2].
  repeat eexists.
  eapply Hm1.
  eapply struct_equiv_str_app_revR in Hs. eapply Hs.
  assumption.
  assumption.
  eapply merge_str_length in Hm.
  repeat rewrite app_length in Hm.
  simpl in Hm. repeat rewrite PeanoNat.Nat.add_1_r in Hm.
  inversion Hm. reflexivity.
  assumption.
Qed.

Lemma merge_app_single : forall {V : Set} G H GH l1 l2 l3 l4 l5 l6 dg dh dgh,
    struct_equiv_str G H ->
    @merge V (G ++ [(l1, l2, dg)]) (H ++ [(l3, l4, dh)]) (GH ++ [(l5, l6, dgh)]) ->
    (l5 = l1 ++ l3) * (l6 = l2 ++ l4) * (dgh = dg) * (dgh = dh).
Proof.
  induction G; intros until 0; intros Hs Hm.
  simpl in *.
  destruct H. simpl in Hm. destruct GH. simpl in *.
  inversion Hm; try discriminate; subst; inv_singleton_str.
  firstorder.
  simpl in Hm. destruct GH; simpl in *;
  inversion Hm; try discriminate; inv_singleton_str; inversion X; discriminate.
  inversion Hs; discriminate.
  destruct H. simpl in *. inversion Hs; try discriminate.
  inversion Hs. inv_singleton_str.
  destruct GH.
  simpl in *.  inversion Hm; try discriminate.
  subst. inv_singleton_str. destruct ns1.
  simpl in *. inversion X; try discriminate.
  destruct ns2. inversion H2; discriminate.
  simpl in X. inversion X; discriminate.

  simpl in Hm. inversion Hm; try discriminate.
  inv_singleton_str.
  edestruct IHG. eassumption. eassumption.
  sD.
  firstorder.
Qed.

Lemma merge_single : forall {V : Set} A1 A2 B1 B2 d,
    @merge V [(A1,A2,d)] [(B1,B2,d)] [(A1++B1,A2++B2,d)].
Proof.
  intros.  econstructor 3; try econstructor; reflexivity.
Qed.

Ltac get_hyp_merge_weakened_nseqR :=
  match goal with
  | [ H1 : merge ?X1 ?X2 ?X3, H2 : struct_equiv_str ?X1 ?X2 |- _ ] =>
    pose proof (merge_weakened_nseqR _ _ _ H2 H1)
  end.



Lemma merge_app_single_rev : forall {V : Set} G H GH A1 A2 B1 B2 d,
    struct_equiv_str G H ->
    merge G H GH ->
    @merge V (G ++ [(A1,A2,d)]) (H ++ [(B1,B2,d)]) (GH ++ [(A1++B1,A2++B2,d)]).
  Proof.
    induction G; intros until 0; intros Hstr Hm.
    inversion Hstr; try discriminate; subst.

    simpl. inversion Hm; try discriminate; subst;
             simpl; eapply merge_single.

    inversion Hstr. subst. inv_app_hd_tl_full.
    subst.  simpl in *.
    inversion Hm; try discriminate.
    subst. inversion H3. inversion H4.
    subst. simpl.
    econstructor 3; try reflexivity.
    eapply IHG; eassumption.
  Qed.

Ltac merge_solve_single :=
  list_assoc_r_single; eapply merge_single.

Ltac merge_solve_primitive :=
  repeat (eassumption || match goal with
   | [ |- merge [(?L1, ?L2, ?d)] [(?M1, ?M2, ?d)] [(?L1++?M1, ?L2++?M2, ?d)] ] =>
     merge_solve_single
(*    | [ |- merge (?H1 ++ [(?L1, ?L2, ?d)]) (?H2 ++ [(?M1, ?M2, ?d)]) (?H3 ++ [(?L1++?M1, ?L2++?M2, ?d)]) ] => eapply merge_app_single_rev
 *)
   | [ |- merge (?H1 ++ [(?L1, ?L2, ?d)]) ?H4 (?H3 ++ [(?M1, ?M2, ?d2)]) ] => eapply merge_app_single_rev; [struct_equiv_str_solve_primitive | ]; merge_solve_primitive
   | [H:merge ?H1 ?H2 ?H3, Hstr : struct_equiv_str ?H1 ?H2
      |- merge (?H1 ++ ?G1) (?H2 ++ ?G2) (?H3 ++ ?G3)] => eapply (merge_app (struct_equiv_str_length _ _ Hstr) H)     
   | [ H : merge ?H1 ?H2 ?H3 |- merge (?H1 ++ ?G1) (?H2 ++ ?G2) (?H3 ++ ?G3) ] =>
      eapply (merge_app _ H)
                         end).

Lemma merge_app_struct_equiv_strR_explicit : forall {V : Set} G H GHseq Γ Δ d,
  @merge V G (H ++ [(Γ,Δ,d)]) GHseq ->
  struct_equiv_str G (H ++ [(Γ,Δ,d)]) ->
  existsT2 G' Γ' Δ' GH,
        (G = G' ++ [(Γ',Δ',d)]) *
        (GHseq = GH ++ [(Γ'++Γ,Δ'++Δ,d)]) *
        (merge G' H GH) *
        (struct_equiv_str G' H).
Proof.
  intros until 0; intros Hm Hstr.
  eapply merge_app_struct_equiv_strR in Hstr; [ |eapply Hm].
  sD; subst.
  inversion_prod.
  eapply merge_app_rev in Hm.
  sD. inversion Hm0; try discriminate.
  inv_singleton_str.
  inversion H3. inversion H4.
  subst.
  repeat eexists. eapply Hm. eapply Hstr5.
  eapply struct_equiv_str_length. assumption.
  symmetry. eapply merge_str_length. eassumption.
  eassumption.
Qed.

Lemma struct_equiv_str_mergeL : forall V G1 G2 G3,
    struct_equiv_str G1 G2 ->
    merge G1 G2 G3 ->
    @struct_equiv_str V G1 G3.
Proof.
  induction G1; intros G2 G3 Hs Hm.
  inversion Hs; subst; inversion Hm; subst; try discriminate; econstructor.
  inversion Hm; subst; try discriminate.
  eapply struct_equiv_str_refl.
  inversion_cons. 
  econstructor; try reflexivity.
  eapply IHG1.
  inversion Hs; try discriminate.
  repeat inversion_cons. all : eassumption.
Qed.

Lemma struct_equiv_str_mergeR : forall V G1 G2 G3,
    struct_equiv_str G1 G2 ->
    merge G1 G2 G3 ->
    @struct_equiv_str V G2 G3.
Proof.
  induction G1; intros G2 G3 Hs Hm.
  inversion Hs; subst; inversion Hm; subst; try discriminate; econstructor.
  inversion Hm; subst; try discriminate.
  inversion Hs; try discriminate.
  inversion_cons.
  econstructor; try reflexivity.
  eapply IHG1.
  inversion Hs; try discriminate.
  repeat inversion_cons. all : eassumption.
Qed.

