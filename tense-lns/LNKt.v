Require Import Kt_semantics.
Require Import Omega.
Require Import List_lemmas Strong_induction.

Set Implicit Arguments.
Export ListNotations.
Open Scope My_scope.

(** Linear nested seuquent calculus for Kt *)

(* Indicates the direction connecting sequents look. *)
Inductive dir : Type :=
| fwd : dir
| bac : dir.
                                                
Reserved Notation "LN|- Δ" (at level 80).
Inductive LN : (list ((list PropF)*(list PropF)*dir)) -> Type :=
| LNId    : forall A Γ Δ δ G H,
    In A Γ  -> In A Δ  -> LN (G ++ (Γ,Δ,δ) :: H)
| LNBot   : forall Γ Δ δ G H,
    In ⊥ Γ  -> LN (G ++ (Γ,Δ,δ) :: H)
(* Note: δ, Γ1, etc. same in both hypotheses and conclusion. *)
| LNImpL  : forall A B Γ1 Γ2 Δ1 Δ2 δ G H,
    LN (G ++ ((Γ1++B::Γ2),(Δ1++Δ2),δ) :: H) ->
    LN (G ++ ((Γ1++Γ2),(Δ1++A::Δ2),δ) :: H) ->
    LN (G ++ ((Γ1++A→B::Γ2),(Δ1++Δ2),δ) :: H)
| LNImpR : forall A B Γ1 Γ2 Δ1 Δ2 δ G H,
    LN (G ++ (Γ1++A::Γ2,Δ1++B::Δ2,δ) :: H) ->
    LN (G ++ (Γ1++Γ2,(Δ1++(A→B)::Δ2),δ) :: H)
| LNWBR  : forall A Γ Δ1 Δ2 δ G,
    LN (G ++ (Γ,Δ1++[.]A::Δ2,fwd) :: [([],[A],δ)]) ->
    LN (G ++ [(Γ,Δ1++[.]A::Δ2,δ)] )
| LNWBL  : forall A Γ1 Γ2 Γ3 Γ4 Δ1 Δ2 δ G H,
    LN (G ++ (Γ1++[.]A::Γ2,Δ1,fwd) :: (Γ3++A::Γ4,Δ2,δ) :: H) ->
    LN (G ++ (Γ1++[.]A::Γ2,Δ1,fwd) :: (Γ3++Γ4,Δ2,δ) :: H)
| LNWBRe : forall A Γ1 Γ2 Γ3 Γ4 Δ1 Δ2 δ G,
    LN (G ++ [(Γ1++A::Γ2,Δ1,δ)]) ->
    LN (G ++ (Γ1++Γ2,Δ1,bac) :: [(Γ3++[.]A::Γ4,Δ2,δ)])
| LNBBR  : forall A Γ Δ1 Δ2 δ G,
    LN (G ++ (Γ,Δ1++[#]A::Δ2,bac) :: [([],[A],δ)]) ->
    LN (G ++ [(Γ,Δ1++[#]A::Δ2,δ)] )
| LNBBL  : forall A Γ1 Γ2 Γ3 Γ4 Δ1 Δ2 δ G H,
    LN (G ++ (Γ1++[#]A::Γ2,Δ1,bac) :: (Γ3++A::Γ4,Δ2,δ) :: H) ->
    LN (G ++ (Γ1++[#]A::Γ2,Δ1,bac) :: (Γ3++Γ4,Δ2,δ) :: H)
| LNBBRe : forall A Γ1 Γ2 Γ3 Γ4 Δ1 Δ2 δ G,
    LN (G ++ [(Γ1++A::Γ2,Δ1,δ)]) ->
    LN (G ++ (Γ1++Γ2,Δ1,bac) :: [(Γ3++[#]A::Γ4,Δ2,δ)])
where "LN|- Δ" := (LN Δ) : My_scope.

Fixpoint LNheight  {G} (D : LN|- G) :=
  match D with
  | LNId _ _ _ _ _ _ _ _ => 0 
  | LNBot _ _ _ _ _ _  => 0
  | LNImpL _ _ _ _ _ _ _ _ _ D1 D2 => S (max (LNheight D1) (LNheight D2))
  | LNImpR _ _ _ _ _ _ _ _ _ D' => S (LNheight D')
  | LNWBL _ _ _ _ _ _ _ _ _ _ D' => S (LNheight D')
  | LNWBR _ _ _ _ _ _ D' => S (LNheight D')
  | LNWBRe _ _ _ _ _ _ _ _ _ D' => S (LNheight D')
  | LNBBL _ _ _ _ _ _ _ _ _ _ D' => S (LNheight D')
  | LNBBR _ _ _ _ _ _ D' => S (LNheight D')
  | LNBBRe _ _ _ _ _ _ _ _ _ D' => S (LNheight D')
  end.

(* Lemma that allows us to do case analysis on the last rule applied to the derivation, in this case for Id or Bot. *)
Lemma ht_eq_0 : forall {G} (D : LN|- G),
    LNheight D = 0 ->
    (exists A Γ Δ G0 H0 δ,
        G = (G0 ++ (Γ,Δ,δ) :: H0) /\ In A Γ /\ In A Δ) \/
    (exists Γ Δ G0 H0 δ,
        G = (G0 ++ (Γ,Δ,δ) :: H0) /\ In ⊥ Γ).
Proof.
  induction D; intros HD; try discriminate.
  -  simpl in *. left. exists A, Γ, Δ, G, H, δ.
     apply conj. reflexivity. apply conj; assumption.
  -  simpl in *. right. exists Γ, Δ, G, H, δ.
     apply conj. reflexivity.  assumption.
Qed.

(* Lemma that allows us to do case analysis on the last rule applied to the derivation, in this case for ImpL, ImpR, WBR, WBL, WBRe, BBR, BBL or BBRe. *)
Lemma ht_eq_Sn : forall GG (D : LN|- GG) n,
    LNheight D = S n ->
    (exists A B Γ1 Γ2 Δ1 Δ2 δ G H
            (D1 : LN (G ++ ((Γ1++B::Γ2),(Δ1++Δ2),δ) :: H))
            (D2 : LN (G ++ ((Γ1++Γ2),(Δ1++A::Δ2),δ) :: H)),
        GG = (G ++ ((Γ1++A→B::Γ2),(Δ1++Δ2),δ) :: H) /\
        max (LNheight D1) (LNheight D2) = n) \/
    (exists A B Γ1 Γ2 Δ1 Δ2 δ G H
            (D1 : LN (G ++ (Γ1++A::Γ2,Δ1++B::Δ2,δ) :: H)),
        GG =  (G ++ (Γ1++Γ2,(Δ1++(A→B)::Δ2),δ) :: H) /\
        LNheight D1 = n) \/
    (exists A Γ Δ1 Δ2 δ G
            (D1 :  LN (G ++ (Γ,Δ1++[.]A::Δ2,fwd) :: [([],[A],δ)])),
        GG = (G ++ [(Γ,Δ1++[.]A::Δ2,δ)] ) /\
        LNheight D1 = n) \/
    (exists A Γ1 Γ2 Γ3 Γ4 Δ1 Δ2 δ G H
            (D1 :  LN (G ++ (Γ1++[.]A::Γ2,Δ1,fwd) :: (Γ3++A::Γ4,Δ2,δ) :: H)),
        GG = (G ++ (Γ1++[.]A::Γ2,Δ1,fwd) :: (Γ3++Γ4,Δ2,δ) :: H) /\
        LNheight D1 = n) \/
    (exists A Γ1 Γ2 Γ3 Γ4 Δ1 Δ2 δ G
            (D1 : LN (G ++ [(Γ1++A::Γ2,Δ1,δ)])),
        GG =  (G ++ (Γ1++Γ2,Δ1,bac) :: [(Γ3++[.]A::Γ4,Δ2,δ)]) /\
        LNheight D1 = n) \/
    (exists A Γ Δ1 Δ2 δ G
            (D1 : LN (G ++ (Γ,Δ1++[#]A::Δ2,bac) :: [([],[A],δ)])),
        GG = (G ++ [(Γ,Δ1++[#]A::Δ2,δ)] ) /\
        LNheight D1 = n) \/
    (exists A Γ1 Γ2 Γ3 Γ4 Δ1 Δ2 δ G H
            (D1 : LN (G ++ (Γ1++[#]A::Γ2,Δ1,bac) :: (Γ3++A::Γ4,Δ2,δ) :: H) ),
        GG = (G ++ (Γ1++[#]A::Γ2,Δ1,bac) :: (Γ3++Γ4,Δ2,δ) :: H) /\
        LNheight D1 = n) \/
    (exists A Γ1 Γ2 Γ3 Γ4 Δ1 Δ2 δ G
            (D1 : LN (G ++ [(Γ1++A::Γ2,Δ1,δ)])),
        GG = (G ++ (Γ1++Γ2,Δ1,bac) :: [(Γ3++[#]A::Γ4,Δ2,δ)]) /\
        LNheight D1 = n).
Proof.
  destruct D; intros n Ht; try discriminate;
    simpl in Ht; inversion Ht as [Ht']; rewrite Ht';
      [left | right; left | right; right; left |
       right; right; right; left|
       right; right; right; right; left|
       right; right; right; right; right; left|
       right; right; right; right; right; right; left |
       right; right; right; right; right; right; right];
      (repeat eexists; try apply conj; try apply Ht').
Qed.

Require Import List_lemmas.
Lemma LN_eq_sub_ht : forall G1 G2 (D1 : LN|- G1),
    G1 = G2  ->
    exists (D2 : LN|- G2), LNheight D1 = LNheight D2.
Proof.
  intros G1 G2 D1. apply subst_dep.
Qed.

(* Some tactics for the following proofs. *)

Ltac LN_rewrite_ht1 D1 D1' Ht1' := 
    destruct (LN_eq_sub_ht D1
               (list_rearr1 _ _ _ _ )) as [D1' Ht1'];
    rewrite Ht1' in *; clear Ht1'.

Ltac LN_rewrite_ht2 D1 D1' Ht1' := 
    destruct (LN_eq_sub_ht D1
               (list_rearr2 _ _ _ _ )) as [D1' Ht1'];
    rewrite Ht1' in *; clear Ht1'.

Ltac LN_rewrite_ht4 D1 D1' Ht1' := 
      destruct (LN_eq_sub_ht D1
               (list_rearr4 _ _ _ _ _ _ _ _ _ )) as [D1' Ht1'];
      rewrite Ht1' in *; clear Ht1'.

Ltac LN_rewrite_ht5 D1 D1' Ht1' := 
      destruct (LN_eq_sub_ht D1
               (list_rearr5 _ _ _ _ _ _ _ _)) as [D1' Ht1'];
      rewrite Ht1' in *; clear Ht1'.

Ltac ht_admis_ex1_ImpR_IH IHn D1 D2 HD2 :=
      destruct (IHn _ (Nat.eq_le_incl _ _ eq_refl)
                    _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].

Ltac LN_rewrite_ht6 D1 D1' Ht1' := 
          destruct (LN_eq_sub_ht D1
               (list_rearr6 _ _ _ _ _ _ _ _)) as [D1' Ht1'];
          rewrite Ht1' in *; clear Ht1'.

Ltac LN_rewrite_ht7 D2 D2' Ht2' := 
      destruct (LN_eq_sub_ht D2
               (list_rearr7 _ _ _ _ _ _ _ _)) as [D2' Ht2'];
      rewrite Ht2' in *; clear Ht2'.

Ltac LN_rewrite_ht8 D1 D1' Ht1' := 
      destruct (LN_eq_sub_ht D1
               (list_rearr8 _ _ _ _ _ _ _ _)) as [D1' Ht1'];
      rewrite Ht1' in *; clear Ht1'.

Ltac LN_rewrite_ht9 D2 D2' Ht2' := 
      destruct (LN_eq_sub_ht D2
               (list_rearr9 _ _ _ _ _ _ _ _)) as [D2' Ht2'];
      rewrite Ht2' in *; clear Ht2'.

Ltac LN_rewrite_ht10 D1 D1' Ht1' := 
destruct (LN_eq_sub_ht D1
               (list_rearr10 _ _ _ _ _ _ _ _ _)) as [D1' Ht1'];
        rewrite Ht1' in *; clear Ht1'.

Ltac LN_rewrite_ht11 D2 D2' Ht2' := 
      destruct (LN_eq_sub_ht D2
               (list_rearr11 _ _ _ _ _ _ _ _ _ )) as [D2' Ht2'];
      rewrite Ht2' in *; clear Ht2'.

Ltac LN_rewrite_ht12 D1 D1' Ht1' :=
  destruct (LN_eq_sub_ht D1 (app_assoc_reverse _ _ _)) as [D1' Ht1'];
  rewrite Ht1' in *; clear Ht1'.

Ltac LN_rewrite_ht13 D2 D2' Ht2' := 
    destruct (LN_eq_sub_ht D2
              (list_rearr13 _ _ _ _)) as [D2' Ht2'];
      rewrite Ht2' in *; clear Ht2'.

(* Height admissible exchange on the left *)

(* Lemma for the base cases. *)
Lemma in_exch : forall {A : Type} (l1 l2 : list A) a b c,
  In a (l1 ++ b :: c :: l2) ->
  In a (l1 ++ c :: b :: l2).
Proof.
  intros A l1 l2 a b c P1.
  apply in_or_app. 
  apply in_app_or in P1. destruct P1 as [P1 | P1].
  left. assumption.
  right. apply in_inv in P1. destruct P1 as [P1 | P1]. apply in_cons.
  rewrite P1. apply in_eq. apply in_inv in P1. destruct P1 as [P1 | P1].
  rewrite P1. apply in_eq. do 2 apply in_cons. assumption.
Qed.

(* Weakening for ImpL *)
Lemma ht_admis_ex1_ImpL : forall n G H Γ1 Γ2 Δ  A B δ
                                 E F Γ3 Γ4 Δ1 Δ2 δ0 G0 H0
                                 (  D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H)
                                 (  D1 : LN|- G0 ++ (Γ3 ++ F :: Γ4, Δ1 ++ Δ2, δ0) :: H0)
                                 (  D2 : LN|- G0 ++ (Γ3 ++ Γ4, Δ1 ++ E :: Δ2, δ0) :: H0),
    (forall m : nat,
        m <= n ->
        forall (G H : list (list PropF * list PropF * dir)) (Γ1 Γ2 Δ : list PropF)
               (A B : PropF) (δ : dir) (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
          LNheight D = m ->
          exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= m) ->

    G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H =
    G0 ++ (Γ3 ++ E → F :: Γ4, Δ1 ++ Δ2, δ0) :: H0 ->
    Init.Nat.max (LNheight D1) (LNheight D2) = n ->
    exists D0 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D0 <= S n.
Proof.
  intros until 0. intros D D1 D2 IHn P1 P2.
  apply partition_2_2 in P1.
  destruct P1 as [ [l5 [Heq1 Heq2]] | [[Heq1 [Heq2 Heq3]] | [l5 [Heq1 Heq2]]]].
  * subst G H0.
    pose proof (Nat.le_max_r (LNheight D1) (LNheight D2)) as P3.
    pose proof (Nat.le_max_l (LNheight D1) (LNheight D2)) as P4.
    rewrite P2 in *. 
    generalize dependent D1. generalize dependent D2. 
    rewrite app_cons_single. rewrite (app_assoc _ l5). intros D2 Ht2.
    rewrite app_cons_single. rewrite (app_assoc _ l5). intros D1 Hmax Ht1.
    destruct (IHn _ Ht1 _ _ _ _ _ _ _ _ _ eq_refl) as [D1' Ht1'].
    destruct (IHn _ Ht2 _ _ _ _ _ _ _ _ _ eq_refl) as [D2' Ht2'].
    generalize dependent D1'.
    generalize dependent D2'.
    do 2 rewrite <- app_assoc. simpl.  intros D2' Ht2'.
    do 2 rewrite <- app_assoc. simpl. intros D1' Ht1'.
    rewrite <- app_assoc. simpl.
    exists (LNImpL _ _ _ _ _ _ _ _ _ D1' D2').
    simpl. apply le_n_S. rewrite <- Hmax.
    apply Nat.max_le_compat;  assumption.

  * subst G0 H0. inversion Heq2 as [[P1 P3 P4]].
    subst δ0 Δ. apply partition_2_3 in P1.
    destruct P1 as [ [P1 PP2] | [ [l5 [P1 PP2]] | [ [P1 PP2] | [ [P1 PP2] | [l5  [P1 PP2] ]]]]].
    **  subst Γ3. inversion PP2. subst A Γ4. 
        pose proof (Nat.le_max_l (LNheight D1) (LNheight D2)) as Ht.
        rewrite P2 in Ht.
        destruct (IHn _ Ht _ _ _ _ _ _ _ _ D1 eq_refl) as [D1' P3].
        generalize dependent D1'. rewrite (app_cons_single _ _ B).
        intros D1' P3. generalize dependent D2.
        rewrite (app_cons_single _ _ B). intros D2 P2.
        rewrite (app_cons_single _ _ B).
        exists (LNImpL _ _ _ _ _ _ _ _  _ D1' D2).
        simpl. apply le_n_S. rewrite <- P2.
        apply Nat.max_le_compat. assumption.
        apply Nat.le_refl.
    ** subst Γ1. destruct l5.
       (* l5 = nil *)
       simpl in *. inversion PP2.
       subst A Γ4. rewrite <- (app_assoc _ []).
       simpl in *.
       pose proof (Nat.le_max_l (LNheight D1) (LNheight D2)) as P3.
       rewrite P2 in P3.
       destruct (IHn _ P3 _ _ _ _ _ _ _ _ D1 eq_refl) as [D1' P4].
       generalize dependent D1'. rewrite (app_cons_single _ _ B).
       intros D1' HD1'. generalize dependent D2.
       rewrite (app_cons_single _ _ B).
       intros D2 HD2.
       rewrite (app_cons_single _ _ B).
       exists  (LNImpL _ _ _ _ _ _ _ _ _ D1' D2).
       simpl. apply le_n_S. rewrite <- HD2.
       apply Nat.max_le_compat. assumption.
       apply Nat.le_refl.

       (* l5 = cons *)
       simpl in PP2. inversion PP2. subst p Γ4.
       pose proof (Nat.le_max_l (LNheight D1) (LNheight D2)) as P3.
       pose proof (Nat.le_max_r (LNheight D1) (LNheight D2)) as P4.            
       rewrite P2 in *.
       generalize dependent D1.
       rewrite (app_cons_single _ _ F). rewrite (app_assoc _ l5).
       intros D1 HD HD1.
       generalize dependent D2.
       rewrite (app_assoc _ l5).
       intros D2 HD2 Hmax.                   
       destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D1' HD1'].
       destruct (IHn _ HD2 _ _ _ _ _ _ _ _ D2 eq_refl) as [D2' HD2'].
       generalize dependent D1'.
       rewrite <- (app_assoc _ l5). rewrite <- app_assoc.
       simpl. intros D1' HD1'.
       generalize dependent D2'. rewrite <- app_assoc.
       intros D2' HD2'. rewrite <- app_assoc. simpl.
       exists (LNImpL _ _ _ _ _ _ _ _ _ D1' D2').
       simpl. apply le_n_S. rewrite <- Hmax.
       apply Nat.max_le_compat; assumption.
    ** subst Γ3. inversion PP2. subst B Γ4.
       generalize dependent D1.
       rewrite <- app_assoc. simpl. intros D1 HD1.
       generalize dependent D2.
       rewrite <- app_assoc. simpl. intros D2 HD2.
       pose proof (Nat.le_max_l (LNheight D1) (LNheight D2)) as P3.
       pose proof (Nat.le_max_r (LNheight D1) (LNheight D2)) as P4.
       rewrite HD2 in *.
       destruct (IHn _ P3 _ _ _ _ _ _ _ _ D1 eq_refl) as [D1' HD1'].
       exists  (LNImpL _ _ _ _ _ _ _ _ _ D1' D2).
       simpl. apply le_n_S.  rewrite <- HD2.
       apply Nat.max_le_compat. assumption.
       apply Nat.le_refl.
    ** subst Γ3 Γ2. 
       generalize dependent D1.
       rewrite <- app_assoc. simpl. intros D1 HD1.
       generalize dependent D2.
       rewrite <- app_assoc. simpl. intros D2 HD2.
       pose proof (Nat.le_max_l (LNheight D1) (LNheight D2)) as P3.
       pose proof (Nat.le_max_r (LNheight D1) (LNheight D2)) as P4.
       rewrite HD2 in *.
       destruct (IHn _ P3 _ _ _ _ _ _ _ _ D1 eq_refl) as [D1' HD1'].
       destruct (IHn _ P4 _ _ _ _ _ _ _ _ D2 eq_refl) as [D2' HD2'].
       generalize dependent D1'.
       rewrite (app_cons_single _ _ B).
       rewrite (app_cons_single _ _ A).
       intros D1' HD1'. 
       generalize dependent D2'.
       rewrite (app_cons_single _ _ B).
       rewrite (app_cons_single _ _ A).
       intros D2' HD2'.             
       rewrite (app_cons_single _ _ B).
       rewrite (app_cons_single _ _ A).
       exists (LNImpL _ _ _ _ _ _ _ _ _ D1' D2').
       simpl. apply le_n_S.  rewrite <- HD2.
       apply Nat.max_le_compat; assumption.
    ** subst Γ3 Γ2. 
       generalize dependent D1. simpl.
       rewrite <- app_assoc. simpl.
       intros D1 HD1.
       generalize dependent D2. simpl.
       rewrite <- app_assoc. simpl.
       intros D2 HD2.
       pose proof (Nat.le_max_l (LNheight D1) (LNheight D2)) as P3.
       pose proof (Nat.le_max_r (LNheight D1) (LNheight D2)) as P4.
       rewrite HD2 in *.
       destruct (IHn _ P3 _ _ _ _ _ _ _ _ D1 eq_refl) as [D1' HD1'].
       destruct (IHn _ P4 _ _ _ _ _ _ _ _ D2 eq_refl) as [D2' HD2'].
       generalize dependent D1'.
       rewrite (app_cons_single _ _ B).
       rewrite (app_cons_single _ _ A).
       rewrite (app_assoc _ l5).
       intros D1' HD1'. 
       generalize dependent D2'.
       rewrite (app_cons_single _ _ B).
       rewrite (app_cons_single _ _ A).
       rewrite (app_assoc _ l5).
       intros D2' HD2'. 
       rewrite (app_cons_single _ _ B).
       rewrite (app_cons_single _ _ A).
       rewrite (app_assoc _ l5).
       exists (LNImpL _ _ _ _ _ _ _ _ _ D1' D2').
       simpl. apply le_n_S. rewrite <- HD2.
       apply Nat.max_le_compat; assumption.
  * subst H G0.
    generalize dependent D2.
    rewrite <- app_assoc. simpl.
    intros D2 HD2.
    generalize dependent D1.
    rewrite <- app_assoc. simpl.
    intros D1 HD1.
    pose proof (Nat.le_max_l (LNheight D1) (LNheight D2)) as P3.
    pose proof (Nat.le_max_r (LNheight D1) (LNheight D2)) as P4.
    rewrite HD1 in *.
    destruct (IHn _ P3 _ _ _ _ _ _ _ _ D1 eq_refl) as [D1' HD1'].
    destruct (IHn _ P4 _ _ _ _ _ _ _ _ D2 eq_refl) as [D2' HD2'].
    generalize dependent D1'.
    rewrite (app_cons_single G).
    rewrite (app_assoc _ l5).
    intros D1' HD1'.
    generalize dependent D2'.
    rewrite (app_cons_single G).
    rewrite (app_assoc _ l5).
    intros D2' HD2'.
    rewrite (app_cons_single G).
    rewrite (app_assoc _ l5).
    exists (LNImpL _ _ _ _ _ _ _ _ _  D1' D2').
    simpl. apply le_n_S.  rewrite <- HD1.
    apply Nat.max_le_compat; assumption.
Qed.

(* Weakening for ImpR *)
Lemma ht_admis_ex1_ImpR : forall n G H Γ1 Γ2 Δ  A B δ
(  D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
(forall m : nat,
        m <= n ->
        forall (G H : list (list PropF * list PropF * dir)) (Γ1 Γ2 Δ : list PropF)
          (A B : PropF) (δ : dir) (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
        LNheight D = m ->
        exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= m) ->
( exists
         (A0 B0 : PropF) (Γ3 Γ4 Δ1 Δ2 : list PropF) (δ0 : dir) 
       (G0 H0 : list (list PropF * list PropF * dir)) (D1 : LN|- 
                                                            G0 ++
                                                            (Γ3 ++ A0 :: Γ4,
                                                            Δ1 ++ B0 :: Δ2, δ0) :: H0),
         G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H =
         G0 ++ (Γ3 ++ Γ4, Δ1 ++ A0 → B0 :: Δ2, δ0) :: H0 /\ LNheight D1 = n) ->
exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= S n.
Proof.
  intros n G H Γ1 Γ2 Δ A B δ D IHn
         [E [F [Γ3 [Γ4 [Δ1 [Δ2 [δ0 [G0 [H0 [D1 [P1 P2]]]]]]]]]]].
  subst n. ap_part_2_2 P1 l5 P3 P4 P5.  
  + subst G H0.
    LN_rewrite_ht1 D1 D1' Ht1'.
    ht_admis_ex1_ImpR_IH IHn D1' D2 HD2.
    LN_rewrite_ht2 D2 D2' Ht2'.
    rewrite <- app_assoc. simpl.
    exists (LNImpR _ _ _ _ _ _ _ _ _ D2').
    finish_ht_admis_ex1.
  + subst G0 H0. inversion P4 as [[P5 P6 P7]].
    subst δ0 Δ. ap_part_2_3 P5 l5 P55.
    * subst Γ3 Γ4.
      LN_rewrite_ht4 D1 D1' Ht1'.
      ht_admis_ex1_ImpR_IH IHn D1' D2 HD2.
      LN_rewrite_ht5 D2 D2' Ht2'.
      exists (LNImpR _ _ _ _ _ _ _ _ _ D2').  
      finish_ht_admis_ex1.
    * subst Γ1 Γ4.
      LN_rewrite_ht6 D1 D1' Ht1'.
      ht_admis_ex1_ImpR_IH IHn D1' D2 HD2.
      LN_rewrite_ht7 D2 D2' Ht2'.
      rewrite <- app_assoc.
      exists (LNImpR _ _ _ _ _ _ _ _ _ D2').
      finish_ht_admis_ex1.
    * subst Γ3 Γ4.
      LN_rewrite_ht5 D1 D1' Ht1'.
      ht_admis_ex1_ImpR_IH IHn D1' D2 HD2.
      LN_rewrite_ht4 D2 D2' Ht2'.
      destruct (IHn _ HD2
                    _ _ _ _ _ _ _ _ D2' eq_refl) as [D3 HD3].
      LN_rewrite_ht5 D3 D3' Ht3'.
      exists (LNImpR _ _ _ _ _ _ _ _ _ D3').
      finish_ht_admis_ex3.
    * subst Γ3 Γ4.
      LN_rewrite_ht8 D1 D1' Ht1'.
      ht_admis_ex1_ImpR_IH IHn D1' D2 HD2.
      LN_rewrite_ht9 D2 D2' Ht2'.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      exists (LNImpR _ _ _ _ _ _ _ _ _ D2').
      finish_ht_admis_ex1.
    * subst Γ3 Γ2.
      LN_rewrite_ht10 D1 D1' Ht1'.
      ht_admis_ex1_ImpR_IH IHn D1' D2 HD2.
      LN_rewrite_ht11 D2 D2' Ht2'.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).      
      rewrite (app_assoc _ l5).
      exists (LNImpR _ _ _ _ _ _ _ _ _ D2').
      finish_ht_admis_ex1.
  + subst G0 H.
    LN_rewrite_ht12 D1 D1' Ht1'.
    ht_admis_ex1_ImpR_IH IHn D1' D2 HD2.
    LN_rewrite_ht13 D2 D2' Ht2'.
    rewrite list_rearr13.
    exists (LNImpR _ _ _ _ _ _ _ _ _ D2').
    finish_ht_admis_ex1.
Qed.

(* Old proof. *)

(*
Proof.
  intros n G H Γ1 Γ2 Δ A B δ D IHn
         [E [F [Γ3 [Γ4 [Δ1 [Δ2 [δ0 [G0 [H0 [D1 [P1 P2]]]]]]]]]]].
  apply partition_2_2 in P1. subst n.
  destruct P1 as [ [l5 [P3 P4]] | [ [P3 [P4 P5]] |  [l5 [P3 P4]]]].
  + subst G H0. generalize dependent D1.
    rewrite app_cons_single.
    rewrite app_assoc. intros D1 IHn.
    destruct (IHn _  (Nat.eq_le_incl _ _ eq_refl)  _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
    generalize dependent D2.
    rewrite <- app_assoc. rewrite <- app_cons_single.
    intros D2 HD2. rewrite <- app_assoc. simpl.
    exists (LNImpR _ _ _ _ _ _ _ _ _ D2).
    simpl. apply le_n_S. assumption.
  + subst G0 H0. inversion P4 as [[P5 P6 P7]].
    subst δ0 Δ. apply partition_2_3 in P5.
    destruct P5 as [ [P5 PP5] | [ [l5 [P5 PP5]] | [[P5 PP5] | [[P5 PP5] | [l5 [P5 PP5]]]]]].
    * subst Γ3 Γ4.
      generalize dependent D1. rewrite (app_cons_single _ _ E).
      intros D1 HD1. pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2. rewrite <- app_assoc.
      simpl. intros D2 HD2. exists (LNImpR _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S.  rewrite <- HD1'. assumption.    
    * subst Γ1 Γ4. generalize dependent D1.
      rewrite (app_cons_single Γ3).
      rewrite (app_assoc _ l5). intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      rewrite HD1' in HD2.
      generalize dependent D2. do 3  rewrite <- app_assoc.
      simpl. intros D2 HD2. exists (LNImpR _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. assumption.
    * subst Γ3 Γ4. generalize dependent D1.
      rewrite <- app_assoc. simpl.
      intros D1 HD1. pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2. rewrite (app_cons_single _ _ E).
      intros D2 HD2. rewrite  HD1' in HD2.
      destruct (IHn _ HD2 _ _ _ _ _ _ _ _ D2 eq_refl) as [D3 HD3].
      generalize dependent D3. rewrite <- app_assoc.
      simpl. intros D3 HD3.
      exists (LNImpR _ _ _ _ _ _ _ _ _ D3).
      simpl. apply le_n_S. apply (Nat.le_trans _ _ _ HD3 HD2).
    * subst Γ3 Γ4.
      generalize dependent D1. rewrite <- app_assoc.
      simpl. intros D1 HD1. pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      intros D2 HD2. 
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      exists (LNImpR _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. apply (Nat.le_trans _ _ _ HD2 HD1).
    * subst Γ3 Γ2.  generalize dependent D1.
      rewrite <- app_assoc. simpl.
      intros D1 HD1. pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite (app_assoc _ l5). intros D2 HD2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).      
      rewrite (app_assoc _ l5).
      exists (LNImpR _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. apply (Nat.le_trans _ _ _ HD2 HD1).
  + subst G0 H. generalize dependent D1.
    rewrite <- app_assoc. simpl. intros D1 HD1.
    pose proof HD1 as HD1'.
    apply Nat.eq_le_incl in HD1.
    destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
    generalize dependent D2.
    rewrite (app_cons_single G).
    rewrite (app_assoc _ l5).
    intros D2 HD2.
    rewrite (app_cons_single G).
    rewrite (app_assoc _ l5).
    exists (LNImpR _ _ _ _ _ _ _ _ _ D2).
    simpl. apply le_n_S. apply (Nat.le_trans _ _ _ HD2 HD1).
Qed.
*)

(* Weakening for WBR *)
Lemma ht_admis_ex1_WBR : forall n G H Γ1 Γ2 Δ  A B δ,
    forall  (IHn : forall m : nat,
                m <= n ->
                forall (G H : list (list PropF * list PropF * dir)) (Γ1 Γ2 Δ : list PropF)
                       (A B : PropF) (δ : dir) (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
                  LNheight D = m ->
                  exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= m)
            (  D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
      ( exists
          (A0 : PropF) (Γ Δ1 Δ2 : list PropF) (δ0 : dir) (G0 : 
                                                            list
                                                              (list PropF * list PropF * dir)) 
          (D1 : LN|- G0 ++ [(Γ, Δ1 ++ [.] A0 :: Δ2, fwd); ([], [A0], δ0)]),
          G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H = G0 ++ [(Γ, Δ1 ++ [.] A0 :: Δ2, δ0)] /\
          LNheight D1 = n) ->
      exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= S n.
Proof.
  intros n G H Γ1 Γ2 Δ A B δ IHn D [C [Γ [Δ1 [Δ2 [δ0 [G0 [D1 [P1 P2]]]]]]]].
  pose proof P1 as P1'.
  apply partition_2_2 in P1'.
  destruct P1' as [ [l5 [P3 P4]] | [ [P3 [P4 P5]] | [l5 [P3 P4]]]].
  + subst G. destruct l5; discriminate.
  + subst G0 H. inversion P4 as [[P5 P6 P7]].
    subst δ0 Δ Γ. pose proof P2 as P2'.
    apply Nat.eq_le_incl in P2. 
    destruct (IHn _ P2 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
    exists (LNWBR _ _ _ _ _ _ D2).
    simpl. apply le_n_S. rewrite <- P2'. assumption.
  + subst H G0. app_assoc_hyp_inv G P1.
    generalize dependent D1. rewrite <- app_assoc. simpl.
    intros D1 HD1. pose proof HD1 as HD1'.
    apply Nat.eq_le_incl in HD1.
    destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
    generalize dependent D2.  rewrite app_cons_single.
    rewrite (app_assoc _ l5).
    intros D2 HD2. rewrite app_cons_single.
    rewrite (app_assoc _ l5). 
    exists (LNWBR _ _ _ _ _ _ D2).
    simpl. apply le_n_S. rewrite <- HD1'. assumption.
Qed.

Lemma ht_admis_ex1_WBL : forall n G H Γ1 Γ2 Δ  A B δ
   (IHn : forall m : nat,
       m <= n ->
       forall (G H : list (list PropF * list PropF * dir)) (Γ1 Γ2 Δ : list PropF)
              (A B : PropF) (δ : dir) (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
         LNheight D = m ->
         exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= m)
   (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
    (exists
        (A0 : PropF) (Γ3 Γ4 Γ5 Γ6 Δ1 Δ2 : list PropF) (δ0 : dir)
        (G0 H0 : list (list PropF * list PropF * dir))
        (D1 : LN|- G0 ++ (Γ3 ++ [.] A0 :: Γ4, Δ1, fwd) :: 
                     (Γ5 ++ A0 :: Γ6, Δ2, δ0) :: H0),
        G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H =
        G0 ++ (Γ3 ++ [.] A0 :: Γ4, Δ1, fwd) :: (Γ5 ++ Γ6, Δ2, δ0) :: H0 /\
        LNheight D1 = n) ->
    exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= S n.
Proof.
  intros n G H Γ1 Γ2 Δ A B δ IHn D [C [Γ3 [Γ4 [Γ5 [Γ6 [Δ1 [Δ2 [δ0 [G0 [H0 [D1 [P1 P2]]]]]]]]]]]].
  pose proof P1 as P1'.
  apply partition_2_2 in P1'.
  destruct P1' as [ [l5 [P3 P4]] | [ [P3 [P4 P5]] | [l5 [P3 P4]]]].
  + subst G.
    destruct l5. simpl in *. inversion P4 as [[P5 P6]].
    subst Δ δ0 H0. symmetry in P5.
    pose proof P5 as P5'. apply partition_2_3 in P5.
    destruct P5 as [[P5 PP5] | [ [l5 [P5 PP5]] | [[P5 PP5] | [[P5 PP5] | [l5 [P5 PP5]]]]]].
    * subst Γ5 Γ6.
      generalize dependent D1. rewrite app_cons_single.
      rewrite (app_cons_single _ _ C). intros D1 HD1.
      pose proof HD1. apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2. rewrite <- app_assoc.
      rewrite <- app_assoc. simpl. intros D2 HD2.
      rewrite <- app_assoc.
      simpl. exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.
    * subst Γ1 Γ6. generalize dependent D1.
      rewrite app_cons_single. rewrite (app_cons_single _ _ C).
      rewrite (app_assoc _ l5).
      intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2.
      do 3 rewrite <- app_assoc. simpl. intros D2 HD2.
      do 2 rewrite <- app_assoc. simpl.
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.
    * subst Γ5 Γ6. generalize dependent D1.
      rewrite (app_cons_single G0).
      intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2.
      rewrite <- (app_cons_single _ _ A).
      intros D2 HD2. subst n.
      destruct (IHn _ HD2 _ _ _ _ _ _ _ _ D2 eq_refl) as [D3 HD3].
      generalize dependent D3.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite <- (app_assoc G0).
      intros D3 HD3.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite <- (app_assoc G0).
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D3).
      simpl. apply le_n_S. apply (le_trans _ _ _ HD3 HD2).
    * subst Γ5 Γ6.
      generalize dependent D1.
      rewrite (app_cons_single G0).
      rewrite <- (app_assoc Γ1).
      simpl. intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite <- (app_assoc G0).
      intros D2 HD2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite <- (app_assoc G0).      
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.
    * subst Γ5 Γ2. generalize dependent D1.
      rewrite <- (app_assoc Γ1).
      simpl. rewrite (app_cons_single G0).
      intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2.
      rewrite <- (app_assoc G0).
      simpl. rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite (app_assoc _ l5).
      intros D2 HD2. 
      rewrite <- (app_assoc G0).
      simpl. rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite (app_assoc _ l5).
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.

    * simpl in P4. inversion P4 as [[P5 P6]].
      subst p H0. generalize dependent D1.
      rewrite (app_cons_single G0).
      rewrite (app_cons_single).
      rewrite (app_assoc _ l5).
      intros D1 HD1. 
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2.
      do 3 rewrite <- app_assoc. simpl.
      intros D2 HD2.
      rewrite <- app_assoc. simpl.
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.
  + subst G0 H.
    inversion P4 as [[P5 P6 P7]].
    subst δ Δ1. apply partition_2_3 in P5.
    destruct P5 as [ [P5 PP5] | [ [l5 [ P5 PP5]] | [[P5 PP5] | [ [P5 PP5] | [l5 [P5 PP5]]]]]].
    * subst Γ3. inversion PP5. subst A Γ4.
      pose proof P2 as HD1'.
      apply Nat.eq_le_incl in P2.
      destruct (IHn _ P2 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      generalize dependent D2.
      rewrite (app_cons_single Γ1). intros D2 HD2.
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.
    * subst Γ1.  destruct l5.
      ** simpl in *. inversion PP5. subst A Γ4.
         rewrite <- (app_assoc Γ3). simpl.
         pose proof P2 as HD1'.
         apply Nat.eq_le_incl in P2.
         destruct (IHn _ P2 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
         generalize dependent D2. rewrite (app_cons_single _ _ B).
         intros D2 HD2.
         exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
         simpl. apply le_n_S. subst n. assumption.
      ** simpl in PP5. inversion PP5. subst p Γ4. 
         generalize dependent D1.
         rewrite (app_cons_single Γ3).
         rewrite (app_assoc _ l5).
         intros D1 HD1.
         pose proof HD1 as HD1'.
         apply Nat.eq_le_incl in HD1.
         destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
         generalize dependent D2.
         do 2 rewrite <- app_assoc.  simpl. intros D2 HD2.
         rewrite <- app_assoc. 
         exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
         simpl. apply le_n_S. subst n. assumption.
    * subst Γ3. inversion PP5. subst B Γ4.  
      generalize dependent D1.
      rewrite <- app_assoc.
      simpl. intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.
    * subst Γ3 Γ2. inversion P4. app_assoc_hyp_inv Γ1 H1.
      generalize dependent D1.
      rewrite <- app_assoc. simpl.
      intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
      generalize dependent D2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      intros D2 HD2.
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.
    * subst Γ3 Γ2. inversion P4. 
      generalize dependent D1.
      rewrite <- app_assoc. simpl. intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
      generalize dependent D2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite (app_assoc _ l5).
      intros D2 HD2.
      exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
      simpl. apply le_n_S. subst n. assumption.
  + subst G0 H. generalize dependent D1.
    rewrite <- app_assoc. simpl. intros D1 HD1.
    pose proof HD1 as HD1'.
    apply Nat.eq_le_incl in HD1.
    destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
    generalize dependent D2.
    rewrite (app_cons_single G).
    rewrite (app_assoc _ l5).
    intros D2 HD2.
    rewrite (app_cons_single G).
    rewrite (app_assoc _ l5).
    exists (LNWBL _ _ _ _ _ _ _ _ _ _ D2).
    simpl. apply le_n_S. subst n. assumption.
Qed.      

Lemma ht_admis_ex1_WBRe : forall n G H Γ1 Γ2 Δ  A B δ
       (IHn : forall m : nat,   m <= n ->
                forall (G H : list (list PropF * list PropF * dir)) (Γ1 Γ2 Δ : list PropF)
                       (A B : PropF) (δ : dir) (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
                  LNheight D = m ->
                  exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= m)
       (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
    (exists
        (A0 : PropF) (Γ3 Γ4 Γ5 Γ6 Δ1 Δ2 : list PropF) (δ0 : dir) 
        (G0 : list (list PropF * list PropF * dir))
        (D1 : LN|- G0 ++ [(Γ3 ++ A0 :: Γ4, Δ1, δ0)]),
        G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H =
        G0 ++ [(Γ3 ++ Γ4, Δ1, bac); (Γ5 ++ [.] A0 :: Γ6, Δ2, δ0)] /\ 
        LNheight D1 = n) ->
    exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= S n.
Proof.
  intros n G H Γ1 Γ2 Δ A B δ IHn D [A0 [Γ3 [Γ4 [Γ5 [Γ6 [Δ1 [Δ2 [δ0 [G0 [D1 [P1 P2]]]]]]]]]]].
  pose proof P1 as P1'. rewrite (app_cons_single G0) in P1.
  apply partition_2_2 in P1'.
  destruct P1' as [ [l5 [P3 P4]] | [ [P3 [P4 P5]] | [l5 [P3 P4]]]].
  - subst G. destruct l5. simpl in P4. inversion P4. subst Δ2 δ0 H.
    apply partition_2_2 in H1.
    destruct H1 as [ [l5 [P3 P5]] | [ [P3 [P5 P6]] |  [l5 [P3 P5]]]].
    + subst Γ5. destruct l5. simpl in *.
      inversion P5. subst B Γ6. rewrite <- app_assoc.
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D1). simpl.
      apply le_n_S. apply Nat.eq_le_incl. assumption.
      simpl in P5. inversion P5. subst p Γ2.
      rewrite <- app_assoc. simpl. rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A). rewrite (app_assoc _ l5).
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D1). simpl.
      apply le_n_S. apply Nat.eq_le_incl. assumption.
    + subst Γ5 A Γ6. rewrite <- app_assoc.
      rewrite (app_cons_single _ _ B).
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D1). simpl.
      apply le_n_S. apply Nat.eq_le_incl. assumption.
    + subst Γ1 Γ6. do 2 rewrite <- app_assoc. simpl.      
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D1). simpl.
      apply le_n_S. apply Nat.eq_le_incl. assumption.
    + simpl in P4. inversion P4. destruct l5; discriminate.      

  - subst G0 H. inversion P4 as [[P5 P6 P7]].
    subst Δ1. apply partition_2_3 in P5.
    destruct P5 as [ [P5 PP5] | [ [l5 [P5 PP5]] | [[P5 PP5] | [[P5 PP5] | [l5 [P5 PP5]]]]]].
    + subst Γ3 δ Γ4. generalize dependent D1. 
      rewrite (app_cons_single _ _ A0). intros D1 HD1.
      pose proof HD1 as HD1'. apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
      generalize dependent D2. rewrite <- app_assoc.
      intros D2 HD2.
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D2). simpl.
      apply le_n_S. subst n. assumption.
    + subst Γ1 δ Γ4. generalize dependent D1.
      rewrite (app_cons_single _ _ A0).
      rewrite (app_assoc _ l5).
      intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
      generalize dependent D2. do 2 rewrite <- app_assoc.
      simpl. intros D2 HD2. rewrite <- app_assoc.
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D2). simpl.
      apply le_n_S. subst n. assumption.
    + subst δ Γ3 Γ4. pose proof P2 as HD1'.
      apply Nat.eq_le_incl in P2.
      destruct (IHn _ P2 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
      generalize dependent D2. rewrite <- app_assoc.
      simpl. intros D2 HD2. subst n.
      destruct (IHn _ HD2 _ _ _ _ _ _ _ _ D2 eq_refl) as [D3 HD3].      
      generalize dependent D3.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      intros D3 HD3.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D3). simpl.
      apply le_n_S. apply (le_trans _ _ _ HD3 HD2).
    + subst δ Γ3 Γ4. 
      generalize dependent D1.
      rewrite <- app_assoc. simpl. intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
      generalize dependent D2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      intros D2 HD2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D2). simpl.
      apply le_n_S. subst n. assumption.
    + subst δ Γ3 Γ2. generalize dependent D1.
      rewrite <- app_assoc.
      simpl. intros D1 HD1.
      pose proof HD1 as HD1'.
      apply Nat.eq_le_incl in HD1.
      destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
      generalize dependent D2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite (app_assoc _ l5).
      intros D2 HD2.
      rewrite (app_cons_single _ _ B).
      rewrite (app_cons_single _ _ A).
      rewrite (app_assoc _ l5).
      exists (LNWBRe _ _ _ _ _ _ _ _ _ D2). simpl.
      apply le_n_S. subst n. assumption.
  - subst G0 H. generalize dependent D1.
    rewrite <- app_assoc. simpl. intros D1 HD1.
    pose proof HD1 as HD1'.
    apply Nat.eq_le_incl in HD1.
    destruct (IHn _ HD1 _ _ _ _ _ _ _ _ D1 eq_refl) as [D2 HD2].      
    generalize dependent D2.
    rewrite (app_cons_single G). rewrite (app_assoc _ l5).
    intros D2 HD2.
    rewrite (app_cons_single G). rewrite (app_assoc _ l5).
    exists (LNWBRe _ _ _ _ _ _ _ _ _ D2). simpl.
    apply le_n_S. subst n. assumption.
Qed.

Lemma ht_admis_ex1_BBL : forall n G H Γ1 Γ2 Δ  A B δ
  (IHn : forall m : nat,
        m <= n ->
        forall (G H : list (list PropF * list PropF * dir)) (Γ1 Γ2 Δ : list PropF)
          (A B : PropF) (δ : dir) (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
        LNheight D = m ->
        exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= m)
 ( D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
 ( exists
         (A0 : PropF) (Γ Δ1 Δ2 : list PropF) (δ0 : dir) (G0 : 
                                                         list
                                                           (list PropF * list PropF * dir)) 
       (D1 : LN|- G0 ++ [(Γ, Δ1 ++ [#] A0 :: Δ2, bac); ([], [A0], δ0)]),
         G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H = G0 ++ [(Γ, Δ1 ++ [#] A0 :: Δ2, δ0)] /\
         LNheight D1 = n) ->
 exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= S n.
Admitted.

Lemma ht_admis_ex1_BBR : forall n G H Γ1 Γ2 Δ  A B δ
  (IHn : forall m : nat,
        m <= n ->
        forall (G H : list (list PropF * list PropF * dir)) (Γ1 Γ2 Δ : list PropF)
          (A B : PropF) (δ : dir) (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
        LNheight D = m ->
        exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= m)
 ( D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
 ( exists
         (A0 : PropF) (Γ3 Γ4 Γ5 Γ6 Δ1 Δ2 : list PropF) (δ0 : dir) 
       (G0 H0 : list (list PropF * list PropF * dir)) (D1 : LN|- 
                                                            G0 ++
                                                            (Γ3 ++ [#] A0 :: Γ4, Δ1, bac)
                                                            :: 
                                                            (Γ5 ++ A0 :: Γ6, Δ2, δ0) :: H0),
         G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H =
         G0 ++ (Γ3 ++ [#] A0 :: Γ4, Δ1, bac) :: (Γ5 ++ Γ6, Δ2, δ0) :: H0 /\
         LNheight D1 = n) ->
 exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= S n.
Admitted.


Lemma ht_admis_ex1_BBRe : forall n G H Γ1 Γ2 Δ  A B δ
 ( IHn : forall m : nat,
        m <= n ->
        forall (G H : list (list PropF * list PropF * dir)) (Γ1 Γ2 Δ : list PropF)
          (A B : PropF) (δ : dir) (D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
        LNheight D = m ->
        exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= m)
 ( D : LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
 ( exists
         (A0 : PropF) (Γ3 Γ4 Γ5 Γ6 Δ1 Δ2 : list PropF) (δ0 : dir) 
       (G0 : list (list PropF * list PropF * dir)) (D1 : LN|- 
                                                         G0 ++ 
                                                         [(Γ3 ++ A0 :: Γ4, Δ1, δ0)]),
         G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H =
         G0 ++ [(Γ3 ++ Γ4, Δ1, bac); (Γ5 ++ [#] A0 :: Γ6, Δ2, δ0)] /\ 
         LNheight D1 = n) ->
 exists D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H, LNheight D2 <= S n.
  Admitted.

Lemma ht_admis_ex1 : forall n G H Γ1 Γ2 Δ A B δ
                            (D: LN|- G ++ (Γ1 ++ A :: B :: Γ2, Δ, δ) :: H),
    LNheight D = n ->
    exists (D2 : LN|- G ++ (Γ1 ++ B :: A :: Γ2, Δ, δ) :: H),
      LNheight D2 <= n.
Proof.
  intros n.
  induction n as [ | n IHn] using strong_induction ; intros until 0; intros HD.

  (* height of derivation equals 0 *)
  apply ht_eq_0 in HD.
  destruct HD as [ [C [Γ0 [Δ0 [G0 [H0 [δ0 [P1 [P2 P3]]]]]]]] |
                   [Γ0 [Δ0 [G0 [H0 [δ0 [P1 P2]]]]]]].
  - pose proof P1 as P1'. apply partition_2_2 in P1.
    + destruct P1 as [ [l5 [P4a P4b]] | [[P4a [P4b P4c]] | [l5 [P4a P4b]]]]; subst.
      * rewrite <- app_assoc.
        exists (LNId _ _ _ _ _ _ P2 P3). auto. 
      * inversion P4b as [[H1 H2 H3]]. subst.
        eexists (LNId _ _ _ _ _ _ _ P3). auto. 
        Unshelve. apply in_exch. assumption.
      * rewrite app_cons_single. rewrite app_assoc.
        exists (LNId _ _ _ _ _ _ P2 P3). auto.
  - pose proof P1 as P1'. apply partition_2_2 in P1.
    + destruct P1 as [ [l5 [P4a P4b]] | [[P4a [P4b P4c]] | [l5 [P4a P4b]]]]; subst.
      * rewrite <- app_assoc.
        exists (LNBot _ _ _ _ _ P2). auto. 
      * inversion P4b as [[H1 H2 H3]]. subst.
        eexists (LNBot  _ _ _ _ _ _). auto.
        Unshelve. apply in_exch. assumption.
      * rewrite app_cons_single. rewrite app_assoc.
        exists (LNBot _ _ _ _ _ P2). auto.

  (* height of derivation is greater than 0 *)
  - apply ht_eq_Sn in HD.
    destruct HD as [ [E [F [Γ3 [Γ4 [Δ1 [Δ2 [δ0 [G0 [H0 [D1 [D2 [P1 P2]]]]]]]]]]]]
                   | [H1
                     | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]].   
    + apply ht_admis_ex1_ImpL with (D1 := D1) (D2 := D2); assumption.
    + apply ht_admis_ex1_ImpR; assumption.
    + apply ht_admis_ex1_WBR; assumption.
    + apply ht_admis_ex1_WBL; assumption.
    + apply ht_admis_ex1_WBRe; assumption.
    + apply ht_admis_ex1_BBL; assumption.
    + apply ht_admis_ex1_BBR; assumption.
    + apply ht_admis_ex1_BBRe; assumption.
Qed.

Print Assumptions ht_admis_ex1.