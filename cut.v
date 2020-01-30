Require Import ssreflect.

Require Import genT.
Require Import ddT.
Require Import List_lemmasT.
Require Import lntT lntacsT lntlsT lntbRT lntmtacsT.
Require Import lntb1LT lntb2LT.
Require Import lntkt_exchT.
Require Import lnt_weakeningT.
Require Import lnt_contractionT.
Require Import existsT.
Require Import lnt_weakeningT lnt_contraction_mrT.


(* TACTICS *)


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
(*        | [ H : ?a :: [] = ?c :: [] |- _ ] => inversion H; subst *)
       | [ H : ?a :: ?b = ?c :: ?d |- _ ] => inversion H; subst
(*           | [ H : ?b :: ?c = [?a] |- _ ] => inversion H; subst
           | [ H : [?a] = ?b :: ?c |- _ ] => inversion H; subst
           | [ H : ?b :: ?c = [?a] |- _ ] => inversion H; subst
           | [ H : [?a] = [?b] |- _ ] => inversion H; subst
           | [ H : [?b] = [?a] |- _ ] => inversion H; subst
*)
           | [ H : ((?a,?b) = ?c) |- _ ] => inversion H; subst
           | [ H : ?c = (?a,?b) |- _ ] => inversion H; subst
                           end; clear_useless).

Ltac inversion_cons :=
  repeat match goal with
         | [ H : ?a :: ?l1 = ?b :: ?l2 |- _] => inversion H; subst; clear_useless
         end.

(* ------------------------- *)

(* STRUCTURAL EQUIVALENCE *)
                    
(* Use this one to help with full structural equivalence definition. *)
Inductive struct_equiv_str {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type :=
| se_nil2 : struct_equiv_str [] []
| se_step2 Γ1 Δ1 d Γ2 Δ2 ns1 ns2 ns3 ns4 :
    ns3 = ((Γ1, Δ1, d) :: ns1) ->
    ns4 = ((Γ2, Δ2, d) :: ns2) ->
    struct_equiv_str ns1 ns2 ->
    struct_equiv_str ns3 ns4.

(* Use this one for structural equivalence. *)
Inductive struct_equiv_weak {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type :=
| se_wk2_extL ns1 ns2 ns3 ns4 :
    ns4 = (ns1 ++ ns3) -> struct_equiv_str ns1 ns2 -> struct_equiv_weak ns4 ns2
| se_wk2_extR ns1 ns2 ns3 ns4 :
    ns4 = (ns2 ++ ns3) -> struct_equiv_str ns1 ns2 -> struct_equiv_weak ns1 ns4.

Inductive struct_equiv {V : Set} n1 n2 : Type :=
| se : @struct_equiv_weak V n1 n2 -> struct_equiv n1 n2.

Lemma struct_equiv_str_weak : forall {V : Set} G1 G2,
   @struct_equiv_str V G1 G2 -> @struct_equiv_weak V G1 G2.
Proof.
  intros V G1 G2 H.
  eapply se_wk2_extL in H. 2 : reflexivity.
  erewrite app_nil_r in H.  exact H.
Qed.

Lemma struct_equiv_str_length : forall {V : Set} G1 G2,
    @struct_equiv_str V G1 G2 -> length G1 = length G2.
Proof.
  induction G1; intros H2 H; destruct H2;
    subst; (reflexivity || inversion H).
  discriminate. discriminate. 
  subst. simpl. erewrite IHG1. reflexivity.
  inversion H1. inversion H0. subst.
  assumption.
Qed.

Lemma struct_equiv_weak_str : forall {V : Set} G1 G2,
    @struct_equiv_weak V G1 G2 -> length G1 = length G2 ->
    @struct_equiv_str V G1 G2.
Proof.
  intros V G1 G2 H1 H2.
  inversion H1; subst;
    rewrite app_length in H2.
  inversion H0; subst. simpl in *.
  apply length_zero_iff_nil in H2. subst.
  constructor.
  simpl; pose proof H4 as H4';
  eapply struct_equiv_str_length in H4;
  simpl in H2; rewrite H4 in H2;
  destruct ns3; simpl in *; [
  rewrite app_nil_r;  econstructor; try reflexivity; try assumption |
  firstorder ].

  inversion H0; subst. simpl in *.
  symmetry in H2.
  apply length_zero_iff_nil in H2. subst.
  constructor.
  simpl; pose proof H4 as H4';
  eapply struct_equiv_str_length in H4;
  simpl in H2; rewrite H4 in H2;
  destruct ns3; simpl in *; [
  rewrite app_nil_r;  econstructor; try reflexivity; try assumption |
  firstorder ].
Qed.

Lemma struct_equiv_weak_cons : forall {V : Set} l1 l2 a1 a2,
    struct_equiv_weak (a1::l1) (a2::l2) ->
    @struct_equiv_weak V l1 l2.
Proof.
  intros V l1 l2 a1 a2 H3.
  inversion H3 as [l3 H4 l4 H5 H6 H7 | H4 l3 l4 H5 H6 H7]; subst.
  destruct l3 as [| a ns1];
    inversion H7; try discriminate; subst.
  simpl in *. unfold rel in *.
  inversion_cons.
  econstructor. reflexivity. assumption.

  destruct l3 as [| a ns1];
    inversion H7; try discriminate; subst.
  simpl in *. unfold rel in *.
  inversion_cons.
  econstructor 2. reflexivity. assumption.
Qed.

Lemma struct_equiv_weak_cons_rev : forall {V : Set} l1 l2 a1 a2 b1 b2 d,
    @struct_equiv_weak V l1 l2 ->
    struct_equiv_weak ((a1,b1,d)::l1) ((a2,b2,d)::l2).
Proof.
  intros V l1 l2 a1 a2 b1 b2 d H3.
  inversion H3; subst.
  econstructor.
  rewrite cons_singleton. rewrite app_assoc.
  reflexivity.
  econstructor 2; try reflexivity. assumption.

  econstructor 2.  rewrite cons_singleton. rewrite app_assoc.
  reflexivity.
  econstructor 2; try reflexivity. assumption.
Qed.

Ltac struct_equiv_str_nil :=
  match goal with
  | [H : struct_equiv_str [] ?n |- _] => inversion H; discriminate
  | [H : struct_equiv_str ?n [] |- _] => inversion H; discriminate
  end.

Ltac struct_equiv_str_cons :=
  match goal with
  | [H : struct_equiv_str (?a :: ?la) (?b :: ?lb) |- _] => inversion H; subst
  end.

Lemma struct_equiv_weak_d : forall {V : Set} ns1 ns2 seq1 seq2 d1 d2,
    @struct_equiv_weak V ((seq1,d1)::ns1) ((seq2,d2)::ns2) ->
    d1 = d2.
Proof.
  intros until 0; intros H3.
  inversion H3 as [l3 H4 l4 H5 H6 H7 | H4 l3 l4 H5 H6 H7]; subst. 
  destruct l3. simpl in *.
  struct_equiv_str_nil.
  simpl in *.
  inversion_cons.
  struct_equiv_str_cons. 
  unfold rel in *. inversion_cons.
  reflexivity.
  
  destruct l3. simpl in *.
  struct_equiv_str_nil.
  simpl in *.
  inversion_cons.
  struct_equiv_str_cons. 
  unfold rel in *. inversion_cons.
  reflexivity.
Qed.  

Lemma struct_equiv_str_weak_equiv : forall {V : Set} G1 G2,
    iffT (@struct_equiv_str V G1 G2)
         (struct_equiv_weak G1 G2 * (length G1 = length G2)).
Proof.
  intros.
  split; intros HH. split. apply struct_equiv_str_weak.
  assumption. apply struct_equiv_str_length. assumption.
  apply struct_equiv_weak_str; apply HH.
Qed.

Lemma struct_equiv_weak_nil : forall (V : Set),
    @struct_equiv_weak V nil nil.
Proof.
  econstructor. erewrite app_nil_r.
  reflexivity. econstructor.
Qed.
  
Lemma struct_equiv_str_refl : forall {V : Set} G, @struct_equiv_str V G G.
Proof.
  induction G as [|a G IHG]. constructor.
  destruct a as [ [Γ Δ] d].
  econstructor 2. reflexivity.
  reflexivity. assumption.
Qed.

Lemma struct_equiv_weak_refl : forall {V : Set} G,
    @struct_equiv_weak V G G.
Proof.
  intros V G. econstructor.
  erewrite app_nil_r. reflexivity.
  apply struct_equiv_str_refl.
Qed.


(* --------------------------- *)

(* MERGE *)

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

(* ----------- *)
(* Equivalence *)
(* ----------- *)

(* Equality that ignores the last, irrelevant direction. *)
Inductive LNS_eq {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type :=
| LNS_eq_nil n1 n2 : n1 = [] -> n2 = [] -> LNS_eq n1 n2
| LNS_eq_base n1 n2 seq d1 d2 : n1 = [(seq,d1)] -> n2 = [(seq,d2)] -> LNS_eq n1 n2
| LNS_eq_step ns1 ns2 nseq1 nseq2 : nseq1 = nseq2 -> LNS_eq ns1 ns2 -> LNS_eq (nseq1 :: ns1) (nseq2 :: ns2).

Lemma LNS_eq_eq {V : Set} : forall n1 n2,
    n1 = n2 -> @LNS_eq V n1 n2.
Proof.
  intros n1 n2 H. subst. induction n2.
  econstructor. reflexivity. reflexivity.
  destruct n2. destruct a. econstructor 2.  reflexivity. reflexivity.
  econstructor 3. reflexivity.
  apply IHn2.
Qed.

Lemma LNS_eq_cons_same : forall {V : Set} l1 l2 a,
    LNS_eq (a :: l1) (a :: l2) -> @LNS_eq V l1 l2.
Proof.
  intros V l1 l2 a H.
  inversion H. discriminate.
  inversion H0. inversion H1. subst.
  econstructor. reflexivity. reflexivity.
  subst. assumption.
Qed.

Lemma LNS_eq_cons : forall {V : Set} l1 l2 a b,
    LNS_eq (a :: l1) (b :: l2) -> @LNS_eq V l1 l2.
Proof.
  intros V l1 l2 a b H.
  inversion H. discriminate.
  inversion H0. inversion H1. subst.
  econstructor. reflexivity. reflexivity.
  subst. assumption.
Qed.

Lemma LNS_eq_cons_hd : forall {V : Set} l1 l2 a b,
    @LNS_eq V (a :: l1) (b :: l2) -> (a = b) + ( (l1 = []) * (l2 = []) ).
Proof.
  intros V l1 l2 a b H.
  inversion H. discriminate.
  inversion H0. inversion H1. subst.
  firstorder. subst. firstorder.
Qed.

Lemma LNS_eq_refl : forall (V : Set) n, @LNS_eq V n n.
Proof.
  induction n. constructor; reflexivity.
  econstructor 3. reflexivity. assumption.
Qed.

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

(* ---------------------- *)
(* Contracted definitions *)
(* ---------------------- *)

Inductive contracted_multi {T : Type} : list T -> list T -> Type :=
| cont_multi_refl X : @contracted_multi T X X
(*| cont_multi_base X Y   : @contracted_gen T X Y -> contracted_multi X Y *)
| cont_multi_step X Y Z : @contracted_gen T X Y -> contracted_multi Y Z -> contracted_multi X Z.

Inductive contracted_multi_enum {T : Type} : list T -> list T -> nat -> Type :=
| cont_multi_enum_refl X : @contracted_multi_enum T X X 0
(*| cont_multi_base X Y   : @contracted_gen T X Y -> contracted_multi X Y *)
| cont_multi_enum_step X Y Z n : @contracted_gen T X Y -> contracted_multi_enum Y Z n -> contracted_multi_enum X Z (S n).

Lemma cont_multi__enum : forall {T : Type} (X Y : list T),
    contracted_multi X Y -> existsT2 n, contracted_multi_enum X Y n.
Proof.
  intros T X Y Hc.
  induction Hc. exists 0. eapply cont_multi_enum_refl.
  destruct IHHc as [n IH].
  exists (S n). eapply cont_multi_enum_step.
  eapply c. apply IH.
Qed.

Lemma cont_multi__enum_rev : forall {T : Type} (X Y : list T) n,
    contracted_multi_enum X Y n -> contracted_multi X Y.
Proof.
  intros T X Y n Hc.
  induction Hc. eapply cont_multi_refl.
  eapply cont_multi_step. eapply c.
  assumption.
Qed.

Inductive contracted_seqL {T : Type} : ((list T) * (list T) * dir) -> ((list T) * (list T) * dir) -> Type :=
| cont_seqL X Y Δ d : contracted_multi X Y -> contracted_seqL (X,Δ,d) (Y,Δ,d).

Inductive contracted_seqR {T : Type} : ((list T) * (list T) * dir) -> ((list T) * (list T) * dir) -> Type :=
| cont_seqR X Y Γ d : contracted_multi X Y -> contracted_seqR (Γ,X,d) (Γ,Y,d).

Inductive contracted_seq {T : Type} : ((list T) * (list T) * dir) -> ((list T) * (list T) * dir) -> Type :=
| cont_seq_baseL s1 s2 : contracted_seqL s1 s2 -> contracted_seq s1 s2
| cont_seq_baseR s1 s2  : contracted_seqR s1 s2 -> contracted_seq s1 s2
| cont_seq_stepL s1 s2 s3 : contracted_seqL s1 s2 -> contracted_seq s2 s3 -> contracted_seq s1 s3
| cont_seq_stepR s1 s2 s3 : contracted_seqR s1 s2 -> contracted_seq s2 s3 -> contracted_seq s1 s3.

Inductive contracted_nseq {T : Type} : list ((list T) * (list T) * dir) -> list ((list T) * (list T) * dir) -> Type :=
| cont_nseq_nil  : contracted_nseq [] []
| cont_nseq_cons s1 s2 ns1 ns2 : contracted_seq s1 s2 -> contracted_nseq ns1 ns2 ->
                                 contracted_nseq (s1::ns1) (s2::ns2).

Lemma derrec_contracted_multiL : forall {V : Set} Γ1 Γ2 Δ d X Y,
  contracted_multi Γ1 Γ2 ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [(Γ1, Δ, d)] ++ Y) ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [(Γ2, Δ, d)] ++ Y).
Proof.
  intros V Γ1 Γ2 Δ d X Y Hc Hd.
  revert X Y Δ d Hd.
  induction Hc; intros XX YY Δ d Hd.
  assumption.
  eapply IHHc.
  inversion c; subst;
  eapply LNSKt_contL_gen.
  eapply Hd. reflexivity. reflexivity.
  eapply Hd. reflexivity. reflexivity.
Qed.

Lemma derrec_contracted_multiR : forall {V : Set} Γ Δ1 Δ2 d X Y,
  contracted_multi Δ1 Δ2 ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [(Γ, Δ1, d)] ++ Y) ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [(Γ, Δ2, d)] ++ Y).
Proof.
  intros V Γ Δ1 Δ2 d X Y Hc Hd.
  revert X Y Γ d Hd.
  induction Hc; intros XX YY Γ d Hd.
  assumption.
  eapply IHHc.
  inversion c; subst;
  eapply LNSKt_contR_gen.
  eapply Hd. reflexivity. reflexivity.
  eapply Hd. reflexivity. reflexivity.
Qed.

Lemma derrec_contracted_seqL: forall {V : Set} s1 s2 X Y,
  contracted_seqL s1 s2 ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [s1] ++ Y) ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [s2] ++ Y).
Proof.
  intros V s1 s3 X Y Hc Hd.
  inversion Hc. subst.
  eapply derrec_contracted_multiL.
  exact H. assumption.
Qed.

Lemma derrec_contracted_seqR: forall {V : Set} s1 s2 X Y,
  contracted_seqR s1 s2 ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [s1] ++ Y) ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [s2] ++ Y).
Proof.
  intros V s1 s3 X Y Hc Hd.
  inversion Hc. subst.
  eapply derrec_contracted_multiR.
  exact H. assumption.
Qed.
  
Lemma derrec_contracted_seq: forall {V : Set} s1 s2 X Y,
  contracted_seq s1 s2 ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [s1] ++ Y) ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ [s2] ++ Y).
Proof.
  intros V s1 s2 X Y Hc. revert X Y. 
  induction Hc as [s1 s2 Hc | s1 s2 Hc | s1 s2 s3 Hc Hc2 | s1 s2 s3 Hc Hc2 ];
    intros X Y Hd; subst; try eapply IHHc2;
      (eapply derrec_contracted_seqL; eassumption) ||
      (eapply derrec_contracted_seqR; eassumption).
Qed.

Lemma derrec_contracted_nseq: forall {V : Set} ns1 ns2 X Y,
  contracted_nseq ns1 ns2 ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ ns1 ++ Y) ->
derrec (LNSKt_rules (V:=V)) (fun _ => False) (X ++ ns2 ++ Y).
Proof.
  intros V s1 s2 X Y Hc.
  revert X Y. 
  induction Hc as [ | ];
    intros X Y Hd; subst.
  +{ eapply Hd. }
  +{ simpl in Hd. 
     rewrite cons_singleton in Hd.
     eapply derrec_contracted_seq in Hd.
     2 : exact c.
     simpl. rewrite app_cons_single. eapply IHHc.
     rewrite <- app_cons_single. exact Hd. }
Qed.

Lemma contracted_gen_cons : forall {T : Type} Y Z (a : T),
    contracted_gen Y Z ->
    contracted_gen (a :: Y) (a :: Z).
Proof.
  intros until 0; intros Hc; inversion Hc; subst.
  rewrite ?app_comm_cons.
  eapply contracted_genL_I.
  reflexivity. reflexivity.
  rewrite ?app_comm_cons.
  eapply contracted_genR_I.
  reflexivity. reflexivity.
Qed.

Lemma contracted_multi_cons : forall {T : Type} Y Z (a : T),
    contracted_multi Y Z ->
    contracted_multi (a :: Y) (a :: Z).
Proof.
  intros until 0; intros Hc.
  induction Hc. subst. eapply cont_multi_refl.
  subst.
  eapply cont_multi_step. eapply contracted_gen_cons.
  eapply c.
  assumption.
Qed.

Lemma contracted_multi_cons_tl : forall {T : Type} Y Z (a : T),
    contracted_multi Y Z ->
    contracted_multi (Y ++ [a]) (Z ++ [a]).
Proof.
  intros until 0; intros Hc.
  induction Hc. eapply cont_multi_refl.
  inversion c. subst. 
  eapply cont_multi_step.
  list_assoc_r'. simpl. eapply contracted_genL_I.
  reflexivity. reflexivity.
  do 3 rewrite <- app_assoc in IHHc. assumption.

  subst. eapply cont_multi_step.
  list_assoc_r'. simpl. eapply contracted_genR_I.
  reflexivity. reflexivity.
  do 3 rewrite <- app_assoc in IHHc. assumption.
Qed.

Lemma contracted_multi_L : forall {T : Type} (X Y Z : list T),
    contracted_multi Y Z ->
    contracted_multi (X ++ Y) (X ++ Z).
Proof.
  induction X; intros Y Z Hc. assumption.
  simpl. eapply contracted_multi_cons.
  apply IHX. apply Hc.
Qed.

Lemma contracted_multi_R : forall {T : Type} (X Y Z : list T),
    contracted_multi Y Z ->
    contracted_multi (Y ++ X) (Z ++ X).
Proof.
  induction X; intros Y Z Hc. do 2 rewrite app_nil_r. assumption.
  rewrite cons_singleton. do 2 rewrite app_assoc.
  eapply IHX. eapply contracted_multi_cons_tl. assumption.
Qed.

Lemma contracted_multi_multi : forall {T : Type} Γ X Y Z,
    @contracted_multi T (X ++ Γ ++ Y ++ Γ ++ Z) (X ++ Γ ++ Y ++ Z).
Proof.
  induction X; intros.
  simpl.
  list_assoc_l'. eapply contracted_multi_R.
  list_assoc_r'.
  revert Y Z.
  induction Γ; intros Y Z.
  simpl. rewrite app_nil_r. apply cont_multi_refl.
  simpl. eapply cont_multi_step.
  2 :{ eapply contracted_multi_cons. eapply IHΓ. auto. }
  eapply (contracted_gen__spec a).
  rewrite (cons_singleton Γ a).
  do 2 rewrite (cons_singleton (Γ ++ _) a).
  cont_solve.

  simpl. eapply contracted_multi_cons. apply IHX.
Qed.

Lemma contracted_multi_double : forall {T : Type} Γ,
    @contracted_multi T (Γ ++ Γ) Γ.
Proof.
  intros T Γ.
  assert (    @contracted_multi T ([] ++ Γ ++ [] ++ Γ ++ []) ([] ++ Γ ++ [] ++ [])) as Hass.
  eapply contracted_multi_multi. 
  repeat rewrite app_nil_r in Hass.  assumption. 
Qed.

Lemma contracted_seq_double : forall {T : Type} Γ Δ d,
    @contracted_seq T (Γ ++ Γ, Δ ++ Δ, d) (Γ, Δ, d).
Proof.
  intros. econstructor 3.
  econstructor. eapply contracted_multi_double.
  econstructor 2. econstructor.
  eapply contracted_multi_double.
Qed.
  
Lemma contracted_seq_refl : forall {T : Type} s,
    @contracted_seq T s s.
Proof.
  intros T [[Γ Δ] d].
  econstructor. econstructor.
  eapply cont_multi_refl.
Qed.

Lemma contracted_nseq_refl : forall {T : Type} ns,
    @contracted_nseq T ns ns.
Proof.
  induction ns. constructor.
  constructor. apply contracted_seq_refl.
  assumption.
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

Lemma derrec_merge_contracted_multiL : forall {V : Set} X Y Δ d G H,
    contracted_multi X Y ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (G ++ [(X, Δ, d)] ++ H) ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (G ++ [(Y, Δ, d)] ++ H).
Proof.
  intros until 0 ; intros Hc; revert G H; induction Hc; intros G H Hd.
  assumption.
  apply IHHc. inversion c; subst.
  eapply LNSKt_contL_gen; [ eapply Hd | ..];  reflexivity.
  eapply LNSKt_contL_gen; [ eapply Hd | ..];  reflexivity. 
Qed.

Lemma derrec_merge_contracted_seqL : forall {V : Set} ss s G H,
    contracted_seqL ss s ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (G ++ [ss] ++ H) ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (G ++ [s] ++ H).
Proof.
  intros until 0; intros Hc.
  inversion Hc. subst.
  eapply derrec_merge_contracted_multiL.
  assumption.
Qed.

Lemma derrec_merge_contracted_multiR : forall {V : Set} X Y Γ d G H,
    contracted_multi X Y ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (G ++ [(Γ, X, d)] ++ H) ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (G ++ [(Γ, Y, d)] ++ H).
Proof.
  intros until 0 ; intros Hc; revert G H; induction Hc; intros G H Hd.
  assumption.
  apply IHHc. inversion c; subst.
  eapply LNSKt_contR_gen; [ eapply Hd | ..];  reflexivity.
  eapply LNSKt_contR_gen; [ eapply Hd | ..];  reflexivity. 
Qed.

Lemma derrec_merge_contracted_seqR : forall {V : Set} ss s G H,
    contracted_seqR ss s ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (G ++ [ss] ++ H) ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (G ++ [s] ++ H).
Proof.
  intros until 0; intros Hc.
  inversion Hc. subst.
  eapply derrec_merge_contracted_multiR.
  assumption.
Qed.

Lemma derrec_merge_contracted_seq : forall {V : Set} ss s G H,
    contracted_seq ss s ->
    derrec (LNSKt_rules (V:=V)) (fun _ => False) (G ++ [ss] ++ H) ->
    derrec (LNSKt_rules (V:=V)) (fun _ => False) (G ++ [s] ++ H).
Proof.
  intros until 0; intros Hc Hd.
  induction Hc.
  +{ eapply derrec_merge_contracted_seqL; eassumption. }
  +{ eapply derrec_merge_contracted_seqR; eassumption. }
  +{ eapply IHHc.  eapply derrec_merge_contracted_seqL; eassumption. }
  +{ eapply IHHc.  eapply derrec_merge_contracted_seqR; eassumption. }
Qed.

Lemma derrec_merge_contracted_nseq_gen : forall {V : Set} H1 H2 G1 G2,
  contracted_nseq H1 H2 ->
  derrec (LNSKt_rules (V:=V)) (fun _ => False) (G1 ++ H1 ++ G2) ->
  derrec (LNSKt_rules (V:=V)) (fun _ => False) (G1 ++ H2 ++ G2).
Proof.
  intros until 0; intros Hc; revert G1 G2; induction Hc; intros G1 G2 Hd.
  inversion Hd. contradiction.
  subst. assumption.

  simpl in *. rewrite cons_singleton.
  rewrite cons_singleton in Hd.
  eapply derrec_merge_contracted_seq.
  eapply c. rewrite app_assoc.
  eapply IHHc.
  rewrite <- app_assoc. assumption.
Qed.
  
Lemma derrec_merge_contracted_nseq : forall {V : Set} G H,
  contracted_nseq H G ->
  derrec (LNSKt_rules (V:=V)) (fun _ => False) H ->
  derrec (LNSKt_rules (V:=V)) (fun _ => False) G.
Proof.
  intros until 0; intros Hc Hd.
  assert (G =  ([] ++ G ++ [])) as Hass1.
  rewrite app_nil_r. reflexivity.
  rewrite Hass1. eapply derrec_merge_contracted_nseq_gen.
  eapply Hc.
  rewrite app_nil_r. assumption.
Qed.
  
Lemma derrec_merge_nseq_double : forall {V : Set} G H,
  merge G G H ->
  derrec (LNSKt_rules (V:=V)) (fun _ => False) H ->
  derrec (LNSKt_rules (V:=V)) (fun _ => False) G.
Proof.
  intros until 0; intros Hm Hd.
  eapply derrec_merge_contracted_nseq.
  eapply merge_contracted_nseq. eassumption.
  assumption.
Qed.

Lemma LNSKt_contraction_cor : forall (V : Set) G1 G2 G3,
    merge G1 G1 G3 ->
    derrec (LNSKt_rules (V:=V)) (fun _ => False) (G3 ++ G2) ->
    derrec (LNSKt_rules (V:=V)) (fun _ => False) (G1 ++ G2).
Proof.
  intros until 0; intros Hm Hd.
  rewrite <- app_nil_l.
  rewrite <- app_nil_l in Hd.
  eapply derrec_merge_contracted_nseq_gen.
  eapply merge_contracted_nseq. eassumption.
  assumption.
Qed.

(* --------------------------------- *)
(* CUT ADMISSIBILITY AND ELIMINATION *)
(* --------------------------------- *)

Definition can_gen_cut {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns1 ns2 :=
  forall G1 G2 G3 seq1 seq2 (d : dir) Γ1 Γ2 Δ1 Δ2 A,
    ns1 = G1 ++ [(seq1, d)] -> seq1 = pair Γ1 (Δ1++[A]) ->
    ns2 = G2 ++ [(seq2, d)] -> seq2 = pair (Γ2++[A]) Δ2 ->
    merge G1 G2 G3 ->
    struct_equiv_str G1 G2 ->
    derrec rules (fun _ => False) (G3 ++ [(Γ1++Γ2, Δ1++Δ2, d)]).

(* TODO: To fill in proof, based off Lemma 16 of paper. *)
Theorem LNSKt_cut_admissibility : forall (V : Set) ns1 ns2
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) ns1)
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) ns2),
      can_gen_cut (@LNSKt_rules V) ns1 ns2.
Admitted.

Definition can_gen_cut_simpl {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns1 ns2 :=
  forall G seq1 seq2 (d : dir) Γ1 Γ2 Δ1 Δ2 A,
    ns1 = G ++ [(seq1, d)] -> seq1 = pair Γ1 (Δ1++[A]) ->
    ns2 = G ++ [(seq2, d)] -> seq2 = pair (Γ2++[A]) Δ2 ->
    derrec rules (fun _ => False) (G ++ [(Γ1++Γ2, Δ1++Δ2, d)]).

Theorem LNSKt_cut_elimination_simpl : forall (V : Set) ns1 ns2
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) ns1)
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) ns2),
    can_gen_cut_simpl (@LNSKt_rules V) ns1 ns2.
Proof.
  intros. unfold can_gen_cut_simpl.
  intros. subst.
  destruct (@merge_ex V _ _ (struct_equiv_weak_refl G)) as [G3 HG3].  
  eapply LNSKt_contraction_cor.
  eassumption.
  eapply LNSKt_cut_admissibility in D2. 2 : exact D1.
  unfold can_gen_cut in D2.
  eapply D2; try reflexivity.
  assumption.
  apply struct_equiv_str_refl.
Qed.

Lemma external_weakeningR : forall {V : Set} ns1 ns2,
    derrec (@LNSKt_rules V) (fun _ => False) ns1 ->
    derrec (@LNSKt_rules V) (fun _ => False) (ns1 ++ ns2).
Proof.
  intros V ns1 ns2. revert ns1.
  induction ns2; intros ns1 Hder.
  rewrite app_nil_r. assumption.
  rewrite app_cons_single. eapply IHns2.
  eapply derI. eapply nEW. constructor.
  destruct a. destruct r. constructor.
  unfold nslclext. simpl. rewrite app_nil_r.
  constructor. eapply Hder.
  eapply dlNil.
Qed.

(* CUT ELIMINATION *)

Inductive Cut_rule {V : Set} : rlsT (list (rel (list (PropF V)) * dir)) :=
| Cut : forall Γ1 Γ2 Δ1 Δ2 d A, Cut_rule ([[(Γ1,Δ1++[A],d)]] ++ [[(Γ2++[A],Δ2,d)]]) [(Γ1++Γ2,Δ1++Δ2, d)].

Inductive LNSKt_cut_rules {V : Set} : rlsT (list (rel (list (PropF V)) * dir)) :=
| LNSKt_rules_woc : forall ps c, LNSKt_rules ps c -> LNSKt_cut_rules ps c
| LNSKt_rules_wc  : forall ps c, nslclrule (@Cut_rule V) ps c -> LNSKt_cut_rules ps c.

Theorem strong_induction_Prop:
forall P : nat -> Prop,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
  intros P Hind.
  assert ((forall n k, k <= n -> P k) -> forall n, P n) as Hass.
    intros HH n. eapply HH. eapply le_n.
  eapply Hass. clear Hass.
    induction n; intros k Hk. eapply PeanoNat.Nat.le_0_r in Hk.
    subst. eapply Hind. firstorder.

    eapply Lt.le_lt_or_eq in Hk. destruct Hk.
    eapply IHn. inversion H. apply le_n. subst. 
    apply Le.le_Sn_le in H1.
    assumption.
    subst. apply Hind. firstorder.
Qed.

Theorem strong_induction:
forall P : nat -> Type,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
  intros P Hind.
  assert ((forall n k, k <= n -> P k) -> forall n, P n) as Hass.
    intros HH n. eapply HH. eapply le_n.
  eapply Hass. clear Hass.
  induction n; intros k Hk.
    eapply PeanoNat.Nat.le_0_r in Hk.
    subst. eapply Hind. firstorder.
    eapply Compare_dec.le_lt_eq_dec in Hk. 
    destruct Hk.
    eapply IHn. inversion l. apply le_n. subst. 
    apply Le.le_Sn_le in H0.
    assumption.
    subst. apply Hind. firstorder.
Qed.

Lemma dersrec_derrec_height : forall {V : Set} rules ps p 
    (ds : dersrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ps)
    (d  : derrec  rules (fun _ : list (rel (list (PropF V)) * dir) => False) p),
    in_dersrec d ds ->
    derrec_height d <= dersrec_height ds.
Proof.
  intros V rules ps p ds d Hin.
  eapply le_dersrec_height.
  2 : eapply le_n.
  assumption.
Qed.

Lemma dersrecD_forall_in_dersrec : forall (X : Type) (rs : list X -> X -> Type) (ps : X -> Type) (cs : list X) (ds : dersrec rs ps cs) (c : X),
    InT c cs -> (existsT2 d : derrec rs ps c, in_dersrec d ds).
Proof.
  induction ds; intros c Hin.
  inversion Hin.
  inversion Hin.
  + subst. exists d. constructor.
  + subst. eapply IHds in X0. destruct X0 as [d2 Hin2].
    exists d2. constructor 2. eapply Hin2.
Qed.

(* Add to ddT.v *)

Lemma dersrec_double: forall X rules prems c1 c2,
  iffT (dersrec rules prems [c1;c2]) ((derrec rules prems (c1 : X)) * (derrec rules prems (c2 : X))).
Proof.
  intros. split; intros H.
  split; (eapply dersrecD_forall; [apply H |]).
  constructor 1. reflexivity.
  constructor 2. constructor 1. reflexivity.
  eapply dersrecI_forall. intros c Hc.
  inversion Hc as [ | ? ? H2]; subst. apply H.
  inversion H2 as [ | ? ? H3]; subst. apply H.
  inversion H3.
Qed.

Definition dersrec_doubleD X rs ps c1 c2 := iffT_D1 (@dersrec_double X rs ps c1 c2).

Lemma dersrec_double_verb: forall X rules prems c1 c2 (d : (dersrec rules prems [c1;c2])),
    existsT2 (d1 : (derrec rules prems (c1 : X))) (d2 : (derrec rules prems (c2 : X))),
      in_dersrec d1 d * in_dersrec d2 d.
Proof.
  intros.
  assert (InT c1 [c1;c2]) as Hin1. constructor. reflexivity.
  assert (InT c2 [c1;c2]) as Hin2. constructor 2. constructor. reflexivity.
  eapply dersrecD_forall_in_dersrec in Hin1.
  destruct Hin1 as [d1 Hin1]. exists d1.
  eapply dersrecD_forall_in_dersrec in Hin2.
  destruct Hin2 as [d2 Hin2]. exists d2.
  split. apply Hin1. apply Hin2.
Qed.

Theorem LNSKt_cut_elimination :
  forall {V : Set} ns,
    derrec (@LNSKt_cut_rules V) (fun _ => False) ns ->
    derrec (@LNSKt_rules V) (fun _ => False) ns.
Proof.
  intros V ns H.
  remember (derrec_height H) as n.
  revert Heqn. revert H. revert ns.
  induction n using strong_induction.
  destruct n.
  +{ intros ns H Heqn. destruct H. contradiction.
     simpl in Heqn. discriminate.
   }
  +{ intros ns H Heqn. remember H as H'.
     destruct H. contradiction.
     simpl in *. rewrite HeqH' in Heqn. inversion Heqn as [Heqn2].
     rewrite <- HeqH' in Heqn.
     inversion l.
     ++{ subst c ps0. eapply derI. apply X0.
         apply dersrecI_forall.
         intros p Hin.
(*         pose proof (dersrecD_forall d Hin) as d3. *)
         pose proof (dersrecD_forall_in_dersrec _ _ _ _ d _ Hin) as [d2 Hin2].
         eapply (X (derrec_height d2)). 2 : reflexivity.
         rewrite Heqn2.
         apply Lt.le_lt_n_Sm.
         eapply le_dersrec_height. exact Hin2.
         apply le_n.
       }
     ++{ subst c ps0.
         inversion X0. subst concl ps. inversion H.
         (* At this point d isn't of the right form I think, so I think that the Cut_rule definition is incorrect. *)
         subst ps0 c. clear H. clear X0.
         pose proof (dersrec_double_verb _ _ _ _ _ d) as [d1 [d2 [Hin1 Hin2]]].
         pose proof (@merge_ex V) as XX.
         edestruct XX as [G3 HG3].
         eapply struct_equiv_weak_refl.
         eapply LNSKt_contraction_cor.
         exact HG3.
         eapply LNSKt_cut_admissibility; [ | | reflexivity | reflexivity | reflexivity | reflexivity | exact HG3 | ..].
         +++{ eapply X. 2 : reflexivity. Unshelve.
              3:{ exact d1. }
              apply Lt.le_lt_n_Sm. rewrite Heqn2.
              eapply dersrec_derrec_height. 
              assumption.
            }
         +++{ eapply X. 2 : reflexivity. Unshelve. 2:{ exact d2. }
              apply Lt.le_lt_n_Sm. rewrite Heqn2.
              eapply dersrec_derrec_height.
              assumption.
            }
         +++{ simpl. apply struct_equiv_str_refl.
            }
       }
   }
Defined.

Print Assumptions LNSKt_cut_elimination.