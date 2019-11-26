Require Import ssreflect.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt lntacs lntls lntbR lntmtacs.
Require Import lntb1L lntb2L.
Require Import lntkt_exch.
Require Import lnt_weakening.
Require Import lnt_contraction.



(* TACTICS *)


Ltac clear_useless :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         end.

Ltac inv_singleton :=
    repeat (clear_useless; match goal with
           | [ H : [?a] = ?b |- _ ] => inversion H; subst
           | [ H : ((?a,?b) = ?c) |- _ ] => inversion H; subst
           end).

(* ------------------------- *)

(* STRUCTURAL EQUIVALENCE *)

Inductive struct_equiv1_str {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type := 
| se_base1 Γ1 Δ1 Γ2 Δ2 d : struct_equiv1_str [(Γ1, Δ1, d)] [(Γ2, Δ2, d)]
| se_step1 Γ1 Δ1 Γ2 Δ2 d ns1 ns2 :
    struct_equiv1_str ns1 ns2 ->
    struct_equiv1_str ((Γ1, Δ1, d) :: ns1) ((Γ2, Δ2, d) :: ns2).

Inductive struct_equiv2_str {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type := 
| se_base2 Γ1 Δ1 d1 Γ2 Δ2 d2 : d1 = d2 -> struct_equiv2_str [(Γ1, Δ1, d1)] [(Γ2, Δ2, d2)]
| se_step2 Γ1 Δ1 d1 Γ2 Δ2 d2 ns1 ns2 ns3 ns4 :
    d1 = d2 ->
    ns3 = ((Γ1, Δ1, d1) :: ns1) ->
    ns4 = ((Γ2, Δ2, d2) :: ns2) ->
    struct_equiv2_str ns1 ns2 ->
    struct_equiv2_str ns3 ns4.

Inductive struct_equiv1_weak {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type :=
| se_wk1_extL ns1 ns2 ns3 : struct_equiv1_str ns1 ns2 -> struct_equiv1_weak (ns1 ++ ns3) ns2
| se_wk1_extR ns1 ns2 ns3 : struct_equiv1_str ns1 ns2 -> struct_equiv1_weak ns1 (ns2 ++ ns3).

Inductive struct_equiv2_weak {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type :=
| se_wk2_extL ns1 ns2 ns3 ns4 :
    ns4 = (ns1 ++ ns3) -> struct_equiv2_str ns1 ns2 -> struct_equiv2_weak ns4 ns2
| se_wk2_extR ns1 ns2 ns3 ns4 :
    ns4 = (ns2 ++ ns3) -> struct_equiv2_str ns1 ns2 -> struct_equiv2_weak ns1 ns4.

Lemma struct_equiv1_str_weak : forall {V : Set} G1 G2,
   @struct_equiv1_str V G1 G2 -> @struct_equiv1_weak V G1 G2.
Proof.
  intros V G1 G2 H.
  eapply se_wk1_extL in H.
  erewrite app_nil_r in H.
  exact H.
Qed.

Lemma struct_equiv2_str_weak : forall {V : Set} G1 G2,
   @struct_equiv2_str V G1 G2 -> @struct_equiv2_weak V G1 G2.
Proof.
  intros V G1 G2 H.
  eapply se_wk2_extL in H. 2 : reflexivity.
  erewrite app_nil_r in H.  exact H.
Qed.

Lemma struct_equiv1_str_length : forall {V : Set} G1 G2,
    @struct_equiv1_str V G1 G2 -> length G1 = length G2.
Proof.
  induction G1; intros H2 H; destruct H2;
    subst; (reflexivity || inversion H).
  reflexivity.
  subst. simpl. erewrite IHG1. reflexivity.
  assumption.
Qed.

Ltac inversion_cons :=
  repeat match goal with
         | [ H : ?a :: ?l1 = ?b :: ?l2 |- _] => inversion H; subst; clear_useless
         end.
Lemma struct_equiv2_str_length : forall {V : Set} G1 G2,
    @struct_equiv2_str V G1 G2 -> length G1 = length G2.
Proof.
  induction G1; intros H2 H; destruct H2;
    subst; (reflexivity || inversion H); subst; try discriminate.
  reflexivity.
  simpl. erewrite IHG1. reflexivity.
  unfold rel in H3.
  inversion_cons. exact H4.
Qed.

Lemma struct_equiv2_weak_cons : forall {V : Set} l1 l2 a1 a2,
    l1 <> [] ->
    l2 <> [] ->
    struct_equiv2_weak (a1::l1) (a2::l2) ->
    @struct_equiv2_weak V l1 l2.
Proof.
  intros V l1 l2 a1 a2 H1 H2 H3.
  inversion H3 as [l3 H4 l4 H5 H6 H7 | H4 l3 l4 H5 H6 H7]; subst.
  destruct l3 as [| a ns1];
    inversion H7; try discriminate; subst.
  contradiction.
  simpl in *. unfold rel in *.
  inversion_cons.
  econstructor. reflexivity. assumption.

  destruct l3 as [| a ns1];
    inversion H7; try discriminate; subst.
  contradiction.
  simpl in *. unfold rel in *.
  inversion_cons.
  econstructor 2. reflexivity. assumption.
Qed.
  
Ltac struct_equiv2_str_nil :=
  match goal with
  | [H : struct_equiv2_str [] ?n |- _] => inversion H; discriminate
  | [H : struct_equiv2_str ?n [] |- _] => inversion H; discriminate
  end.

Ltac struct_equiv2_str_cons :=
  match goal with
  | [H : struct_equiv2_str (?a :: ?la) (?b :: ?lb) |- _] => inversion H; subst
  end.


Lemma struct_equiv2_weak_d : forall {V : Set} ns1 ns2 seq1 seq2 d1 d2,
    ns1 <> [] ->
    ns2 <> [] ->
    @struct_equiv2_weak V ((seq1,d1)::ns1) ((seq2,d2)::ns2) ->
    d1 = d2.
Proof.
  intros until 0; intros H1 H2 H3.
  inversion H3 as [l3 H4 l4 H5 H6 H7 | H4 l3 l4 H5 H6 H7]; subst. 
  destruct l3. simpl in *.
  struct_equiv2_str_nil.
  simpl in *.
  inversion_cons.
  struct_equiv2_str_cons. contradiction.
  unfold rel in *. inversion_cons.
  reflexivity.
  
  destruct l3. simpl in *.
  struct_equiv2_str_nil.
  simpl in *.
  inversion_cons.
  struct_equiv2_str_cons. contradiction.
  unfold rel in *. inversion_cons.
  reflexivity.
Qed.  



(* --------------------------- *)

(* MERGE *)

Inductive merge {V : Set} :  (list (rel (list (PropF V)) * dir)) ->  (list (rel (list (PropF V)) * dir)) ->  (list (rel (list (PropF V)) * dir)) -> Type :=
| merge_base Γ1 Γ2 Δ1 Δ2 d1 d2 d3 ns1 ns2 ns3:
    ns1 = [(Γ1,Δ1,d1)] -> ns2 = [(Γ2,Δ2,d2)] -> ns3 = [(Γ1++Γ2,Δ1++Δ2,d3)] ->
    merge ns1 ns2 ns3
| merge_stepL Γ Δ Σ Π d1 d2 d3 ns ns1 ns2 ns3 :
    ns1 = [(Γ,Δ,d1)] -> ns2 = ((Σ,Π,d2)::ns) -> ns3 = ((Γ++Σ,Δ++Π,d3)::ns) ->
    merge ns1 ns2 ns3 
| merge_stepR Γ Δ Σ Π d1 d2 d3 ns ns1 ns2 ns3:
    ns1 = ((Γ,Δ,d1)::ns) -> ns2 = [(Σ,Π,d2)] -> ns3 = ((Γ++Σ,Δ++Π,d3)::ns) ->
    merge ns1 ns2 ns3
| merge_step Γ Δ Σ Π d1 d2 d3 ns1 ns2 ns3 seq1 seq2 seq3 : seq1 = (Γ,Δ,d1) -> seq2 = (Σ,Π,d2) -> seq3 = (Γ++Σ,Δ++Π) -> d1=d2 -> d1=d3 -> merge ns1 ns2 ns3 -> merge (seq1::ns1) (seq2::ns2) ((seq3,d3)::ns3).

Inductive merge2 {V : Set} :  (list (rel (list (PropF V)) * dir)) ->  (list (rel (list (PropF V)) * dir)) ->  (list (rel (list (PropF V)) * dir)) -> Type :=
| merge2_base Γ1 Γ2 Δ1 Δ2 d1 d2 d3 : merge2 [(Γ1,Δ1,d1)] [(Γ2,Δ2,d2)] [(Γ1++Γ2,Δ1++Δ2,d3)]
| merge2_stepL Γ Δ Σ Π d1 d2 d3 ns : merge2 [(Γ,Δ,d1)] ((Σ,Π,d2)::ns) ((Γ++Σ,Δ++Π,d3)::ns)
| merge2_stepR Γ Δ Σ Π d1 d2 d3 ns : merge2 ((Γ,Δ,d1)::ns) [(Σ,Π,d2)] ((Γ++Σ,Δ++Π,d3)::ns)
| merge2_step Γ Δ Σ Π d1 d2 d3 ns1 ns2 ns3 : d1=d2 -> d1=d3 -> merge2 ns1 ns2 ns3 -> merge2 ((Γ,Δ,d1)::ns1) ((Σ,Π,d2)::ns2) ((Γ++Σ,Δ++Π,d3)::ns3).

(* Equality that ignores the first, irrelevant direction. *)
Inductive LNS_eq {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Prop :=
| LNS_eq_base n1 n2 seq d1 d2 : n1 = [(seq,d1)] -> n2 = [(seq,d2)] -> LNS_eq n1 n2
| LNS_eq_step ns1 ns2 nseq1 nseq2 : nseq1 = nseq2 -> LNS_eq ns1 ns2 -> LNS_eq (nseq1 :: ns1) (nseq2 :: ns2).

Lemma merge_unique {V : Set} : forall n1 n2 n3 n4,
    struct_equiv1_str n1 n2 ->
    merge n1 n2 n3 -> @merge V n1 n2 n4 -> LNS_eq n3 n4.
Proof.
  induction n1; intros n2 n3 n4 H H1 H2.
  inversion H1; subst; discriminate.
  inversion H; subst;
  inversion H1; subst;
  inversion H2; subst;
  try inv_singleton;
  try solve [econstructor; reflexivity];
  try solve [inversion X; subst; discriminate].

  econstructor 2. reflexivity.
  eapply IHn1; eassumption.
Qed.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Lemma merge_existence {V : Set} : forall n1 n2,
      n1<>[] ->
      n2<>[] ->
      struct_equiv2_weak n1 n2 ->
      existsT n3, @merge V n1 n2 n3.
Proof.
  induction n1; intros n2 H1 H2 Hequiv.
  contradiction.
  destruct n2 as [| [[Γ2 Δ2] d2] n2 ]. contradiction.
  destruct a as [[Γ1 Δ1] d1].
  destruct n1 as [| seq  n1].
  exists ((Γ1++Γ2,Δ1++Δ2,d1) :: n2).
  econstructor 2; reflexivity.
  destruct n2 as [|seq2 n2].
  exists ((Γ1++Γ2,Δ1++Δ2,d1) :: (seq :: n1)).
  econstructor 3; reflexivity.
  remember (seq :: n1) as n1'.
  remember (seq2 :: n2) as n2'.
  destruct (IHn1 n2') as [n3 Hn3].
  subst; discriminate.
  subst; discriminate.
  eapply struct_equiv2_weak_cons in Hequiv.
  assumption. subst; discriminate.
  subst; discriminate.
  exists ( (Γ1++Γ2,Δ1++Δ2,d1)::n3).
  econstructor 4; try reflexivity.
  eapply struct_equiv2_weak_d in Hequiv.
  assumption. subst; discriminate.
  subst; discriminate.
  assumption.
Qed.

(*
Old merge that cared about the first direction, but that is irrelevant for the proof system.
Inductive merge {V : Set} :  (list (rel (list (PropF V)) * dir)) ->  (list (rel (list (PropF V)) * dir)) ->  (list (rel (list (PropF V)) * dir)) -> Type :=
| merge_base Γ1 Γ2 Δ1 Δ2 d1 d2 d3 : d1=d2 -> d1=d3 -> merge [(Γ1,Δ1,d1)] [(Γ2,Δ2,d2)] [(Γ1++Γ2,Δ1++Δ2,d3)]
| merge_stepL Γ Δ Σ Π d1 d2 d3 ns : d1=d2 -> d1=d3 -> merge [(Γ,Δ,d1)] ((Σ,Π,d2)::ns) ((Γ++Σ,Δ++Π,d3)::ns)
| merge_stepR Γ Δ Σ Π d1 d2 d3 ns : d1=d2 -> d1=d3 -> merge ((Γ,Δ,d1)::ns) [(Σ,Π,d2)] ((Γ++Σ,Δ++Π,d3)::ns)
| merge_step Γ Δ Σ Π d1 d2 d3 ns1 ns2 ns3 : d1=d2 -> d1=d3 -> merge ns1 ns2 ns3 -> merge ((Γ,Δ,d1)::ns1) ((Σ,Π,d2)::ns2) ((Γ++Σ,Δ++Π,d3)::ns3).
 *)

(* --------------------------- *)
(* CUT ELIMINATION *)

Definition can_gen_cut {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns1 ns2 :=
  forall G1 G2 G3 seq1 seq2 (d : dir) Γ1 Γ2 Δ1 Δ2 A,
    ns1 = G1 ++ [(seq1, d)] -> seq1 = pair Γ1 (A::Δ1) ->
    ns2 = G2 ++ [(seq2, d)] -> seq2 = pair (A::Γ2) Δ2 ->
    merge G1 G2 G3 ->
    struct_equiv2_str G1 G2 ->
    derrec rules (fun _ => False) (G3 ++ [(Γ1++Γ2, Δ1++Δ2, d)]).


Inductive depth_i X (rules : list X -> X -> Prop) (prems : X -> Prop) :
          forall (concl : X), (derrec rules prems concl) -> nat -> Prop :=
| depth_dpI concl d H : d = dpI rules prems concl H -> depth_i X rules prems concl d 0
| depth_derI concl d ps Hrules (d2 : dersrec rules prems ps) n :
    d = derI concl Hrules d2 ->
    depths_i X rules prems ps d2 n ->
    depth_i X rules prems concl d (S n)
with depths_i X (rules : list X -> X -> Prop) (prems : X -> Prop) :
     forall (ps : list X), (dersrec rules prems ps) -> nat -> Prop :=
| depths_dlNil d : d = dlNil rules prems -> depths_i X rules prems [] d 0
| depths_dlCons seq seqs d Hseq Hseqs n m :
    d = dlCons Hseq Hseqs ->
    depth_i X rules prems seq Hseq n ->
    depths_i X rules prems seqs Hseqs m ->
    depths_i X rules prems (seq :: seqs) d (max n m).

(*
Lemma Forall_a_derrec : forall (X : Type) rules prems ps,
    Forall (aderrec rules prems) ps <->
    @Forall X (derrec rules prems) ps.
Proof.
  intros. split; intros H.
  induction ps. auto.
  apply Forall_cons_inv in H.
  apply Forall_cons.
  apply H.
 *)


Lemma depth_i_existence :
  forall X rules concl
  (d : derrec rules _ concl),
  exists n, depth_i X rules (fun _ => False) concl d n.
Proof.
  intros X rules.
  pose proof derrec_all_ind as Hder.
  intros concl.
  eapply (Hder _ _ _ (fun x => exists n, depth_i X rules (fun _ => False) x d n)).
  3 :{ .
  Print derrec_all_ind.
  
  eapply  derrec_all_ind.
  + intros concl0 H0 d0.
    exists 0. eapply (depth_dpI _ _ _ _ _ _ _ ).
  + admit.
    +  
    induction ps; intros concl0 H0 H1 H2 d0.
     exists 0. eapply (depth_dpI _ _ _ _ _ _ _ ).
     eapply IHps.  
     induction ps0.
     
    in d. derIrs d . induction d.
                               induction d.



  
Lemma test : forall (X : Type) rules ps x,
    (derrec (rules : list X -> X -> Prop) (fun _ => False) x ->
     aderrec (rules : list X -> X -> Prop) (fun _ => False) x) /\
    (@Forall X (derrec rules (fun _ => False)) ps ->
        @Forall X (aderrec rules (fun _ => False)) ps).
    
  (*/\
   ( Forall (aderrec rules prems) ps <->
    @Forall X (derrec rules prems) ps). *)
Proof.
  intros X rules ps; induction ps; split; intros H.
  induction H. inversion H.
  
  induction H1. inversion H.
  econstructor 2. exact H. apply dersrec_all in H0.
  
  eapply dersrec_all in H0.
  econstructor 2. apply H. apply H0.
  SearchAbout dersrec Forall.
  induction ps.
  econstructor 2. exact H.
  constructor.
  apply Forall_cons_inv in H0.
  
  
  apply IHps.
  apply dlNil.
  
  
  SearchAbout nil derrec.
  constructor. auto.
  econstructor 2. exact H.
  Print derrec.
  induction ps. auto. constructor.
  econstructor. eapply Forall_cons_inv in H0.
  
  apply dersrec_all.
  

  SearchAbout dersrec Forall.

  
Fixpoint depth  X (rules : list X -> X -> Prop) (prems : X -> Prop)
         (concl : X) (d : derrec rules prems concl) : bool :=
  match d with
  | dpI _ _ _ _ => true
  | _ => true
  end.
  


Definition Lemma16_form A (P : Prop) :=
  forall m n G H I Γ Δ Σ Π {V : Set}
         (rules : rls (list (rel (list (PropF V)) * dir)))
         (D1 : derrec rules (fun _ => False) (G ++ [(Γ,A++Δ,d)]))
         (D2 : derrec rules (fun _ => False) (H ++ [(A++Σ,Π,d)] ++ I)),
    struct_equiv2_str G H ->
    princ A D1 ->
    depth D1 + depth D2 <= m ->
    merge G H GH ->
    derrec rules (fun _ => False) (GH ++ [(Γ++Σ,Δ++Π,d);([],A,fwd)]) ->
    size A <= n ->
    
    





Theorem LNSKt_cut_elimination : forall (V : Set) ns1 ns2
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) ns1)
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) ns2),
      can_gen_cut (@LNSKt_rules V) ns1 ns2.
Admitted.


(*
Lemma LNSKt_weakL: forall (V : Set) ns
  (D : derrec (@LNSKt_rules V) (fun _ => False) ns),
      can_gen_weakL (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H ; subst ; [> pose gen_weakL_step_b2R_lc 
  | pose gen_weakL_step_b1R_lc
  | pose gen_weakL_step_b2L_lc
  | pose gen_weakL_step_b1L_lc
  | pose gen_weakL_step_EW_lc
  | pose gen_weakL_step_pr_lc ] ; 
unfold gen_weakL_step in g ; egx g ;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.
*)