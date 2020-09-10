
Require Export List.
Set Implicit Arguments.
Export ListNotations.

Add LoadPath "../general".

Require Import genT gen.
Require Import ddT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import existsT.

Parameter PropVars : Set.

(* Indicates the direction connecting sequents look. *)
Inductive dir : Type :=
| fwd : dir
| bac : dir.

(* definition of Propositional Formulas, parameterised over prim prop set.
 Originally had unused connectives. 
 Changed to include only the used connectives. 
*)
Inductive PropF (V : Set): Type :=
 | Var : V -> PropF V
 | Bot : PropF V
 | Imp : PropF V -> PropF V -> PropF V
(* | Not : PropF V -> PropF V
 | And : PropF V -> PropF V -> PropF V
 | Or : PropF V -> PropF V -> PropF V *)
 | WBox : PropF V -> PropF V
(* | WDia : PropF V -> PropF V *)
 | BBox : PropF V -> PropF V
(* | BDia : PropF V -> PropF V *)
.

Definition rel (W : Type) : Type := prod W W.
(* statement of exchL fails if using Type here 
Definition rel (W : Set) : Set := prod W W.
*)
Definition trf (W : Type) : Type := W -> W.  

(*
Inductive Seq (X : Set) : Set :=
  | mkseq : X -> X -> Seq X.

Check Seq_rect.
Check Seq_ind.
Check Seq_rec.

Print Seq_rect.
Print Seq_ind.
Print Seq_rec.
*)

(* don't want this approach, try principal rule 
  (effect of rule on principal formulae, then context) 
Inductive seqrule (V : Set) : 
  list (rel (list (PropF V))) -> rel (list (PropF V)) -> Prop :=
  | Id : forall A Gamma Delta,
    In A Gamma -> In A Delta -> seqrule [] (pair Gamma Delta)
  (*
  | AndR : forall A B Gamma Delta,
    seqrule [pair Gamma (A :: Delta); pair Gamma (B :: Delta)]
      (pair Gamma ((And A B) :: Delta))
  | OrL : forall A B Gamma Delta,
    seqrule [pair (A :: Gamma) Delta; pair (B :: Gamma) Delta]
      (pair ((Or A B) :: Gamma) Delta)
  | AndL : forall A B Gamma Delta,
    seqrule [pair (A :: B :: Gamma) Delta] (pair ((And A B) :: Gamma) Delta)
  | OrR : forall A B Gamma Delta,
    seqrule [pair Gamma (A :: B :: Delta)] (pair Gamma ((Or A B) :: Delta))
  *)
  | ExchR : forall A B Gamma Delta1 Delta2,
    seqrule [pair Gamma (Delta1 ++ A :: B :: Delta2)]
     (pair Gamma (Delta1 ++ B :: A :: Delta2))
  | ExchL : forall A B Gamma1 Gamma2 Delta,
    seqrule [pair (Gamma1 ++ A :: B :: Gamma2) Delta]
     (pair (Gamma1 ++ B :: A :: Gamma2) Delta)
.
*)

Inductive princrule (V : Set) : rlsT (rel (list (PropF V))) :=
  | Id' : forall A, princrule [] (pair [A] [A])
  | ImpR' : forall A B, princrule [pair [A] [B]] (pair [] [Imp A B])
  | ImpL' : forall A B, princrule
    [pair [B] [] ; pair [] [A]] (pair [Imp A B] [])
  | BotL' : princrule [] (pair [Bot V] []).

(* principal formula rules, where principal formula copied into premises
  (for the Imp rules), propositional version of Idrule *)
Inductive princrule_pfc (V : Set) : rlsT (rel (list (PropF V))) :=
  | Id_pfc : forall p, princrule_pfc [] (pair [Var p] [Var p])
  | ImpR_pfc : forall A B,
    princrule_pfc [pair [A] [Imp A B ; B]] (pair [] [Imp A B])
  | ImpL_pfc : forall A B, princrule_pfc
      [pair [Imp A B ; B] [] ; pair [Imp A B] [A]] (pair [Imp A B] [])
  | BotL_pfc : princrule_pfc [] (pair [Bot V] []).

(* we may also want to refer to rules individually *)
Inductive Idrule (W : Type) : rlsT (rel (list W)) :=
  | Idrule_I : forall A, Idrule [] (pair [A] [A]).

(* propositional version of axiom rule *)
Inductive Idrule_p (V : Set) : rlsT (rel (list (PropF V))) :=
  | Idrule_p_I : forall p, Idrule_p [] (pair [Var p] [Var p]).

Inductive Botrule (V : Set) : rlsT (rel (list (PropF V))) :=
  | Botrule_I : Botrule [] (pair [Bot V] []).

Inductive ImpLrule (V : Set) : rlsT (rel (list (PropF V))) :=
  | ImpLrule_I : forall A B,
    ImpLrule [pair [B] [] ; pair [] [A]] (pair [Imp A B] []).

Inductive ImpRrule (V : Set) : rlsT (rel (list (PropF V))) :=
  | ImpRrule_I : forall A B, ImpRrule [pair [A] [B]] (pair [] [Imp A B]).

Definition Sctxt_Id' V A Γ1 Γ2 Δ1 Δ2 :=
  @Sctxt_nil (PropF V) (@princrule V) ([A], [A]) Γ1 Γ2 Δ1 Δ2 (Id' A).

Lemma sr_Id_alt X (A : X) ant suc: InT A ant -> InT A suc ->
  seqrule (@Idrule X) [] (ant, suc).
Proof. intros. apply InT_split in X1.
apply InT_split in X0. cD. subst. 
eapply Sctxt_eq. apply (Idrule_I A).
simpl. reflexivity.  simpl. reflexivity.  simpl. reflexivity. Qed.

(*
Lemma Sctxt_Id :
  forall (V : Set) (A : PropF V) (Γ1 Γ2 Δ1 Δ2 : list (PropF V)),
  seqrule (princrule (V:=V)) [] (Γ1 ++ A :: Γ2, Δ1 ++ A :: Δ2).
to be completed.
*)

(* w : Set fails *)
Definition nsext (W : Type) G H (d : dir) (seq : W) := G ++ (seq, d) :: H.

Lemma nsext_def: forall (W : Type) G H d seq, 
  @nsext W G H (d : dir) (seq : W) = G ++ (seq, d) :: H.
Proof.  unfold nsext. reflexivity.  Qed.

Inductive nsrule (W : Type) (sr : rlsT W) : 
    rlsT (list (W * dir)) :=
  | NSctxt : forall ps c G H d, sr ps c -> 
    nsrule sr (map (nsext G H d) ps) (nsext G H d c).

Lemma NSctxt_nil: forall (W : Type) sr G H d c, (sr [] c : Type) ->
  @nsrule W sr [] (nsext G H d c).
Proof.
  intros until 0; intros H0.
  eapply NSctxt in H0.  simpl in H0. exact H0.
Qed.

Lemma NSctxt': forall W (sr : rlsT W) ps c G H d, sr ps c ->
    nsrule sr (map (nsext G H d) ps) (G ++ (c, d) :: H).
Proof. intros. rewrite <- nsext_def. apply NSctxt. assumption. Qed.

Definition nstail {W : Type} H (d : dir) (seq : W) := (seq, d) :: H.
Lemma nstail_def: forall {W : Type} H d seq, 
  nstail H (d : dir) (seq : W) = (seq, d) :: H.
Proof.  unfold nstail. reflexivity.  Qed.

Lemma nstail_ext: forall (W : Type) H d seq, 
  nstail H (d : dir) (seq : W) = nsext [] H d seq.
Proof.  unfold nsext.  unfold nstail. reflexivity.  Qed.

(* as above but where context allowed on left only (names ns -> nslc) *)
Definition nslcext (W : Type) G (d : dir) (seq : W) := G ++ [(seq, d)].

Lemma nslcext_def: forall (W : Type) G d seq, 
  @nslcext W G (d : dir) (seq : W) = G ++ [(seq, d)].
Proof.  unfold nslcext. reflexivity.  Qed.

Inductive nslcrule (W : Type) (sr : rlsT W) : 
    rlsT (list (W * dir)) :=
  | NSlcctxt : forall ps c G d, sr ps c -> 
    nslcrule sr (map (nslcext G d) ps) (nslcext G d c).

Lemma NSlcctxt_nil: forall (W : Type) sr G d c, (sr [] c : Type) ->
  @nslcrule W sr [] (nslcext G d c).
Proof.
  intros until 0; intros H.
  eapply NSlcctxt in H.  simpl in H. exact H.  Qed.

Lemma NSlcctxt': forall W (sr : rlsT W) ps c G d, sr ps c ->
    nslcrule sr (map (nslcext G d) ps) (G ++ [(c, d)]).
Proof. intros. rewrite <- nslcext_def. apply NSlcctxt. assumption. Qed.

Definition nslctail {W : Type} (d : dir) (seq : W) := (seq, d) :: [].
Lemma nslctail_def: forall {W : Type} d seq, 
  nslctail (d : dir) (seq : W) = (seq, d) :: [].
Proof.  unfold nslctail. reflexivity.  Qed.

Lemma nslctail_ext: forall (W : Type) d seq, 
  nslctail (d : dir) (seq : W) = nslcext [] d seq.
Proof.  unfold nslcext.  unfold nslctail. reflexivity.  Qed.


(* context of a nested sequent *)
Definition nslext W (G H seqs : list W) := G ++ seqs ++ H.

Lemma nslext_def: forall W G H seqs, @nslext W G H seqs = G ++ seqs ++ H.
Proof.  unfold nslext. reflexivity.  Qed.

Lemma nslext2_def: forall W G H seq1 seq2,
  @nslext W G H [seq1 ; seq2] = G ++ seq1 :: seq2 :: H.
Proof.  unfold nslext. simpl. reflexivity.  Qed.

Lemma nslext2_def': forall W G H seq1 seq2,
  @nslext W G H [seq1 ; seq2] = (G ++ [seq1]) ++ seq2 :: H.
Proof.  unfold nslext. simpl. intros.  apply list_rearr22.  Qed.

Inductive nslrule W (sr : rlsT (list W)) : rlsT (list W) :=
  | NSlctxt : forall ps c G H, sr ps c ->
    nslrule sr (map (nslext G H) ps) (nslext G H c).

Lemma NSlctxt': forall W (sr : rlsT (list W)) ps c G H, sr ps c ->
    nslrule sr (map (nslext G H) ps) (G ++ c ++ H).
Proof. intros. rewrite <- nslext_def. apply NSlctxt. assumption. Qed.

Lemma NSlctxt2: forall W (sr : rlsT (list W)) ps x y G H, sr ps [x ; y] ->
    nslrule sr (map (nslext G H) ps) (G ++ x :: y :: H).
Proof. intros. rewrite list_rearr20. apply NSlctxt'. assumption. Qed.  

(* left context of a nested sequent *)
Definition nslclext W (G seqs : list W) := G ++ seqs.

Lemma nslclext_def: forall W G seqs, @nslclext W G seqs = G ++ seqs.
Proof.  unfold nslclext. reflexivity.  Qed.

Lemma nslclext2_def: forall W G seq1 seq2,
  @nslclext W G [seq1 ; seq2] = G ++ [seq1; seq2].
Proof.  unfold nslclext. simpl. reflexivity.  Qed.

Lemma nslclext2_def': forall W G seq1 seq2,
  @nslclext W G [seq1 ; seq2] = (G ++ [seq1]) ++ [seq2].
Proof.  unfold nslclext. simpl. intros.  apply list_rearr22.  Qed.

Inductive nslclrule W (sr : rlsT (list W)) : rlsT (list W) :=
  | NSlclctxt : forall ps c G, sr ps c ->
    nslclrule sr (map (nslclext G) ps) (nslclext G c).

Lemma NSlclctxt': forall W (sr : rlsT (list W)) ps c G, sr ps c ->
    nslclrule sr (map (nslclext G) ps) (G ++ c).
Proof. intros. rewrite <- nslclext_def. apply NSlclctxt. assumption. Qed.

Check princrule.
Check seqext.
Check seqrule.
Check nsext.
Check nstail.
Check nsrule.
Check (fun V => nsrule (seqrule (@princrule V))).

(* problem with the seqrule/princrule approach, try this instead *)

Lemma princrule_L : forall {V : Set} ps Γ Δ,
    @princrule V ps (Γ, Δ) ->
    Γ = [] \/ exists E, Γ = [E].
Proof.
  intros V ps Γ Δ P.
  inversion P as [ A P2| P2 | A B P2 | P2];
    try (left; reflexivity).
  right. exists A. reflexivity.
  right. exists (Imp A B). reflexivity.
  right. exists (Bot V). reflexivity.
Qed.

Lemma princrule_LT : forall {V : Set} ps Γ Δ,
    @princrule V ps (Γ, Δ) ->
    (Γ = []) + (existsT E, Γ = [E]).
Proof.
  intros V ps Γ Δ P.
  inversion P as [ A P2| P2 | A B P2 | P2];
    try (left; reflexivity).
  right. exists A. reflexivity.
  right. exists (Imp A B). reflexivity.
  right. exists (Bot V). reflexivity.
Qed.

Lemma princrule_R : forall {V : Set} ps Γ Δ,
    @princrule V ps (Γ, Δ) ->
    Δ = [] \/ exists E, Δ = [E].
Proof.
  intros V ps Γ Δ P. inversion P as [ A P2| A B P2 | P2 | P2];
                       try (left; reflexivity).
  right. exists A. reflexivity.
  right. exists (Imp A B). reflexivity.
Qed.

Lemma princrule_RT : forall {V : Set} ps Γ Δ,
    @princrule V ps (Γ, Δ) ->
    (Δ = []) + (existsT E, Δ = [E]).
Proof.
  intros V ps Γ Δ P. inversion P as [ A P2| A B P2 | P2 | P2];
                       try (left; reflexivity).
  right. exists A. reflexivity.
  right. exists (Imp A B). reflexivity.
Qed.

Lemma princrule_pfc_L : forall {V : Set} ps Γ Δ,
    @princrule_pfc V ps (Γ, Δ) ->
    Γ = [] \/ exists E, Γ = [E].
Proof.
  intros V ps Γ Δ P.
  inversion P as [ p P2| P2 | A B P2 | P2];
    try (left; reflexivity).
  right. exists (Var p). reflexivity.
  right. exists (Imp A B). reflexivity.
  right. exists (Bot V). reflexivity.
Qed.

Lemma princrule_pfc_LT : forall {V : Set} ps Γ Δ,
    @princrule_pfc V ps (Γ, Δ) ->
    (Γ = []) + (existsT E, Γ = [E]).
Proof.
  intros V ps Γ Δ P.
  inversion P as [ p P2| P2 | A B P2 | P2];
    try (left; reflexivity).
  right. exists (Var p). reflexivity.
  right. exists (Imp A B). reflexivity.
  right. exists (Bot V). reflexivity.
Qed.

Lemma princrule_pfc_R : forall {V : Set} ps Γ Δ,
    @princrule_pfc V ps (Γ, Δ) ->
    Δ = [] \/ exists E, Δ = [E].
Proof.
  intros V ps Γ Δ P. inversion P as [ p P2| A B P2 | P2 | P2];
                       try (left; reflexivity).
  right. exists (Var p). reflexivity.
  right. exists (Imp A B). reflexivity.
Qed.

Lemma princrule_pfc_RT : forall {V : Set} ps Γ Δ,
    @princrule_pfc V ps (Γ, Δ) ->
    (Δ = []) + existsT E, Δ = [E].
Proof.
  intros V ps Γ Δ P. inversion P as [ p P2| A B P2 | P2 | P2];
                       try (left; reflexivity).
  right. exists (Var p). reflexivity.
  right. exists (Imp A B). reflexivity.
Qed.


Definition rules_L_oe {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps x y Δ, rules ps (x ++ y, Δ) -> x = [] \/ y = [].

Definition rules_R_oe {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps x y Γ, rules ps (Γ, x ++ y) -> x = [] \/ y = [].


Definition rules_L_oeT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps x y Δ, rules ps (x ++ y, Δ) -> (x = []) + (y = []).

Definition rules_R_oeT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps x y Γ, rules ps (Γ, x ++ y) -> (x = []) + (y = []).

Lemma princrule_L_oeT : forall {V : Set} ps x y Δ,
    @princrule V ps (x ++ y, Δ) -> (x = []) + (y = []).
Proof.
  intros until 0; intros H; apply princrule_LT in H;
  repeat sD'; list_eq_ncT. tauto. sD; tauto.
Qed.

Lemma princrule_R_oe : forall {V : Set} ps x y Γ,
    @princrule V ps (Γ, x ++ y) -> x = [] \/ y = [].
Proof.
  intros until 0. intros H.
  apply princrule_R in H. sD ; list_eq_nc ; tauto.
Qed.

Lemma princrule_R_oeT : forall {V : Set} ps x y Γ,
    @princrule V ps (Γ, x ++ y) -> (x = []) + (y = []).
Proof.
  intros until 0. intros H.
  apply princrule_RT in H. repeat sD' ; list_eq_ncT.  tauto.
  sD'; tauto.
Qed.

Lemma princrule_L_oe'T: forall V, rules_L_oeT (@princrule V).
Proof.
  unfold rules_L_oe.  intros until 0. intros H.
  eapply princrule_L_oeT.  
Qed.

Lemma princrule_R_oe': forall V, rules_R_oe (@princrule V).
Proof.
  unfold rules_R_oe.  intros until 0. intros H.
  eapply princrule_R_oe.  exact H.
Qed.

Lemma princrule_R_oe'T: forall V, rules_R_oeT (@princrule V).
Proof.
  unfold rules_R_oeT.  intros until 0. intros H.
  eapply princrule_R_oeT.  exact H.
Qed.

Lemma princrule_pfc_L_oeT : forall {V : Set} ps x y Δ,
    @princrule_pfc V ps (x ++ y, Δ) -> (x = []) + (y = []).
Proof.
  intros until 0. intros H. apply princrule_pfc_LT in H.
  sD ; list_eq_ncT ; sD ; tauto. 
Qed.

Lemma princrule_pfc_R_oeT : forall {V : Set} ps x y Γ,
    @princrule_pfc V ps (Γ, x ++ y) -> (x = []) + (y = []).
Proof.
  intros until 0. intros H. apply princrule_pfc_RT in H.
  sD ; list_eq_ncT ; tauto.
Qed.

Lemma princrule_pfc_L_oe'T: forall V, rules_L_oeT (@princrule_pfc V).
Proof.
  unfold rules_L_oeT.   intros until 0. intros H.
  eapply princrule_pfc_L_oeT.  exact H.
Qed.

Lemma princrule_pfc_R_oe'T: forall V, rules_R_oeT (@princrule_pfc V).
Proof.
  unfold rules_R_oeT.  intros until 0. intros H.
  eapply princrule_pfc_R_oeT.  exact H.
Qed.

Lemma Idrule_L_oe : forall {V : Set} ps x y Δ,
    @Idrule V ps (x ++ y, Δ) -> x = [] \/ y = [].
Proof.
  intros until 0. intros H. inversion H. subst.
  acacD'. tauto.  list_eq_nc. tauto.
Qed.

Lemma Idrule_R_oe : forall {V : Set} ps x y Γ,
    @Idrule V ps (Γ, x ++ y) -> x = [] \/ y = [].
Proof.
  intros until 0. intros H. inversion H. subst.
  acacD'. tauto. list_eq_nc. tauto.
Qed.

Lemma Idrule_p_L_oe : forall {V : Set} ps x y Δ,
    @Idrule_p V ps (x ++ y, Δ) -> x = [] \/ y = [].
Proof.
  intros until 0. intros H. inversion H. subst.
  acacD'. tauto.  list_eq_nc. tauto.
Qed.

Lemma Idrule_p_R_oe : forall {V : Set} ps x y Γ,
    @Idrule_p V ps (Γ, x ++ y) -> x = [] \/ y = [].
Proof.
  intros until 0. intros H. inversion H. subst.
  acacD'. tauto.  list_eq_nc. tauto.
Qed.

Lemma Idrule_L_oe': forall (V : Set), rules_L_oe (@Idrule V).
Proof.
  unfold rules_L_oe.  intros until 0. intros H.
  eapply Idrule_L_oe.  exact H.
Qed.

Lemma Idrule_R_oe': forall (V : Set), rules_R_oe (@Idrule V).
Proof.
  unfold rules_R_oe.  intros until 0. intros H.
  eapply Idrule_R_oe.  exact H.
Qed.

Lemma Idrule_p_L_oe': forall (V : Set), rules_L_oe (@Idrule_p V).
Proof.
  unfold rules_L_oe.  intros until 0. intros H.
  eapply Idrule_p_L_oe.  exact H.
Qed.

Lemma Idrule_p_R_oe': forall (V : Set), rules_R_oe (@Idrule_p V).
Proof.
  unfold rules_R_oe. intros until 0. intros H.
  eapply Idrule_p_R_oe.  exact H.
Qed.

