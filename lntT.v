
Require Export List.
Set Implicit Arguments.
Export ListNotations.
Require Import genT gen.
Require Import ddT.
Require Import List_lemmasT.
Require Import existsT.

Parameter PropVars : Set.

(* Indicates the direction connecting sequents look. *)
Inductive dir : Type :=
| fwd : dir
| bac : dir.

(* definition of Propositional Formulas, parameterised over prim prop set,
  note, we can have unused connectives as long as we don't want to prove
  that the Id rule, restricted to atoms, is sufficient *)
Inductive PropF (V : Set): Type :=
 | Var : V -> PropF V
 | Bot : PropF V
 | Imp : PropF V -> PropF V -> PropF V
 | Not : PropF V -> PropF V
 | And : PropF V -> PropF V -> PropF V
 | Or : PropF V -> PropF V -> PropF V
 | WBox : PropF V -> PropF V
 | WDia : PropF V -> PropF V
 | BBox : PropF V -> PropF V
 | BDia : PropF V -> PropF V
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

Definition seqext (W : Type) Γ1 Γ2 Δ1 Δ2 (seq : rel (list W)) :=
  match seq with | pair U V => pair (Γ1 ++ U ++ Γ2) (Δ1 ++ V ++ Δ2) end.

Lemma seqext_seqext: forall V (Γ1 Γ2 Δ1 Δ2 Φ1 Φ2 Ψ1 Ψ2 : list V) seq,
  seqext Γ1 Γ2 Δ1 Δ2 (seqext Φ1 Φ2 Ψ1 Ψ2 seq) =
  seqext (Γ1 ++ Φ1) (Φ2 ++ Γ2) (Δ1 ++ Ψ1) (Ψ2 ++ Δ2) seq.
Proof. intros. unfold seqext. destruct seq.
rewrite !app_assoc. reflexivity. Qed.  

Inductive seqrule (W : Type) (pr : rlsT (rel (list W))) : 
    rlsT (rel (list W)) := 
  | Sctxt : forall ps c Φ1 Φ2 Ψ1 Ψ2, pr ps c -> 
    seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).

Lemma seqext_def : forall (W : Type) Φ1 Φ2 Ψ1 Ψ2 U V,
      @seqext W Φ1 Φ2 Ψ1 Ψ2 (U,V) = (Φ1 ++ U ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof. reflexivity. Qed.

Lemma Sctxt_e: forall (W : Type) (pr : rlsT (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (Φ1 ++ U ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof.
  intros until 0. intros H. rewrite <- seqext_def.
  apply Sctxt. exact H.
Qed.

Lemma Sctxt_eq: forall (W : Type) pr ps mps (ca cs U V Φ1 Φ2 Ψ1 Ψ2 : list W),
  pr ps (U, V) -> ca = Φ1 ++ U ++ Φ2 -> cs = Ψ1 ++ V ++ Ψ2 ->
  mps = map (seqext Φ1 Φ2 Ψ1 Ψ2) ps -> seqrule pr mps (ca, cs).
Proof. intros.  subst. apply Sctxt_e. exact X. Qed.  

Lemma seqrule_id (W : Type) (pr : rlsT (rel (list W))) :
  forall ps c, pr ps c -> seqrule pr ps c.
Proof. intros. destruct c as [ca cs].
apply (Sctxt_eq pr ps ca cs [] [] [] []). assumption.
simpl. rewrite app_nil_r.  reflexivity.
simpl. rewrite app_nil_r.  reflexivity.
clear X. induction ps.  simpl.  reflexivity.
simpl. rewrite <- IHps.
destruct a. unfold seqext. simpl.  rewrite !app_nil_r.
reflexivity. Qed.

Lemma seqrule_seqrule (W : Type) (pr : rlsT (rel (list W))) :
  rsub (seqrule (seqrule pr)) (seqrule pr).
Proof. unfold rsub. intros. inversion X. subst. clear X. 
inversion X0.  subst. clear X0.
rewrite seqext_seqext.
destruct c0 as [ca cs].
eapply Sctxt_eq. exact X. 
reflexivity.  reflexivity.
clear X. induction ps0.  simpl.  reflexivity.
simpl. rewrite IHps0.  rewrite seqext_seqext. reflexivity. Qed.

Definition seqrule_seqrule' (W : Type) pr :=
  rsubD _ _ (@seqrule_seqrule W pr).
 
Lemma derl_seqrule'' (W : Type) (rules : rlsT (rel (list W))) :
  forall Φ1 Φ2 Ψ1 Ψ2, (forall ps c, derl rules ps c -> 
   derl (seqrule rules) (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c)) * 
  (forall ps cs, dersl rules ps cs -> 
    dersl (seqrule rules) (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) 
    (map (seqext Φ1 Φ2 Ψ1 Ψ2)cs)).
Proof. intros Φ1 Φ2 Ψ1 Ψ2.
eapply (derl_dersl_rect_mut (rules := rules)
  (fun ps c => fun _ => derl (seqrule rules)
    (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c))
  (fun ps cs : list _ => fun _ => dersl (seqrule rules)
    (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (map (seqext Φ1 Φ2 Ψ1 Ψ2) cs))).
- simpl. intros. apply asmI.
- intros. eapply dtderI.  apply Sctxt. eassumption.  assumption. 
- simpl. apply dtNil.
- intros. rewrite map_app. simpl. apply dtCons ; assumption. Qed.
 
Definition derl_seqrule' W rules Φ1 Φ2 Ψ1 Ψ2 := 
  fst (@derl_seqrule'' W rules Φ1 Φ2 Ψ1 Ψ2).
Definition dersl_seqrule' W rules Φ1 Φ2 Ψ1 Ψ2 := 
  snd (@derl_seqrule'' W rules Φ1 Φ2 Ψ1 Ψ2).
 
Lemma derl_seqrule (W : Type) (rules : rlsT (rel (list W))) :
  rsub (seqrule (derl rules)) (derl (seqrule rules)).
Proof.  unfold rsub.  intros.  destruct X.  
apply derl_seqrule'. assumption. Qed.

Lemma seqrule_derl_seqrule (W : Type) (rules : rlsT (rel (list W))) :
  rsub (seqrule (derl (seqrule rules))) (derl (seqrule rules)).
Proof.  eapply rsub_trans. apply derl_seqrule.
 unfold rsub.  intros.  eapply derl_mono. 2: eassumption.
 apply seqrule_seqrule. Qed.

Definition seqrule_derl_seqrule' W rules :=
  rsubD _ _ (@seqrule_derl_seqrule W rules).

(* seqrule_s ps c qs d means that d is a sequent extension of c 
  and that each q in qs is a corresponding sequent extension of the
  corresponding p in ps *)
Inductive seqrule_s (W : Type) (ps : list (rel (list W))) (c : rel (list W)) : 
    rlsT (rel (list W)) := 
  | Sctxt_s : forall Φ1 Φ2 Ψ1 Ψ2, 
    seqrule_s ps c (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).

Inductive seqrule' (W : Type) (pr : rlsT (rel (list W))) : 
    rlsT (rel (list W)) := 
  | Sctxt' : forall ps c pse ce,
    pr ps c -> seqrule_s ps c pse ce -> seqrule' pr pse ce.

Check (Sctxt' _ _ (Sctxt_s _ _ _ _ _ _)). 

(* Check, get same as Sctxt but for seqrule' *)
Lemma Sctxt_alt : forall (W : Type) (pr : rlsT (rel (list W))) ps c Φ1 Φ2 Ψ1 Ψ2,
    pr ps c -> seqrule' pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof.
  intros until 0. intros H.
  eapply Sctxt'. exact H. apply Sctxt_s.
Qed.

Lemma Sctxt_e': forall (W : Type) (pr : rlsT (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) ((Φ1 ++ U) ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof.
  intros until 0. intros H.
  rewrite <- app_assoc. apply Sctxt_e. exact H.
Qed.  

Lemma seqext_defp : forall (W : Type) Φ1 Φ2 Ψ1 Ψ2 seq,
      @seqext W Φ1 Φ2 Ψ1 Ψ2 seq =
        let (U, V) := seq in (Φ1 ++ U ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof. reflexivity. Qed.

Lemma seqrule_same: forall (W : Type) pr ps (c c' : rel (list W)),
  seqrule pr ps c -> c = c' -> seqrule pr ps c'.
Proof. intros. subst. assumption. Qed.  

Lemma seqrule_mono X (rulesa rulesb : rlsT (rel (list X))) :
  rsub rulesa rulesb -> rsub (seqrule rulesa) (seqrule rulesb).
Proof. unfold rsub. intros. destruct X1. apply Sctxt. firstorder. Qed.

Lemma Sctxt_nil: forall (W : Type) pr c Γ1 Γ2 Δ1 Δ2, (pr [] c : Type) ->
  @seqrule W pr [] (seqext Γ1 Γ2 Δ1 Δ2 c).
Proof.
  intros until 0.  intros H. eapply Sctxt in H.
  simpl in H. exact H.
Qed.

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

Ltac acacE :=
  repeat match goal with
    | [ H : _ |- _ ] => apply app_eq_app in H ; sE
    | [ H : _ |- _ ] => apply cons_eq_app in H ; sE
    | [ H : _ |- _ ] => apply app_eq_cons in H ; sE
    end.

Ltac acacD :=
  repeat match goal with
    | [ H : _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    end.

Ltac acacD' :=
  repeat match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
         end.

Ltac acacD'T2 :=
  repeat match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_appT2 in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_appT2 in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_consT2 in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
         end.

Ltac acacDe' :=
  match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
    | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
    | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_app in H
    end.

Ltac acacDe'T2 :=
  match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_appT2 in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_appT2 in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_consT2 in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
    | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nilT in H
    | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_appT in H
  end.

Ltac acacDe := repeat (sD' || acacDe').
Ltac acacDeT2 := repeat (sD' || acacDe'T2).

Theorem app_eq_unitT :
    forall {A : Type } (x y:list A) (a:A),
      x ++ y = [a] -> (x = [] /\ y = [a]) + (x = [a] /\ y = []).
Proof.
  intros until 0; intros H; destruct x; auto.
  simpl in H; inversion H as [[H1 H2]]; subst.
  apply app_eq_nil in H2. destruct H2. subst. auto.
Qed.

Theorem unit_eq_appT :
    forall {A : Type } (x y:list A) (a:A),
      [a] = x ++ y -> (x = [] /\ y = [a]) + (x = [a] /\ y = []).
Proof.
  intros until 0; intros H. 
  apply app_eq_unitT. auto.
Qed.

Ltac list_eq_nc :=
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : [] = _ ++ _ :: _  |- _ ] => apply nil_eq_list in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
     | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_app in H
     | [ H : _ ++ _ = [_] |- _ ] => apply app_eq_unit in H
     | [ H : [_] = _ ++ _ |- _ ] => apply unit_eq_app in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_single in H
     | [ H : [_] = _ ++ _ :: _ |- _ ] => apply single_eq_list in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.

(* Type version of list_eq_nc *)
Ltac list_eq_ncT :=
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : [] = _ ++ _ :: _  |- _ ] => apply nil_eq_list in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nilT in H
     | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_appT in H
     | [ H : _ ++ _ = [_] |- _ ] => apply app_eq_unitT in H
     | [ H : [_] = _ ++ _ |- _ ] => apply unit_eq_appT in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_singleT in H
     | [ H : [_] = _ ++ _ :: _ |- _ ] => apply single_eq_listT in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.


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

