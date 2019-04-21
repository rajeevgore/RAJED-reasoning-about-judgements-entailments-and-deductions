
Require Export List.
Set Implicit Arguments.
Export ListNotations.
Require Import gen.
Require Import dd.
Require Import List_lemmas.

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

Inductive princrule (V : Set) : rls (rel (list (PropF V))) :=
  | Id' : forall A, princrule [] (pair [A] [A])
  | ImpR' : forall A B, princrule [pair [A] [B]] (pair [] [Imp A B])
  | ImpL' : forall A B, princrule
    [pair [B] [] ; pair [] [A]] (pair [Imp A B] [])
  | BotL' : princrule [] (pair [Bot V] []).

(* we may also want to refer to rules individually *)
Inductive Idrule (V : Set) : rls (rel (list (PropF V))) :=
  | Idrule_I : forall A, Idrule [] (pair [A] [A]).

Inductive Botrule (V : Set) : rls (rel (list (PropF V))) :=
  | Botrule_I : Botrule [] (pair [Bot V] []).

Inductive ImpLrule (V : Set) : rls (rel (list (PropF V))) :=
  | ImpLrule_I : forall A B,
    ImpLrule [pair [B] [] ; pair [] [A]] (pair [Imp A B] []).

Inductive ImpRrule (V : Set) : rls (rel (list (PropF V))) :=
  | ImpRrule_I : forall A B, ImpRrule [pair [A] [B]] (pair [] [Imp A B]).

Definition seqext (W : Type) Γ1 Γ2 Δ1 Δ2 (seq : rel (list W)) :=
  match seq with | pair U V => pair (Γ1 ++ U ++ Γ2) (Δ1 ++ V ++ Δ2) end.

Inductive seqrule (W : Type) (pr : rls (rel (list W))) : 
    rls (rel (list W)) := 
  | Sctxt : forall ps c Φ1 Φ2 Ψ1 Ψ2, pr ps c -> 
    seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).

(* seqrule_s ps c qs d means that d is a sequent extension of c 
  and that each q in qs is a corresponding sequent extension of the
  corresponding p in ps *)
Inductive seqrule_s (W : Type) (ps : list (rel (list W))) (c : rel (list W)) : 
    rls (rel (list W)) := 
  | Sctxt_s : forall Φ1 Φ2 Ψ1 Ψ2, 
    seqrule_s ps c (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).

Inductive seqrule' (W : Type) (pr : rls (rel (list W))) : 
    rls (rel (list W)) := 
  | Sctxt' : forall ps c pse ce,
    pr ps c -> seqrule_s ps c pse ce -> seqrule' pr pse ce.

Check (Sctxt' _ _ (Sctxt_s _ _ _ _ _ _)). 

(* Check, get same as Sctxt but for seqrule' *)
Lemma Sctxt_alt : forall (W : Type) (pr : rls (rel (list W))) ps c Φ1 Φ2 Ψ1 Ψ2,
    pr ps c -> seqrule' pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (seqext Φ1 Φ2 Ψ1 Ψ2 c).
Proof.  intros. eapply Sctxt'. exact H. apply Sctxt_s. Qed.

Lemma seqext_def : forall (W : Type) Φ1 Φ2 Ψ1 Ψ2 U V,
      @seqext W Φ1 Φ2 Ψ1 Ψ2 (U,V) = (Φ1 ++ U ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof. reflexivity. Qed.

Lemma Sctxt_e: forall (W : Type) (pr : rls (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (Φ1 ++ U ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof. intros.  rewrite <- seqext_def. apply Sctxt. exact H. Qed.  

Lemma Sctxt_e': forall (W : Type) (pr : rls (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) ((Φ1 ++ U) ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof. intros. rewrite <- app_assoc. apply Sctxt_e. exact H. Qed.  

Lemma seqext_defp : forall (W : Type) Φ1 Φ2 Ψ1 Ψ2 seq,
      @seqext W Φ1 Φ2 Ψ1 Ψ2 seq =
        let (U, V) := seq in (Φ1 ++ U ++ Φ2, Ψ1 ++ V ++ Ψ2).
Proof. reflexivity. Qed.

Lemma seqrule_same: forall (W : Type) pr ps (c c' : rel (list W)),
  seqrule pr ps c -> c = c' -> seqrule pr ps c'.
Proof. intros. subst. assumption. Qed.  

Lemma Sctxt_nil: forall (W : Type) pr c Γ1 Γ2 Δ1 Δ2, (pr [] c : Prop) ->
  @seqrule W pr [] (seqext Γ1 Γ2 Δ1 Δ2 c).
Proof.  intros.  eapply Sctxt in H.  simpl in H. exact H.  Qed.

Definition Sctxt_Id' V A Γ1 Γ2 Δ1 Δ2 :=
  @Sctxt_nil (PropF V) (@princrule V) ([A], [A]) Γ1 Γ2 Δ1 Δ2 (Id' A).

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
Proof.
unfold nsext. reflexivity.
Qed.

Inductive nsrule (W : Type) (sr : rls W) : 
    rls (list (W * dir)) :=
  | NSctxt : forall ps c G H d, sr ps c -> 
    nsrule sr (map (nsext G H d) ps) (nsext G H d c).

Lemma NSctxt_nil: forall (W : Type) sr G H d c, (sr [] c : Prop) ->
  @nsrule W sr [] (nsext G H d c).
Proof.  intros.  eapply NSctxt in H0.  simpl in H0. exact H0.  Qed.

Lemma NSctxt': forall W (sr : rls W) ps c G H d, sr ps c ->
    nsrule sr (map (nsext G H d) ps) (G ++ (c, d) :: H).
Proof. intros. rewrite <- nsext_def. apply NSctxt. assumption. Qed.

Definition nstail {W : Type} H (d : dir) (seq : W) := (seq, d) :: H.
Lemma nstail_def: forall {W : Type} H d seq, 
  nstail H (d : dir) (seq : W) = (seq, d) :: H.
Proof.  unfold nstail. reflexivity.  Qed.

Lemma nstail_ext: forall (W : Type) H d seq, 
  nstail H (d : dir) (seq : W) = nsext [] H d seq.
Proof.  unfold nsext.  unfold nstail. reflexivity.  Qed.

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

Inductive nslrule W (sr : rls (list W)) : rls (list W) :=
  | NSlctxt : forall ps c G H, sr ps c ->
    nslrule sr (map (nslext G H) ps) (nslext G H c).

Lemma NSlctxt': forall W (sr : rls (list W)) ps c G H, sr ps c ->
    nslrule sr (map (nslext G H) ps) (G ++ c ++ H).
Proof. intros. rewrite <- nslext_def. apply NSlctxt. assumption. Qed.

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

Lemma princrule_R : forall {V : Set} ps Γ Δ,
    @princrule V ps (Γ, Δ) ->
    Δ = [] \/ exists E, Δ = [E].
Proof.
  intros V ps Γ Δ P. inversion P as [ A P2| A B P2 | P2 | P2];
                       try (left; reflexivity).
  right. exists A. reflexivity.
  right. exists (Imp A B). reflexivity.
Qed.

Inductive proprule (V : Set) : rls (rel (list (PropF V))) :=
  | Id : forall U Φ1 Φ2 Ψ1 Ψ2, 
    proprule [] (pair (Φ1 ++ U :: Φ2) (Ψ1 ++ U :: Ψ2))
  | ImpR : forall U W Φ Ψ1 Ψ2, 
    proprule [pair (U :: Φ) (Ψ1 ++ W :: Ψ2)] (pair Φ (Ψ1 ++ Imp U W :: Ψ2))
  | ImpL : forall U W Φ1 Φ2 Ψ, 
    proprule [pair (Φ1 ++ W :: Φ2) Ψ ; pair (Φ1 ++ Φ2) (U :: Ψ)]
      (pair (Φ1 ++ Imp U W :: Φ2) Ψ)
  | BotL : forall Φ1 Φ2 Ψ, proprule [] (pair (Φ1 ++ (Bot V) :: Φ2) Ψ)
.

Definition can_exchL (V : Set) 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ1 (A B : PropF V) Γ2 Δ, 
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ A :: B :: Γ2) Δ ->
  derrec rules (fun _ => False) (G ++ (pair (Γ1 ++ B :: A :: Γ2) Δ, d) :: H).

(*
Lemma exchL: forall (V : Set) ns (D : derrec (nsrule (@proprule V)) 
  (fun _ => False) ns) G H seq d Γ1 A B Γ2 Δ, 
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ A :: B :: Γ2) Δ ->
  derrec (nsrule (@proprule V)) (fun _ => False) 
    (G ++ (pair (Γ1 ++ B :: A :: Γ2) Δ, d) :: H).
intro.  intro.  intro.
Check derrec_all_ind.
eapply derrec_all_ind in D.
(* eexact D. fails - why? *)
or, which doesn't work without using can_exchL
intro.  intro.
eapply derrec_all_ind.
tauto.
*)

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

Ltac list_eq_nc :=
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
     | [ H : _ ++ _ = [_] |- _ ] => apply app_eq_unit in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_single in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.

Definition rules_L_oe {W : Set} (rules : rls (rel (list W))) := 
  forall ps x y Δ, rules ps (x ++ y, Δ) -> x = [] \/ y = [].

Definition rules_R_oe {W : Set} (rules : rls (rel (list W))) := 
  forall ps x y Γ, rules ps (Γ, x ++ y) -> x = [] \/ y = [].

Lemma princrule_L_oe : forall {V : Set} ps x y Δ,
    @princrule V ps (x ++ y, Δ) -> x = [] \/ y = [].
Proof.  intros. apply princrule_L in H. sD ; list_eq_nc ; tauto.  Qed.

Lemma princrule_R_oe : forall {V : Set} ps x y Γ,
    @princrule V ps (Γ, x ++ y) -> x = [] \/ y = [].
Proof.  intros. apply princrule_R in H. sD ; list_eq_nc ; tauto.  Qed.

Lemma princrule_L_oe': forall V, rules_L_oe (@princrule V).
Proof. unfold rules_L_oe.  intros.  eapply princrule_L_oe.  exact H.  Qed.

Lemma princrule_R_oe': forall V, rules_R_oe (@princrule V).
Proof. unfold rules_R_oe.  intros.  eapply princrule_R_oe.  exact H.  Qed.

Lemma Idrule_L_oe : forall {V : Set} ps x y Δ,
    @Idrule V ps (x ++ y, Δ) -> x = [] \/ y = [].
Proof.
  intros. inversion H. subst. acacD'. tauto.
  apply eq_sym in H1.  list_eq_nc. tauto.
Qed.

Lemma Idrule_R_oe : forall {V : Set} ps x y Γ,
    @Idrule V ps (Γ, x ++ y) -> x = [] \/ y = [].
Proof.
  intros. inversion H. subst. acacD'. tauto.
  apply eq_sym in H1.  list_eq_nc. tauto.
Qed.

Lemma Idrule_L_oe': forall V, rules_L_oe (@Idrule V).
Proof. unfold rules_L_oe.  intros.  eapply Idrule_L_oe.  exact H.  Qed.

Lemma Idrule_R_oe': forall V, rules_R_oe (@Idrule V).
Proof. unfold rules_R_oe.  intros.  eapply Idrule_R_oe.  exact H.  Qed.

Lemma exchL: forall (V : Set) ns 
  (D : derrec (nsrule (@proprule V)) (fun _ => False) ns),
  can_exchL (nsrule (@proprule V)) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.  unfold nsext in H5.
unfold can_exchL.  intros. 
unfold nsext in H7.
(* cases of where the exchange occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ1 ++ B :: A :: Γ2, Δ) as seqe.

decompose [or] H7. clear H7.  cE.
(* case where the rule is applied in a sequent to the right
  of where the exchange takes place *)
remember (G0 ++ (seqe, d0) :: x) as Ge.
remember (map (nsext Ge H2 d) ps0) as pse.

apply derI with pse. subst pse. subst H6.
rewrite list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqGe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchL in c0.
unfold nsext. subst Ge. subst seqe.
rewrite <- list_rearr14.
eapply c0. 2:reflexivity.
unfold nsext. subst G. subst seq.
rewrite list_rearr14.  reflexivity.

all : revgoals. clear H7. cE.
(* now the case where the rule is applied in a sequent to the left
  of where the exchange takes place *)
remember (x ++ (seqe, d0) :: H6) as He.
remember (map (nsext G He d) ps0) as pse.

apply derI with pse. subst pse. subst G0.
rewrite <- list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqHe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchL in c0.
unfold nsext. subst He. subst seqe.
rewrite list_rearr14.

eapply c0. 2:reflexivity.
unfold nsext. subst H2. subst seq.
apply list_rearr14.

(* now case where exchange and rule application occur in the same sequent *)
cE. clear H7. injection H10 as. 
inversion H3.  subst. rename_last eqll. 
(* case of Id rule *)
injection eqll as eql eqr. subst. 
apply derI with [].  2: apply dlNil.
rewrite <- nsext_def. apply NSctxt_nil.
acacD ; subst ;
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
  repeat (apply Id || rewrite list_rearr16 || rewrite list_rearr15).

all : revgoals.
(* case of BotL rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst. 
apply derI with [].  2: apply dlNil.
rewrite <- nsext_def. apply NSctxt_nil.
acacD ; subst ;
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
  repeat (apply BotL || rewrite list_rearr16 || rewrite list_rearr15).

all : revgoals. (* ImpL and ImpR rules remain *)
(* case of ImpR rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst. 
clear H H0 H3.
eapply derI.  rewrite <- nsext_def. apply NSctxt.  apply ImpR.
rewrite dersrec_all. rewrite Forall_forall. intros.
rewrite Forall_forall in H1. simpl in H1. simpl in H. sD.
subst.  unfold can_exchL in H1. unfold nsext. rewrite app_comm_cons.
eapply H1.
left. reflexivity.
apply nsext_def. 
rewrite app_comm_cons.  reflexivity.

(* now for the ImpL rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst.
clear H H3. (* not H0 in this case as will need non-exchanged premises *)
rewrite dersrec_all in H0.  rewrite Forall_forall in *.
unfold can_exchL in H1. simpl in *.  
(* rewrite <- nsext_def in H1. fails, why? *)
rewrite <- nsext_def.
pose (H0 _ (or_intror (or_introl eq_refl))) as H0re.
(* can't apply derI right away as premises will vary *)
acacD ; subst ; eapply derI ;
  try (apply NSctxt ;
    repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
    repeat (apply ImpL || rewrite list_rearr16 || rewrite list_rearr15)) ;
  rewrite dersrec_all ; rewrite Forall_forall ; intros p inps ;
  simpl in inps ; sD ; subst ; 
  rewrite ?app_nil_r in * ; 
  rewrite ?app_nil_r ; rewrite <- ?list_rearr16'.

(*
Check (or_introl (nsext_def _ _ _ _)).
Check (H0 _ (or_introl (nsext_def _ _ _ _))).
pose (H0 _ (or_introl (nsext_def _ _ _ _))) as H0l.
Check (or_intror (or_introl (nsext_def _ _ _ _))).
pose (H0 _ (or_intror (or_introl (nsext_def _ _ _ _)))) as H0r.
pose (H1 _ (or_intror (or_introl eq_refl))) as H1re.
pose (H1 _ (or_introl eq_refl)) as H1le.
pose (H1 _ (or_introl eq_refl)) as H1le.
Check (H1re _ _ _ _ _ _ _ _ _ eq_refl).
pose (H1le G H6) as H1lee.
Check (H1le G H6 _ d0 _ _ _ _ _ (nsext_def _ _ _ _)).
pose (H1le G H6 _ d0 _ _ _ _ _ (nsext_def _ _ _ _)).
(* pose (H1re _ _ _ _ _ _ _ _ _ eq_refl) as H1ree. fails *)
(* pose (H1le _ _ _ _ _ _ _ _ _ eq_refl) as H1lee. fails *)
*)

eapply H1. left. reflexivity. apply nsext_def.  reflexivity.

exact H0re.

eapply H1. left. reflexivity. apply nsext_def.
rewrite <- list_rearr16. reflexivity.

rewrite <- !list_rearr16 in H0re. exact H0re.

list_assoc_r.  eapply H1.  left. reflexivity. apply nsext_def.  list_eq_assoc.

list_assoc_r. 
eapply H1. right. left. reflexivity. apply nsext_def.
list_eq_assoc.

eapply H1.  left. reflexivity. apply nsext_def.  reflexivity.

exact H0re.

list_assoc_l.  eapply H1. left. reflexivity. apply nsext_def.  list_eq_assoc.

list_assoc_l. eapply H1. right. left. reflexivity. apply nsext_def.
list_eq_assoc.

Qed.

Ltac nsrule_rewrites :=  (match goal with
                          | [ |- nsrule ?a ?b ?c ] => apply NSctxt;
(match goal with
| [ |- proprule ?a (?Γ, ?Δ1 ++ ?B :: Imp ?U ?W :: ?Δ2)] =>
  rewrite list_rearr16_R
| [ |- proprule ?a (?Γ, ?Δ1 ++ ?B :: ?A :: ?eqr3 ++ Imp ?U ?W :: ?Ψ2)] =>
  rewrite list_rearr17_R
| [ |- proprule ?ps (?Γ, (?Ψ1 ++ Imp ?U ?W :: ?eqr1) ++ ?B :: ?A :: ?Δ2)] =>
  rewrite <- list_rearr15_R; simpl
| _ => trivial end); apply ImpR
| _ => trivial end).


Definition can_exchR (V : Set) 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ Δ1 (A B : PropF V) Δ2 ,
  ns = G ++ (seq, d) :: H -> seq = pair Γ (Δ1 ++ A :: B :: Δ2) ->
  derrec rules (fun _ => False) (G ++ (pair Γ (Δ1 ++ B :: A :: Δ2), d) :: H).

Lemma exchR: forall (V : Set) ns 
  (D : derrec (nsrule (@proprule V)) (fun _ => False) ns),
  can_exchR (nsrule (@proprule V)) ns.
Proof.
intros.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.  unfold nsext in H5.
unfold can_exchR.  intros. 
unfold nsext in H7.
(* cases of where the exchange occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ, Δ1 ++ B :: A :: Δ2) as seqe.

decompose [or] H7. clear H7.  cE.
(* case where the rule is applied in a sequent to the right
  of where the exchange takes place *)
remember (G0 ++ (seqe, d0) :: x) as Ge.
remember (map (nsext Ge H2 d) ps0) as pse.

apply derI with pse. subst pse. subst H6.
rewrite list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqGe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchR in c0.
unfold nsext. subst Ge. subst seqe.
rewrite <- list_rearr14.
eapply c0. 2:reflexivity.
unfold nsext. subst G. subst seq.
rewrite list_rearr14.  reflexivity.

all : revgoals. clear H7. cE.
(* now the case where the rule is applied in a sequent to the left
  of where the exchange takes place *)
remember (x ++ (seqe, d0) :: H6) as He.
remember (map (nsext G He d) ps0) as pse.

apply derI with pse. subst pse. subst G0.
rewrite <- list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqHe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchR in c0.
unfold nsext. subst He. subst seqe.
rewrite list_rearr14.

eapply c0. 2:reflexivity.
unfold nsext. subst H2. subst seq.
apply list_rearr14.

(* now case where exchange and rule application occur in the same sequent *)
cE. clear H7. injection H10 as. 
inversion H3.  subst. rename_last eqll. 
(* case of Id rule *)
injection eqll as eql eqr. subst. 
apply derI with [].  2: apply dlNil.
rewrite <- nsext_def. apply NSctxt_nil.
acacD ; subst ;
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
  repeat (apply Id || rewrite list_rearr16 || rewrite list_rearr15).

all : revgoals.
(* case of BotL rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst. 
apply derI with [].  2: apply dlNil.
rewrite <- nsext_def. apply NSctxt_nil.
acacD ; subst ;
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
  repeat (apply BotL || rewrite list_rearr16 || rewrite list_rearr15).

all : revgoals. (* ImpL and ImpR rules remain *)
(* case of ImpR rule *)
1-3:(rewrite <- list_rearr15; simpl;
     (rewrite list_rearr17_R || rewrite list_rearr16_R));
  constructor.

subst. rename_last eqll.  injection eqll as eql eqr. subst. 
rewrite dersrec_all in H0.  rewrite Forall_forall in *.
unfold can_exchL in H1. simpl in *.  
(* rewrite <- nsext_def in H1. fails, why? *)
rewrite <- nsext_def.
pose (H0 _ ( (or_introl eq_refl))) as H0re.
(* can't apply derI right away as premises will vary *)

acacD; subst; eapply derI; nsrule_rewrites;
  try (rewrite dersrec_all ; rewrite Forall_forall ; intros p inps ;
  simpl in inps ; sD ; subst ; 
  rewrite ?app_nil_r in * ; 
  rewrite ?app_nil_r ; rewrite <- ?list_rearr16'; unfold can_exchR in H1).

 eapply H1. left. reflexivity.
unfold nsext. reflexivity. reflexivity.

eapply H1. left. reflexivity.
unfold nsext. reflexivity.  rewrite <- app_assoc. reflexivity.

rewrite <- app_assoc. simpl.
eapply H1. left. reflexivity. reflexivity.
rewrite <- app_assoc. reflexivity.

eapply H1. left. reflexivity. reflexivity. reflexivity.

rewrite list_rearr16_R. rewrite app_assoc.
eapply H1. left. reflexivity. reflexivity. rewrite <- app_assoc.
rewrite <- list_rearr16_R. reflexivity.

(* now for the ImpL rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst. 
clear H H0 H3.
eapply derI.  rewrite <- nsext_def. apply NSctxt.  apply ImpL.
rewrite dersrec_all. rewrite Forall_forall. intros.
rewrite Forall_forall in H1. simpl in H1. simpl in H. sD.
subst.  unfold can_exchR in H1. unfold nsext. 
eapply H1.
left. reflexivity.
apply nsext_def. reflexivity.

subst.
unfold can_exchR in H1. rewrite app_comm_cons. 
eapply H1.
right. left. reflexivity. apply nsext_def. reflexivity.
Qed.

Check can_exchL.
Check can_exchR.
