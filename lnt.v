
Require Export List.
Set Implicit Arguments.
Export ListNotations.
Require Import dd.
Require Import List_lemmas.

Parameter PropVars : Set.

(* Indicates the direction connecting sequents look. *)
Inductive dir : Type :=
| fwd : dir
| bac : dir.

(* definition of Propositional Formulas, parameterised over prim prop set *)
Inductive PropF (V : Set): Set :=
 | Var : V -> PropF V
 | Bot : PropF V
 | Imp : PropF V -> PropF V -> PropF V
 (*
 | Not : PropF V -> PropF V
 | And : PropF V -> PropF V -> PropF V
 | Or : PropF V -> PropF V -> PropF V
 *)
 | WBox : PropF V -> PropF V
 | WDia : PropF V -> PropF V
 | BBox : PropF V -> PropF V
 | BDia : PropF V -> PropF V
.

(* statement of exchL fails if using Type here 
Definition rel (W : Type) : Type := prod W W.
*)
Definition rel (W : Set) : Set := prod W W.
Definition rls (W : Type) : Type := list W -> W -> Prop.  
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
  | Id : forall A, princrule [] (pair [A] [A])
  | ImpR : forall A B, princrule [pair [A] [B]] (pair [] [Imp A B])
  | ImpL : forall A B, princrule
    [pair [B] [] ; pair [] [A]] (pair [Imp A B] [])
  | BotL : princrule [] (pair [Bot V] []).

Definition seqext (W : Set) Γ1 Γ2 Δ1 Δ2 (seq : rel (list W)) :=
  match seq with | pair U V => pair (Γ1 ++ U ++ Γ2) (Δ1 ++ V ++ Δ2) end.

Inductive seqrule (W : Set) (pr : rls (rel (list W))) : 
    rls (rel (list W)) := 
  | Sctxt : forall ps c Γ1 Γ2 Δ1 Δ2, pr ps c -> 
    seqrule pr (map (seqext Γ1 Γ2 Δ1 Δ2) ps) (seqext Γ1 Γ2 Δ1 Δ2 c).

(* w : Set fails *)
Definition nsext (W : Type) G H (d : dir) (seq : W) := G ++ (seq, d) :: H.
Lemma nsext_def: forall (W : Type) G H d seq, 
  @nsext W G H (d : dir) (seq : W) = G ++ (seq, d) :: H.
Proof.
unfold nsext. reflexivity.
Qed.

Inductive nsrule (W : Set) (sr : rls (rel (list W))) : 
    rls (list (rel (list W) * dir)) :=
  | NSctxt : forall ps c G H d, sr ps c -> 
    nsrule sr (map (nsext G H d) ps) (nsext G H d c).

Check princrule.
Check seqext.
Check seqrule.
Check nsext.
Check nsrule.

Definition can_exchL (V : Set) 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ1 (A B : PropF V) Γ2 Δ, 
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ A :: B :: Γ2) Δ ->
  derrec rules (fun _ => False) (G ++ (pair (Γ1 ++ B :: A :: Γ2) Δ, d) :: H).

(*
Lemma exchL: forall (V : Set) ns (D : derrec (nsrule (seqrule (@princrule V))) 
  (fun _ => False) ns) G H seq d Γ1 A B Γ2 Δ, 
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ A :: B :: Γ2) Δ ->
  derrec (nsrule (seqrule (@princrule V))) (fun _ => False) 
    (G ++ (pair (Γ1 ++ B :: A :: Γ2) Δ, d) :: H).
intro.  intro.  intro.
Check derrec_all_ind.
eapply derrec_all_ind in D.
(* eexact D. fails - why? *)
*)

(*
Lemma exchL: forall (V : Set) ns 
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_exchL (nsrule (seqrule (@princrule V))) ns.
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
(* these need fixing 
cE. clear H7. inversion_clear H10.
inversion H3.  subst.  clear H.
unfold seqext in H3.

apply app_eq_app in .  
*)






*)

(* or, which doesn't work without using can_exchL
intro.  intro.
eapply derrec_all_ind.
tauto.
*)


