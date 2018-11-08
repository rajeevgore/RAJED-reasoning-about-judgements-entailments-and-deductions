
Require Export List.
Set Implicit Arguments.
Export ListNotations.

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

Definition rel (W : Type) : Type := prod W W.
Definition rules (W : Type) : Type := list W -> W -> Prop.  
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

Inductive princrule (V : Set) : rules (rel (list (PropF V))) :=
  | Id : forall A, princrule [] (pair [A] [A])
  | ImpR : forall A B, princrule [pair [A] [B]] (pair [] [Imp A B])
  | ImpL : forall A B, princrule
    [pair [B] [] ; pair [] [A]] (pair [Imp A B] [])
  | BotL : princrule [] (pair [Bot V] []).

Definition seqext (W : Set) Γ1 Γ2 Δ1 Δ2 (seq : rel (list W)) :=
  match seq with | pair U V => pair (Γ1 ++ U ++ Γ2) (Δ1 ++ V ++ Δ2) end.

Inductive seqrule (W : Set) (pr : rules (rel (list W))) : 
    rules (rel (list W)) := 
  | Sctxt : forall ps c Γ1 Γ2 Δ1 Δ2, pr ps c -> 
    seqrule pr (map (seqext Γ1 Γ2 Δ1 Δ2) ps) (seqext Γ1 Γ2 Δ1 Δ2 c).

(* w : Set fails *)
Definition nsext (W : Type) G H (d : dir) (seq : W) := G ++ (seq, d) :: H.

Inductive nsrule (W : Set) (sr : rules (rel (list W))) : 
    rules (list (rel (list W) * dir)) :=
  | NSctxt : forall ps c G H d, sr ps c -> 
    nsrule sr (map (nsext G H d) ps) (nsext G H d c).

Check princrule.
Check seqext.
Check seqrule.
Check nsext.
Check nsrule.

