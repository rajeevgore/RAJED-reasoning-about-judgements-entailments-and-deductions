
Require Export List.
Set Implicit Arguments.
Export ListNotations.

Parameter PropVars : Set.

(* definition of Propositional Formulas, parameterised over prim prop set *)
Inductive PropF (V : Set): Set :=
 | Var : V -> PropF V
 | Not : PropF V -> PropF V
 | Imp : PropF V -> PropF V -> PropF V
 | And : PropF V -> PropF V -> PropF V
 | Or : PropF V -> PropF V -> PropF V
 | WBox : PropF V -> PropF V
 | WDia : PropF V -> PropF V
 | BBox : PropF V -> PropF V
 | BDia : PropF V -> PropF V
.

Inductive Seq (X : Set) : Set :=
  | mkseq : X -> X -> Seq X.

Check Seq_rect.
Check Seq_ind.
Check Seq_rec.

Print Seq_rect.
Print Seq_ind.
Print Seq_rec.

(* fails Error: Large non-propositional inductive types must be in Type
Inductive S3eq (X : Type) : Set :=
  | mks3eq : list X -> list X -> S3eq X.
*)

Check (Seq (list (PropF PropVars))).

Inductive seqrule (V : Set) : 
  list (Seq (list (PropF V))) -> Seq (list (PropF V)) -> Prop :=
  | Id : forall A Gamma Delta,
    In A Gamma -> In A Delta -> seqrule [] (mkseq Gamma Delta)
  | AndR : forall A B Gamma Delta,
    seqrule [mkseq Gamma (A :: Delta); mkseq Gamma (B :: Delta)]
      (mkseq Gamma ((And A B) :: Delta))
  | OrL : forall A B Gamma Delta,
    seqrule [mkseq (A :: Gamma) Delta; mkseq (B :: Gamma) Delta]
      (mkseq ((Or A B) :: Gamma) Delta)
  | AndL : forall A B Gamma Delta,
    seqrule [mkseq (A :: B :: Gamma) Delta] (mkseq ((And A B) :: Gamma) Delta)
  | OrR : forall A B Gamma Delta,
    seqrule [mkseq Gamma (A :: B :: Delta)] (mkseq Gamma ((Or A B) :: Delta))
  | ExchR : forall A B Gamma Delta1 Delta2,
    seqrule [mkseq Gamma (Delta1 ++ A :: B :: Delta2)]
     (mkseq Gamma (Delta1 ++ B :: A :: Delta2))
  | ExchL : forall A B Gamma1 Gamma2 Delta,
    seqrule [mkseq (Gamma1 ++ A :: B :: Gamma2) Delta]
     (mkseq (Gamma1 ++ B :: A :: Gamma2) Delta)
.

