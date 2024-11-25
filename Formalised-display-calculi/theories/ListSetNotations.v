Require Import List ListSet.
Import ListNotations.
Require Import EqDec.

Section MSET_SET.
  Context {A : Type}.
  Context `{AED : EqDec A}.

  Definition count := count_occ eqdec.
  Definition erase := set_remove eqdec.

  Definition set_eq (l l' : list A) : Prop := forall x, In x l <-> In x l'.

  Definition mset_incl (l l' : list A) : Prop :=
    forall x, count l x <= count l' x.

  Definition mset_eq (l l' : list A) : Prop :=
    forall x, count l x = count l' x.
End MSET_SET.

Notation "x ∈ S" := (In x S) (at level 75).
Notation "x ∉ S" := (~ x ∈ S) (at level 75).
Notation "S ≃ T" := (set_eq S T) (at level 70).
Notation "S ⊆ T" := (incl S T) (at level 70).
Notation "S ≡ T" := (mset_eq S T) (at level 70).
Notation "S ⫅ T" := (mset_incl S T) (at level 70).
