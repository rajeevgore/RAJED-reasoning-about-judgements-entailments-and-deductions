Require Import String.
Require Import List.
Require Import Arith.

Definition eq_dec (A : Type) := forall (x y : A), {x = y} + {x <> y}.
Definition iffT (A B : Type) : Type := (A -> B) * (B -> A).
Notation "A <+> B" := (iffT A B) (at level 50).

Class EqDec (A : Type) := {
  eqdec : forall x y : A, {x = y} + {x <> y} }.

#[export] Instance EqDec_nat : EqDec nat := {| eqdec := Nat.eq_dec |}.
#[export] Instance EqDec_list {A} `{AED : EqDec A} : EqDec (list A) :=
{| eqdec := list_eq_dec eqdec |}.
#[export] Instance EqDec_prod {A B} `{AED : EqDec A} `{BED : EqDec B} : EqDec (A * B).
constructor. decide equality; apply eqdec. Defined.
#[export] Instance EqDec_string : EqDec string := {| eqdec := string_dec |}.
