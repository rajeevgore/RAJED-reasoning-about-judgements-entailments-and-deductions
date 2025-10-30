From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import ops.

From S4sat Require Import data.
From S4sat Require Import defs.

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import String.
Open Scope string_scope.


Definition get_contra_seqt : forall se : seqt,
      {p : string | In (var p) (s_G se) /\ In (neg p) (s_G se)}
    + {forall p, In (var p) (s_G se) -> ~ In (neg p) (s_G se)} :=
fun se => get_contra (s_G se).

Definition get_and_seqt : forall se : seqt,
  {p : nnf * nnf | In (and (fst p) (snd p)) (s_G se)} +
  {forall phi psi, ~ In (and phi psi) (s_G se)} :=
fun se => get_and (s_G se).

Definition get_or_seqt : forall se : seqt,
  {p : nnf * nnf | In (or (fst p) (snd p)) (s_G se)} +
  {forall phi psi, ~ In (or phi psi) (s_G se)} :=
fun se => get_or (s_G se).

Definition get_box_seqt : forall se : seqt,
  {p : nnf | In (box p) (s_G se)}
+ {forall phi, ~ In (box phi) (s_G se)} :=
fun se => get_box (s_G se).

Definition get_dia_seqt : forall se : seqt,
  {p : nnf | In (dia p) (s_G se)}
+ {forall phi, ~ In (dia phi) (s_G se)} :=
fun se => get_dia (s_G se).