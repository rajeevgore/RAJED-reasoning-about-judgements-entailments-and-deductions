From Ksat Require Import defs.
From Ksat Require Import size.
From Ksat Require Import ops.
From Ksat Require Import semantics.
From Ksat Require Import model.
From Ksat Require Import full_language.
From Ksat Require Import marking.
From Ksat Require Import rules.
From Ksat Require Import jump.

Require Import List.
Import ListNotations.


Definition fml_is_sat (G : list fml) : bool := is_sat (map to_nnf G).

Theorem classical_correctness (G : list fml) :
  fml_is_sat G = true <-> exists (k : kripke) s, fml_sat k s G.
Proof.
unfold fml_is_sat. setoid_rewrite sat_fml_nnf_iff. apply correctness.
Qed.