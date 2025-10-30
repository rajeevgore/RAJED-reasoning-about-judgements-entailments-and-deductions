From Ksat Require Import defs.
From Ksat Require Import full_language.

From KTsat Require Import defs.
From KTsat Require Import vanilla.

Require Import List.


Definition fml_is_sat (G : list fml) : bool := is_sat (map to_nnf G).

Theorem classical_correctness (G : list fml) :
  fml_is_sat G = true <-> exists (M : KT) w, fml_sat M w G.
Proof.
unfold fml_is_sat. setoid_rewrite sat_fml_nnf_iff. apply correctness.
Qed.