Require Import cut.
Require Import Extraction.

Extraction Language Haskell.

(* Extraction works, but takes a while. *)
Time Extraction LNSKt_cut_elimination.

