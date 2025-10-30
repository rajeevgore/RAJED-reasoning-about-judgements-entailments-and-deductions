From Ksat Require Import full_language.

From S4sat Require Import tableau.

Require Import List.
Import ListNotations.
Require Extraction.
Require Import Coq.extraction.ExtrOcamlNativeString.



Definition is_sat (phi : fml) : bool := fml_tableau_sat [phi].


Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
(* Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))". *)
Extraction "S4.ml" is_sat.
