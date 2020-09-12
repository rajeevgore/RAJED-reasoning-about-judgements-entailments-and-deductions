
Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT.
Require Import swappedT.
Require Import fmlsext.
Require Import lldefs ll_exch ll_cam.
Require Import gstep.

Check cut_adm_mall'. (* which is cut-admissibility depending on exchange *)
Check adm_exch_mall. (* which is admissibility of exchange *)

(* cut admissibility for MALL *)
Definition cut_adm_mall V A := cut_adm_mall' A (@adm_exch_mall V).

