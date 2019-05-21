
Require Import ssreflect.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.
Require Import lntacs.

Ltac ms_cgs acm := 
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_swapL_def' in acm ;
rewrite -> ?can_gen_swapR_def' in acm ;
unfold nslclext ; unfold nslext.

(* where exchange is in the first of two sequents of the modal rule *)
Ltac use_acm1 acm rs ith := 
(* interchange two sublists of list of formulae *)
derIrs rs ; [> 
apply NSlctxt2 || apply NSlclctxt' ;
assoc_single_mid ;
apply ith |
ms_cgs acm ;
list_assoc_r' ; simpl ; eapply acm ] ; [> | 
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; 
swap_tac.

(* where swapping is in second sequent of modal rule,
  in which conclusion has no principal formula *)
Ltac use_acm2s acm rs ith rw :=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
apply ith |
ms_cgs acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22 ; eapply acm ] ; [> | 
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; swap_tac.

Ltac use_acm_sw_sep acm rs swap ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ;
eapply acm in swap ] ;
[> (rewrite - list_rearr21 ; eapply swap) || 
  (list_assoc_r' ; simpl ; eapply swap) |
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ].

Ltac use_drs rs drs ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith | exact drs].

Ltac use_drs_mid rs drs ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
assoc_single_mid ; apply ith | exact drs].

Ltac use_acm_os acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith |
ms_cgs acm ;
eapply acm in swap ] ;
[> eapply swap |
  unfold nslext ; unfold nslclext ; reflexivity |
  reflexivity ].

