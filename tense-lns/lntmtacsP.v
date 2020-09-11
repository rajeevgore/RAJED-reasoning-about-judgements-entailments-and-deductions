Add LoadPath "../general".

Require Import ssreflect.

Require Import gen.
Require Import ddP.
Require Import List_lemmasP.
Require Import lntP.
Require Import lntacsP.

Ltac ms_cgs acm := 
rewrite ?dersrec_map_2 ;
rewrite ?dersrec_map_single ;
rewrite -> ?Forall_map_single in acm ;
rewrite -> ?Forall_map_2 in acm ;
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

Ltac acmi_snr acmi swap := 
  eapply acmi ; [> exact swap | apply nslclext_def | reflexivity ].

Ltac use_acm_2 acm rs swap ith :=
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr acm1 swap | acmi_snr acm2 swap ]
].

Ltac acmi_snr_ass acmi swap := list_assoc_r' ; eapply acmi ;
  [> exact swap | 
    list_assoc_l' ; apply nslclext_def |
    reflexivity ].

Ltac use_acm_2_ass acm rs swap ith :=
derIrs rs ; [> list_assoc_l' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_ass acm1 swap | acmi_snr_ass acm2 swap ]
].

Ltac acmi_snr_snd acmi swap := rewrite list_rearr16' ; eapply acmi ;
  [> exact swap | 
    list_assoc_r' ; simpl ; apply nslclext_def |
    reflexivity ].

Ltac use_acm_2_snd acm rs swap ith :=
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_snd acm1 swap | acmi_snr_snd acm2 swap ]
].

Ltac acmi_snr_sw acmi swap := eapply acmi ;
  [> | apply nslclext_def | reflexivity ] ; [> swap_tac ].

Ltac acmi_snr_sw'' acmi swap rw3 rw4 := rw3 ; eapply acmi ;
  [> | rw4 ; apply nslclext_def | reflexivity ] ; [> swap_tac ].

Ltac use_acm_2_sw acm rs swap rw ith :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_sw acm1 swap | acmi_snr_sw acm2 swap ]
].

Ltac use_acm_2_sw'' acm rs swap rw1 rw2 rw3 rw4 ith :=
derIrs rs ; [> rw1 ;
apply NSlclctxt' || apply NSlctxt2 ;
rw2 ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_sw'' acm1 swap rw3 rw4 | 
        acmi_snr_sw'' acm2 swap rw3 rw4 ]
].

(* case of exchange in sequent to the left of where rule applied,
  no need to expand sppc *) 
Ltac exchL2 rs sppc acm swap :=
derIrs rs ; [> list_assoc_l' ;
    apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
rewrite dersrec_forall ; intros L H ;
rewrite -> in_map_iff in H ; destruct H ; destruct H as [H1 H2] ; subst ;
rewrite -> Forall_forall in acm ; eapply in_map in H2 ; eapply acm in H2 ;
eapply can_gen_swapL_imp in H2 || eapply can_gen_swapR_imp in H2 ;
  [> | exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact H2
    | unfold nslclext ; list_assoc_r' ; reflexivity].









