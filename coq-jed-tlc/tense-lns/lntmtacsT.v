Add LoadPath "../general".

Require Import ssreflect.

Require Import genT gen.
Require Import ddT.
Require Import List_lemmasT.
Require Import gen_tacs swappedT lntT.
Require Import lntacsT.

Ltac ms_cgs acm := 
rewrite ?dersrec_map_2 ;
rewrite ?dersrec_map_single ;
rewrite -> ?Forall_map_single in acm ;
rewrite -> ?Forall_map_2 in acm ;
rewrite -> ?can_gen_swapL_def' in acm ;
rewrite -> ?can_gen_swapR_def' in acm ;
unfold nslclext ; unfold nslext.

Lemma ForallT_map_2_rev: forall (A B : Type) (P : B -> Type) (f : A -> B) (x y : A),
      iffT (P (f x) * P (f y)) (ForallT P (map f [x; y])).
Proof.  intros.  simpl.  split; intros HH; apply ForallT_2; tauto. Qed. 

Ltac ms_cgsTT1 acm :=
  try apply dersrec_map_2 ;
try apply dersrec_map_single ;
try (apply ForallT_map_2 in acm || apply ForallT_map_rev in acm );
try eapply can_gen_swapL_def' in acm ;
try eapply can_gen_swapR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac ms_cgsT_fst acm :=
  try apply dersrec_map_2 ;
try apply dersrec_map_single ;
try (apply ForallT_map_2 in acm || apply ForallT_map_rev in acm ).

Ltac ms_cgsT_snd acm acm1 acm2 :=
  (destruct acm as [acm1 acm2];
   ((eapply can_gen_swapL_def' in acm1; eapply can_gen_swapL_def' in acm2) ||
    (eapply can_gen_swapR_def' in acm1; eapply can_gen_swapR_def' in acm2))) ||
  (eapply can_gen_swapL_def' in acm || eapply can_gen_swapR_def' in acm).

Ltac ms_cgsT_all acm acm1 acm2 :=
  ms_cgsT_fst acm; ms_cgsT_snd acm acm1 acm2.

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

Ltac use_acm1TT acm rs ith := 
(* interchange two sublists of list of formulae *)
derIrs rs ; [> 
apply NSlctxt2 || apply NSlclctxt' ;
assoc_single_mid ;
apply ith |
ms_cgsTT1 acm ;
list_assoc_r' ; simpl] ; [>  eassumption | | 
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

Ltac use_acm_osTT acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith |
ms_cgsTT1 acm ] ;
[> apply acm | eapply swap |
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

Ltac use_acm_2TT acm rs swap ith :=
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
             let acm1 := fresh "acm" in
             let acm2 := fresh "acm" in
             ms_cgsT_all acm acm1 acm2 ;
             unfold nslclext;
             (exact swap || apply nslclext_def || reflexivity || split);
             [eapply acm1 | eapply acm2]].

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

Ltac use_acm_2_swT acm rs swap rw ith :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
             rw ; apply ith |];
              let acm1 := fresh "acm" in
              let acm2 := fresh "acm" in
              ms_cgsT_all acm acm1 acm2  ; 
                (apply nslclext_def || reflexivity || (split; [eapply acm1 | eapply acm2]) || idtac);
                (list_assoc_r'; swap_tac).

Ltac use_acm_2_sw'' acm rs swap rw1 rw2 rw3 rw4 ith :=
derIrs rs ; [> rw1 ;
apply NSlclctxt' || apply NSlctxt2 ;
rw2 ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_sw'' acm1 swap rw3 rw4 | 
        acmi_snr_sw'' acm2 swap rw3 rw4 ]
            ].

Ltac use_acm_2_sw''T acm rs swap rw1 rw2 rw3 rw4 ith :=
derIrs rs ; [> rw1 ;
apply NSlclctxt' || apply NSlctxt2 ;
rw2 ; apply ith | ];
              let acm1 := fresh "acm" in
              let acm2 := fresh "acm" in
ms_cgsT_all acm acm1 acm2;
((unfold nslclext; rw4; apply nslclext_def) ||
                                          reflexivity ||
                                          (unfold nslclext; split; [rw3; eapply acm1 | rw3; eapply acm2]) || idtac); swap_tac.

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

Ltac exchL2T rs sppc acm swap :=
derIrs rs ; [> list_assoc_l' ;
    apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
apply dersrec_forall ; intros L H ;
apply InT_mapE in H ; destruct H as [x H] ; destruct H as [H1 H2] ; subst ;
eapply InT_map in H2; eapply ForallTD_forall in acm ; [|exact H2];
eapply can_gen_swapL_imp in acm || eapply can_gen_swapR_imp in acm ;
  [> | exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact acm
  | unfold nslclext ; list_assoc_r' ; reflexivity].


Ltac use_acm2sT acm rs ith rw :=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
apply ith |
ms_cgsTT1 acm] ;
[list_assoc_r' ; simpl ; rewrite ?list_rearr22 ; eapply acm | |
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; swap_tac.

   Ltac use_acm_sw_sepT acm rs swap ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
             ms_cgsTT1 acm ] ;
[eapply acm | exact swap | reflexivity | reflexivity].

        Ltac use_acm_sw_sepT2 acm rs swap ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
             ms_cgsTT1 acm ] ;
[rewrite <- list_rearr21; eapply acm | exact swap |
 rewrite list_rearr21; reflexivity | reflexivity].

   Ltac use_acm_sw_sepT3 acm rs swap ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
             ms_cgsTT1 acm ] ;
[  rewrite <- app_nil_r; rewrite <- app_assoc; rewrite <- list_rearr21;
   eapply acm | exact swap | ..]; list_assoc_r'; reflexivity.
(*
   Ltac use_acm_2_sndTT acm rs swap ith :=
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |];
             let acm1 := fresh "acm" in
             let acm2 := fresh "acm" in
             ms_cgsT_all acm acm1 acm2;
               (exact swap || (rewrite list_rearr16'; apply nslclext_def)
                || reflexivity || idtac);
               split; rewrite list_rearr16'; (eapply acm1 || eapply acm2).



   Ltac use_acm_2_sndTT acm rs swap ith :=
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |];
             let acm1 := fresh "acm" in
             let acm2 := fresh "acm" in
             ms_cgsT_all acm acm1 acm2;
               (exact swap || (rewrite list_rearr16'; apply nslclext_def)
                || reflexivity || idtac);
               split; rewrite list_rearr16'; (eapply acm1 || eapply acm2).


*)

(*
   Ltac use_acm_2_sndTT acm rs swap ith :=
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |];
             let acm1 := fresh "acm" in
             let acm2 := fresh "acm" in
             ms_cgsT_all acm acm1 acm2;
               (exact swap || (rewrite list_rearr16'; apply nslclext_def)
                || reflexivity || idtac);
               split; rewrite list_rearr16'; (eapply acm1 || eapply acm2).


Ltac use_acm_2_sndTT acm rs swap ith :=
lntacsT.derIrs rs ; [> lntacsT.list_assoc_r' ;
apply lntT.NSlclctxt' || apply lntT.NSlctxt2 ;
apply ith |];
             let acm1 := fresh "acm" in
             let acm2 := fresh "acm" in
             ms_cgsT_all acm acm1 acm2;
               (exact swap || (rewrite List_lemmasT.list_rearr16'; apply lntT.nslclext_def)
                || reflexivity || idtac);
               split; rewrite List_lemmasT.list_rearr16'; (eapply acm1 || eapply acm2).


*)

