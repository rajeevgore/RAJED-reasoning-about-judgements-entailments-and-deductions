Require Import ssreflect.
 
Require Import gen.
Require Import ddP.
Require Import List_lemmasP.
Require Import lntP lntacsP lntlsP lntbRP lntmtacsP.
Require Import lntb1LP lntb2LP.
Require Import lnt_weakeningP.
Require Import lntkt_exchP.
Require Import swappedP.
Require Import lnt_contractionP.

(* ------- *)
(* TACTICS *)
(* ------- *)

Ltac ms_cgs_cont acm := 
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_contL_gen_def' in acm ;
rewrite -> ?can_gen_contR_gen_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac use_acm_os_cont acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith |
ms_cgs_cont acm ;
eapply acm in swap ] ;
[> eapply swap |
  unfold nslext ; unfold nslclext ; reflexivity |
  reflexivity ].

Ltac nsgen_sw_cont rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; subst q ;
rewrite -> Forall_forall in acm ;
rename_last inps0 ;  eapply in_map in inps0 ;
eapply acm in inps0 ;
rewrite -> ?can_gen_contL_gen_def' in inps0 ;
rewrite -> ?can_gen_contR_gen_def' in inps0 ; 
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply inps0 ; [> exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | reflexivity ]].

Ltac rem_nil_hyp :=
  repeat match goal with
  | [ H : context[ [] ++ ?A ] |- _ ] => rem_nil_hyp_arg H
  | [ H : context[ ?A ++ [] ] |- _ ] => rem_nil_hyp_arg H
  | _ => idtac
  end.

Ltac rem_nil := rem_nil_hyp; rem_nil_goal.

Ltac check_nil_cons_contr :=
  match goal with
  | [H : [] = ?l1 ++ ?a :: ?l2 |- _] => contradiction (nil_eq_list l1 l2 a H)
  | [H : ?l1 ++ ?a :: ?l2 = [] |- _] => symmetry in H; contradiction (nil_eq_list l1 l2 a H)
  | _ => idtac
  end.

Ltac cont_solve2 :=
   match goal with
   | [ |- context[?a :: ?l]] =>
     match l with
     | context[?a :: ?l2] =>  
   list_assoc_r_single;
   eapply (contracted_gen__spec a);
   cont_solve
     end
   end.

Ltac cont_setup_constr constr :=
  match goal with
  | [ |- context[ (@constr ?V ?A) :: ?l ] ] => list_assoc_r_single; assoc_mid ([@constr V A])
  end.

Ltac use_acm1_cont_constr acm rs ith constr :=
     derIrs rs; [ 
apply NSlctxt2 || apply NSlclctxt' ;
cont_setup_constr constr;
apply ith | 
ms_cgs_cont acm ;
  list_assoc_r' ; simpl] ;
   first [eapply acm | list_assoc_l'; rewrite <- app_assoc; eapply acm];
   unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl; try reflexivity; cont_solve2.

Ltac use_acm2s_cont acm rs ith :=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
apply ith |
ms_cgs_cont acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22 ; eapply acm ] ; [> | 
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; cont_solve2.

Ltac cont_setup_apply_constr constr :=
  list_assoc_r_single;
  match goal with
  | [ acm : context[ @constr ?V ?A ] |- _ ] =>
    repeat match goal with
    | [ acm : context[ ?l1 ++ A :: ?l2 ++ ?l3 ] |-
        derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
      match K1 with
      | ?l5 ++ l2 ++ ?l4 => idtac
      | ?l5 ++ ?l4 => rewrite (app_assoc l5)
      end
    end
  end.

Ltac cont_setup_apply_constr2 constr :=
  list_assoc_r_single;
  match goal with
  | [ acm : context[ @constr ?V ?A ] |- _ ] =>
    repeat match goal with
    | [ acm : context[ ?l1 ++ A :: ?l2 ++ ?l3 ] |-
        derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
      match K1 with
      | ?l5 ++ l3 ++ ?l4 => idtac
      | ?l5 ++ ?l4 => rewrite (app_assoc l5)
      end
    end
  end.

Ltac cont_setup_apply_constr3 constr :=
  list_assoc_r_single;
  match goal with
  | [ acm : context[ @constr ?V ?A ] |- _ ] =>
    repeat match goal with
    | [ acm : context[ ?l1 ++ A :: ?l2 ] |-
        derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
      match K1 with
      | ?l5 ++ l2 ++ ?l4 => idtac
      | ?l5 ++ ?l4 => rewrite (app_assoc l5)
      end
    end
  end.

Ltac use_acm2s_cont' acm rs ith constr :=
  derIrs rs ;
  [> apply NSlctxt2 || apply NSlclctxt' ;
   apply ith |
   ms_cgs_cont acm ;
   list_assoc_r' ; simpl ;
   rewrite ?list_rearr22 ; eapply acm ] ;
  [> | unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; cont_solve2.

Ltac use_acm_sw_sep_cont acm rs weak ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs_cont acm ;
eapply acm in weak ] ;
[> (rewrite - list_rearr21 ; eapply weak) || 
  (list_assoc_r' ; simpl ; eapply weak) |
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ].

Ltac cont_setup_apply_constr4 constr :=
  list_assoc_r_single;
  repeat match goal with
         | [ acm : context[ ?l1 ++ @constr ?V ?A :: ?l2 ++ ?l3 ] |-
             derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
         end.

Ltac cont_setup_apply_constr5 constr :=
  list_assoc_r_single;
  repeat match goal with
         | [ acm : context[ ?l1 ++ @constr ?V ?A :: ?l3 ++ ?l2 ] |-
             derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
         end.

Ltac cont_setup_apply_constr6 constr :=
  list_assoc_r_single;
  repeat match goal with
         | [ acm : context[ ?l1 ++ @constr ?V ?A :: ?l2 ] |-
             derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
         end.

Ltac cont_setup_apply_constr7 constr:=
  list_assoc_r_single;
  repeat match goal with
         | [ acm : context[ ?l1 ++ @constr ?V ?A :: ?l2 ] |-
             derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
           match K1 with
           | ?l5 ++ [@constr V A] ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
         end.

Ltac no_use_acm_cont rs drs constr:=
  derIrs rs;
  [apply NSlclctxt'; apply constr |
   exact drs].

Ltac acmi_snr_cont acmi swap := 
  eapply acmi ; [> apply nslclext_def | reflexivity ].

Ltac use_acm_2_cont acm rs swap ith :=
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
inversion swap; (subst; split ; 
[ acmi_snr_cont acm1 swap | acmi_snr_cont acm2 swap ])
            ].

Lemma can_gen_contL_gen_imp: forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_contL_gen rules ns -> forall G K seq Γ Δ Γ' (d : dir), 
  contracted_gen Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros until 0. intro.
  rewrite -> can_gen_contL_gen_def' in H. exact H. Qed.

Lemma can_gen_contR_gen_imp: forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_contR_gen rules ns -> forall G K seq Γ Δ Δ' (d : dir), 
  contracted_gen Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K).
Proof.  intros until 0. intro.
  rewrite -> can_gen_contR_gen_def' in H. exact H. Qed.


Ltac contL2 rs sppc acm swap :=
derIrs rs ; [> list_assoc_l' ;
    apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
rewrite dersrec_forall ; intros L H ;
rewrite -> in_map_iff in H ; destruct H ; destruct H as [H1 H2] ; subst ;
rewrite -> Forall_forall in acm ; eapply in_map in H2 ; eapply acm in H2 ;
eapply can_gen_contL_gen_imp in H2 || eapply can_gen_contR_gen_imp in H2 ;
  [> | exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact H2
    | unfold nslclext ; list_assoc_r' ; reflexivity].

Ltac use_acm_2_snd_cont acm rs swap ith :=
derIrs rs ; [ list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
inversion swap; (subst; split;
[ acmi_snr_snd_weak acm1 swap | acmi_snr_snd_weak acm2 swap ])
            ].


Ltac ltstart' acm acm1 acm2 :=
  ms_cgs acm ; destruct acm as [acm1 acm2];
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  list_assoc_r_single.

Ltac ltsolve' acm1a acm1b acm2a acm2b :=
  list_assoc_r_s_arg acm1a;
  list_assoc_r_s_arg acm1b;
  list_assoc_r_s_arg acm2a;
  list_assoc_r_s_arg acm2b;
  list_assoc_r_single;
  split; [ exact acm1a || exact acm1b | exact acm2a || exact acm2b].

Ltac ltsolve_pre acm1a acm1b acm2a acm2b :=
  list_assoc_r_s_arg acm1a;
  list_assoc_r_s_arg acm1b;
  list_assoc_r_s_arg acm2a;
  list_assoc_r_s_arg acm2b;
  list_assoc_r_single.

Ltac ltsolve_end acm1a acm1b acm2a acm2b :=
    split; [ exact acm1a || exact acm1b | exact acm2a || exact acm2b].

Ltac ltmidacm' acm1 acm2 acm1a acm1b acm2a acm2b :=
  edestruct acm1 as [acm1a acm1b]; [reflexivity | reflexivity |];
  edestruct acm2 as [acm2a acm2b]; [reflexivity | reflexivity |].


Ltac ltbrack1 acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G ([(?Γ, ?l, ?d)] ++ ?seq)) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 => idtac
    | ?l2 ++ (?l3 ++ ?l4) => rewrite (app_assoc l2) in acm1
    end
         end.

Ltac ltbrack2 acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G ([(?Γ, ?l, ?d)] ++ ?seq)) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ [a] ++ ?l4 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ ?l4 => rewrite (app_assoc l3) in acm1
    end
         end.

Ltac assoc_mid_hyp l H := 
  list_assoc_r_s_arg H ;
  rewrite ?app_comm_cons in H ;
  repeat ((rewrite - (app_assoc _ l _) in H; fail 1) || rewrite app_assoc in H) ;
  rewrite - (app_assoc _ l _)  in H.

Ltac ltbrack_concl_pre Γ l :=
  repeat match goal with
  | [ |- context[ (Γ, ?l1, ?d) ] ] =>
    match l1 with
    | l ++ ?l2 => idtac
    | ?l2 ++ ?l3 => rewrite (app_assoc l2)
    end
         end.

Ltac ltbrack_concl acm1 :=
  match type of acm1 with
  | context[ [(?Γ, ?l1 ++ [?A] ++ ?l2, ?d)] ++ ?seq ] =>
    ltbrack_concl_pre Γ l1
  end.

Ltac ltapplyrule rs WBox1Rs acm1 :=
  derIrs rs; [apply NSlclctxt'; simpl; apply WBox1Rs |
              list_assoc_r_single; ms_cgs acm1].

Ltac ltsolve_full_pre acm acm1 acm2 acm1a acm1b acm2a acm2b A rs WBox1Rs a :=
  ltstart' acm acm1 acm2;
  assoc_mid_hyp [A] acm1;
  ltbrack_concl acm1;
  ltapplyrule rs WBox1Rs acm1;
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  ltbrack1 acm1 a;
  ltbrack2 acm1 a;
  ltbrack1 acm2 a;
  ltbrack2 acm2 a;
  ltmidacm' acm1 acm2 acm1a acm1b acm2a acm2b.

Ltac apply_exch Hexch :=
  eapply Hexch; [tauto | | reflexivity | reflexivity].

Ltac sep_nil :=
  match goal with
  | [ |- context[ [?a] ++ [?a] ++ ?l2] ] =>
    rewrite <- (app_nil_l ([a] ++ l2))
  end.

Ltac ltapplyrule2 rs rw WBox1Rs acm1 :=
  derIrs rs; [apply NSlclctxt'; rw; simpl; apply WBox1Rs |
  list_assoc_r_single; ms_cgs acm1].

Ltac ltbrack1_snd acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G (?seq ++ [(?Γ, ?l, ?d)])) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 => idtac
    | ?l2 ++ (?l3 ++ ?l4) => rewrite (app_assoc l2) in acm1
    end
  end.

Ltac ltbrack2_snd acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G (?seq ++ [(?Γ, ?l, ?d)])) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ [a] ++ ?l4 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ ?l4 => rewrite (app_assoc l3) in acm1
    end
  end.

Ltac ltbrack1_mid acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G (?seq ++ [(?Γ, ?l, ?d)] ++ ?seq2)) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 => idtac
    | ?l2 ++ (?l3 ++ ?l4) => rewrite (app_assoc l2) in acm1
    end
  end.

Ltac ltbrack2_mid acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G (?seq ++ [(?Γ, ?l, ?d)] ++ ?seq2)) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ [a] ++ ?l4 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ ?l4 => rewrite (app_assoc l3) in acm1
    end
  end.

Ltac ltmidacm'2 acm1 acm2 acm1a acm1b acm2a acm2b G :=
  edestruct acm1 as [acm1a acm1b];
  [unfold nslclext; rewrite (app_assoc G); reflexivity | reflexivity |];
  edestruct acm2 as [acm2a acm2b];
  [unfold nslclext; rewrite (app_assoc G); reflexivity | reflexivity |].  

Ltac ltsolve_full_pre2 acm acm1 acm2 acm1a acm1b acm2a acm2b A rs Constr WBox1Rs a G:=
  ltstart' acm acm1 acm2;
  assoc_mid_hyp [A] acm1;
  ltbrack_concl acm1;
  ltapplyrule2 rs ltac : (assoc_mid [(@Constr _  A)]) WBox1Rs acm1;
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  ltbrack1_snd acm1 a;
  ltbrack2_snd acm1 a;
  ltbrack1_mid acm2 a;
  ltbrack2_mid acm2 a;
  ltmidacm'2 acm1 acm2 acm1a acm1b acm2a acm2b G.

Ltac ltmidacm'3 acm1 acm2 acm1a acm1b acm2a acm2b G :=
  edestruct acm1 as [acm1a acm1b];
  [unfold nslclext; rewrite (app_assoc G); reflexivity | try sep_nil; reflexivity |];
  edestruct acm2 as [acm2a acm2b];
  [unfold nslclext; rewrite (app_assoc G); reflexivity | try sep_nil ; reflexivity |].

Ltac ltsolve_full_pre3 acm acm1 acm2 acm1a acm1b acm2a acm2b A rs Constr WBox1Rs a G:=
  ltstart' acm acm1 acm2;
  ltbrack_concl acm1;
  ltapplyrule2 rs ltac : (assoc_mid [@Constr _ A]) WBox1Rs acm1;
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  ltbrack1_snd acm1 a;
  ltbrack2_snd acm1 a;
  ltbrack1_mid acm2 a;
  ltbrack2_mid acm2 a;
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  ltmidacm'3 acm1 acm2 acm1a acm1b acm2a acm2b G.

Ltac b1R_extra1 Hexch acm1b acm2a A0 :=
  split;
  [rewrite (app_assoc A0); apply_exch Hexch;
   list_assoc_r_single; apply_exch Hexch;
   exact acm1b |
   apply_exch Hexch; exact acm2a].

Ltac b1R_extra2 Hexch acm1b acm2b A0 H4 :=
  split;
  [rewrite (app_assoc A0); rewrite (app_assoc H4);
   apply_exch Hexch; list_assoc_r_single; exact acm1b |
   exact acm2b].

Ltac b1R_extra3 Hexch acm1b acm2b A0 :=
  split;
  [rewrite (app_assoc A0); apply_exch Hexch;
   list_assoc_r_single; exact acm1b | exact acm2b].

Ltac b1R_extra1_look Hexch acm1b acm2a :=
  match goal with
  | [ |- context[ _ ++ [(?Γ, ?A0 ++ ?l, ?d)] ++ _ ] ] =>
    b1R_extra1 Hexch acm1b acm2a A0
  end.

Ltac b1R_extra2_look Hexch acm1b acm2b :=
  match goal with
  | [ |- context[ _ ++ [(?Γ, ?A0 ++ ?l ++ ?H4 ++ ?l2, ?d)] ++ _ ] ] =>
    b1R_extra2 Hexch acm1b acm2b A0 H4
  end.

Ltac b1R_extra3_look Hexch acm1b acm2b :=
  match goal with
  | [ |- context[ _ ++ [(?Γ, ?A0 ++ ?l, ?d)] ++ _ ] ] =>
    b1R_extra3 Hexch acm1b acm2b A0
  end.

Ltac ltsolve_full acm A rs WBox1Rs a Hexch :=
  let acm1 := fresh "acm1" in let acm2 := fresh "acm2" in
  let acm1a := fresh "acm1a" in let acm1b := fresh "acm1b" in
  let acm2a := fresh "acm2a" in let acm2b := fresh "acm2b" in               
  ltsolve_full_pre acm acm1 acm2 acm1a acm1b acm2a acm2b A rs WBox1Rs a;
  ltsolve_pre acm1a acm1b acm2a acm2b;
  try ltsolve_end acm1a acm1b acm2a acm2b;   
  b1R_extra1_look Hexch acm1b acm2a ||
  b1R_extra2_look Hexch acm1b acm2b ||
  b1R_extra3_look Hexch acm1b acm2b.

Ltac ltsolve_full23 acm A rs WBox WBox1Rs a G :=
  let acm1 := fresh "acm1" in let acm2 := fresh "acm2" in
  let acm1a := fresh "acm1a" in let acm1b := fresh "acm1b" in
  let acm2a := fresh "acm2a" in let acm2b := fresh "acm2b" in               
  (ltsolve_full_pre2 acm acm1 acm2 acm1a acm1b acm2a acm2b A rs WBox WBox1Rs a G ||
  ltsolve_full_pre3 acm acm1 acm2 acm1a acm1b acm2a acm2b A rs WBox WBox1Rs a G);
  ltsolve' acm1a acm1b acm2a acm2b.
   
Ltac process swap :=
  inversion_clear swap; subst;
  repeat (acacDe ; subst ; simpl ; rem_nil).
    

(* ------------------------ *)
(* CONTRACTION FOR B2RRULES *)
(* ------------------------ *)

Lemma gen_contL_gen_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contL_gen_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
   + use_acm_os_cont acm rs weak WBox2Rs.
   + use_acm_os_cont acm rs weak BBox2Rs. }
(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_cont rs sppc c (Γ', Δ, d) acm inps0 weak. }
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
    * use_acm_os_cont acm rs weak WBox2Rs.
    }
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
    * use_acm_os_cont acm rs weak BBox2Rs.
    }
  }
Qed.

Lemma gen_contR_gen_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contR_gen_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak; subst;
   repeat (acacD' ; subst ; simpl ; rem_nil) ;
   try discriminate; rem_nil; subst;
   check_nil_cons_contr;   
   use_acm1_cont_constr acm rs WBox2Rs WBox. }
+{ inversion_clear weak; subst;
   repeat (acacD' ; subst ; simpl ; rem_nil) ;
   try discriminate; rem_nil; subst;
   check_nil_cons_contr;
   use_acm1_cont_constr acm rs BBox2Rs BBox.
     (* 10 subgoals *)
}
}
-{ nsgen_sw_cont rs sppc c (Γ, Δ', d) acm inps0 weak. }
-{ inversion sppc ; subst ; clear sppc.  (* 2 subgoals *)
(* WBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
*{ inversion_clear weak; subst;
   repeat (acacD' ; subst ; simpl ; rem_nil) ;
   try discriminate; rem_nil; subst;
   check_nil_cons_contr;   
    use_acm1_cont_constr acm rs WBox2Rs WBox. }
}
(* BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
*{ inversion_clear weak; subst;
   repeat (acacD' ; subst ; simpl ; rem_nil) ;
   try discriminate; rem_nil; subst;
   check_nil_cons_contr;   
    use_acm1_cont_constr acm rs BBox2Rs BBox. }
} }
Qed.


(* ------------------------ *)
(* CONTRACTION FOR B1LRULES *)
(* ------------------------ *)

Lemma gen_contL_gen_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contL_gen_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* swap in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
   +{ inversion_clear weak; subst;
      repeat (acacD' ; subst ; simpl ; rem_nil) ;
      try discriminate; rem_nil; subst;
      check_nil_cons_contr;
      use_acm1_cont_constr acm rs WBox1Ls WBox.
    }
   +{ inversion_clear weak; subst;
      repeat (acacD' ; subst ; simpl ; rem_nil) ;
      try discriminate; rem_nil; subst;
      check_nil_cons_contr;
      use_acm1_cont_constr acm rs BBox1Ls BBox.
    }
 }
(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_cont rs sppc c (Γ', Δ, d) acm inps0 weak. }

(* here, weak in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak; subst;
      repeat (acacD' ; subst ; simpl ; rem_nil) ;
      try discriminate; rem_nil; subst;
      check_nil_cons_contr;
      use_acm1_cont_constr acm rs WBox1Ls WBox.
 }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak; subst;
acacD' ; subst;
  try (  acacDe; subst; rem_nil;
  (cont_setup_apply_constr WBox;
   use_acm2s_cont' acm rs WBox1Ls WBox) ||
  (cont_setup_apply_constr2 WBox;
   use_acm2s_cont' acm rs WBox1Ls WBox) ||
  (cont_setup_apply_constr3 WBox;
   use_acm2s_cont' acm rs WBox1Ls WBox)).
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)

{ use_acm2s_cont acm rs WBox1Ls. }
  }
  }

(* WBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak; subst;
      repeat (acacD' ; subst ; simpl ; rem_nil) ;
      try discriminate; rem_nil; subst;
      check_nil_cons_contr;
      use_acm1_cont_constr acm rs BBox1Ls BBox.
 }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak; subst;
acacD' ; subst;
  try (  acacDe; subst; rem_nil;
  (cont_setup_apply_constr BBox;
   use_acm2s_cont' acm rs BBox1Ls BBox) ||
  (cont_setup_apply_constr2 BBox;
   use_acm2s_cont' acm rs BBox1Ls BBox) ||
  (cont_setup_apply_constr3 BBox;
   use_acm2s_cont' acm rs BBox1Ls BBox)).
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)

{ use_acm2s_cont acm rs BBox1Ls. }
  }
 }
 }
Qed.

Lemma gen_contR_gen_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contR_gen_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contR_gen_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; [> 
  use_acm_sw_sep_cont acm rs weak WBox1Ls |
  use_acm_sw_sep_cont acm rs weak BBox1Ls ]. }
-{ nsgen_sw_cont rs sppc c (Γ, Δ', d) acm inps0 weak. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_cont acm rs weak WBox1Ls. }
*{ use_acm_sw_sep_cont acm rs weak WBox1Ls. }
}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_cont acm rs weak BBox1Ls. }
*{ use_acm_sw_sep_cont acm rs weak BBox1Ls. }
}
}  
Qed.

(* ------------------------ *)
(* CONTRACTION FOR B2LRULES *)
(* ------------------------ *)

Lemma gen_contL_gen_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contL_gen_step.
intros lreq nsr drs acm rs. (* no clear drs. *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contL_gen_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* weak in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak; subst;
   acacD' ; subst ; simpl ; rewrite ?app_nil_r; (* 4 subgoals *)
       acacDe; subst; rem_nil;
      try (cont_setup_apply_constr4 WBox;
           use_acm2s_cont' acm rs WBox2Ls WBox);
      try (cont_setup_apply_constr5 WBox;
           use_acm2s_cont' acm rs WBox2Ls WBox);
      try (cont_setup_apply_constr6 WBox;
           use_acm2s_cont' acm rs WBox2Ls WBox);
      use_acm2s_cont' acm rs WBox2Ls WBox.
 }
+{ inversion_clear weak; subst;
   acacD' ; subst ; simpl ; rewrite ?app_nil_r; (* 4 subgoals *)
   acacDe; subst; rem_nil;
      try (cont_setup_apply_constr4 BBox;
           use_acm2s_cont' acm rs BBox2Ls BBox);
      try (cont_setup_apply_constr5 BBox;
           use_acm2s_cont' acm rs BBox2Ls BBox);
      try (cont_setup_apply_constr6 BBox;
           use_acm2s_cont' acm rs BBox2Ls BBox);
      use_acm2s_cont' acm rs BBox2Ls WBox.
}
 }
(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_cont rs sppc c (Γ', Δ, d) acm inps0 weak. }

(* here, swap in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
   +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
+{ inversion_clear weak; subst;
   acacD' ; subst ; simpl ; rewrite ?app_nil_r; (* 4 subgoals *)
       acacDe; subst; rem_nil;
      try (cont_setup_apply_constr4 WBox;
           use_acm2s_cont' acm rs WBox2Ls WBox);
      try (cont_setup_apply_constr5 WBox;
           use_acm2s_cont' acm rs WBox2Ls WBox);
      try (cont_setup_apply_constr6 WBox;
           use_acm2s_cont' acm rs WBox2Ls WBox);
      use_acm2s_cont' acm rs WBox2Ls WBox.
 }

+{ inversion_clear weak; subst;
   acacD' ; subst ; simpl ; rewrite ?app_nil_r; (* 4 subgoals *)
   acacDe; subst; rem_nil;
   try  (list_assoc_r_single; no_use_acm_cont rs drs WBox2Ls);
   try (   list_assoc_r_single; cont_setup_apply_constr7 WBox;
           no_use_acm_cont rs drs WBox2Ls).
 }
    }

(* BBox *)
   +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
+{ inversion_clear weak; subst;
   acacD' ; subst ; simpl ; rewrite ?app_nil_r; (* 4 subgoals *)
       acacDe; subst; rem_nil;
      try (cont_setup_apply_constr4 BBox;
           use_acm2s_cont' acm rs BBox2Ls BBox);
      try (cont_setup_apply_constr5 BBox;
           use_acm2s_cont' acm rs BBox2Ls BBox);
      try (cont_setup_apply_constr6 BBox;
           use_acm2s_cont' acm rs BBox2Ls BBox);
      use_acm2s_cont' acm rs BBox2Ls BBox.
 }
 
+{ inversion_clear weak; subst;
   acacD' ; subst ; simpl ; rewrite ?app_nil_r; (* 4 subgoals *)
   acacDe; subst; rem_nil;
   try  (list_assoc_r_single; no_use_acm_cont rs drs BBox2Ls);
   try (   list_assoc_r_single; cont_setup_apply_constr7 BBox;
           no_use_acm_cont rs drs BBox2Ls).
 }
    }
 }
Qed.

Lemma gen_contR_gen_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contR_gen_step.
intros lreq nsr drs acm rs. (* no clear drs! *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contR_gen_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; 
  [> use_acm_sw_sep_cont acm rs weak WBox2Ls |
     use_acm_sw_sep_cont acm rs weak BBox2Ls ]. }
-{ nsgen_sw_cont rs sppc c (Γ, Δ', d) acm inps0 weak. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_cont acm rs weak WBox2Ls. }
*{ use_drs rs drs WBox2Ls. }
}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_cont acm rs weak BBox2Ls. }
*{ use_drs rs drs BBox2Ls. }
}
}  
Qed.


(* ------------------------ *)
(* CONTRACTION FOR B1RRULES *)
(* ------------------------ *)

Lemma gen_contL_gen_step_b1R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1rrules V) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contL_gen_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contL_gen_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
   + use_acm_2_cont acm rs swap WBox1Rs.
   + use_acm_2_cont acm rs swap BBox1Rs.
 }
(* case of exchange in sequent to the left of where rule applied,
  no need to expand sppc *) 
- contL2 rs sppc acm swap.

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
* use_acm_2_cont acm rs swap WBox1Rs.
(* swapping in antecedent of second sequent in rule skeleton *)
*  use_acm_2_snd_cont acm rs swap WBox1Rs.

}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
* use_acm_2_cont acm rs swap BBox1Rs.
(* swapping in antecedent of second sequent in rule skeleton *)
* use_acm_2_snd_cont acm rs swap BBox1Rs.
 }
 } 
Qed.

Lemma gen_contR_gen_step_b1R_lc: forall V ps concl last_rule rules,
(forall (V : Set) ns
  (D : derrec rules (fun _ => False) ns),
      can_gen_swapR rules ns) ->
  last_rule = nslclrule (@b1rrules V) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hexch. unfold gen_contR_gen_step.
  intros lreq nsr drs acm rs. clear drs. subst.
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  rewrite can_gen_contR_gen_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.
  acacD' ; subst ; rem_nil. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

  -{ inversion sppc ; subst ; clear sppc. (* 2 subgoals, WBox and BBox *)
     +{ process swap; ltsolve_full acm A rs WBox1Rs a Hexch. }
     +{ process swap; ltsolve_full acm A rs BBox1Rs a Hexch. }
   }     
  -{ contL2 rs sppc acm swap. }
  -{ inversion sppc ; subst ; clear sppc. (* 2 subgoals, WBox and BBox *)
     +{ acacDe ; subst ; simpl ; rem_nil. (* 2 subgoals *)
        (* swap in first sequent in rule skeleton *)
        *{ process swap ; ltsolve_full acm A rs WBox1Rs a Hexch. }   
        *{ process swap ; check_nil_cons_contr; 
           ltsolve_full23 acm A rs WBox WBox1Rs a G. }
      }
      
     +{ acacDe ; subst ; simpl ; rem_nil. (* 2 subgoals *)
        (* swap in first sequent in rule skeleton *)
        *{ process swap; ltsolve_full acm A rs BBox1Rs a Hexch. }   
        *{ process swap; check_nil_cons_contr; 
           ltsolve_full23 acm A rs BBox BBox1Rs a G. }
      }
   }
Qed.


(* ------------------ *)
(* CONTRACTION FOR EW *)
(* ------------------ *)

Lemma gen_contR_gen_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contR_gen_step.
intros lreq nsr drs acm rs. subst. (* keep drs in this case *)

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contR_gen_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacDe ; subst ; rewrite -> ?app_nil_r in *. 

- inversion sppc ; subst ; clear sppc.

+ derIrs rs.
* apply NSlclctxt.  apply EW.
* apply drs.

- contL2 rs sppc acm swap.

- inversion sppc ; subst ; clear sppc.
acacDe ; subst ; rewrite -> ?app_nil_r in *.
derIrs rs.
+ apply NSlclctxt.  apply EW.
+ apply drs.
Qed.

Lemma gen_contL_gen_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contL_gen_step.
intros lreq nsr drs acm rs. subst. (* keep drs in this case *)

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_contL_gen_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacDe ; subst ; rewrite -> ?app_nil_r in *. 

- inversion sppc ; subst ; clear sppc.

+ derIrs rs.
* apply NSlclctxt.  apply EW.
* apply drs.

- contL2 rs sppc acm swap.

- inversion sppc ; subst ; clear sppc.
acacDe ; subst ; rewrite -> ?app_nil_r in *.
derIrs rs.
+ apply NSlclctxt.  apply EW.
+ apply drs.
Qed.


(* ----------------------------------------- *)
(* FULL LEFT AND RIGHT CONTRACTION FOR LNSKT *)
(* ----------------------------------------- *)

Lemma LNSKt_contR_gen: forall (V : Set) ns
  (D : derrec (@LNSKt_rules V) (fun _ => False) ns),
      can_gen_contR_gen (@LNSKt_rules V) ns.
Proof.
  intros. eapply derrec_all_ind in D.
  exact D. tauto.
  intros. inversion H ; subst ;
          [> pose gen_contR_gen_step_b2R_lc as g
  | pose gen_contR_gen_step_b1R_lc as g; egx_app g LNSKt_exchR
  | pose gen_contR_gen_step_b2L_lc as g
  | pose gen_contR_gen_step_b1L_lc as g
  | pose gen_contR_gen_step_EW_lc as g
  | pose gen_contR_gen_step_pr_lc as g ;  egx_app g LNSKt_exchR ]; 
        unfold gen_contR_gen_step in g; try egx g;
          clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.

Lemma LNSKt_contL_gen: forall (V : Set) ns
  (D : derrec (@LNSKt_rules V) (fun _ => False) ns),
      can_gen_contL_gen (@LNSKt_rules V) ns.
Proof.
  intros.  eapply derrec_all_ind in D.
  exact D. tauto.
  intros. inversion H ; subst ;
          [> pose gen_contL_gen_step_b2R_lc as g
  | pose gen_contL_gen_step_b1R_lc as g
  | pose gen_contL_gen_step_b2L_lc as g
  | pose gen_contL_gen_step_b1L_lc as g
  | pose gen_contL_gen_step_EW_lc as g
  | pose gen_contL_gen_step_pr_lc as g ; egx_app g LNSKt_exchL ]; 
  unfold gen_contL_gen_step in g; try egx g;
  clear g ; unfold rsub ; intros;
  [> apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.
