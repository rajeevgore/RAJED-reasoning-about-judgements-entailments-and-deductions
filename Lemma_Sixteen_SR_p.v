Require Import ssreflect.
Require Import Lia.

Require Import gen genT.
Require Import ddT.
Require Import dd_fc.
Require Import List_lemmasT.
Require Import lntT lntacsT lntlsT lntbRT lntmtacsT.
Require Import lntb1LT lntb2LT.
Require Import lntkt_exchT.
Require Import lnt_weakeningT.
Require Import lnt_contractionT.
Require Import existsT.
Require Import lnt_weakeningT lnt_contraction_mrT.
Require Import ind_lex.
Require Import contractedT weakenedT.
Require Import structural_equivalence.
Require Import merge.
Require Import lnt_gen_initT.
Require Import size principal.
Require Import cut_setup.
Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen_SR_wb.
Require Import Lemma_Sixteen_SR_bb.
Require Import Lemma_Sixteen_SR_wb_fwd.

Set Implicit Arguments.

(* -------------------------- *)
(* Lemma_Sixteen_SR_p_WBox2Rs *)
(* -------------------------- *)

Lemma dersrec_height_nil : forall {X : Type} rl prems (D : @dersrec X rl prems []),
    dersrec_height D = 0.
Proof.
  intros.
  remember [] as G.
  destruct D. reflexivity.
  discriminate.
Qed.

Lemma dersrec_height_nil_gen : forall {X : Type} rl prems G (D : @dersrec X rl prems G),
    G = [] ->
    dersrec_height D = 0.
Proof.
  intros. destruct D. reflexivity.
  discriminate.
Qed.

(* Move to Lemma_Sixteen_setup.v *)
Ltac get_SR_p_from_IH IH HSR n m :=   
  assert (SR_p (n,m)) as HSR;
  [eapply IH; ( (econstructor 1; try reflexivity; lia)
  || (econstructor 2; try reflexivity; lia) ) | ].

Ltac get_SR_p_pre_from_IH IH HSR n m :=
  assert (SR_p_pre n m) as HSR;
  [fold (SR_p ( n, m));
   apply IH; ( (econstructor 1; try reflexivity; lia)
  || (econstructor 2; try reflexivity; lia) ) | ].

Definition get_dersrecD {X} rules prems lG lH D pf :=
(let (D', HD') := (fun (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (lG lH : list X) (D1 : dersrec rules prems lG) (H0 : lG = lH) =>
eq_rect_r
  (fun lG0 : list X =>
   forall D2 : dersrec rules prems lG0,
   existsT2 D3 : dersrec rules prems lH, dersrec_height D2 = dersrec_height D3)
  (fun D2 : dersrec rules prems lH =>
     existT (fun D3 : dersrec rules prems lH => dersrec_height D2 = dersrec_height D3) D2 eq_refl) H0 D1)
              X rules prems
lG lH D pf in D').

Definition get_dersrec_heightD {X : Type} (rules : list X -> X -> Type) (prems : X -> Type) (lG lH : list X) 
  (D : dersrec rules prems lG) (pf : lG = lH) :=
 EqdepFacts.internal_eq_rew_r_dep
   (fun (lG0 : list X) (pf0 : lG0 = lH) =>
    forall D0 : dersrec rules prems lG0, dersrec_height D0 = dersrec_height (get_dersrecD D0 pf0))
   (fun D0 : dersrec rules prems lH => eq_refl) pf D.


Ltac get_concl_of_derrec :=
  match goal with
  | [ |- derrec _ _ ?C ] => idtac C (*constr:(C)*)
  end.

Ltac get_snd_last_app_of_concl_of_derrec :=
  match goal with
  | [ |- derrec _ _ ?C ] => get_snd_last_app C
  end.

Ltac bracket_setup_SR_p1 rl :=
  match rl with
  | Id_pfc =>
    match goal with
    | [ |- context[?A ++ [Var ?p] ++ ?B ++ ?C] ] =>
      rewrite (app_assoc _ B); rewrite (app_assoc A)
    end
  | ImpR_pfc =>
    match goal with
    | [ H : context[seqext ?Γ1 ?Γ2 _ _ _] |- _] => rewrite (app_assoc Γ1)
    end
  end.

      (*
      Ltac bracket_setup_SR_p1 rl :=
  match rl with
  | Id_pfc =>
    match goal with
    | [ |- context[?A ++ [Var ?p] ++ ?B ++ ?C] ] =>
      rewrite (app_assoc _ B); rewrite (app_assoc A)
    end
  end.
*)


      Ltac solve_SR_p_case_B_d_WBox2Rs D2' HSR rl :=
      list_assoc_l;
      match goal with
      | [ |- context[WBox ?AA] ] =>   assoc_mid_loc [WBox AA]
      end;
      fill_tac_WBox2Rs D2' WBox2Rs;
econstructor; [  | econstructor ]; unfold nslcext || unfold nslclext; simpl;
list_assoc_r_single;
bracket_setup_SR_p1 rl;
      eapply HSR;
      [ match rl with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      |
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eassumption
      | eassumption].

Ltac solve_LNSKt_rules_Id_pfc :=
  list_assoc_l; eapply prop;
  (eapply NSlcctxt_nil || idtac );
  list_assoc_r_single;
  (eapply Sctxt_eq || idtac);
  (reflexivity || econstructor).

    Ltac solve_LNSKt_rules_ImpR_pfc :=
      list_assoc_l; eapply prop;
  (eapply NSlcctxt_nil || eapply NSlcctxt );
  list_assoc_r_single;
  (eapply Sctxt_eq || eapply Sctxt);
  (reflexivity || econstructor 2).

Ltac finish_SR_p_case_B_d Hdp :=
  (simpl ; erewrite (dersrec_height_nil (dersrec_nil _ _));
   simpl; erewrite <- get_dpD; eapply Hdp) ||
  (simpl ; erewrite <- get_dersrec_heightD;
   erewrite <- get_dpD; eapply Hdp).

Ltac Hdp_rearr Hdp'' Hdp''' :=
  pose proof Hdp'' as Hdp''';
  simpl in Hdp''';
  rewrite <- PeanoNat.Nat.add_1_l in Hdp''';
  eapply PeanoNat.Nat.le_add_le_sub_l in Hdp'''.

         
(* 
Approach 2
Case B.d.
*)
Lemma Lemma_Sixteen_SR_p_WBox2Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2' Hdp HdpD2 Hdp'' Hdp'.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id *)
     inversion X. subst.
     simpl in Hdp''.  
     rewrite dersrec_height_nil in Hdp''.
     clear X Hdp' Hprinc D2 rl H1 Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3;  assoc_mid [WBox AA]; Hdp_rearr Hdp'' Hdp'''.
     ++{         
         solve_SR_p_case_B_d_WBox2Rs D2' HSR Id_pfc.
         finish_SR_p_case_B_d Hdp'''.
        } 
       
     ++{         
         solve_SR_p_case_B_d_WBox2Rs D2' HSR Id_pfc.
         finish_SR_p_case_B_d Hdp'''.         
       }       
    }
    
  +{ (* Last rule in D1 is ImpR *)
     inversion X. subst.
     simpl in Hdp''. simpl in Hdp'.
     destruct (dersrec_derrec_dp D2 eq_refl) as [D1 HdpD1].
     assert (Hdp1'' : dp D1 + S (dp D2') <= m); [ rewrite HdpD1  |  ].
     apply Le.le_Sn_le. assumption.
     clear X Hprinc rl Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3; try discriminate; list_assoc_r_single.
     
     ++{
         solve_SR_p_case_B_d_WBox2Rs D2' HSR ImpR_pfc. 
         finish_SR_p_case_B_d Hdp'.           
       }
     ++{
         solve_SR_p_case_B_d_WBox2Rs D2' HSR ImpR_pfc. 
         finish_SR_p_case_B_d Hdp'. 
       }       
     ++{ destruct Hl2; discriminate. }
    }
    Unshelve.
   
   all : (solve [solve_LNSKt_rules_Id_pfc] ||
          solve [solve_LNSKt_rules_ImpR_pfc] ||
    (unfold nslclext; solve_eqs)).
Qed.

(* -------------------------- *)
(* Lemma_Sixteen_SR_p_BBox2Rs *)
(* -------------------------- *)


Ltac solve_SR_p_case_B_d_BBox2Rs D2' HSR rl :=
      list_assoc_l;
      match goal with
      | [ |- context[BBox ?AA] ] =>   assoc_mid [BBox AA]
      end;
                  eapply derI;
            [eapply b2r; econstructor;
            simpl; eapply BBox2Rs | ];
      econstructor; [  | econstructor ]; unfold nslcext || unfold nslclext; simpl;
      list_assoc_r_single;
bracket_setup_SR_p1 rl;
      eapply HSR;
      [ match rl with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      |
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eassumption
      | eassumption].


(* 
Approach 2
Case B.d.
*)

Lemma Lemma_Sixteen_SR_p_BBox2Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2' Hdp HdpD2 Hdp'' Hdp'.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id *)
     inversion X. subst.
     simpl in Hdp''.  
     rewrite dersrec_height_nil in Hdp''.
     clear X Hdp' Hprinc D2 rl H1 Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3;  assoc_mid [BBox AA]; Hdp_rearr Hdp'' Hdp'''.
     ++{
         solve_SR_p_case_B_d_BBox2Rs D2' HSR Id_pfc.
         finish_SR_p_case_B_d Hdp'''.
        } 
       
     ++{         
         solve_SR_p_case_B_d_BBox2Rs D2' HSR Id_pfc.
         finish_SR_p_case_B_d Hdp'''.         
       }       
    }
    
  +{ (* Last rule in D1 is ImpR *)
     inversion X. subst.
     simpl in Hdp''. simpl in Hdp'.
     destruct (dersrec_derrec_dp D2 eq_refl) as [D1 HdpD1].
     assert (Hdp1'' : dp D1 + S (dp D2') <= m); [ rewrite HdpD1  |  ].
     apply Le.le_Sn_le. assumption.
     clear X Hprinc rl Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3; try discriminate; list_assoc_r_single.
     
     ++{
         solve_SR_p_case_B_d_BBox2Rs D2' HSR ImpR_pfc. 
         finish_SR_p_case_B_d Hdp'.           
       }
     ++{
         solve_SR_p_case_B_d_BBox2Rs D2' HSR ImpR_pfc. 
         finish_SR_p_case_B_d Hdp'. 
       }       
     ++{ destruct Hl2; discriminate. }
    }
    Unshelve.
   
   all : (solve [solve_LNSKt_rules_Id_pfc] ||
          solve [solve_LNSKt_rules_ImpR_pfc] ||
    (unfold nslclext; solve_eqs)).
Qed.


(* -------------------------- *)
(* Lemma_Sixteen_SR_p_WBox1Rs *)
(* -------------------------- *)


Lemma le_S_minus : forall n m,
    S n <= m -> n <= m - 1.
Proof. intros. lia. Qed.

(* 
Approach 2
Case B.d.
*)

Lemma Lemma_Sixteen_SR_p_WBox1Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d2); (L2, L5 ++ WBox AA :: L6, bac)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d2); (L2, L5 ++ WBox AA :: L6, bac)];
          nslclext ctxt
            [(L1, L3 ++ L4, d2); (L2, L5 ++ WBox AA :: L6, bac); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s Hmax1 Hmax2.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id *)
     inversion X. subst.
     simpl in Hdpa''. simpl in Hdpb''.
     rewrite dersrec_height_nil in Hdpa''.
     rewrite dersrec_height_nil in Hdpb''.
     clear X Hdpa' Hdpb' Hprinc D2 rl H1 Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3;  assoc_mid [WBox AA]. (*; Hdp_rearr Hdp'' Hdp'''. *)
     ++{

                pose proof (merge_app_struct_equiv_strR _ _ _ _ Hme Hstr).
      sD. subst.

      dest_pairs.
      eapply merge_app_single in Hme; [ | eassumption].
      sD. subst.





      list_assoc_l;
      match goal with
      | [ |- context[WBox ?AA] ] =>   assoc_mid_loc [WBox AA]
      end;
      match goal with
      | |- derrec _ _ (?G ++ ?H) => rewrite <- (app_assoc _ _ H)
      | _ => idtac 70
      end.
  eapply derI;
  [eapply b1r; econstructor; list_assoc_r_single;
  bracket_set_up1_redo D2b WBox1Rs |].
  simpl; rewrite (app_assoc l2). eapply WBox1Rs.
      econstructor; [  | econstructor; [ | econstructor] ]; unfold nslcext || unfold nslclext; simpl;
        list_assoc_r_single;
        bracket_setup_SR_p1 Id_pfc.
         rewrite (app_assoc X1).
      eapply HSR;
      [ match Id_pfc with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      | 
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eapply struct_equiv_str_app_single;  eassumption
      | eapply merge_app_single_rev; eassumption ].

      simpl.
      rewrite dersrec_height_nil. simpl.
      rewrite <- get_dpD.
      simpl in Hdpa''.
      eapply le_S_minus. eapply Hdpa''.

      Unshelve.

      2:{ 
      econstructor.
      }

      2:{
      eapply prop.
      eapply NSlcctxt_nil.
      rewrite <- seqext_def.
      eapply Sctxt_nil.
      econstructor.
      }


      2:{
        unfold nslclext. solve_eqs.
      }







         rewrite (app_assoc X1).
      eapply HSR;
      [ match Id_pfc with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      | 
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eapply struct_equiv_str_app_single;  eassumption
      | eapply merge_app_single_rev; eassumption ].

      simpl.
      rewrite dersrec_height_nil. simpl.
      rewrite <- get_dpD.
      simpl in Hdpb''.
      eapply le_S_minus. eapply Hdpb''.

      Unshelve.
      
      econstructor.
      

      eapply prop.
      eapply NSlcctxt_nil.
      rewrite <- seqext_def.
      eapply Sctxt_nil.
      econstructor.

      unfold nslclext. solve_eqs.

       }
       
      




     ++{

      list_assoc_l;
      match goal with
      | [ |- context[WBox ?AA] ] =>   assoc_mid_loc [WBox AA]
      end;
      match goal with
      | |- derrec _ _ (?G ++ ?H) => rewrite <- (app_assoc _ _ H)
      | _ => idtac 70
      end.
  eapply derI;
  [eapply b1r; econstructor; list_assoc_r_single;
  bracket_set_up1_redo D2b WBox1Rs |].
  eapply WBox1Rs.
      econstructor; [  | econstructor; [ | econstructor] ]; unfold nslcext || unfold nslclext; simpl;
        list_assoc_r_single;
        bracket_setup_SR_p1 Id_pfc.

      eapply HSR;
      [ match Id_pfc with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      | 
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eassumption | eassumption ].

      simpl.
      rewrite dersrec_height_nil. simpl.
      rewrite <- get_dpD.
      simpl in Hdpa''.
      eapply le_S_minus. eapply Hdpa''.

      Unshelve.

      2:{ 
      econstructor.
      }

      2:{
      eapply prop.
      eapply NSlcctxt_nil.
      rewrite <- seqext_def.
      eapply Sctxt_nil.
      econstructor.
      }


      2:{
        unfold nslclext. solve_eqs.
      }





      eapply HSR;
      [ match Id_pfc with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      | 
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      |  eassumption
      | eassumption ].

      simpl.
      rewrite dersrec_height_nil. simpl.
      rewrite <- get_dpD.
      simpl in Hdpb''.
      eapply le_S_minus. eapply Hdpb''.

      Unshelve.
      
      econstructor.
      

      eapply prop.
      eapply NSlcctxt_nil.
      rewrite <- seqext_def.
      eapply Sctxt_nil.
      econstructor.

      unfold nslclext. solve_eqs.

       }

     ++{

      list_assoc_l;
      match goal with
      | [ |- context[WBox ?AA] ] =>   assoc_mid_loc [WBox AA]
      end;
      match goal with
      | |- derrec _ _ (?G ++ ?H) => rewrite <- (app_assoc _ _ H)
      | _ => idtac 70
      end.
  eapply derI;
  [eapply b1r; econstructor; list_assoc_r_single;
   bracket_set_up1_redo D2b WBox1Rs |].
  rewrite (app_assoc Δ1).
  rewrite (app_assoc (Δ1 ++ _)).
  eapply WBox1Rs.
      econstructor; [  | econstructor; [ | econstructor] ]; unfold nslcext || unfold nslclext; simpl;
        list_assoc_r_single;
        bracket_setup_SR_p1 Id_pfc.

      eapply HSR;
      [ match Id_pfc with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      | 
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eassumption | eassumption ].

      simpl.
      rewrite dersrec_height_nil. simpl.
      rewrite <- get_dpD.
      simpl in Hdpa''.
      eapply le_S_minus. eapply Hdpa''.

      Unshelve.

      2:{ 
      econstructor.
      }

      2:{
      eapply prop.
      eapply NSlcctxt_nil.
      rewrite <- seqext_def.
      eapply Sctxt_nil.
      econstructor.
      }


      2:{
        unfold nslclext. solve_eqs.
      }





      eapply HSR;
      [ match Id_pfc with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      | 
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      |  eassumption
      | eassumption ].

      simpl.
      rewrite dersrec_height_nil. simpl.
      rewrite <- get_dpD.
      simpl in Hdpb''.
      eapply le_S_minus. eapply Hdpb''.

      Unshelve.
      
      econstructor.
      

      eapply prop.
      eapply NSlcctxt_nil.
      rewrite <- seqext_def.
      eapply Sctxt_nil.
      econstructor.

      unfold nslclext. solve_eqs.

       }
    }


    +{ 
        admit.
      }
Admitted.

     (* 
assert
 ( (fun l : list (PropF V) =>
           derrec (LNSKt_rules (V:=V))
             (fun _ : list (rel (list (PropF V)) * dir) => False)
             (ctxt ++ [(L1, L3 ++ AA :: L4, d2); (l, L5 ++ WBox AA :: L6, bac)])) =
(fun l : list (PropF V) =>
           derrec (LNSKt_rules (V:=V))
             (fun _ : list (rel (list (PropF V)) * dir) => False)
             ((fun ll => (ctxt ++ [(L1, L3 ++ AA :: L4, d2); (ll, L5 ++ WBox AA :: L6, bac)])) l )) ) as Hass.
admit.


rewrite Hass.
assert ( (ctxt ++ [(L1, L3 ++ AA :: L4, d2); (l, L5 ++ WBox AA :: L6, bac)]) =
 (ctxt ++ [(L1, L3 ++ AA :: L4, d2); (l, L5 ++ WBox AA :: L6, bac)])) as Hass.
unfold nslclext in D2a.
rewrite (dp_same_fun_r _ D2a).

      SearchAbout dp eq_rect_r.
      rewrite get_dpD.
      SearchAbout dp get_D.
      rewrite dp_same.
      
      Search seqrule nil.
      eapply Sctxt_Id'.
      econstructor.
      
   match goal with
   | |- context [ WBox ?AA ] => assoc_mid_loc [WBox AA]
   end;
      match goal with
   | |- derrec _ _ (?G ++ ?H) => rewrite <- (app_assoc _ _ H)
   | _ => idtac 70
   end.
  
  eapply derI.
  eapply b1r. econstructor. list_assoc_r_single.
  bracket_set_up1_redo D2b WBox1Rs.
  simpl. eapply WBox1Rs.
  

   econstructor; [  | econstructor ].
   unfold nslcext || unfold nslclext; simpl; list_assoc_r_single;
     bracket_setup_SR_p1 Id_pfc.
   rewrite (app_assoc X1).
   unfold SR_p_pre in HSR.
   eapply HSR.
   econstructor. reflexivity. econstructor. reflexivity. reflexivity. reflexivity.
   reflexivity.
   admit.
   simpl in *. assumption.
   econstructor. reflexivity.
   eapply struct_equiv_str_app_single.
   eassumption.
   eapply merge_app_single_rev. eassumption. eassumption.
SearchAbout merge cons.
   eassumption.
   [match Id_pfc with
     | Id_pfc => econstructor
     | ImpR_pfc => econstructor 2
   end; [ reflexivity | econstructor; reflexivity ]
   | 
   | simpl in *; lia || eassumption
   | econstructor; reflexivity
   | eassumption
   | ..].
   admit.
   admit.
   admit. econstructor. Unshelve. admit. admit.

         
           eapply derI;
   [ eapply b1r; econstructor; list_assoc_r_single;
      bracket_set_up1_redo_twoprem D1 D2a D2b WBox1Rs; simpl; 
      eapply WBox1Rs
   |  ].
fill_tac_case_G_b1r D1 D2a' D2b' WBox1Rs.
         


         
    solve_case_G_gen_draft2 D1 D2a D2b D2a' D2b' D3 HSR Hdpa' Hdpb' WBox1Rs fill_tac_case_G_b1r.

         

         list_assoc_l;
   match goal with
   | |- context [ WBox ?AA ] => assoc_mid_loc [WBox AA]
   end.

         eapply derI.
         eapply b1r. econstructor. list_assoc_r_single.
         assoc_mid_loc [WBox AA]. bracket_set_up1_redo D2b WBox1Rs.
   [ eapply b1r; econstructor; list_assoc_r_single; bracket_set_up1_redo D2' WBox1Rs;
      simpl; eapply WBox1Rs
   |  ].
         
   fill_tac_WBox2Rs D2' WBox2Rs. ; econstructor; [  | econstructor ];
   unfold nslcext || unfold nslclext; simpl; list_assoc_r_single;
   bracket_setup_SR_p1 rl; eapply HSR;
   [ match rl with
     | Id_pfc => econstructor
     | ImpR_pfc => econstructor 2
     end; [ reflexivity | econstructor; reflexivity ]
   | 
   | simpl in *; lia || eassumption
   | econstructor; reflexivity
   | eassumption
   | eassumption ]
         
         solve_SR_p_case_B_d_WBox2Rs D2' HSR Id_pfc.
         finish_SR_p_case_B_d Hdp'''.
        } 
       
     ++{         
         solve_SR_p_case_B_d_WBox2Rs D2' HSR Id_pfc.
         finish_SR_p_case_B_d Hdp'''.         
       }       
    }
    
  +{ (* Last rule in D1 is ImpR *)
     inversion X. subst.
     simpl in Hdp''. simpl in Hdp'.
     destruct (dersrec_derrec_dp D2 eq_refl) as [D1 HdpD1].
     assert (Hdp1'' : dp D1 + S (dp D2') <= m); [ rewrite HdpD1  |  ].
     apply Le.le_Sn_le. assumption.
     clear X Hprinc rl Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3; try discriminate; list_assoc_r_single.
  
Admitted.
*)

(* -------------------------- *)
(* Lemma_Sixteen_SR_p_BBox1Rs *)
(* -------------------------- *)

(* 
Approach 2
Case B.d.
*)

Lemma Lemma_Sixteen_SR_p_BBox1Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d2); (L2, L5 ++ BBox AA :: L6, fwd)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d2); (L2, L5 ++ BBox AA :: L6, fwd)];
          nslclext ctxt
            [(L1, L3 ++ L4, d2); (L2, L5 ++ BBox AA :: L6, fwd); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Admitted.


(* -------------------------- *)
(* Lemma_Sixteen_SR_p_WBox2Ls *)
(* -------------------------- *)


Ltac SR_p_WBox2Ls_snd_last_comp D2 AA A HSR Hdp' :=
          eapply derI;
         [
         eapply b2l;
         econstructor;
         bracket_list_assoc_r_arg_derrec2 D2 AA;
         eapply WBox2Ls |];
         econstructor; [|constructor];
         unfold SR_p_pre in HSR;
         list_assoc_r_single;
         bracket_D2_B D2 A;      
         eapply HSR; try eassumption;
         erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
         eapply Hdp'.

(* 
Approach 2
Case B.a.
*)

Lemma Lemma_Sixteen_SR_p_WBox2Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d2); (L3 ++ WBox AA :: L4, L6, bac)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d2)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d D1 ctxt AA d2 L1 L2 L3 L4 L5 L6
  Heqconcl Hprinc D2s Hdp Hsize HBox Hstr Hme.
  unfold nslclext in *.
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  rename Heqconcl into Heqconcl'.
  
  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl';
    inv_app_hd_tl_full.
  -{
      app_eq_app_dest3; try contradiction;
      tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  +{ (* A in last component *)
      
      pose proof (merge_app_struct_equiv_strR _ _ _ _ Hme Hstr).
      sD. subst.

      dest_pairs.
      eapply merge_app_single in Hme; [ | eassumption].
      sD. subst.

      
list_assoc_r_single.
      eapply derI.
      eapply b2l.
      econstructor.
      simpl.
      list_assoc_l.
      eapply WBox2Ls.


      econstructor; [ | econstructor].

      unfold nslclext.
      list_assoc_r_single.
      rewrite <- (app_nil_r [_]).
      unfold SR_p_pre in HSR.
Admitted.
(*
      eapply HSR.








      list_assoc_l;
      match goal with
      | [ |- context[WBox ?AA] ] =>   assoc_mid_loc [WBox AA]
      end;
      match goal with
      | |- derrec _ _ (?G ++ ?H) => rewrite <- (app_assoc _ _ H)
      | _ => idtac 70
      end.
  eapply derI;
  [eapply b1r; econstructor; list_assoc_r_single;
  bracket_set_up1_redo D2b WBox1Rs |].
  simpl; rewrite (app_assoc l2). eapply WBox1Rs.
      econstructor; [  | econstructor; [ | econstructor] ]; unfold nslcext || unfold nslclext; simpl;
        list_assoc_r_single;
        bracket_setup_SR_p1 Id_pfc.
         rewrite (app_assoc X1).
      eapply HSR;
      [ match Id_pfc with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      | 
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eapply struct_equiv_str_app_single;  eassumption
      | eapply merge_app_single_rev; eassumption ].

      simpl.
      rewrite dersrec_height_nil. simpl.
      rewrite <- get_dpD.
      simpl in Hdpa''.
      eapply le_S_minus. eapply Hdpa''.

      Unshelve.

      2:{ 
      econstructor.
      }

      2:{
      eapply prop.
      eapply NSlcctxt_nil.
      rewrite <- seqext_def.
      eapply Sctxt_nil.
      econstructor.
      }


      2:{
        unfold nslclext. solve_eqs.
      }







         rewrite (app_assoc X1).
      eapply HSR;
      [ match Id_pfc with
        | Id_pfc => econstructor
        | ImpR_pfc => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      | 
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eapply struct_equiv_str_app_single;  eassumption
      | eapply merge_app_single_rev; eassumption ].

      simpl.
      rewrite dersrec_height_nil. simpl.
      rewrite <- get_dpD.
      simpl in Hdpb''.
      eapply le_S_minus. eapply Hdpb''.

      Unshelve.
      
      econstructor.
      

      eapply prop.
      eapply NSlcctxt_nil.
      rewrite <- seqext_def.
      eapply Sctxt_nil.
      econstructor.

      unfold nslclext. solve_eqs.

       }








      
      SR_p_WBox2Ls_snd_last_comp D2 AA A HSR Hdp'.
      Unshelve.
      all : (repeat rewrite app_nil_r;  solve_eqs).
      }
  +{ (* WBox A not in snd last component *)

      inv_app_hd_tl_full;
     tac_cons_singleton;     
     eapply derI; [
     eapply b2l;     
     list_assoc_l';
     eapply nslclrule_b2lrules2; [reflexivity | reflexivity |];
     list_assoc_r';
     eapply WBox2Ls | ];
     
     econstructor; [ | econstructor].
     unfold nslclext;
     list_assoc_r; simpl;
       tac_cons_singleton.

     eapply HSR; try eassumption;
       erewrite (dp_get_D D2) in Hdp'; eapply Hdp'.
    } 
    Unshelve. all : try solve [subst; solve_eqs].
   }

      admit. }

   -{ 
  inv_app_hd_tl_full.
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  eapply partition_singleton_app in Heqconcl'. sD; subst.
  +{ (* A in snd last component *)
      app_eq_app_dest3; try contradiction;
      SR_p_WBox2Ls_snd_last_comp D2 AA A HSR Hdp'.
      Unshelve.
      all : (repeat rewrite app_nil_r;  solve_eqs).
      }
  +{ (* WBox A not in snd last component *)

      inv_app_hd_tl_full;
     tac_cons_singleton;     
     eapply derI; [
     eapply b2l;     
     list_assoc_l';
     eapply nslclrule_b2lrules2; [reflexivity | reflexivity |];
     list_assoc_r';
     eapply WBox2Ls | ];
     
     econstructor; [ | econstructor].
     unfold nslclext;
     list_assoc_r; simpl;
       tac_cons_singleton.

     eapply HSR; try eassumption;
       erewrite (dp_get_D D2) in Hdp'; eapply Hdp'.
    } 
    Unshelve. all : try solve [subst; solve_eqs].
   }
Qed.

(*
SR_p_WBox2Ls_snd_last_comp D2 AA A HSR Hdp'.
           Unshelve.
      repeat rewrite app_nil_r. solve_eqs.

    eapply derI;
         [
         eapply b2l;
         econstructor;
         bracket_list_assoc_r_arg_derrec2 D2 AA;
         eapply WBox2Ls |];
         econstructor; [|constructor];
         unfold SR_p_pre in HSR;


         list_assoc_r_single.
    bracket_D2_B D2 A.
(*
rewrite <- (app_nil_r);
      list_assoc_r_single;
  *)       
      eapply HSR; try eassumption;
      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
      eapply Hdp'.

           Unshelve.
      2 : {repeat rewrite app_nil_r. solve_eqs. }


      
      eapply derI.
      eapply b2l.
      econstructor.
      bracket_list_assoc_r_arg_derrec2 D2 AA.
      eapply WBox2Ls.
      econstructor; [ | econstructor].
      unfold SR_p_pre in HSR.
(*      unfold nslclext. 

      rewrite <- (app_nil_r);
      list_assoc_r_single;
      rewrite (app_assoc L1).
      rewrite (app_assoc _ H1).
 *)
      list_assoc_r_single.
bracket_D2_B D2 A.

(*
bracket_list_assoc_r_arg_derrec3 D2 A.

           tac_match2 l1 L1 B
L1 ++ AA :: H1 ++ [A] ++ Σ2
(Γ ++ L1)
A
 *)

      eapply HSR; try eassumption;
      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
      eapply Hdp'.

           Unshelve.
 repeat rewrite app_nil_r. solve_eqs. 








    eapply derI;
         [
         eapply b2l;
         econstructor;
         bracket_list_assoc_r_arg_derrec2 D2 AA;
         eapply WBox2Ls |];
         econstructor; [|constructor];
         unfold SR_p_pre in HSR;
         unfold nslclext;

      rewrite <- (app_nil_r);
      list_assoc_r_single;
      rewrite (app_assoc L1).
      rewrite (app_assoc _ H1).
         
      eapply HSR; try eassumption;
      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
      eapply Hdp'.

           Unshelve.
 repeat rewrite app_nil_r. solve_eqs. 




 
      
      eapply derI.
      eapply b2l.
      econstructor.
      bracket_list_assoc_r_arg_derrec2 D2 AA.
      eapply WBox2Ls.
      econstructor; [ | econstructor].
      unfold SR_p_pre in HSR.
      unfold nslclext.
      
      rewrite <- (app_nil_r).
      list_assoc_r_single.
      eapply HSR; try eassumption.
      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp'.
      eapply Hdp'.
      Unshelve.
      2 : {repeat rewrite app_nil_r. solve_eqs. }

      
      eapply derI.
      eapply b2l.
      econstructor.
      bracket_list_assoc_r_arg_derrec2 D2 AA.
      eapply WBox2Ls.
      econstructor; [ | econstructor].
      unfold SR_p_pre in HSR.
      unfold nslclext.
      
      rewrite <- (app_nil_r).
      list_assoc_r_single.
      rewrite (app_assoc L1).
      rewrite (app_assoc _ H1).
      eapply HSR; try eassumption.
      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp'.
      eapply Hdp'.

      Unshelve.
      repeat rewrite app_nil_r. solve_eqs.
} 


      repeat rewrite app_nil_r. solve_eqs.
      
      eassumption.
      
     ( eapply derI;
         [
         eapply b2l;
         econstructor;
         bracket_list_assoc_r_arg_derrec2 D2 AA;
         eapply WBox2Ls |];
         econstructor; [|constructor];
           unfold SR_wb_fwd_pre in HSR;
           bracket_list_assoc_r_arg_derrec3 D2 (WBox A);
           eapply HSR; [
             prep_to_weaken_derrec D3;
             eapply LNSKt_weakL; [| reflexivity | reflexivity];
                                   list_assoc_r;
             list_assoc_r_arg D3; simpl in D3; exact D3
           | econstructor 2; eassumption
           |      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
                  eapply Hdp'
           | eassumption | eassumption | simpl; lia]).

      

Ltac SR_wb_fwd_WBox2Ls_snd_last_comp D2 D3 AA A HSR Hdp' :=
      app_eq_app_dest3; try contradiction;
     ( eapply derI;
         [
         eapply b2l;
         econstructor;
         bracket_list_assoc_r_arg_derrec2 D2 AA;
         eapply WBox2Ls |];
         econstructor; [|constructor];
           unfold SR_wb_fwd_pre in HSR;
           bracket_list_assoc_r_arg_derrec3 D2 (WBox A);
           eapply HSR; [
             prep_to_weaken_derrec D3;
             eapply LNSKt_weakL; [| reflexivity | reflexivity];
                                   list_assoc_r;
             list_assoc_r_arg D3; simpl in D3; exact D3
           | econstructor 2; eassumption
           |      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
                  eapply Hdp'
           | eassumption | eassumption | simpl; lia]).

      
      SR_wb_fwd_WBox2Ls_snd_last_comp D2 D3 AA A HSR Hdp'.
    }
 *)
     (*
     solve_HSR HSR D2 D3 Hdp'.

      
      SR_wb_fwd_WBox2Ls_not_snd_last_comp D2 D3 HSR Hdp'.


      Ltac SR_wb_fwd_WBox2Ls_not_snd_last_comp D2 D3 HSR Hdp' :=
      inv_app_hd_tl_full;
     tac_cons_singleton;     
     eapply derI; [
     eapply b2l;     
     list_assoc_l';
     eapply nslclrule_b2lrules2; [reflexivity | reflexivity |];
     list_assoc_r';
     eapply WBox2Ls | ];
     
     econstructor; [ | econstructor];
     unfold nslclext;
     list_assoc_r; simpl;
     tac_cons_singleton;
     solve_HSR HSR D2 D3 Hdp'.
    }
   Unshelve. all : try solve [subst; solve_eqs].
Qed.
Admitted.
*)
*)
(* -------------------------- *)
(* Lemma_Sixteen_SR_p_BBox2Ls *)
(* -------------------------- *)

(* 
Approach 2
Case B.a.
 *)

Lemma Lemma_Sixteen_SR_p_BBox2Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d2); (L3 ++ BBox AA :: L4, L6, fwd)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d2)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Admitted.


(* -------------------------- *)
(* Lemma_Sixteen_SR_p_WBox1Ls *)
(* -------------------------- *)

(* 
Approach 2
Case B.d.
 *)

Lemma Lemma_Sixteen_SR_p_WBox1Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d2); (L3 ++ L4, L6, fwd)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d2); (L3 ++ AA :: L4, L6, fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Admitted.


(* -------------------------- *)
(* Lemma_Sixteen_SR_p_BBox1Ls *)
(* -------------------------- *)

(* 
Approach 2
Case B.d.
 *)

Lemma Lemma_Sixteen_SR_p_BBox1Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d2); (L3 ++ L4, L6, bac)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d2); (L3 ++ AA :: L4, L6, bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Admitted.


(* --------------------- *)
(* Lemma_Sixteen_SR_p_EW *)
(* --------------------- *)

(* 
Approach 2
Case B.b.
 *)

Lemma Lemma_Sixteen_SR_p_EW : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt L1 L2 d2
  (Heqconcl : nslclext ctxt [(L1, L2, d2)] = H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False) 
          [nslclext ctxt []])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.
  unfold nslclext in *.
  get_SR_p_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl.

  +{ (* A in last component. *)
      inv_app_hd_tl_full.
      eapply derrec_weakened_nseq.
      2:{ eapply derI.
          eapply nEW.
          econstructor.
          econstructor.

          simpl. econstructor; [ | econstructor].
          apply D2. }

      unfold nslclext.
      apply weakened_nseq_app_sameR.
      eapply merge_weakened_nseqR; eassumption.
    }
    
  +{ (*  A not in last component. *)
      inv_app_hd_tl_full.
      tac_cons_singleton.
      list_assoc_l.
      eapply derI.
      eapply nEW. econstructor. econstructor.
      simpl. econstructor; [ | econstructor].
      unfold nslclext.
      rewrite app_nil_r.
      list_assoc_r_single.

      eapply HSR; try eassumption.
      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp'.
      eapply Hdp'.

      Unshelve. repeat rewrite app_nil_r; solve_eqs.
    } 
Qed.


(* ------------------------- *)
(* Lemma_Sixteen_SR_p_Id_pfc *)
(* ------------------------- *)

(* Solves a goal of the form 
InT a l
where l is a series of cons and apps.
*)
Ltac solve_InT := 
  list_assoc_r; repeat (
                    (eapply InT_eq'; reflexivity) ||
                    (eapply InT_cons) ||
                    eapply InT_appR).

(* Solves a goal of the form
derrec (LNSKt_rules _) _ G
where it is a valid application of Id_pfc.
*)
Ltac solve_Id_pfc :=
  list_assoc_l;
  match goal with 
  | |- derrec _ _ (?G ++ [(?l1,?l2,?d)])  =>
    match l1 with
    | context[ Var ?p ] =>
      match l2 with
      | context[ Var p ] =>
        eapply (Id_InT _ _ _ _ p)
      end;
        solve_InT
    end
  end.

(* 
Approach 2
Case A.b + B.c.
 *)

Lemma Lemma_Sixteen_SR_p_Id_pfc : forall
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt d2 Φ1 Φ2 Ψ1 Ψ2 p
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Var p :: Φ2, Ψ1 ++ Var p :: Ψ2) =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (Hbox : not_box A),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  
  +{ (* Last rule in D1 is Id;
      Approach 2
      Case A.b *)
      inversion X. subst.
      app_eq_app_dest3.
      unfold nslcext in *.
      app_eq_app_dest3;
        solve_Id_pfc.
    }
  +{ (* Last rule in D1 is ImpR 
        Approach 2
        Case B.c
      *)
      admit.
    } 
Admitted.


(* --------------------------- *)
(* Lemma_Sixteen_SR_p_ImpR_pfc *)
(* --------------------------- *)

(* Solves a goal of the form
... ++ [a] = [] 
or
[] = ... ++ [a]
*)
Ltac discriminate_single_end :=
  repeat (match goal with
          | H : [] = ?l1 ++ ?l2 |- _ => apply nil_eq_appT in H
          | H : ?l1 ++ ?l2 = [] |- _ => symmetry in H
          end; sD; try discriminate).

(* 
Approach 2
Case B.d.
 *)

Lemma Lemma_Sixteen_SR_p_ImpR_pfc : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt d2 Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Φ2, Ψ1 ++ Imp AA BB :: Ψ2) =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d2 (Φ1 ++ AA :: Φ2, Ψ1 ++ Imp AA BB :: BB :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2' Hdp HdpD2 Hdp'' Hdp'.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id 
      Approach 2
      Case B.d.
      *)
     inversion X. subst.
     simpl in Hdp''.  
     rewrite dersrec_height_nil in Hdp''.
     clear X Hdp' Hprinc D2 rl H1 Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       unfold nslcext in Heqconcl;
       app_eq_app_dest3; try contradiction.
     admit.
     admit.
     admit.
    } 

  +{ (* Last rule in D1 is ImpR_pfc 
      Approach 2
      Case B.d
      *)
     inversion X. subst.
     simpl in Hdp''.  
     unfold nslcext in Heqconcl.
     simpl in Hdp'.
     clear Hprinc X rl Hbox.
     destruct (dersrec_derrec_dp D2 eq_refl) as [D1 HdpD1].
     assert (Hdp1'' : dp D1 + S (dp D2') <= m); [ rewrite HdpD1  |  ].
     apply Le.le_Sn_le. assumption.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3; try contradiction; try discriminate;
         discriminate_single_end.


     admit.
     admit.
     admit.
}     

Admitted.


(* --------------------------- *)
(* Lemma_Sixteen_SR_p_ImpL_pfc *)
(* --------------------------- *)

Lemma map_singleton:
  forall (A B : Type) (f : A -> B) (x : A), map f [x] = [f x].
Proof. reflexivity. Qed.

Lemma map_double_singleton : forall {A B : Type} (f : A -> B) (x y : A),
    map f [x;y] = [f x; f y].
Proof. reflexivity. Qed.

(* From dd_fc *)
Ltac tfm_dersrec_derrec2_dp_keep D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
  Hmax1 Hmax2 :=
  assert (HeqD2s : dersrec_height D2s = dersrec_height D2s); [ reflexivity |  ];
   destruct (dersrec_derrec2_dp D2s HeqD2s) as [D2a [D2b HdpD2]]; clear HeqD2s;
   epose proof (Max.le_max_r _ _) as Hmax1; epose proof (Max.le_max_l _ _) as Hmax2;
   rewrite <- HdpD2 in Hmax1; rewrite <- HdpD2 in Hmax2;
   match goal with
   | H:dp ?D1 + S (dersrec_height D2s) <= ?m
     |- _ =>
         assert (Hdpa'' : dp D1 + S (dp D2a) <= m); [ lia |  ];
          assert (Hdpb'' : dp D1 + S (dp D2b) <= m); [ lia |  ];
          assert (Hdpa' : dp D1 + dp D2a <= m - 1); [ lia |  ];
          assert (Hdpb' : dp D1 + dp D2b <= m - 1); [ lia |  ]; clear HdpD2 Hdp
          Hmax1 Hmax2
   end.

(*
Lemma contracted_nseq_trans : forall {T : Type} G1 G2 G3,
    @contracted_nseq T G1 G2 ->
    contracted_nseq G2 G3 ->
    contracted_nseq G1 G3.
Admitted.
*)
(*
Lemma rev_list_indT : forall {A : Type} (P:list A-> Type),
    P [] ->
    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list A, P (rev l).
Proof.
  induction l. eassumption.
  simpl. firstorder. 
Qed.
             

Lemma rev_indT : forall {A : Type} (P:list A -> Type),
P [] ->
(forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
Proof.
intros A P Hnil Hind l.
       rewrite <- rev_involutive.
               apply rev_list_indT. assumption.
               intros. simpl. apply Hind. assumption.
               Qed.
 *)

Lemma contracted_multi_from_nil : forall {V : Set} Γ,
    @contracted_multi V [] Γ -> Γ = [].
Proof.
  induction Γ; intros H. reflexivity.
  inversion H; subst. inversion H0; subst;
  repeat match goal with
  | [ H : [] = ?l |- _ ] => try contradiction (app_cons_not_nil _ _ _ H)
  | [ H : ?l = [] |- _ ] => try contradiction (app_cons_not_nil _ _ _ H)
  end.
Qed.

Lemma contracted_multi_trans : forall {T} X Y Z,
    contracted_multi X Y ->
    contracted_multi Y Z ->
    @contracted_multi T X Z.
Proof.
  intros.
  induction X0. eassumption.
  econstructor. eassumption. eapply IHX0.
  eassumption.
Qed.

Lemma contracted_multi_to_nil : forall {V : Set} l,
    @contracted_multi V l [] -> l = [].
Proof.
  intros V l H.
  remember [] as l2.
  induction H. reflexivity.
  subst. specialize (IHcontracted_multi eq_refl).
  subst.
  inversion c.
  repeat match goal with
         | [ H : [] = ?l |- _ ] => try contradiction (app_cons_not_nil _ _ _ H)
         | [ H : ?l = [] |- _ ] => try contradiction (app_cons_not_nil _ _ _ H)
         end.
  destruct A; destruct B; discriminate.
Qed.

Lemma contracted_gen_InT_fwd : forall {V : Set} Γ Σ,
    @contracted_gen V Γ Σ ->
    (forall a, InT a Σ -> InT a Γ).
Proof.
  intros V Γ Σ Hc.
  inversion Hc; intros b Hin; subst.
  apply InT_appE in Hin;
  destruct Hin as [Hin | Hin].
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  assumption.

    apply InT_appE in Hin;
  destruct Hin as [Hin | Hin].
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  assumption.
Qed.

Lemma contracted_gen_InT_rev : forall {T : Type} Γ Σ,
    @contracted_gen T Γ Σ ->
    (forall a, InT a Γ -> InT a Σ).
Proof.
  intros V Γ Σ Hc.
  inversion Hc; intros b Hin; subst.
  apply InT_appE in Hin;
  destruct Hin as [Hin | Hin].
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  assumption.

  apply InT_appE in Hin;
  destruct Hin as [Hin | Hin].
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  assumption.
Qed.
  
Lemma contracted_multi_InT_fwd : forall {V : Set} Γ Σ,
  @contracted_multi V Γ Σ ->
  (forall a, InT a Σ -> InT a Γ).
Proof.
  intros V Γ Σ Hc.
  induction Hc; intros b Hin.
  subst. assumption.
  eapply contracted_gen_InT_fwd.
  eassumption.
  apply IHHc. assumption.
Qed.

Lemma contracted_multi_InT_rev : forall {V : Set} Γ Σ,
  @contracted_multi V Γ Σ ->
  (forall a, InT a Γ -> InT a Σ).
Proof.
  intros V Γ Σ Hc.
  induction Hc; intros b Hin.
  subst. assumption.
  apply IHHc.
  eapply contracted_gen_InT_rev.
  eassumption.
  assumption.
Qed.


Lemma contracted_multi_insertL_pre : forall {T : Type} l1 l3 a,
    (InT a l1) ->
    contracted_multi l1 l3 ->
    @contracted_multi T ([a] ++ l1) l3.
Proof.
  intros V l1 l3 a Hin Hc.
  induction Hc.

  econstructor; [ | econstructor].
  eapply InT_split in Hin.
  destruct Hin as [l1 [l2 Hin]].
  subst.
  list_assoc_r_single.
  rewrite <- (app_nil_l (_ ++ (l1 ++ _))).
  econstructor; reflexivity.
  
  eapply contracted_multi_trans; [| eapply IHHc].
  eapply contracted_multi_cons. 
  econstructor. eassumption. econstructor.
  eapply contracted_gen_InT_rev. eassumption.
  assumption.
Qed.


Lemma contracted_multi_insertL : forall {T : Type} l1 l2 l3 a,
    (InT a l1 + InT a l2) ->
    contracted_multi (l1 ++ l2) l3 ->
    @contracted_multi T (l1 ++ [a] ++ l2) l3.
Proof.
  intros until 0; intros Hin Hc.
  econstructor; [ | eapply Hc].
  destruct Hin as [Hin | Hin].

  list_assoc_l.
  eapply cont_gen_R.
  eapply InT_split in Hin.
  destruct Hin as [l1' [l2' Hin']].
  subst. list_assoc_r_single.
  rewrite <- (app_nil_r [a]).
  econstructor. reflexivity.
  repeat rewrite app_nil_r. reflexivity.
  
  eapply cont_gen_L.
  eapply InT_split in Hin.
  destruct Hin as [l1' [l2' Hin']].
  subst. list_assoc_r_single.
  rewrite <- (app_nil_l [a]).
  repeat rewrite <- app_assoc.
  econstructor; reflexivity.
Qed.


Lemma contracted_multi_appL_InT : forall {V : Set} Γ Σ,
    (forall a, InT a Σ -> InT a Γ) ->
    @contracted_multi V (Γ ++ Σ) Γ.
Proof.
  intros V Γ Σ; revert Γ.
  induction Σ; intros Γ H.
  rewrite app_nil_r. econstructor.

  assert (InT a Γ) as H2.
  eapply H. econstructor. reflexivity.
  eapply contracted_multi_insertL.
  left. assumption.
  apply IHΣ.
  intros b Hb. apply H. econstructor 2. assumption.
Qed.

Lemma contracted_multi_appR_InT : forall {V : Set} Γ Σ,
    (forall a, InT a Σ -> InT a Γ) ->
    @contracted_multi V (Σ ++ Γ) Γ.
Proof.
  intros V Γ Σ; revert Γ.
  induction Σ; intros Γ H.
  simpl. econstructor.

  assert (InT a Γ) as H2.
  eapply H. econstructor. reflexivity.
  simpl. eapply contracted_multi_insertL_pre.
  eapply InT_appR. assumption.

  apply IHΣ.
  intros b Hb. apply H. econstructor 2. assumption.
Qed.

Lemma contracted_multi_appL : forall {V : Set} Γ Σ,
    contracted_multi Γ Σ ->
    @contracted_multi V (Γ ++ Σ) Γ.
Proof.
  intros. apply contracted_multi_appL_InT.
  apply contracted_multi_InT_fwd.
  assumption.
Qed.

Lemma contracted_multi_appL_rev : forall {V : Set} Γ Σ,
    contracted_multi Σ Γ ->
    @contracted_multi V (Γ ++ Σ) Γ.
Proof.
  intros. apply contracted_multi_appL_InT.  
  apply contracted_multi_InT_rev.
  assumption.
Qed.

Lemma contracted_multi_appR : forall {V : Set} Γ Σ,
    contracted_multi Γ Σ ->
    @contracted_multi V (Σ ++ Γ) Γ.
Proof.
  intros. apply contracted_multi_appR_InT.
  apply contracted_multi_InT_fwd.
  assumption.
Qed.

Lemma contracted_multi_appR_rev : forall {V : Set} Γ Σ,
    contracted_multi Σ Γ ->
    @contracted_multi V (Σ ++ Γ) Γ.
Proof.
  intros. apply contracted_multi_appR_InT.
  apply contracted_multi_InT_rev.
  assumption.
Qed.

Lemma contracted_seq_dir_same : forall {V : Set} p1 p2 d1 d2,
    @contracted_seq V (p1,d1) (p2,d2) -> d1 = d2.
Proof.
  intros.
  remember (p1, d1) as s1.
  remember (p2, d2) as s2.
  revert Heqs1 Heqs2.
  revert  p1 p2 d1 d2.
  induction H; intros; subst.

  inversion c; subst. reflexivity.
  inversion c; subst. reflexivity.
  inversion c; subst. eapply IHcontracted_seq. reflexivity. reflexivity.
  inversion c. subst. eapply IHcontracted_seq. reflexivity. reflexivity.
Qed.

(*
Lemma contracted_seq_multiR_pre_pre : forall {V : Set} Γ Δ Σ Π d1 d2,
    @contracted_seq V (Γ, Δ, d1) (Σ, Π, d2) ->
    contracted_multi Γ Σ.
Proof.
  intros.
  remember (Γ, Δ, d1) as s1.
  remember (Σ, Π, d2) as s2.
  revert Heqs1 Heqs2.
  revert  Γ Δ Σ Π d1 d2.
  induction H; intros; subst.
  inversion c. subst. eassumption.
  inversion c. subst. econstructor.

  inversion c. subst.
  pose proof (IHcontracted_seq _ _ _ _ _ _ eq_refl eq_refl).
  eapply contracted_multi_trans; eassumption.

  inversion c. subst.
  eapply IHcontracted_seq; reflexivity.
Qed.
*)

(*
  remember (Γ, Δ, d2) as s1.
  remember (Σ, Δ, d2) as s2.
  revert Heqs1 Heqs2.
  revert  Γ Δ Σ d2.
  induction H; intros. eassumption.
  inversion c; subst.
  inversion_pair.
  econstructor. econstructor.

  subst.
  econstructor.
  inversion c; subst.
  eapply contracted_multi_trans.
  eassumption.
  epose proof (IHcontracted_seq _ _ _ _ eq_refl eq_refl) as HH.
  inversion HH. assumption.

  subst.
  inversion c; subst.
  eapply contracted_multi_trans.
  eassumption.
  epose proof (IHcontracted_seq _ _ _ _ eq_refl eq_refl) as HH.
  inversion HH. assumption.
  
  eapply cont_seqL.
  SearchAbout contracted_multi "trans".
  econstructor; [ | eapply H4].
  eapply IHcontracted_seq.
  

  eassumption.
  subst.
  inversion c. subst. 
  eassumption.
  
  intros. inversion H.
  subst. eassumption.
  subst.
Admitted.
*)

Lemma contracted_seq_multiR : forall {V : Set} Γ Δ Σ Π d1 d2,
    @contracted_seq V (Γ, Δ, d1) (Σ, Π, d2) ->
    contracted_multi Δ Π.
Proof.
  intros.
  remember (Γ, Δ, d1) as s1.
  remember (Σ, Π, d2) as s2.
  revert Heqs1 Heqs2.
  revert  Γ Δ Σ Π d1 d2.
  induction H; intros; subst.
  inversion c. subst. econstructor. 
  inversion c. subst. eassumption.

  inversion c. subst.
  eapply IHcontracted_seq; reflexivity.

  inversion c. subst.
  pose proof (IHcontracted_seq _ _ _ _ _ _ eq_refl eq_refl).
  eapply contracted_multi_trans; eassumption.
Qed.

  (*
  intros until 0; intros H.
  eapply contracted_seq_multiR_pre in H.
  inversion H. eapply cont_multi_refl.
Qed.

  SearchAbout contracted_seq "ind".
  remember (Γ,Δ,d) as s1.
  remember (Σ,Π,d) as s2.
  
  revert Heqs1 Heqs2. revert Γ Δ Σ Π d.

  induction H. admit. admit.

  intros. subst.
  destruct s2. destruct p.
  pose proof (contracted_seq_dir_same H). subst.
  inversion c. eapply IHcontracted_seq; reflexivity.

  intros. subst.
  destruct s2. destruct p.
  pose proof (contracted_seq_dir_same H). subst.
  inversion c. subst. eapply IHcontracted_seq. ; reflexivity.

  
  pose proof (IHcontracted_seq _ _ _ _ _ (eq_refl _) eq_refl).
  inversion c. subst. eassumption.
  
  ; intros; subst. admit. admit.

  
  subst. inversion H0. eapply cont_multi_refl.
  subst. inversion H0. subst. eassumption.
  subst. inversion H0. subst.
Admitted.
*)
Lemma contracted_seq_multiL : forall {V : Set} Γ Δ Σ Π d1 d2,
    @contracted_seq V (Γ, Δ, d1) (Σ, Π, d2) ->
    contracted_multi Γ Σ.
Proof.
  intros.
  remember (Γ, Δ, d1) as s1.
  remember (Σ, Π, d2) as s2.
  revert Heqs1 Heqs2.
  revert  Γ Δ Σ Π d1 d2.
  induction H; intros; subst.
  inversion c. subst. eassumption.
  inversion c. subst. econstructor.

  inversion c. subst.
  pose proof (IHcontracted_seq _ _ _ _ _ _ eq_refl eq_refl).
  eapply contracted_multi_trans; eassumption.

  inversion c. subst.
  eapply IHcontracted_seq; reflexivity.
Qed.

Lemma contracted_seq_seqL : forall {V : Set} Γ Δ Σ d1 d2,
    @contracted_seq V (Γ, Δ, d1) (Σ, Δ, d2) ->
    contracted_seqL (Γ, Δ, d1) (Σ, Δ, d2).
Proof.
  intros.
  pose proof (contracted_seq_dir_same H). subst.
  econstructor.
  eapply contracted_seq_multiL in H.
  eassumption.
Qed.
  
Lemma contracted_seq_seqR : forall {V : Set} Γ Δ Π d1 d2,
    @contracted_seq V (Γ, Δ, d1) (Γ, Π, d2) ->
    contracted_seqR (Γ, Δ, d1) (Γ, Π, d2).
Proof.
  intros.
  pose proof (contracted_seq_dir_same H). subst.
  econstructor.
  eapply contracted_seq_multiR in H.
  eassumption.
Qed.

Lemma contracted_seq_merge_app2L : forall {V : Set} Γ Δ Σ Π d,
  contracted_seq (Γ, Δ, d) (Σ, Π, d) ->
  @contracted_seq V (Γ ++ Σ, Δ ++ Π, d) (Γ, Δ, d).
Proof.
  intros until 0; intros H.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_appL.
  eapply contracted_seq_multiR. eassumption.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appL.
  eapply contracted_seq_multiL. eassumption.
Qed.

Lemma contracted_seq_merge_app2R : forall {V : Set} Γ Δ Σ Π d,
  contracted_seq (Γ, Δ, d) (Σ, Π, d) ->
  @contracted_seq V (Σ ++ Γ, Π ++ Δ, d) (Γ, Δ, d).
Proof.
  intros until 0; intros H.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_appR.
  eapply contracted_seq_multiR. eassumption.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appR.
  eapply contracted_seq_multiL. eassumption.
Qed.

Lemma contracted_seq_merge_app2L_rev : forall {V : Set} Γ Δ Σ Π d,
  contracted_seq (Σ, Π, d) (Γ, Δ, d)  ->
  @contracted_seq V (Γ ++ Σ, Δ ++ Π, d) (Γ, Δ, d).
Proof.
  intros until 0; intros H.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_appL_rev.
  eapply contracted_seq_multiR. eassumption.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appL_rev.
  eapply contracted_seq_multiL. eassumption.
Qed.

Lemma contracted_seq_merge_app2R_rev : forall {V : Set} Γ Δ Σ Π d,
  contracted_seq (Σ, Π, d) (Γ, Δ, d)  ->
  @contracted_seq V (Σ ++ Γ, Π ++ Δ, d) (Γ, Δ, d).
Proof.
  intros until 0; intros H.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_appR_rev.
  eapply contracted_seq_multiR. eassumption.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appR_rev.
  eapply contracted_seq_multiL. eassumption.
Qed.


(*
  remember (Γ,Δ,d) as s1.
  remember (Σ,Π,d) as s2.
  remember (Γ ++ Σ, Δ ++ Π, d) as s3.
  revert Heqs1 Heqs2 Heqs3.
  revert Γ Δ Σ Π.
  induction H; subst; intros. admit. admit.

  subst.
  
  inversion c. subst. inversion_pair.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_double.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appL. assumption.

  inversion c. subst. inversion_pair.
  eapply cont_seq_stepL.
  econstructor.
  eapply contracted_multi_double.
  eapply cont_seq_baseR.
  econstructor.
  eapply contracted_multi_appL. assumption.

  subst.

  inversion H0. subst.
  eapply cont_seq_stepL.
  econstructor.
  eapply contracted_multi_double.
  eapply cont_seq_baseR.
  econstructor.
  eapply contracted_multi_appL. assumption.
  eapply contracted_multi_double.


  subst.
  SearchAbout contracted_multi app.
  
  induction H. inversion c. subst.
  inversion H. subst.
Admitted.
*)

Lemma contracted_nseq_merge_fwdL : forall {V : Set} G1 G2 G3,
    @merge V G1 G2 G3 ->
    contracted_nseq G1 G2 ->
    contracted_nseq G3 G1.
Proof.
  intros V.
  induction G1; intros ? ? Hm Hc .
  inversion Hm; subst;
    inversion Hc; subst; econstructor.
  
  inversion Hm; subst; try discriminate.
  eapply contracted_nseq_refl.
  inversion_cons.
  inversion Hm; try discriminate.
  inversion_cons.
  inversion Hc; subst.
  econstructor.
  
  eapply contracted_seq_merge_app2L; eassumption.

  eapply IHG1; eassumption.
Qed.

(*
  eapply contracted_seq_merge_app2. eassumption.
  eapply contracted_seq_merge_app2. eassumption.
  eapply contracted_seq_merge_app2. eassumption.
  admit.
  inversion H. subst.
  admit.
  inversion H
            admit.
  
  eapply cont_seq_stepL; [ | eapply cont_seq_baseR].
  econstructor.
  
  intros.
  inversion Hc. subst.
  
  
  eapply rev_indT G1.
  eapply rev_ind.
  induction G1 using rev_ind.
Admitted.
*)
Lemma contracted_nseq_merge_fwdR : forall {V : Set} G1 G2 G3,
             @merge V G1 G2 G3 ->
             contracted_nseq G1 G2 ->
             contracted_nseq G3 G2.
Proof.
  intros V.
  induction G1; intros ? ? Hm Hc .
  inversion Hm; subst;
    inversion Hc; subst; econstructor.
  
  inversion Hm; subst; try discriminate.
  inversion Hc. 
  inversion_cons.
  inversion Hm; try discriminate.
  inversion_cons.
  inversion Hc; subst.
  econstructor.

  eapply contracted_seq_merge_app2R_rev; eassumption.

  eapply IHG1; eassumption.
Qed.

Lemma contracted_nseq_merge_revL : forall {V : Set} G1 G2 G3,
    @merge V G1 G2 G3 ->
    contracted_nseq G2 G1 ->
    contracted_nseq G3 G1.
Proof.
  intros V.
  induction G1; intros ? ? Hm Hc .
  inversion Hm; subst;
    inversion Hc; subst; econstructor.
  
  inversion Hm; subst; try discriminate.
  eapply contracted_nseq_refl.
  inversion_cons.
  inversion Hm; try discriminate.
  inversion_cons.
  inversion Hc; subst.
  econstructor.
  
  eapply contracted_seq_merge_app2L_rev; eassumption.

  eapply IHG1; eassumption.
Qed.

Lemma contracted_nseq_merge_revR : forall {V : Set} G1 G2 G3,
    @merge V G1 G2 G3 ->
    contracted_nseq G2 G1 ->
    contracted_nseq G3 G2.
Proof.
  intros V.
  induction G1; intros ? ? Hm Hc .
  inversion Hm; subst;
    inversion Hc; subst; econstructor.
  
  inversion Hm; subst; try discriminate.
  inversion Hc. 
  inversion_cons.
  inversion Hm; try discriminate.
  inversion_cons.
  inversion Hc; subst.
  econstructor.

  eapply contracted_seq_merge_app2R; eassumption.

  eapply IHG1; eassumption.
Qed.


         (* Starts by going through all the hypotheses of the form
            merge G G GG
            and adding 
            contracted_nseq GG G
            to the hypotheses if it doesn't already have it.

            Then for every other merge statements for which the first two inputs
            are contractions, produce the contraction hypotheses directly deducible.
            E.g. If you have
              merge GH GHGH GHGHGH
            and
              contracted_nseq GHGH GH
            then produce hypothesese
              contracted_nseq GHGHGH GH
            and
              contracted_nseq GHGHGH GHGH.
          *)
         Ltac solve_contracted_nseq_merge_pre1 :=
           try assumption; repeat
           (match goal with
           | [H : merge ?G1 ?G1 ?G2 |- _ ] =>
             lazymatch goal with
             | [ H2 : contracted_nseq G2 G1 |- _ ] => fail
             | _ => pose proof (merge_contracted_nseq _ _ H)
             end
           | [H1 : merge ?G1 ?G2 ?G3 |- _ ] =>
             lazymatch goal with
             | [H3 : contracted_nseq G3 G1, H2 : contracted_nseq G3 G2 |- _ ] => fail
             | [H2 : contracted_nseq G1 G2 |- _ ] =>
               pose proof (contracted_nseq_merge_fwdL H1 H2);
               pose proof (contracted_nseq_merge_fwdR H1 H2)
             | [H2 : contracted_nseq G2 G1 |- _ ] =>
               pose proof (contracted_nseq_merge_revL H1 H2);
               pose proof (contracted_nseq_merge_revR H1 H2)
             end
           | _ => idtac 0          
           end; try assumption).
(*               
           | [H1 : merge ?G1 ?G2 ?G3, H2 : contracted_nseq ?G1 ?G2 |- _ ] =>
             pose proof (contracted_nseq_mergeL H1 H2);
             pose proof (contracted_nseq_mergeR H1 H2)
           | [H1 : merge ?G1 ?G2 ?G3, H2 : contracted_nseq ?G2 ?G1 |- _ ] =>
             pose proof (contracted_nseq_mergeL H1 H2);
             pose proof (contracted_nseq_mergeR H1 H2)
           | _ => idtac 0 
           end).
         
           | [H : merge ?G1 ?G2 ?G3 |- _ ] => progress (
         
         Ltac get_contracted_nseq_from_merge :=
           match goal with
           | [H : merge ?G1 ?G2 ?G3 |- _ ] =>
             match goal with
             | [H2 : contracted_nseq ?G3 ?G1, H3 : contracted_nseq ?G3 ?G2 |- _ ] => idtac
             | [H3
           match goal with
           | [ H2 : merge ?G ?H ?GH , H : contracted_nseq ?GH ?G |- _ ] => fail
           | [ H2 : merge ?G ?H ?GH , H : contracted_nseq ?GH ?H |- _ ] => fail

                                                                                      Ltac solve_contracted_nseq_pre :=
         repeat match goal with
                | |- contracted_nseq (?G ++ ?H) (?G' ++ ?H') => apply contracted_nseq_app
                | [ H : merge ?G1 ?G2 ?G3 |- contracted_nseq ?G3 ?G2 ] =>
                end.
 *)

                    Definition inclT {A : Type} (l m:list A) := forall a:A, InT a l -> InT a m.

           Lemma inclT_consL_InT : forall {T : Type} (l1 l2 : list T) a,
             inclT (a :: l1) l2 -> (InT a l2).
           Proof.
             intros until 0; intros Hincl.
             apply Hincl. econstructor. reflexivity.
           Qed.
           
           Lemma inclT_consL_inclT : forall {T : Type} (l1 l2 : list T) a,
               inclT (a :: l1) l2 -> inclT l1 l2.
           Proof.
             intros until 0; intros Hincl.
             intros b Hin. apply Hincl.
             econstructor 2. assumption.
           Qed.
           
           Lemma contracted_multi_appR_inclT : forall {T : Type} (L1 L2 : list T),
             inclT L2 L1 ->
             contracted_multi (L1 ++ L2) L1.
           Proof.
             induction L2; intros Hincl.
             rewrite app_nil_r. econstructor.
             pose proof (inclT_consL_InT Hincl) as Hin.
             pose proof (inclT_consL_inclT Hincl) as Hincl2.
             list_assoc_r_single.
             eapply contracted_multi_insertL. left. assumption.
             eapply IHL2. assumption.
           Qed.
           
           Lemma contracted_multi_appL_inclT : forall {T : Type} (L1 L2 : list T),
             inclT L2 L1 ->
             contracted_multi (L2 ++ L1) L1.
           Proof.
             induction L2; intros Hincl.
             econstructor.
             simpl.
             pose proof (inclT_consL_InT Hincl) as Hin.
             pose proof (inclT_consL_inclT Hincl) as Hincl2.
             list_assoc_r_single.
             apply contracted_multi_insertL_pre.
             apply InT_appR. assumption.
             eapply IHL2. assumption.
           Qed.

                     Lemma contracted_gen_insert_InT : forall {T : Type} (l1 l2 : list T) a,
               (InT a l1 + InT a l2) ->
               contracted_gen (l1 ++ [a] ++ l2) (l1 ++ l2).
           Proof.
             intros T l1 l2 a Hin.
             destruct Hin as [Hin | Hin];
               apply InT_split in Hin; destruct Hin as [L1 [L2 HH]];
                 subst;
                 list_assoc_r_single;
                 econstructor; reflexivity.
           Qed.
           
           Lemma contracted_multi_insert_inclT : forall {T : Type} (L1 L2 L3 L4 : list T),
           (inclT L2 L1 + inclT L2 L3) ->
           contracted_multi (L1 ++ L3) L4 ->
           contracted_multi (L1 ++ L2 ++ L3) L4.
           Proof.
             induction L2; intros until 0; intros Hincl Hcont.
             simpl in *. assumption.
             list_assoc_r_single.
             econstructor; [ | eapply IHL2]; try eassumption.
             destruct Hincl as [Hincl | Hincl]; apply inclT_consL_InT in Hincl.
             apply contracted_gen_insert_InT. firstorder.
             apply contracted_gen_insert_InT. right. apply InT_appR. assumption.
             destruct Hincl as [Hincl | Hincl]; apply inclT_consL_inclT in Hincl;
               firstorder.
           Qed.

           Lemma inclT_appL : forall {T : Type} (L1 L2 L3 : list T),
               inclT L1 L3 ->
               inclT L2 L3 ->
               inclT (L1 ++ L2) L3.
           Proof.
             intros T L1 L2 L3 Hincl1 Hincl2 a Hin.
             apply InT_appE in Hin.
             destruct Hin as [Hin | Hin];
               [apply Hincl1 | apply Hincl2]; assumption.             
           Qed.


           Lemma inclT_refl : forall {T : Type} (L : list T),
               inclT L L.
           Proof. intros T L a Ha; assumption. Qed.

           Lemma inclT_appL_refl : forall {T : Type} (L1 L2 : list T),
               inclT L1 (L1 ++ L2).
           Proof.
             intros T L1 L2 a Ha.
             apply InT_appL. assumption.
           Qed.
           
           Lemma inclT_appRL : forall {T : Type} (L1 L2 L3 : list T),
               inclT L1 L3 ->
               inclT L1 (L2 ++ L3).
           Proof.
             intros T L1 L2 L3 Hincl a Ha.
             apply InT_appR. apply Hincl. assumption.
           Qed.

           Ltac solve_inclT :=
             repeat
               match goal with
               | [ |- inclT (?L1 ++ ?L2) ?L3 ] => apply inclT_appL
           | [ |- inclT ?L1 ?L1 ] => apply inclT_refl
           | [ |- inclT ?L1 (?L1 ++ ?L2) ] => apply inclT_appL_refl
           | [ |- inclT ?L1 (?L2 ++ ?L3) ] => apply inclT_appRL
               end.
           
           Ltac solve_contracted_multi :=
           repeat match goal with
           | [ |- contracted_multi ?L1 ?L2 ] =>
             match L1 with
             | L2 => apply cont_multi_refl
             | L2 ++ ?L3 => apply contracted_multi_appR_inclT
             | ?l3 ++ L2 => apply contracted_multi_appL_inclT (* I think should work but haven't tested *)
             | ?l1 ++ (?l2 ++ ?l3) =>
               match L2 with
               | l1 ++ (l2 ++ ?m2) => rewrite (app_assoc l1 l2 l3);
                                        rewrite (app_assoc l1 l2 m2)
               | l1 ++ l2 => rewrite (app_assoc l1 l2 l3)
               | l1 ++ (?m1 ++ ?m2) => apply contracted_multi_insert_inclT
               end
             | _ => idtac 333
             end
           | [ |- _ ] => list_assoc_r_single; solve_inclT
           end.



(* 
Approach 2
Case A.a + B.d.
 *)

Lemma Lemma_Sixteen_SR_p_ImpL_pfc : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt d2 Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  ( D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d2 (Φ1 ++ Imp AA BB :: BB :: Φ2, Ψ1 ++ Ψ2);
          nslcext ctxt d2 (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ AA :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
(*  pose proof D2s as D2'. *)
(*  eremember (derI _ _ D2s) as D2.  *)
(*  remember D2s as D2'. rewrite HeqD2' in Hdp. *)

(*
  eremember (derI _ _ D2s) as D2. 
 *)
 (* 
  Unshelve.
  3:{ eapply prop.
      rewrite <- map_double_singleton. econstructor.
      eapply Sctxt_eq.
      eapply ImpL_pfc.
      reflexivity.
      reflexivity.
      reflexivity.
  }
  
  eassert (dp D1 + dp D2 <= m) as HdpD2'.
  rewrite HeqD2. simpl. eassumption.
  *)
  pose proof Hdp as Hdp_keep.
  tfm_dersrec_derrec2_dp_keep D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
  Hmax1 Hmax2.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id 
      Approach 2
      Case B.d.
      *)
     inversion X. subst.
     simpl in Hdpa''.  
     simpl in Hdpb''.
     rewrite dersrec_height_nil in Hdpa''.
     rewrite dersrec_height_nil in Hdpb''.
     simpl in *.
     clear X Hdpa' Hdpb' Hprinc rl Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       unfold nslcext in Heqconcl;
       app_eq_app_dest3; try contradiction; try discriminate.
     admit.
     admit.
     admit.
    } 

  +{ (* Last rule in D1 is ImpR_pfc  *)
      destruct (merge_ex_str GH GH) as [GHGH HmeGH].
      eapply struct_equiv_str_refl.
      destruct (merge_ex_str GHGH GH) as [GHGHGH HmeGHGH].
      eapply struct_equiv_str_comm.
      eapply struct_equiv_str_mergeR.
      eapply struct_equiv_str_refl.
      eapply HmeGH.      
      
     inversion X as [? ? ? ? ? D1'] . subst.
     simpl in Hdpa''.  
     simpl in Hdpb''.
     unfold nslclext in Heqconcl.
     simpl in Hdpa'.
     simpl in Hdpb'.
     simpl in *.
     clear Hprinc X rl Hbox.
(*     eremember (derI _ _ D1') as D1. *)
(*     epose proof (derI _ _ D1') as D1. *)
(*     Unshelve.
     3:{ apply prop. econstructor. econstructor. econstructor. }
*)
     destruct (dersrec_derrec_dp D1' eq_refl) as [D1'' HdpD1''].
     assert (Hdp1a'' : dp D1'' + S (dp D2a) <= m); [ rewrite HdpD1''  |  ].
     apply Le.le_Sn_le. assumption.
     assert (Hdp1b'' : dp D1'' + S (dp D2b) <= m); [ rewrite HdpD1''  |  ].
     apply Le.le_Sn_le. assumption.

     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       unfold nslcext in Heqconcl;
       app_eq_app_dest3; try contradiction; try discriminate;
         discriminate_single_end.

     ++{ (* Approach 2
            Case B.d
          *)
         admit.
       } 
     ++{ (* Approach 2
            Case B.d
          *)
         admit.
       } 
     ++{ (* Approach 2
            Case A.a
          *)
         rewrite app_nil_r in Hstr, Hme.
         inversion_Kt_fml. subst.
         eremember (derI _ _ D1') as D1.
         eremember (derI _ _ D2s) as D2.
      (*   
  Unshelve.
  3:{ eapply prop.
      rewrite <- map_double_singleton. econstructor.
      eapply Sctxt_eq.
      eapply ImpL_pfc.
      reflexivity.
      reflexivity.
      reflexivity.
  }
       *)
         Unshelve.
         3:{ eapply prop.
             rewrite <- map_singleton.
             econstructor. eapply Sctxt_eq.
             eapply ImpR_pfc. reflexivity. reflexivity.
             simpl. reflexivity.
         }
         3:{  eapply prop.
              rewrite <- map_double_singleton. econstructor.
              eapply Sctxt_eq.
              eapply ImpL_pfc.
              reflexivity.
              reflexivity.
              reflexivity.
         } 
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ GH _ _ D1 D2a _ _ _ _) as CCa.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ GH _ _ D1 D2b _ _ _ _) as CCb.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ GH _ _ D1'' D2 _ _ _ _) as CC3.
         clear HSR_wb; clear HSR_bb; clear HSL.
         split_L16_IH IH.
         simpl in CCb. list_assoc_r_single_arg CCb.
         assoc_mid_hyp [AA] CCb.
         simpl in CC3. list_assoc_r_single_arg CC3.
         assoc_mid_hyp [AA] CC3.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CCb CC3 _ _ _ _) as CC4.
         simpl in CCa. list_assoc_r_single_arg CCa.
         assoc_mid_hyp [BB] CCa.
         rewrite (app_assoc _ Ψ2) in CC4.
         rewrite (app_assoc _ Δ1) in CC4.
         rewrite app_nil_r in CC4.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CC4 CCa _ _ _ _) as CC5.
         eapply derrec_contracted_nseq; [ | eapply CC5].
         repeat rewrite app_nil_r.
(*         eapply contracted_nseq_app; [eapply contracted_nseq_refl | ]. *)

         Unshelve.
         18:{ eapply Le.le_refl.  }
         16:{ eapply Le.le_refl. }
         22:{ eapply Le.le_refl.  }
         21:{ eapply Le.le_refl. }

         all : try (eassumption || (rewrite (app_nil_r); eassumption) ||
                    (rewrite HeqD1; simpl; eassumption) ||
                    (econstructor; [reflexivity | reflexivity | lia]) ).

         list_assoc_r_single.
         apply contracted_nseq_app.
         



           solve_contracted_nseq_merge_pre1.

           econstructor.
           eapply contracted_multi_seq.

 
           solve_contracted_multi.
           solve_contracted_multi.
           econstructor.
         
         subst. simpl.
         rewrite HdpD1''.
         eapply le_S_minus. eassumption.
         
         eapply struct_equiv_str_refl.

         eapply struct_equiv_str_comm.
         eapply struct_equiv_str_mergeR.
         eapply struct_equiv_str_refl.
         eapply HmeGH.
} 

         
         (*
         eapply contracted_nseq_app. eapply contracted_nseq_refl.
         econstructor.
         list_assoc_r_single.
           cont_solve'.
         
         admit.
 *)


(*
       rewrite (app_nil_r). eassumption.
         rewrite (app_nil_r H). eassumption.

         rewrite HeqD1. simpl. eassumption. 

         rewrite (app_nil_r H). eassumption.
         rewrite (app_nil_r H). eassumption.

         subst. simpl.
         rewrite HdpD1''.
         eapply le_S_minus. eassumption.

         eassumption.
         rewrite app_nil_r. eassumption.
         rewrite app_nil_r. eassumption.

         5:{ eapply Le.le_refl. }
         3:{ eapply Le.le_refl. }
         econstructor. reflexivity. reflexivity. lia.

         eapply struct_equiv_str_refl.
         eassumption.

         5:{ eapply Le.le_refl. }
         4:{  eapply Le.le_refl. }
         econstructor. reflexivity. reflexivity.
         lia.
         SearchAbout merge sigT.
         2:{ eapply struct_equiv_str_comm.
             eapply struct_equiv_str_mergeR.
             eapply struct_equiv_str_refl.
             eapply HmeGH.
         }
         2:{ eassumption. }
       } 
         *)
     ++{ (* Approach 2
            Case B.d
          *)
         admit.
       } 


Admitted.






(*

  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id 
      Approach 2
      Case B.d.
      *)
     inversion X. subst.
     simpl in Hdpa''.  
     simpl in Hdpb''.
     rewrite dersrec_height_nil in Hdpa''.
     rewrite dersrec_height_nil in Hdpb''.
     clear X Hdpa' Hdpb' Hprinc rl Hbox D2.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       unfold nslcext in Heqconcl;
       app_eq_app_dest3; try contradiction; try discriminate.
     admit.
     admit.
     admit.
    } 

  +{ (* Last rule in D1 is ImpR_pfc 
      Approach 2
      Case A.a
      *)
     inversion X. subst.
     simpl in Hdpa''.  
     simpl in Hdpb''.
     unfold nslclext in Heqconcl.
     simpl in Hdpa'.
     simpl in Hdpb'.
     clear Hprinc X rl Hbox.
     epose proof (derI _ _ D2) as D2'.
     Unshelve.
     3:{ apply prop. econstructor. econstructor. econstructor. }
     destruct (dersrec_derrec_dp D2 eq_refl) as [D1 HdpD1].
     assert (Hdp1a'' : dp D1 + S (dp D2a) <= m); [ rewrite HdpD1  |  ].
     apply Le.le_Sn_le. assumption.
     assert (Hdp1b'' : dp D1 + S (dp D2b) <= m); [ rewrite HdpD1  |  ].
     apply Le.le_Sn_le. assumption.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       unfold nslcext in Heqconcl;
       app_eq_app_dest3; try contradiction; try discriminate;
         discriminate_single_end.
     
         


     admit.
     admit.
     admit.
     admit.
}     

Admitted.

*)

(* --------------------------- *)
(* Lemma_Sixteen_SR_p_BotL_pfc *)
(* --------------------------- *)

(* Solves a goal of the form 
derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (... ++ [( ... ++ [Bot V] ++ ..., _, _)])
but apply BotL.
*)
Ltac der_BotL V :=
  assoc_mid [Bot V];
  eapply derI;
  [eapply prop; econstructor;
   eapply Sctxt_eq; [eapply BotL_pfc | reflexivity  ..]
  | econstructor ].

(* 
Approach 2
Case A.c + B.c.
 *)

Lemma Lemma_Sixteen_SR_p_BotL_pfc : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt d2 Φ1 Φ2 Ψ1 Ψ2
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Bot V :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (Hbox : not_box A),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HHSR_wb HHSR_bb IH;  
  split_L16_IH IH.
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d D1 ctxt d2 Φ1 Φ2 Ψ1 Ψ2 
          Heqconcl Hprinc HBox.
  unfold nslcext in *.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3; try contradiction; try discriminate; try der_BotL V.
  (* Impossible *)
  inversion Hprinc as [? ? ? H1 | ? ? ? H1]; inversion H1; discriminate.
Qed.

(* ------------------ *)
(* Lemma_Sixteen_SR_p *)
(* ------------------ *)

Lemma Lemma_Sixteen_SR_p : forall n m,
    SR_wb (S n, m) ->
    SR_bb (S n, m) ->
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SR_p (S n, m).
Proof.
  intros n m HSR_wb HSR_bb IH. unfold SR_p. unfold SR_p_pre.
  intros until 0. intros Hprinc Hdp Hsize Hbox Hstr Hme.
(*  inversion Hprinc. subst.
  (* A is atom *)
  +{  admit. }
  (* A is implication *)
  +{ 
*)
  remember D2 as D2'.
  remember  (H ++ [(Σ1 ++ [A] ++ Σ2, Π, d)] ++ I) as concl.
  destruct D2' as [|ps concl rl D2s]. contradiction.
  remember rl as rl'. 
  destruct rl' as [ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns ];
    remember Hns as Hns'.

  (* Box2Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA L1 L2 L3 | AA L1 L2 L3].
  (* WBox2Rs *)
  simpl in *. subst. eapply Lemma_Sixteen_SR_p_WBox2Rs; eassumption.
  (* BBox2Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_p_BBox2Rs; eassumption.

  
  (* Box1Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6].
  (* WBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_p_WBox1Rs; eassumption.

  (* BBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_p_BBox1Rs; eassumption.

  (* Box2Ls *)
  destruct Hns' as [ps c ctxt rl2];
    remember rl2 as rl2';
    destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6 ].
  (* WBox2Ls*)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_p_WBox2Ls; eassumption.
  simpl in *. subst.
  (* BBox2Ls *)
  eapply Lemma_Sixteen_SR_p_BBox2Ls; eassumption.

  (* Box1Ls *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6 ].
    (* WBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_p_WBox1Ls; eassumption.
   
    (* BBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_p_BBox1Ls; eassumption.

  (* EW *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [L1 L2 d2].
    (* EW_rule *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_p_EW; eassumption.

  (* prop *)
  destruct Hns' as [ps c ctxt d2 srl].
  remember srl as srl'.
  destruct srl as [ps c Φ1 Φ2 Ψ1 Ψ2 rl2].
  remember rl2 as rl2'.
  destruct rl2' as [p | AA BB | AA BB | ].
    (* Id_pfc *)
  simpl in *. subst.
  clear Hstr Hsize Hme Hdp D2s HSR_wb HSR_bb IH.
  
  eapply Lemma_Sixteen_SR_p_Id_pfc; eassumption.
 
    (* ImpR *)
    simpl in *. subst. 
    eapply Lemma_Sixteen_SR_p_ImpR_pfc; eassumption. 

    (* ImpL *) simpl in *. subst.
    eapply Lemma_Sixteen_SR_p_ImpL_pfc; eassumption.

    (* Bot  *) 
    simpl in *. subst.
    clear Hsize Hstr Hme Hdp D2s.
    eapply Lemma_Sixteen_SR_p_BotL_pfc; eassumption.
Qed.

Print Assumptions Lemma_Sixteen_SR_p.
