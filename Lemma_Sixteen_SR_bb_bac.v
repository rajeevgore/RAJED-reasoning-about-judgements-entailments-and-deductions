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
Require Import Lemma_Sixteen_SR_wb_fwd.
Require Import Lemma_Sixteen_SR_wb_bac.
Require Import Lemma_Sixteen_SR_wb.
Require Import Lemma_Sixteen_SR_bb_fwd.


Set Implicit Arguments.


(* Just slightly adapted lemmas from SR_wb cases.

SR_bb_bac, [.]^i_S   ---->   SR_wb_fwd, [-]^i_S
where 
 * [.] \in { [ ], [X] }
 * i   \in { 1, 2 }
 * S   \in { L, R }
 * [-] :=  opposite of [.]

 *)

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_WBox2Rs *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac_WBox2Rs : forall n m 
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros.
  get_SR_bb_bac_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.

  all : solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox2Rs fill_tac_BBox2Rs.
  Unshelve. all : (subst ; solve_eqs).
Qed.

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_BBox2Rs *)
(* ------------------------------- *)


 Lemma Lemma_Sixteen_SR_bb_bac_BBox2Rs : forall n m 
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros.
  get_SR_bb_bac_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.
 
  app_eq_app_dest3; try contradiction; try discriminate.


  all : solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox2Rs fill_tac_WBox2Rs.
     Unshelve. all : (subst ; solve_eqs).
Qed.

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_WBox1Rs *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac_WBox1Rs : forall n m  
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d); (L2, L5 ++ WBox AA :: L6, bac)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d); (L2, L5 ++ WBox AA :: L6, bac)];
          nslclext ctxt
            [(L1, L3 ++ L4, d); (L2, L5 ++ WBox AA :: L6, bac); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_bb_bac_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3;
    [eapply merge_app_struct_equiv_strR_explicit in Hme; [ | eassumption];
     sD; subst | | ];
    list_assoc_r_single;
    solve_case_G_gen_draft_setup D2a D2a' D2b D2b';
    fill_tac_case_G_b1r D1 D2a' D2b' WBox1Rs;
    try  solve_case_G_gen_draft_finish''' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
      solve_case_G_gen_draft_finish'' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
      Unshelve. all : (subst; solve_eqs).
Qed.

 
(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_BBox1Rs *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac_BBox1Rs : forall n m  
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d); (L2, L5 ++ BBox AA :: L6, fwd)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d); (L2, L5 ++ BBox AA :: L6, fwd)];
          nslclext ctxt
            [(L1, L3 ++ L4, d); (L2, L5 ++ BBox AA :: L6, fwd); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_bb_bac_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3;
    solve_case_G_gen_draft2 D1 D2a D2b D2a' D2b' D3 HSR Hdpa' Hdpb' BBox1Rs fill_tac_case_G_b1r.
    Unshelve. all : ( subst; solve_eqs ).
Qed.


(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_WBox2Ls *)
(* ------------------------------- *)

Ltac prep_apply_WBox2Ls_preR AA :=
  repeat
   match goal with
   | |- b2lrules ?ps (?L1 ++ [(?L2, _, _)]) =>
         match L2 with
         | _ ++ [WBox AA] ++ _ => idtac
         | ?L2a ++ _ ++ _ => rewrite (app_assoc L2a)
         end
   end.
   
Ltac prep_apply_WBox2Ls :=
  match goal with
  | H:context [ nslclext ?H [(?L1 ++ ?AA :: ?L2, _, _)] ]
    |- b2lrules ?ps ([(?L3, ?L4, ?d1)] ++ [(?L5, ?L6, ?d2)]) =>
        match L5 with
        | context [ WBox AA ] => idtac L1 L3
        end; prep_apply_BBox2Ls_preL L2 L3; prep_apply_WBox2Ls_preR AA
  end.
    
Lemma Lemma_Sixteen_SR_bb_bac_WBox2Ls : forall n m  
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d); (L3 ++ WBox AA :: L4, L6, bac)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros.
  get_SR_bb_bac_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl.

  +{ (* WBox A in last component. *)

      rewrite <- (app_nil_l Γ).
      rewrite <- app_assoc.
      eapply LNSKt_weakL; [ | reflexivity | reflexivity].
      rewrite app_nil_l.
      rewrite <- (app_nil_l (Δ1 ++ _)).
      eapply LNSKt_weakR; [ | reflexivity | reflexivity].
      eapply LNSKt_weakR; [ | reflexivity | reflexivity].
      rewrite app_nil_l.
      
      unfold nslclext in Heqconcl. inv_app_hd_tl_arg Heqconcl.
      subst.
      pose proof (merge_app_struct_equiv_strR _ _ _ _ Hme Hstr).
      sD. subst.

      list_assoc_r_single.
      rewrite <- (nslclext_def X1).
      
      get_hyp_merge_weakened_nseqR.
      eapply derrec_weakened_nseq_nslclext. eassumption.

      dest_pairs.
      eapply merge_app_single in Hme; [ | eassumption].
      sD. subst.

      (* Splits into cases where WBox A is right or left of BBox AA. *) 
      app_eq_app_dest3; try contradiction; try discriminate;      
      (eapply derI; [
      eapply b2l;
      econstructor;
      list_assoc_r_single;
      prep_apply_WBox2Ls;
      econstructor 1 | 
      econstructor; [ | econstructor];
      (eapply derrec_weakened_nseq; [ | eapply D2]);
      eapply weakened_nseq_app;
      [eapply weakened_nseq_refl |
       list_assoc_r_single;
      econstructor ;
        [eapply weakened_seq_appL | econstructor]]]).
    }

    
  +{ (* WBox A not in last component. *)
      unfold nslclext in Heqconcl. tac_cons_singleton_eq_hyp.
      tac_cons_singleton.
      app_eq_app_dest3'.
      ++{ (* WBox A not in second last component. *)
          list_assoc_l. rewrite <- (app_assoc).
          eapply derI. eapply b2l.          
          econstructor. simpl. rewrite <- app_assoc. eapply WBox2Ls.

          simpl. list_assoc_r_single.
          econstructor; [ | econstructor].

          solve_HSR HSR D2 D3 Hdp'.
        }
        Unshelve. rem_nil. list_assoc_r_single. reflexivity.
      ++{ (* WBox A in second last component. *)
          (* AA left of WBox A in D2 but not adjacent. *)

          simpl. list_assoc_r_single.
          eapply derI. eapply b2l.          
          econstructor.
          rewrite (app_assoc Γ). eapply WBox2Ls.

          econstructor; [ | econstructor].

          list_assoc_r_single.
          list_assoc_r_single_arg D3.

          rewrite (app_assoc L1).
          rewrite (app_assoc (L1 ++ _)).
          solve_HSR_except_D3 HSR D2 D3 Hdp'.
          list_assoc_r_single.
          rewrite (app_assoc Γ).
          eapply LNSKt_weakL; [ | reflexivity | reflexivity].
          list_assoc_r_single.
          eapply D3.
        }
        Unshelve. rem_nil. list_assoc_r_single. reflexivity.
      ++{ (* WBox A in second last component. *)
          (* AA right of WBox A in D2. *)

          simpl. list_assoc_r_single.
          eapply derI. eapply b2l.          
          econstructor.
          rewrite (app_assoc Γ).
          rewrite (app_assoc (Γ ++ _)).
          eapply WBox2Ls.

          econstructor; [ | econstructor].

          list_assoc_r_single.
          list_assoc_r_single_arg D3.

          solve_HSR_except_D3 HSR D2 D3 Hdp'.
          list_assoc_r_single.
          rewrite (app_assoc Γ).
          rewrite (app_assoc (Γ ++ _)).
          eapply LNSKt_weakL; [ | reflexivity | reflexivity].
          list_assoc_r_single.
          eapply D3.
        }
                Unshelve. rem_nil. list_assoc_r_single. reflexivity.

      ++{ (* WBox A in second last component. *)
          (* AA left of WBox A in D2, adjacent. *)
          
          simpl. list_assoc_r_single.
          eapply derI. eapply b2l.          
          econstructor.
          rewrite (app_assoc Γ). eapply WBox2Ls.

          econstructor; [ | econstructor].

          list_assoc_r_single.
          list_assoc_r_single_arg D3.
          rewrite (app_assoc Σ1).
          
          solve_HSR_except_D3 HSR D2 D3 Hdp'.
          list_assoc_r_single.
          rewrite (app_assoc Γ).
          eapply LNSKt_weakL; [ | reflexivity | reflexivity].
          list_assoc_r_single.
          eapply D3.
        }
        Unshelve. rem_nil. list_assoc_r_single. reflexivity.
    }
Qed.


(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_BBox2Ls *)
(* ------------------------------- *)

  Ltac SR_bb_bac_BBox2Ls_snd_last_comp D2 D3 AA A HSR Hdp' :=
    app_eq_app_dest3; try contradiction;
   (eapply derI;
     [ eapply b2l; econstructor; bracket_list_assoc_r_arg_derrec2 D2 AA;
        eapply BBox2Ls
     |  ]; econstructor; [  | constructor ]; unfold SR_bb_bac_pre in HSR;
     bracket_list_assoc_r_arg_derrec3 D2 (BBox A); eapply HSR;
     [ prep_to_weaken_derrec D3; eapply LNSKt_weakL;
        [  | reflexivity | reflexivity ]; list_assoc_r; 
        list_assoc_r_arg D3; simpl in D3; exact D3
     | econstructor 2; eassumption
     | erewrite (dp_get_D D2) in Hdp'; eapply Hdp'
     | eassumption
     | eassumption
     | simpl; lia ]).

Ltac  SR_bb_bac_BBox2Ls_not_snd_last_comp D2 D3 HSR Hdp' :=
        inv_app_hd_tl_full; tac_cons_singleton; eapply derI;
   [ eapply b2l; list_assoc_l'; eapply nslclrule_b2lrules2;
      [ reflexivity | reflexivity |  ]; list_assoc_r'; 
      eapply BBox2Ls
   |  ]; econstructor; [  | econstructor ]; unfold nslclext; list_assoc_r; 
   simpl; tac_cons_singleton; solve_HSR HSR D2 D3 Hdp'.

  
Lemma Lemma_Sixteen_SR_bb_bac_BBox2Ls : forall n m  
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d); (L3 ++ BBox AA :: L4, L6, fwd)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros n m IH V G γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
  Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  unfold nslclext in *.
  get_SR_bb_bac_pre_from_IH IH HSR (S n) (m - 1).
  rename Heqconcl into Heqconcl'. 
  (* WBox not in last component because of structural equivalence. *)

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl'.
  inv_app_hd_tl_full.
  inv_app_hd_tl_full.
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  eapply partition_singleton_app in Heqconcl'. sD; subst.
  +{ (* WBox A in snd last component *)     
      SR_bb_bac_BBox2Ls_snd_last_comp D2 D3 AA A HSR Hdp'.
    }
  +{ (* WBox A not in snd last component *)
      SR_bb_bac_BBox2Ls_not_snd_last_comp D2 D3 HSR Hdp'.
    }
   Unshelve. all : try solve [subst; solve_eqs].
Qed.

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_WBox1Ls *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac_WBox1Ls : forall n m  
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt AA d L1 L2 L3 L4 L5 L6 
  (Heqconcl : nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d); (L3 ++ L4, L6, fwd)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d); (L3 ++ AA :: L4, L6, fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros.
  get_SR_bb_bac_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.

  app_eq_app_dest3; try contradiction; try discriminate.

  all : solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_BBox1Ls.
  Unshelve. all : (subst ; solve_eqs).
Qed.

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_BBox1Ls *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac_BBox1Ls : forall n m  
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt AA d L1 L2 L3 L4 L5 L6 
  (Heqconcl : nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d); (L3 ++ L4, L6, bac)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d); (L3 ++ AA :: L4, L6, bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_bb_bac_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl.
  +{ (* WBox A in last component. *)
      (* Therefore not principal. To be treated in CASE (F). *)

      tac_cons_singleton_hyp Heqconcl.
      app_eq_app_dest3; try contradiction.

      ++{ 
      subst.
      eapply merge_app_struct_equiv_strR_explicit in Hme; [ | eassumption].
      sD; subst.
            solve_case_F_gen_draft3 D1 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_WBox1Ls.
        } 
      ++{ 
      subst.
      eapply merge_app_struct_equiv_strR_explicit in Hme; [ | eassumption].
      sD; subst.

      solve_case_F_gen_draft3 D1 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_WBox1Ls.
                }
    }
    
  +{ tac_cons_singleton_hyp Heqconcl.
     app_eq_app_dest3; try contradiction.

     ++{ (* WBox A somewhere to the left of the component containing principle WBox. *)
         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_WBox1Ls.
       } 
     ++{ (* WBox A in same component as principle WBox but to its right. *)
         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_WBox1Ls.
       }
     ++{ (* WBox A in same component as principle WBox but to its left. *)

         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_WBox1Ls.
       }

       Unshelve. all : (subst; solve_eqs).
        ++{ (* WBox A is princ WBox. *)
         (* Case could be cleaned up but low priority since it is a once-off proof. *)
         inv_singleton_str.
         unfold SR_wb_pre in HSR_wb.
         unfold SL_pre in HSL.

         edestruct (derrec_dp_same2 D2) as [D2' HdpD2'].
         repeat rewrite app_nil_r.
         list_assoc_r_single.
         reflexivity.
         rewrite HdpD2' in Hdp', Hdp''.
         clear HdpD2' D2.

         edestruct (@merge_ex V GH GH) as [XX HmergeXX].
         eapply struct_equiv_weak_refl.
         
         epose proof (@HSR_bb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D1 D2' D3  _ _ _ _ _ ) as D6.
         rewrite (app_assoc GH) in D6.
         
         list_assoc_l'_arg D3.
         rewrite <- (app_nil_r [([],_,_)]) in D3.
         change ([A]) with ([] ++ [A] ++ []) in D3.
         
         epose proof (@HSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D3 D6 _ _ _ _) as D7.
         repeat rewrite app_nil_r in D7.
         simpl in D7.
         list_assoc_r_single.
         
         eapply derrec_contracted_nseq.
         list_assoc_l.
         eapply contracted_nseq_app.
         eapply contracted_nseq_app.
         eapply merge_contracted_nseq. eapply HmergeXX.
         eapply contracted_nseq_refl.
         eapply contracted_nseq_refl.
         
         eapply derrec_contracted_nseq;
           [ | eapply D7 ].
         eapply contracted_nseq_app.
         eapply contracted_nseq_app.
         eapply contracted_nseq_refl.
         list_assoc_r. eapply contracted_nseq_single.
         eapply contracted_nseq_refl.
         Unshelve.
         exact (S n). 
         exact (m-1).
         econstructor 2; try reflexivity. lia.
         econstructor 2. eassumption.
         eassumption.
         assumption.
         assumption.
         simpl. lia.
         exact n.
         exact (plus (dp D3) (dp D6)).
         econstructor; try reflexivity. lia.
         eapply PeanoNat.Nat.le_refl.
         assumption.
         list_assoc_r.
         eapply struct_equiv_str_refl.
         eapply merge_app. reflexivity.
         assumption.
         list_assoc_r.
         econstructor 3; try reflexivity.
         econstructor; reflexivity.
         solve_eqs.
          }         
} 
Qed.

(* -------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_EW *)
(* -------------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac_EW : forall n m  
 (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, bac)]))
  ctxt L1 L2 d
  (Heqconcl : nslclext ctxt [(L1, L2, d)] = H ++ (Σ1 ++ BBox A :: Σ2, Π, bac) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False) 
          [nslclext ctxt []])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, bac) :: I).
Proof.
  intros.
  unfold nslclext in *.
  get_SR_bb_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl.

  +{ (* WBox A in last component. *)
      inv_app_hd_tl_full.
      eapply derI.
      eapply nEW.
      econstructor.      
      econstructor.

      simpl. econstructor; [| econstructor].
      unfold nslclext. rewrite app_nil_r.

      eapply derrec_struct_equiv_mergeR.
      eassumption. eassumption.
      eapply (@get_D _ _ _ _ _ D2).
      repeat rewrite app_nil_r; solve_eqs.      
    }
  +{ (* WBox A not in last component. *)
      inv_app_hd_tl_full.
      tac_cons_singleton.
      list_assoc_l.
      eapply external_weakeningR.
      list_assoc_r. simpl.
      solve_HSR HSR D2 D3 Hdp'.
    }
    Unshelve. repeat rewrite app_nil_r; solve_eqs.
Qed.


(* -------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_ImpR_pfc *)
(* -------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac_ImpR_pfc : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d2
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, d2)]))
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d (Φ1 ++ Φ2, Ψ1 ++ Imp AA BB :: Ψ2) =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, d2) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d (Φ1 ++ AA :: Φ2, Ψ1 ++ Imp AA BB :: BB :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2) :: I).
Proof.
  intros.
(*
  get_SR_wb_fwd_pre_from_IH IH HSRfwd (S n) (m - 1).
  get_SR_wb_bac_pre_from_IH IH HSRbac (S n) (m - 1).
*)
  get_SR_bb_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslcext in *.
  destruct d2;
  (destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full;              
    [app_eq_app_dest3; try contradiction; try discriminate | ]);
  solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' ImpR_pfc fill_tac_ImpR_pfc.
     Unshelve. all : (subst ; solve_eqs).
Qed.


(* -------------------------------- *)
(* Lemma_Sixteen_SR_bb_bac_ImpL_pfc *)
(* -------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac_ImpL_pfc : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d2
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, d2)]))
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, d2) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2); ([], [A], bac)]))
  (Hprinc : principal_BBox2Rs D1 (BBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d (Φ1 ++ Imp AA BB :: BB :: Φ2, Ψ1 ++ Ψ2);
          nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ AA :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH.
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d2 D1  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_bb_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.

  unfold nslcext in *.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3; try contradiction; try discriminate.
+{ 
  solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.

      eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
     bracket_set_up1_redo_twoprem D1 D2a' D2b' ImpL_pfc; simpl | ].

eapply Sctxt_eq. eapply ImpL_pfc. reflexivity. reflexivity. reflexivity.

  econstructor; [  | econstructor; [  | econstructor ] ];
    unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.
  solve_HSR_except_D3' HSR D2a D3 Hdpa'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.
  solve_HSR_except_D3' HSR D2b D3 Hdpb'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.
}
  Unshelve.
  all : try solve [subst; solve_eqs].
+{ 
  
  solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.

      eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
     bracket_set_up1_redo_twoprem D1 D2a' D2b' ImpL_pfc; simpl | ].

      eapply Sctxt_eq. eapply ImpL_pfc.
      
      reflexivity.
      reflexivity.
      reflexivity.

  econstructor; [  | econstructor; [  | econstructor ] ];
    unfold nslcext || unfold nslclext; unfold seqext;
  list_assoc_r_single.

  assoc_mid_loc H1. rewrite <- (app_assoc Γ).
  rewrite (app_assoc _ H1).

    solve_HSR_except_D3' HSR D2a D3 Hdpa'.
    solve_D3_weakened D3. struct_equiv_str_solve_primitive.
    
  assoc_mid_loc H1. rewrite <- (app_assoc Γ).
  rewrite (app_assoc _ H1).

    solve_HSR_except_D3' HSR D2b D3 Hdpb'.
    solve_D3_weakened D3. struct_equiv_str_solve_primitive.
  }

  Unshelve.
  all : (subst; solve_eqs).

+{ 

  solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.
  rewrite (app_assoc _ Hl2).

      eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
     bracket_set_up1_redo_twoprem D1 D2a' D2b' ImpL_pfc; simpl | ].

      eapply Sctxt_eq. eapply ImpL_pfc.
      
      reflexivity.
      reflexivity.
      reflexivity.

  econstructor; [  | econstructor; [  | econstructor ] ];
    unfold nslcext || unfold nslclext; unfold seqext;
  list_assoc_r_single.


    solve_HSR_except_D3' HSR D2a D3 Hdpa'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

    solve_HSR_except_D3' HSR D2b D3 Hdpb'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.
} 
  Unshelve.
  all : (subst; solve_eqs).
Qed.

(* ----------------------- *)
(* Lemma_Sixteen_SR_bb_bac *)
(* ----------------------- *)

Lemma Lemma_Sixteen_SR_bb_bac : forall n m,
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SR_bb_bac (S n, m).
Proof.
  intros n m IH. unfold SR_bb_bac. unfold SR_bb_bac_pre.
  intros until 0. intros D3 Hprinc Hdp Hstr Hme Hsize.
  eapply principal_BBR_bac in Hprinc ; [ | reflexivity].
  simpl in Hsize. apply le_S_n in Hsize.

  remember D2 as D2'.
  remember  (H ++ [(Σ1 ++ [BBox A] ++ Σ2, Π, bac)] ++ I) as concl.
  destruct D2' as [|ps concl rl D2s]. contradiction.
  remember rl as rl'. 
  destruct rl' as [ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns ];
    remember Hns as Hns'.

  (* Box2Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA L1 L2 L3 | AA L1 L2 L3].
  (* WBox2Rs *)
  simpl in *. subst. eapply Lemma_Sixteen_SR_bb_bac_WBox2Rs; eassumption.
  (* BBox2Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_bb_bac_BBox2Rs;  eassumption.

  
  (* Box1Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6].
  (* WBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_bb_bac_WBox1Rs; eassumption.


  (* BBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_bb_bac_BBox1Rs; try eassumption.

  (* Box2Ls *)
  destruct Hns' as [ps c ctxt rl2];
    remember rl2 as rl2';
    destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6 ].
  (* WBox2Ls *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_bb_bac_WBox2Ls; eassumption.
  simpl in *. subst.
  (* BBox2Ls *)
  eapply Lemma_Sixteen_SR_bb_bac_BBox2Ls; try eassumption. 

  (* Box1Ls *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6 ].
    (* WBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_bb_bac_WBox1Ls; eassumption.
   
    (* BBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_bb_bac_BBox1Ls; eassumption.

  (* EW *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [L1 L2 d].
    (* EW_rule *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_bb_bac_EW; eassumption.

  (* prop *)
  destruct Hns' as [ps c ctxt d srl].
  remember srl as srl'.
  destruct srl as [ps c Φ1 Φ2 Ψ1 Ψ2 rl2].
  remember rl2 as rl2'.
  destruct rl2' as [p | AA BB | AA BB | ].
    (* Id_pfc *)
    simpl in *. subst.
    clear Hsize D3 Hme Hdp D2s Hprinc.
    clear D1 IH.
    eapply Lemma_Sixteen_SR_bb_Id_pfc. eassumption.
 
    (* ImpR *)
    simpl in *. subst. 
    eapply Lemma_Sixteen_SR_bb_bac_ImpR_pfc; eassumption. 

    (* ImpL *) simpl in *. subst.
    eapply Lemma_Sixteen_SR_bb_bac_ImpL_pfc; eassumption.

    (* Bot  *) 
    simpl in *. subst.
    clear Hsize D3 Hme Hdp D2s Hprinc.
    clear D1 IH.
    eapply Lemma_Sixteen_SR_bb_BotL_pfc. eassumption.
Qed.

Print Assumptions Lemma_Sixteen_SR_bb_bac.
