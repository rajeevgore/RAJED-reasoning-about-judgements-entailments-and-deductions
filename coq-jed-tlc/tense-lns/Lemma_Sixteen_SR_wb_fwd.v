Add LoadPath "../general".
Require Import Lia.

Require Import gen genT gen_seq.
Require Import ddT dd_fc.
Require Import lntacsT gen_tacs.
Require Import lntT.
Require Import lntkt_exchT.
Require Import size.
Require Import merge.
Require Import structural_equivalence.
Require Import principal.
Require Import ind_lex.
Require Import List_lemmasT.
Require Import lnt_gen_initT.
Require Import lntb2LT.
Require Import lnt_weakeningT.
Require Import weakenedT.
Require Import lntbRT lntb1LT.
Require Import Lemma_Sixteen_setup.
Require Import lnt_contraction_mrT.
Require Import contractedT.


Set Implicit Arguments.


(* -------------------------- *)
(* Lemma_Sixteen_SR_wb_Id_pfc *)
(* -------------------------- *)

Lemma Lemma_Sixteen_SR_wb_Id_pfc : forall {V : Set} GH H I ctxt d d2 Γ Σ1 Σ2 Δ1 Δ2 Π Φ1 Φ2 Ψ1 Ψ2 p A,
    (nslcext ctxt d (Φ1 ++ Var p :: Φ2, Ψ1 ++ Var p :: Ψ2) =
     H ++ (Σ1 ++ [WBox A] ++ Σ2, Π, d2) :: I) ->
    derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
           (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2) :: I).
Proof.
  intros until 0; intros Heqconcl.
  unfold nslcext in Heqconcl.
  apply partition_singleton_app in Heqconcl.
  destruct Heqconcl as [[[HH1 HH2] HH3] | [HH1 [HH2 HH3]]].
  subst.
  inversion HH3. subst.
  assert ((Var p) <> (WBox A)) as Hneq.
  intros. discriminate.
  epose proof (InT_singleton_mid _ _ _ _ Hneq H1) as Hin.
  destruct Hin as [Hin | Hin].
  epose proof (@Id_InT V _ _ _ _ p) as DD.
  eapply DD.
  eapply InT_appR. apply InT_appL. assumption.
  eapply InT_appR. apply InT_appR.
  eapply InT_appR. econstructor. reflexivity.
  epose proof (@Id_InT V _ _ _ _ p) as DD.
  eapply DD.
  eapply InT_appR. apply InT_appR. assumption.
  eapply InT_appR. apply InT_appR.
  eapply InT_appR. econstructor. reflexivity.

  subst.  
  eapply derI.  
  eapply prop.
  rewrite cons_singleton. repeat rewrite app_assoc.
  econstructor.
  eapply seqrule_same.
  econstructor. apply Id_pfc.
  reflexivity. econstructor.
Qed.


(* ---------------------------- *)
(* Lemma_Sixteen_SR_wb_BotL_pfc *)
(* ---------------------------- *)

Lemma Lemma_Sixteen_SR_wb_BotL_pfc : forall {V : Set} GH H I ctxt d d2 d3 Γ Σ1 Σ2 Δ1 Δ2 Π Φ1 Φ2 Ψ1 Ψ2 A,
 nslcext ctxt d (Φ1 ++ Bot V :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ [WBox A] ++ Σ2, Π, d2) :: I ->
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d3) :: I).
Proof.
  intros until 0; intros Heqconcl.
  unfold nslcext in Heqconcl.
  apply partition_singleton_app in Heqconcl.
  destruct Heqconcl as [[[HH1 HH2] HH3] | [HH1 [HH2 HH3]]].
  subst.
  inversion HH3. subst.
  assert ((Bot V) <> (WBox A)) as Hneq. intros; discriminate.
  epose proof (InT_singleton_mid _ _ _ _ Hneq H1) as Hin.
  destruct Hin as [Hin | Hin].
  epose proof (@BotL_InT V _ _ _ _) as DD.
  eapply DD.
  eapply InT_appR. eapply InT_appL. assumption.
  epose proof (@BotL_InT V _ _ _ _) as DD.
  eapply DD.
  eapply InT_appR. apply InT_appR. assumption.

  subst.  
  eapply derI.  
  eapply prop.
  rewrite cons_singleton. repeat rewrite app_assoc.
  econstructor.
  eapply seqrule_same.
  econstructor. apply BotL_pfc.
  reflexivity. econstructor.
Qed.
(*
Lemma Lemma_Sixteen_SR_wb_fwd_BotL_pfc : forall {V : Set} GH H I ctxt d d2 d3 Γ Σ1 Σ2 Δ1 Δ2 Π Φ1 Φ2 Ψ1 Ψ2 A,
 nslcext ctxt d (Φ1 ++ Bot V :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ [WBox A] ++ Σ2, Π, d2) :: I ->
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d3) :: I).
Proof.
  intros until 0; intros Heqconcl.
  unfold nslcext in Heqconcl.
  apply partition_singleton_app in Heqconcl.
  destruct Heqconcl as [[[HH1 HH2] HH3] | [HH1 [HH2 HH3]]].
  subst.
  inversion HH3. subst.
  assert ((Bot V) <> (WBox A)) as Hneq. intros; discriminate.
  epose proof (InT_singleton_mid _ _ _ _ Hneq H1) as Hin.
  destruct Hin as [Hin | Hin].
  epose proof (@BotL_InT V _ _ _ _) as DD.
  eapply DD.
  eapply InT_appR. eapply InT_appL. assumption.
  epose proof (@BotL_InT V _ _ _ _) as DD.
  eapply DD.
  eapply InT_appR. apply InT_appR. assumption.

  subst.  
  eapply derI.  
  eapply prop.
  rewrite cons_singleton. repeat rewrite app_assoc.
  econstructor.
  eapply seqrule_same.
  econstructor. apply BotL_pfc.
  reflexivity. econstructor.
Qed.
*)

(* ------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_WBox2Ls *)
(* ------------------------------- *)

Ltac bracket_D2_AA D2'' AA :=
  match goal with
  | [ D2'' : derrec ?rules ?prems (?H ++ [(?l1,?l2,?d)]) |-
      ?C ?ps [(?L1,?L2,?d2) ; (?L3,?L4,?d3) ] ] => tac_match l1 [AA]
  end.

Ltac bracket_list_assoc_r_arg_derrec  D2 AA :=
  match goal with
  | [ D2 : derrec ?rules ?prems ?concl |- _ ] =>
    let t := fresh in let Heqt := fresh in
        remember concl as t eqn: Heqt; list_assoc_r_arg Heqt; simpl in Heqt;
        tac_cons_singleton_hyp Heqt;
        let D2' := fresh D2 in
        pose (@get_D _ _ _ _ _ D2 Heqt) as D2';
        bracket_D2_AA D2' AA
  end.

(* Looks at derivation D2 and finds the location of [AA] in the list of l1 ++ l2 ++ ... ++ [AA] ++ ... ++ ln
and brackets the conclusion
Γ ++ l1 ++ l2 ++ ... ++ [AA] ++ ... ln 
into
 (...(...((Γ ++ l1) ++ l2) ++ ... ++ [AA]) ++ ... ln)
*)
Ltac bracket_list_assoc_r_arg_derrec2 D2 AA :=
  list_assoc_r; simpl; bracket_list_assoc_r_arg_derrec D2 AA.

Ltac bracket_D2_B D2'' B :=
  match goal with
  | [ D2'' : derrec ?rules ?prems (?H ++ [(?l1,?l2,?d)]) |-
      derrec ?rules2 ?prems2 (nslclext ?GH [(?L1++?L1',?L2,?d2)]) ] =>
    tac_match2 l1 L1 B
  end.

Ltac bracket_list_assoc_r_arg_derrec3_pre D2 B :=
  match goal with
  | [ D2 : derrec ?rules ?prems ?concl |- _ ] =>
    let t := fresh in let Heqt := fresh in
                      remember concl as t eqn: Heqt;
                      list_assoc_r_arg Heqt;
                      simpl in Heqt;
                      tac_cons_singleton_hyp Heqt;
                      let D2' := fresh D2 in
                      pose (@get_D _ _ _ _ _ D2 Heqt) as D2';
                      bracket_D2_B D2' B
  end.

(*
Looks at D2 and looks where the B formula is (between Lm and Lssm) and brackets the conclusion from
Γ ++ L1 ++ ... ++ Lm ++ Lssm ++ ... ++ Ln
to
Γ ++ (L1 ++ ... ++ Lm) ++ (Lssm ++ ... ++ Ln)
*)
Ltac bracket_list_assoc_r_arg_derrec3 D2 B :=
       simpl; list_assoc_r; tac_cons_singleton;
       bracket_list_assoc_r_arg_derrec3_pre D2 B.

(* For lists of the form 
((...((L1 ++ L2) ++ L3) ++ ... ) ++ Ln),
rebracket so that it becomes
L1 ++ L2 ++ L3 ++ ... Ln.
Used as a helper function todo similar to list_assoc_r but control which level of list nesting (i.e. nested G level or list of formula Γ level.)
*)
Ltac find_head_then_push_r L :=
  match L with
  | ?L1 ++ ?L2 => find_head_then_push_r L1
  | _ => repeat rewrite <- (app_assoc L)
  end.

(* For nested sequents of the form 
((...((L1 ++ L2) ++ L3) ++ ... ) ++ Ln),
rebracket so that it becomes
L1 ++ L2 ++ L3 ++ ... Ln.
Used similar to list_assoc_r but acts only on lists of a certain form, and only on nested level.
Useful after assoc_mid.
*)
Ltac list_assoc_r_nested_level_from_l :=
  match goal with
  | [ |- derrec _ _ ?L ] => find_head_then_push_r L
  end.

(* Finds the list (L3) that is first missing in Γ that is in Γ2, then rebracket L3 in the conclusion so that it is centred, ready to weaken. *)
Ltac find_princ_weak_in_seq Γ Γ2 :=
  match Γ with
  | ?L1 ++ ?L2 =>
    match Γ2 with
    | ?L1 ++ ?L3 => find_princ_weak_in_seq L2 L3
    | ?L3 ++ ?L4 => assoc_mid L3
    end
  | _ =>
    match Γ2 with
    | ?L3 ++ ?L4 => assoc_mid L3
    end
  end.

(* Finds the list that is first missing in ns that is in ns2, then rebracket in the conclusion so that it is centred, ready to weaken. *)
Ltac find_princ_weak_in_snd_last_comp ns ns2 :=
  match ns with
  | [(?Γ,?Δ,?d)] ++ [?seq] =>
    match ns2 with
    | [(?Γ2,?Δ2,?d2)] ++ [?seq2] => find_princ_weak_in_seq Γ Γ2
    end
  | ?GH ++ ?tl =>
    match ns2 with
    | ?GH ++ ?tl2 => find_princ_weak_in_snd_last_comp tl tl2
    end
  end.

Ltac prep_to_weaken_derrec_pre D3 :=
  match goal with
  | [ D3 : derrec ?rules ?prems ?ns |- derrec ?rules ?prems ?ns2 ] =>
    find_princ_weak_in_snd_last_comp ns ns2
  end.

(* Prep conclusion, ready to weaken D3 to get conclusion. *)
Ltac prep_to_weaken_derrec D3 :=
  list_assoc_r_single;
  prep_to_weaken_derrec_pre D3;
  list_assoc_r_nested_level_from_l.

Lemma nslclrule_b2lrules2 : forall V ps concl L L' seq1 seq2,
    L = L' ->
    concl = ((L ++ [seq1]) ++ [seq2]) ->
    b2lrules ps ([seq1;seq2]) ->
    nslclrule (b2lrules (V := V)) (map (nslclext L') ps) concl.
Proof.
  intros until 0; intros Heq1 Heq2 Hb. subst.
  list_assoc_r. simpl. econstructor.
  assumption.
Qed.

Ltac solve_HSR HSR D2 D3 Hdp' :=
  eapply HSR;
  [list_assoc_r_single; eapply D3 | ((econstructor 2; eassumption) || (econstructor 1; eassumption)) |
   erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
   eapply Hdp' |
   eassumption |
   eassumption |
   simpl; lia].

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


Ltac prep_apply_BBox2Ls_preL L2 L3 :=
  match L3 with
  | _ ++ L2 => idtac
  | ?L3a ++ ?L3b ++ ?L3c => rewrite (app_assoc L3a);
                            prep_apply_BBox2Ls_preL L2 ((L3a ++ L3b) ++ L3c)
  end.

Ltac prep_apply_BBox2Ls_preR AA :=
  repeat match goal with
         | [ |- b2lrules ?ps (?L1 ++ [(?L2,_,_)]) ] =>
           match L2 with
           | _ ++ ([BBox AA]) ++ _ => idtac
           | ?L2a ++ _ ++ _ => rewrite (app_assoc L2a)
           end
         end.


Ltac prep_apply_BBox2Ls :=
  match goal with
  | [ H : context [ nslclext ?H [(?L1 ++ ?AA :: ?L2, _, _)] ] |-
      b2lrules ?ps ([(?L3,?L4,?d1)] ++ [(?L5,?L6,?d2) ]) ] =>
    match L5 with
    | context [ BBox AA ] => idtac L1 L3
    end;
    prep_apply_BBox2Ls_preL L2 L3;
    prep_apply_BBox2Ls_preR AA
  end.

Ltac solve_HSR_except_D3 HSR D2 D3 Hdp' :=
  eapply HSR;
  [ | ((econstructor 2; eassumption) || (econstructor 1; eassumption)) |
   erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
   eapply Hdp' |
   try eassumption |
   repeat (eassumption || merge_solve_primitive) |
   simpl; lia].

Ltac bracket_set_up1_pre D2' AA :=
  match type of D2' with
  | derrec ?rules ?prems ?H =>
    match get_last_app H with
    | [(?L1,?L2,?d)] =>  tac_match L1 [AA]
    end
  end.

Ltac bracket_set_up1_preR D1 D2' AA :=
  match type of D2' with
  | derrec ?rules ?prems ?H =>
    match get_last_app H with
    | [(?L1,?L2,?d)] =>
      try (match type of D1 with
      | derrec _ _ ?G => match get_last_app G with
                         | [(_,?Δ1 ++ _, _)] => rewrite (app_assoc Δ1)
                         end
      end);
      tac_match L2 [AA]
    end
  end.

Ltac bracket_set_up1_pre_snd D2' AA :=
  match type of D2' with
  | derrec ?rules ?prems ?H =>
    match get_snd_last_app H with
    | [(?L1,?L2,?d)] =>  tac_match L1 [AA]
    end
  end.

Ltac bracket_set_up1_pre_sndR D1 D2' AA :=
  match type of D2' with
  | derrec ?rules ?prems ?H =>
    match get_snd_last_app H with
    | [(?L1,?L2,?d)] =>
      try (match type of D1 with
           | derrec _ _ ?G => match get_last_app G with
                              | [(_,?Δ1 ++ _, _)] => rewrite (app_assoc Δ1)
                              end
           end);
      tac_match L2 [AA]                             
    end
  end.


Ltac bracket_set_up2_pre D2' :=
  match goal with
  | [ |- context [ WBox ?A ] ] => idtac 21;
        match type of D2' with
        | context [ [WBox A] ] => idtac 22; fail
        | context [ [WBox ?B] ] => idtac 23; bracket_set_up1_pre D2' (WBox B)
        end
  | [ |- context [ BBox ?A ] ] => idtac 21;
        match type of D2' with
        | context [ [BBox A] ] => idtac 22; fail
        | context [ [BBox ?B] ] => idtac 23; bracket_set_up1_pre D2' (BBox B)
        end
  | _ => idtac 24;
        match type of D2' with
        | context [ [WBox ?B] ] => idtac 25; bracket_set_up1_pre D2' (WBox B)
        | context [ [BBox ?B] ] => idtac 25; bracket_set_up1_pre D2' (BBox B)
        | context [ [Imp ?AA ?BB] ] => idtac 26; bracket_set_up1_pre D2' (Imp AA BB)
        end
  end.

Ltac bracket_set_up2_pre_snd D2' :=
  match goal with
  | |- context [ WBox ?A ] =>
        idtac 21;
         match type of D2' with
         | context [ [WBox ?B] ] =>
             lazymatch B with
             | A => idtac 22; fail
             | _ => idtac 23; bracket_set_up1_pre_snd D2' (WBox B)
             end
         end
  | |- context [ BBox ?A ] =>
        idtac 21;
         match type of D2' with
         | context [ [BBox ?B] ] =>
             lazymatch B with
             | A => idtac 22; fail
             | _ => idtac 23; bracket_set_up1_pre_snd D2' (BBox B)
             end
         end
  | |- context [ WBox ?A ] =>
       match type of D2' with
       | context [ [BBox ?B] ] => idtac 25; bracket_set_up1_pre_snd D2' (BBox B)
       end
  | |- context [ BBox ?A ] =>
       match type of D2' with
       | context [ [WBox ?B] ] =>
           idtac 25; bracket_set_up1_pre_snd D2' (WBox B)
       end
  | _ =>
      idtac 24;
       match type of D2' with
       | context [ [WBox ?B] ] =>
           idtac 25; bracket_set_up1_pre_snd D2' (WBox B)
       | context [ [BBox ?B] ] => idtac 25; bracket_set_up1_pre_snd D2' (BBox B)
       end
  end.


(*
  Ltac bracket_set_up2_pre_snd D2' :=
  match goal with
  | [ |- context [ WBox ?A ] ] => idtac 21;
        match type of D2' with
        | context [ [WBox ?B] ] =>
          lazymatch B with
          | A => idtac 22; fail
          | _ => idtac 23; bracket_set_up1_pre_snd D2' (WBox B)
          end
        end
  | [ |- context [ BBox ?A ] ] => idtac 21;
        match type of D2' with
        | context [ [BBox ?B] ] =>
          lazymatch B with
          | A => idtac 22; fail
          | _ => idtac 23; bracket_set_up1_pre_snd D2' (BBox B)
          end
        end
  | _ => idtac 24;
         match type of D2' with
         | context [ [WBox ?B] ] => idtac 25; bracket_set_up1_pre_snd D2' (WBox B)
         | context [ [BBox ?B] ] => idtac 25; bracket_set_up1_pre_snd D2' (BBox B)
         end
  end.
*)
  
Ltac bracket_set_up2 D1 D2' :=
  match type of D1 with
  | derrec _ _ ?G =>
    match G with
    | ?G' ++ [(?Σ,?Π,?d)] =>
      match Π with
      | context [ WBox ?A ] =>
        match type of D2' with
        | derrec _ _ (?GG' ++ [?seq]) =>
          match seq with
          | context [ WBox A ] =>
            idtac 5; bracket_set_up2_pre D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | derrec _ _ (?GG' ++ [?seq] ++ _) =>
          match seq with
          | context [ WBox A ] =>
            idtac 10; bracket_set_up2_pre_snd D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | derrec _ _ (?GG' ++ _ ++ [?seq]) =>
          match seq with
          | context [ WBox A ] =>
            idtac 10; bracket_set_up2_pre D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | _ => idtac 555
        end
      | context [ BBox ?A ] =>
        match type of D2' with
        | derrec _ _ (?GG' ++ [?seq]) =>
          match seq with
          | context [ BBox A ] =>
            idtac 5; bracket_set_up2_pre D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | derrec _ _ (?GG' ++ [?seq] ++ _) =>
          match seq with
          | context [ BBox A ] =>
            idtac 10; bracket_set_up2_pre_snd D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | derrec _ _ (?GG' ++ _ ++ [?seq]) =>
          match seq with
          | context [ BBox A ] =>
            idtac 10; bracket_set_up2_pre D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | _ => idtac 555
        end
      end
    end
  end.

(*
Ltac bracket_set_up2_pre D2' :=
  match goal with
  | [ |- context [ WBox ?A ] ] => idtac 21;
        match type of D2' with
        | context [ [WBox A] ] => idtac 22; fail
        | context [ [WBox ?B] ] => idtac 23; bracket_set_up1_pre D2' (WBox B)
        end
  | _ => idtac 24;
        match type of D2' with
        | context [ [WBox ?B] ] => idtac 25; bracket_set_up1_pre D2' (WBox B)
        | context [ [Imp ?AA ?BB] ] => idtac 26; bracket_set_up1_pre D2' (Imp AA BB)
        end
  end.

Ltac bracket_set_up2_pre_snd D2' :=
  match goal with
  | [ |- context [ WBox ?A ] ] => idtac 21;
        match type of D2' with
        | context [ [WBox ?B] ] =>
          lazymatch B with
          | A => idtac 22; fail
          | _ => idtac 23; bracket_set_up1_pre_snd D2' (WBox B)
          end
        end
  | _ => idtac 24;
         match type of D2' with
         | context [ [WBox ?B] ] => idtac 25; bracket_set_up1_pre_snd D2' (WBox B)
         end
  end.

Ltac bracket_set_up2 D1 D2' :=
  match type of D1 with
  | derrec _ _ ?G =>
    match G with
    | ?G' ++ [(?Σ,?Π,?d)] =>
      match Π with
      | context [ WBox ?A ] =>
        match type of D2' with
        | derrec _ _ (?GG' ++ [?seq]) =>
          match seq with
          | context [ WBox A ] =>
            idtac 5; bracket_set_up2_pre D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | derrec _ _ (?GG' ++ [?seq] ++ _) =>
          match seq with
          | context [ WBox A ] =>
            idtac 10; bracket_set_up2_pre_snd D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | derrec _ _ (?GG' ++ _ ++ [?seq]) =>
          match seq with
          | context [ WBox A ] =>
            idtac 10; bracket_set_up2_pre D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | _ => idtac 555
        end
      end
      match Π with
      | context [ BBox ?A ] =>
        match type of D2' with
        | derrec _ _ (?GG' ++ [?seq]) =>
          match seq with
          | context [ BBox A ] =>
            idtac 5; bracket_set_up2_pre D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | derrec _ _ (?GG' ++ [?seq] ++ _) =>
          match seq with
          | context [ BBox A ] =>
            idtac 10; bracket_set_up2_pre_snd D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | derrec _ _ (?GG' ++ _ ++ [?seq]) =>
          match seq with
          | context [ BBox A ] =>
            idtac 10; bracket_set_up2_pre D2';
            repeat rewrite <- (app_assoc Σ)
          end
        | _ => idtac 555
        end
      end
    end
  end.
*)

Ltac list_assoc_r_arg_derrec2_spec  D2 D2' :=
  match type of D2 with
  | derrec ?rules ?prems ?concl  =>
    let t := fresh in let Heqt := fresh in
         remember concl as t eqn: Heqt; list_assoc_r_arg Heqt; simpl in Heqt;
                      tac_cons_singleton_hyp Heqt;
                      pose (get_D D2 Heqt) as D2'
  end.

Ltac solve_D3_weakened D3 :=
  list_assoc_r_single;
  eapply derrec_weakened_nseq; [ | eapply D3];
  list_assoc_r_single;
  weakened_nseq_solve_nseq;
  weakened_seq_solve;
  weakened_multi_solve.

Ltac bracket_set_up1_redo D2' rl :=
  match rl with
  | ImpR_pfc =>
    match type of D2' with
    | context [ [Imp ?AA ?BB] ] =>
      bracket_set_up1_pre D2' AA; assoc_mid_loc [Imp AA BB]
    end
  | WBox2Rs =>
    match type of D2' with
    | context [ ([], [?AA], fwd) ] => assoc_mid_loc [WBox AA]
    end
  | BBox1Ls =>
    match type of D2' with
    | context [BBox ?AA] => assoc_mid_loc [BBox AA];
                             bracket_set_up1_pre D2' AA
    end
  | BBox2Rs => 
    match type of D2' with
    | context [ ([], [?AA], bac) ] => assoc_mid_loc [BBox AA]
    end
  | WBox1Ls =>
    match goal with
    | [ |- context [ WBox ?A ] ] => assoc_mid_loc [WBox A];
                                    bracket_set_up1_pre D2' A
    end
  | WBox1Rs =>
    match type of D2' with
    | context [ ([], [?AA], fwd) ] => assoc_mid_loc [WBox AA]
    end
  | ImpL_pfc =>
    match type of D2' with
    | context [ Imp ?AA ?BB ] => bracket_set_up1_pre D2' BB; assoc_mid_loc [Imp AA BB]
    end
  end.

(*
Ltac bracket_set_up1_redo D2' rl :=
  match rl with
  | ImpR_pfc =>
    match type of D2' with
    | context [ [Imp ?AA ?BB] ] =>
      bracket_set_up1_pre D2' AA; assoc_mid_loc [Imp AA BB]
    end
  | WBox2Rs =>
    match type of D2' with
    | context [ ([], [?AA], fwd) ] => assoc_mid_loc [WBox AA]
    end
  | BBox1Ls =>
    match type of D2' with
    | context [BBox ?AA] => assoc_mid_loc [BBox AA];
                             bracket_set_up1_pre D2' AA
    end
  | BBox2Rs => idtac 678
  | WBox1Ls =>
    match goal with
    | [ |- context [ WBox ?A ] ] => assoc_mid_loc [WBox A];
                                    bracket_set_up1_pre D2' A
    end
  | WBox1Rs =>
    match type of D2' with
    | context [ ([], [?AA], fwd) ] => assoc_mid_loc [WBox AA]
    end
  | ImpL_pfc =>
    match type of D2' with
    | context [ Imp ?AA ?BB ] => bracket_set_up1_pre D2' BB; assoc_mid_loc [Imp AA BB]
    end
  end.
*)

Ltac bracket_set_up1_redo_twoprem D1 D2a' D2b' rl :=
  match rl with
  | WBox1Rs =>
    match type of D2b' with
    | context [ ([], [?AA], fwd) ] =>
      bracket_set_up1_pre_sndR D1 D2a' AA;
      assoc_mid_loc [WBox AA]
    end
  | BBox1Rs =>
    match type of D2b' with
    | context [ ([], [?AA], bac) ] =>
      bracket_set_up1_pre_sndR D1 D2a' AA;
      assoc_mid_loc [BBox AA]
    end
  | ImpL_pfc =>
    match type of D2b' with
    | context [ Imp ?AA ?BB ] =>
      bracket_set_up1_preR D1 D2b' AA;
      assoc_mid_loc [Imp AA BB]
    end
  end.

Ltac solve_case_F_gen_draft_setup D2 D2' :=
  list_assoc_r_arg_derrec2_spec D2 D2';
  list_assoc_r_single; list_assoc_l.

Ltac solve_case_F_gen_draft_finish D1 D2 D2' D3 HSR Hdp' :=
  econstructor; [ | econstructor];
  unfold nslcext || unfold nslclext ; simpl;
  list_assoc_r_single;
  bracket_set_up2 D1 D2';
  solve_HSR_except_D3 HSR D2 D3 Hdp';
  solve_D3_weakened D3.

Ltac bracket_set_up2_extra :=
  match goal with 
  | [ |- derrec ?rls ?prm (?G1 ++ ?G2 ++ ?G3)] => rewrite (app_assoc G1)
  end.

Ltac solve_case_F_gen_draft_finish' D1 D2 D2' D3 HSR Hdp' :=
  econstructor; [ | econstructor];
  unfold nslcext || unfold nslclext ; simpl;
  list_assoc_r_single;
  bracket_set_up2 D1 D2';
  bracket_set_up2_extra;
  solve_HSR_except_D3 HSR D2 D3 Hdp';
  solve_D3_weakened D3.

Ltac fill_tac_ImpR_pfc D2' rl :=
  eapply derI;
  [eapply prop;
   econstructor;
   list_assoc_r_single ;
   bracket_set_up1_redo D2' rl ;
   eapply Sctxt_eq   ;
   [eapply ImpR_pfc | reflexivity ..] | ].

Ltac fill_tac_WBox2Rs D2' rl :=
  eapply derI;
  [eapply b2r ;
   econstructor;
   list_assoc_r_single;
   bracket_set_up1_redo D2' rl;
   (*      assoc_mid_loc [WBox AA] ; *)
   simpl; eapply rl | ].

Ltac solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' rl fill_tac :=
  solve_case_F_gen_draft_setup D2 D2';
  fill_tac D2' rl;
  solve_case_F_gen_draft_finish D1 D2 D2' D3 HSR Hdp'.
  
Lemma Lemma_Sixteen_SR_wb_fwd_WBox2Ls : forall n m
(IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d); (L3 ++ WBox AA :: L4, L6, bac)] =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros n m IH V G γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
  Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  unfold nslclext in *.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  rename Heqconcl into Heqconcl'. 
  (* WBox not in last component because of structural equivalence. *)

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl'.
  inv_app_hd_tl_full.
  inv_app_hd_tl_full.
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  eapply partition_singleton_app in Heqconcl'. sD; subst.
  +{ (* WBox A in snd last component *)
      SR_wb_fwd_WBox2Ls_snd_last_comp D2 D3 AA A HSR Hdp'.
    }
  +{ (* WBox A not in snd last component *)
      SR_wb_fwd_WBox2Ls_not_snd_last_comp D2 D3 HSR Hdp'.
    }
   Unshelve. all : try solve [subst; solve_eqs].
Qed.


(* -------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_EW *)
(* -------------------------- *)

Lemma Lemma_Sixteen_SR_wb_fwd_EW : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d2
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, d2)]))
  ctxt L1 L2 d
  (Heqconcl : nslclext ctxt [(L1, L2, d)] = H ++ (Σ1 ++ WBox A :: Σ2, Π, d2) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False) 
          [nslclext ctxt []])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2) :: I).
Proof.
  intros.
  unfold nslclext in *.
  get_SR_wb_from_IH IH HSR (S n) (m - 1).
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


(* ------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_BBox2Ls *)
(* ------------------------------- *)
(*
TODO: 
  - find patterns in the "WBox A not in last component" cases as the proofs are all very similar.
  - clean up.
*)
Lemma Lemma_Sixteen_SR_wb_fwd_BBox2Ls : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d); (L3 ++ BBox AA :: L4, L6, fwd)] =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (size : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
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
      prep_apply_BBox2Ls;
      econstructor 2 | 
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
          econstructor. simpl. rewrite <- app_assoc. eapply BBox2Ls.

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
          rewrite (app_assoc Γ). eapply BBox2Ls.

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
          eapply BBox2Ls.

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
          rewrite (app_assoc Γ). eapply BBox2Ls.

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
(* Lemma_Sixteen_SR_wb_fwd_BBox2Rs *)
(* ------------------------------- *)

Ltac fill_tac_BBox2Rs D2' rl :=
  eapply derI;
  [eapply b2r ;
   econstructor;
   rewrite <- app_assoc;
   bracket_set_up1_redo D2' rl;
   (*      assoc_mid_loc [WBox AA] ; *)
   simpl; eapply rl | ].

(* Finished. General one premise rule. *)
Lemma Lemma_Sixteen_SR_wb_fwd_BBox2Rs : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  L1 L2 AA L3 ctxt
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  (Heqconcl : nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac)] =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.

  all : solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox2Rs fill_tac_BBox2Rs.
  Unshelve. all : (subst ; solve_eqs).
Qed.


(* ------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_BBox2Rs *)
(* ------------------------------- *)

  Ltac fill_tac_BBox1Ls D2' rl :=
      eapply derI;
      [eapply b1l ;
       rewrite <- app_assoc;
      econstructor;
      list_assoc_r_single;
      bracket_set_up1_redo D2' rl;
(*      assoc_mid_loc [WBox AA] ; *)
      simpl; eapply rl | ].

(* Case F): single premise, general. *)
Lemma Lemma_Sixteen_SR_wb_fwd_BBox1Ls : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  (V : Set)
  (G : list (list (PropF V) * list (PropF V) * dir))
  (Γ Δ1 Δ2 : list (PropF V))
  (H : list (list (PropF V) * list (PropF V) * dir))
  (Σ1 Σ2 Π : list (PropF V))
  (I GH : list (list (PropF V) * list (PropF V) * dir))
  (A : PropF V)
  (D1 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  (ctxt : list (rel (list (PropF V)) * dir))
  (AA : PropF V)
  (d : dir)
  (L1 L2 L3 L4 L5 L6 : list (PropF V))
  (Heqconcl : nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d); (L3 ++ L4, L6, bac)] =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s :  dersrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d); (L3 ++ AA :: L4, L6, bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.

  app_eq_app_dest3; try contradiction; try discriminate.

  all : solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_BBox1Ls.
  Unshelve. all : (subst ; solve_eqs).
Qed.


(* -------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_ImpR_pfc *)
(* -------------------------------- *)

(* Case F): single premise, general.
Finished but can be generalised. Notice patterns in proof. 
 *)

Lemma Lemma_Sixteen_SR_wb_fwd_ImpR_pfc : forall n m
  {V : Set} G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  ctxt d d2 Φ1 Φ2 Ψ1 Ψ2 AA BB
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
          (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, d2)]))
  (Heqconcl : nslcext ctxt d (Φ1 ++ Φ2, Ψ1 ++ Imp AA BB :: Ψ2) =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, d2) :: I)
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d (Φ1 ++ AA :: Φ2, Ψ1 ++ Imp AA BB :: BB :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (D3 : derrec (LNSKt_rules (V:=V))
                (fun _ : list (rel (list (PropF V)) * dir) => False)
                 (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2); ([], [A], fwd)]))
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2) :: I).
Proof.
  intros.
(*
  get_SR_wb_fwd_pre_from_IH IH HSRfwd (S n) (m - 1).
  get_SR_wb_bac_pre_from_IH IH HSRbac (S n) (m - 1).
*)
  get_SR_wb_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslcext in *.
  destruct d2;
  (destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full;              
    [app_eq_app_dest3; try contradiction; try discriminate | ]);
  solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' ImpR_pfc fill_tac_ImpR_pfc.
     Unshelve. all : (subst ; solve_eqs).
Qed.

(*
Lemma Lemma_Sixteen_SR_wb_fwd_ImpR_pfc : forall n m
  {V : Set} G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
          (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  (Heqconcl : nslcext ctxt d (Φ1 ++ Φ2, Ψ1 ++ Imp AA BB :: Ψ2) =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d (Φ1 ++ AA :: Φ2, Ψ1 ++ Imp AA BB :: BB :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (D3 : derrec (LNSKt_rules (V:=V))
                (fun _ : list (rel (list (PropF V)) * dir) => False)
                 (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslcext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.
              
  app_eq_app_dest3; try contradiction; try discriminate.
     all : solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' ImpR_pfc fill_tac_ImpR_pfc.
     Unshelve. all : (subst ; solve_eqs).
Qed.
*)

(* ------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_WBox2Rs *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_wb_fwd_WBox2Rs : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A ctxt
  (D1 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd)] = H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.
 
  app_eq_app_dest3; try contradiction; try discriminate.

  all : solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox2Rs fill_tac_WBox2Rs.
     Unshelve. all : (subst ; solve_eqs).
Qed.


(* ------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_WBox1Ls *)
(* ------------------------------- *)

Ltac fill_tac_WBox1Ls D2' rl :=
  eapply derI;
  [eapply b1l ;
   rewrite <- app_assoc;
   econstructor;
   list_assoc_r_single;
   bracket_set_up1_redo D2' rl;
   (*      assoc_mid_loc [WBox AA] ; *)
   simpl; eapply rl | ].

Ltac solve_case_F_gen_draft3 D1 D2 D2' D3 HSR Hdp' rl fill_tac :=
  solve_case_F_gen_draft_setup D2 D2';
  fill_tac D2' rl;
  solve_case_F_gen_draft_finish' D1 D2 D2' D3 HSR Hdp'.

(* 
Some cases are Case F): single premise, general.

Check whether cases aren't doubled up needlessly.

Old comment: cause of double ups is "repeat (app_eq_app_dest2; sD; subst)."
So check why it is giving more cases than necessary.
*)

Lemma Lemma_Sixteen_SR_wb_fwd_WBox1Ls : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  (V : Set)
  (G : list (list (PropF V) * list (PropF V) * dir))
  (Γ Δ1 Δ2 : list (PropF V))
  (H : list (list (PropF V) * list (PropF V) * dir))
  (Σ1 Σ2 Π : list (PropF V))
  (I GH : list (list (PropF V) * list (PropF V) * dir))
  (A : PropF V)
  (D1 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  (ctxt : list (rel (list (PropF V)) * dir))
  (AA : PropF V)
  (d : dir)
  (L1 L2 L3 L4 L5 L6 : list (PropF V))
  (Heqconcl : nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d); (L3 ++ L4, L6, fwd)] =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d); (L3 ++ AA :: L4, L6, fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
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
            solve_case_F_gen_draft3 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_WBox1Ls.
        } 
      ++{ 
      subst.
      eapply merge_app_struct_equiv_strR_explicit in Hme; [ | eassumption].
      sD; subst.

      solve_case_F_gen_draft3 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_WBox1Ls.
                }
    }
    
  +{ tac_cons_singleton_hyp Heqconcl.
     app_eq_app_dest3; try contradiction.

     ++{ (* WBox A somewhere to the left of the component containing principle WBox. *)
         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_WBox1Ls.
       } 
     ++{ (* WBox A in same component as principle WBox but to its right. *)
         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_WBox1Ls.
       }
     ++{ (* WBox A in same component as principle WBox but to its left. *)

         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_WBox1Ls.
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
         
         epose proof (@HSR_wb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D1 D2' D3  _ _ _ _ _ ) as D6.
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


(* ------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_WBox1Rs *)
(* ------------------------------- *)

Ltac solve_case_G_gen_draft_setup D2a D2a' D2b D2b' :=
  list_assoc_r_arg_derrec2_spec D2a D2a'; list_assoc_r_single; list_assoc_l;
  list_assoc_r_arg_derrec2_spec D2b D2b'; list_assoc_r_single; list_assoc_l;
  match goal with
  | [ |- derrec _ _ (?G ++ ?H) ] => rewrite <- (app_assoc _ _ H)
  | _ => idtac 70
  end.

Ltac solve_case_G_gen_draft_finish D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb' :=
  econstructor; [ | econstructor; [ | econstructor]];
  unfold nslcext || unfold nslclext ; simpl;
  list_assoc_r_single;
  bracket_set_up2 D1 D2b';
  [solve_HSR_except_D3 HSR D2a D3 Hdpa' |
   solve_HSR_except_D3 HSR D2b D3 Hdpb'];
  solve_D3_weakened D3.
   
Ltac fill_tac_case_G_b1r D1 D2a' D2b' rl :=
  eapply derI;
  [eapply b1r;
   econstructor;
   list_assoc_r_single;
   bracket_set_up1_redo_twoprem D1 D2a' D2b' rl;
   simpl;
   eapply rl | ].

(* TODO: remove the fill_tac input and call fill_tac_case_G_b1r directly for the box cases. *)
Ltac solve_case_G_gen_draft2 D1 D2a D2b D2a' D2b' D3 HSR Hdpa' Hdpb' rl fill_tac :=
  solve_case_G_gen_draft_setup D2a D2a' D2b D2b';
  fill_tac D1 D2a' D2b' rl;
  solve_case_G_gen_draft_finish D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.

(* TODO: prove; two premise general version. *)
Lemma Lemma_Sixteen_SR_wb_fwd_WBox1Rs : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d); (L2, L5 ++ WBox AA :: L6, bac)] =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
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
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3;
    solve_case_G_gen_draft2 D1 D2a D2b D2a' D2b' D3 HSR Hdpa' Hdpb' WBox1Rs fill_tac_case_G_b1r.
    Unshelve. all : ( subst; solve_eqs ).
Qed.

  
(* ------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_BBox1Rs *)
(* ------------------------------- *)

Ltac solve_HSR_except_D3' HSR D2 D3 Hdp' :=
  eapply HSR;
  [ | ((econstructor 2; eassumption) || (econstructor 1; eassumption)) |
    erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
    eapply Hdp' |
    |
    repeat (eassumption || merge_solve_primitive) |
    simpl; lia].

Ltac solve_case_G_gen_draft_finish'' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb' :=
  econstructor; [ | econstructor; [ | econstructor]];
  unfold nslcext || unfold nslclext ; simpl;
  list_assoc_r_single;
  bracket_set_up2 D1 D2b';
  bracket_set_up2_extra;
  [solve_HSR_except_D3' HSR D2a D3 Hdpa' |
   solve_HSR_except_D3' HSR D2b D3 Hdpb'];
  (solve_D3_weakened D3 || struct_equiv_str_solve_primitive).

Ltac solve_case_G_gen_draft_finish''' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb' :=
  econstructor; [ | econstructor; [ | econstructor]];
  unfold nslcext || unfold nslclext ; simpl;
  list_assoc_r_single;
  [solve_HSR_except_D3' HSR D2a D3 Hdpa' |
   solve_HSR_except_D3' HSR D2b D3 Hdpb'];
  (solve_D3_weakened D3 || struct_equiv_str_solve_primitive).

Lemma Lemma_Sixteen_SR_wb_fwd_BBox1Rs : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d); (L2, L5 ++ BBox AA :: L6, fwd)] =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
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
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3;
    [eapply merge_app_struct_equiv_strR_explicit in Hme; [ | eassumption];
     sD; subst | | ];
    list_assoc_r_single;
    solve_case_G_gen_draft_setup D2a D2a' D2b D2b';
    fill_tac_case_G_b1r D1 D2a' D2b' BBox1Rs;
    try  solve_case_G_gen_draft_finish''' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
      solve_case_G_gen_draft_finish'' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
      Unshelve. all : (subst; solve_eqs).
Qed.


(* -------------------------------- *)
(* Lemma_Sixteen_SR_wb_fwd_ImpL_pfc *)
(* -------------------------------- *)

(* TODO: clean up, generalise. *)



Lemma Lemma_Sixteen_SR_wb_fwd_ImpL_pfc : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d2
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, d2)]))
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, d2) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
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
  get_SR_wb_from_IH IH HSR (S n) (m - 1).
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

(*
Lemma Lemma_Sixteen_SR_wb_fwd_ImpL_pfc : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d (Φ1 ++ Imp AA BB :: BB :: Φ2, Ψ1 ++ Ψ2);
          nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ AA :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH.
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
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
*)
(*
Lemma Lemma_Sixteen_SR_wb_fwd_ImpL_pfc : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ1 ++ WBox A :: Δ2, fwd)]))
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ WBox A :: Σ2, Π, fwd) :: I)
  (D3 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], fwd)]))
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ1 Δ2)
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d (Φ1 ++ Imp AA BB :: BB :: Φ2, Ψ1 ++ Ψ2);
          nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ AA :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH.
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.

  unfold nslcext in *.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3; try contradiction; try discriminate.

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

  Unshelve.
  all : try solve [subst; solve_eqs].

  
  
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

  Unshelve.
  3:{ subst. solve_eqs. }

  assoc_mid_loc H1. rewrite <- (app_assoc Γ).
  rewrite (app_assoc _ H1).

    solve_HSR_except_D3' HSR D2b D3 Hdpb'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

  Unshelve.
  2:{ subst. solve_eqs. }



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

  Unshelve.
  2:{ subst. solve_eqs. }

    solve_HSR_except_D3' HSR D2b D3 Hdpb'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

  Unshelve.
  subst. solve_eqs.
Qed.
 *)


(* ----------------------- *)
(* Lemma_Sixteen_SR_wb_fwd *)
(* ----------------------- *)

Lemma Lemma_Sixteen_SR_wb_fwd : forall n m,
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SR_wb_fwd (S n, m).
Proof.
  intros n m IH. unfold SR_wb_fwd. unfold SR_wb_fwd_pre.
  intros until 0. intros D3 Hprinc Hdp Hstr Hme Hsize.
  eapply principal_WBR_fwd in Hprinc; [ | reflexivity].
  simpl in Hsize. apply le_S_n in Hsize.

  remember D2 as D2'.
  remember  (H ++ [(Σ1 ++ [WBox A] ++ Σ2, Π, fwd)] ++ I) as concl.
  destruct D2' as [|ps concl rl D2s]. contradiction.
  remember rl as rl'. 
  destruct rl' as [ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns ];
    remember Hns as Hns'.

  (* Box2Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA L1 L2 L3 | AA L1 L2 L3].
  (* WBox2Rs *)
  simpl in *. subst. eapply Lemma_Sixteen_SR_wb_fwd_WBox2Rs; eassumption.
  (* BBox2Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_wb_fwd_BBox2Rs; eassumption.

  
  (* Box1Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6].
  (* WBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_wb_fwd_WBox1Rs; eassumption.

  (* BBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_wb_fwd_BBox1Rs; eassumption.

  (* Box2Ls *)
  destruct Hns' as [ps c ctxt rl2];
    remember rl2 as rl2';
    destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6 ].
  (* WBox2Ls *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_wb_fwd_WBox2Ls; eassumption.
  simpl in *. subst.
  (* BBox2Ls *)
  eapply Lemma_Sixteen_SR_wb_fwd_BBox2Ls; eassumption.

  (* Box1Ls *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6 ].
    (* WBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_wb_fwd_WBox1Ls; eassumption.
   
    (* BBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_wb_fwd_BBox1Ls; eassumption.

  (* EW *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [L1 L2 d].
    (* EW_rule *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_wb_fwd_EW; eassumption.

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
    eapply Lemma_Sixteen_SR_wb_Id_pfc. eassumption.
 
    (* ImpR *)
    simpl in *. subst. 
    eapply Lemma_Sixteen_SR_wb_fwd_ImpR_pfc; eassumption. 

    (* ImpL *) simpl in *. subst.
    eapply Lemma_Sixteen_SR_wb_fwd_ImpL_pfc; eassumption.

    (* Bot  *) 
    simpl in *. subst.
    clear Hsize D3 Hme Hdp D2s Hprinc.
    clear D1 IH.
    eapply Lemma_Sixteen_SR_wb_BotL_pfc. eassumption.
Qed.

Print Assumptions  Lemma_Sixteen_SR_wb_fwd.
