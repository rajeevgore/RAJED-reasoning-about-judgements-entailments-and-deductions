Section defining_defn.
  
Axiom V : Set.

Definition defn (a : V) :=  a = a.

Print defn.

End defining_defn.

Print defn.
Print Assumptions defn.

Lemma lem : forall (n : nat), defn n.
Definition defn2 := forall (V2 : Set) (a : V2), a = a.
Print defn2.









(*
Lemma_Sixteen_SR_wb_fwd_BBox2Rs
        eapply derI;
      [eapply b2r ;
       econstructor;
       rewrite <- app_assoc |].
        bracket_set_up1_redo D2' BBox2Rs.
        simpl; eapply BBox2Rs.
(*      assoc_mid_loc [WBox AA] ; *)
      simpl; eapply BBox2Rs | ].
    fill_tac_BBox2Rs D2' rl.
   solve_case_F_gen_draft_finish D2 D2' D3 HSR Hdp'.

  all : solve_case_F_gen_draft2 D2 D2' D3 HSR Hdp' BBox2Rs fill_tac_BBox1Ls.

  
  list_assoc_l.
  eapply derI.
  eapply b2r.  econstructor.
  rewrite <- app_assoc. simpl. econstructor 2.

  econstructor; [ | econstructor].
  unfold nslclext. list_assoc_r_single.
  solve_HSR HSR D2 D3 Hdp'.
  Unshelve. solve_eqs.
Qed.
 *)

(*
Lemma_Sixteen_SR_wb_fwd_BBox1Ls
  solve_case_F_gen_draft_setup D2 D2'.
  fill_tac_BBox1Ls D2' BBox1Ls.
       solve_case_F_gen_draft_finish D2 D2' D3 HSR Hdp'.
  Unshelve. 2 : subst; solve_eqs.

  

  econstructor; [  | econstructor ]; unfold nslcext || unfold nslclext; simpl;
   list_assoc_r_single; bracket_set_up2 D2'; solve_HSR_except_D3 HSR D2 D3 Hdp';
   solve_D3_weakened D3.


  
  econstructor; [  | econstructor ].
  unfold nslcext || unfold nslclext; simpl.
  list_assoc_r_single.
  bracket_set_up2 D2'.

    match type of D2' with
  | derrec ?rules ?prems ?H => 
      match get_snd_last_app H with
      | [(?L1, ?L2, ?d)] => idtac L1 L2 d (*tac_match L1 [WBox A]*)
      end
  end.
   bracket_set_up1_pre_snd D2' (WBox A).
              repeat rewrite <- (app_assoc Γ).
  
  solve_HSR_except_D3 HSR D2 D3 Hdp'.

 match type of D2' with
         | context [ [WBox ?A] ] =>
             idtac 12; bracket_set_up1_pre D2' (WBox A);
              repeat rewrite <- (app_assoc Γ)
         end.
  
  solve_HSR_except_D3 HSR D2 D3 Hdp'.
  Unshelve.
   solve_D3_weakened D3.
  
       solve_case_F_gen_draft_finish D2 D2' D3 HSR Hdp'.
  Unshelve. 2 : subst; solve_eqs.

  (solve_case_F_gen_draft_setup D2 D2';
       fill_tac_BBox1Ls D2' BBox1Ls;
       solve_case_F_gen_draft_finish D2 D2' D3 HSR Hdp').
  Unshelve. 2 : subst; solve_eqs.
    solve_case_F_gen_draft_setup D2 D2';
                fill_tac_BBox1Ls D2' BBox1Ls;
          solve_case_F_gen_draft_finish D2 D2' D3 HSR Hdp'.

      solve_case_F_gen_draft_setup D2 D2';
                fill_tac_BBox1Ls D2' BBox1Ls;
          solve_case_F_gen_draft_finish D2 D2' D3 HSR Hdp'.

      eapply derI.
      eapply b1l.
      rewrite <- app_assoc.
      econstructor.
      list_assoc_r_single.
      bracket_set_up1_redo D2' BBox1Ls.
(*      assoc_mid_loc [WBox AA] ; *)
      simpl; eapply BBox1Ls. 
          solve_case_F_gen_draft_finish D2 D2' D3 HSR Hdp'.
  eapply derI;
   [ eapply b1l; econstructor; list_assoc_r_single; bracket_set_up1_redo D2' rl;
      simpl; eapply BBox1Ls
   |  ]

          
          Unshelve. 3: (subst; solve_eqs).
            fill_tac_BBox1Ls D2' BBox1Ls;
          solve_case_F_gen_draft_finish D2 D2' D3 HSR Hdp'.

solve_case_F_gen_draft2 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_BBox1Ls.


  
  +{ list_assoc_l.
  rewrite <- app_assoc.
  eapply derI.
  eapply b1l.
  econstructor.
  list_assoc_r_single. simpl. econstructor.
  econstructor; [ | econstructor].
  unfold nslclext. list_assoc_r_single.
  solve_HSR HSR D2 D3 Hdp'.
   }
  +{
      list_assoc_r_single_arg D3.
      simpl.
      list_assoc_r_single.
      eapply derI.
      eapply b1l.
      econstructor.
      assoc_mid [BBox AA]. simpl.
      econstructor.
      econstructor; [ | econstructor].
      unfold nslclext. list_assoc_r_single.
      rewrite (app_assoc L1).
      rewrite (app_assoc (L1 ++ _)).
      solve_HSR HSR D2 D3 Hdp'.
    }    
  +{
      list_assoc_r_single_arg D3.
      simpl.
      list_assoc_r_single.
      eapply derI.
      eapply b1l.
      econstructor.
      assoc_mid [BBox AA]. simpl.
      econstructor.
      econstructor; [ | econstructor].
      unfold nslclext. list_assoc_r_single.
      solve_HSR HSR D2 D3 Hdp'.
    }
    Unshelve. all :  solve_eqs.
Qed.
 *)

  (* Lemma_Sixteen_SR_wb_fwd_ImpR_pfc

      list_assoc_r_arg_derrec2_spec D2 D2';
      list_assoc_r_single; list_assoc_l;
      eapply derI;
      [eapply prop;
      econstructor;
      list_assoc_r_single ;
      bracket_set_up1_redo D2' ImpR_pfc ;
      eapply Sctxt_eq   ;
      [eapply ImpR_pfc | reflexivity ..] | ];
      econstructor; [ | econstructor];
      unfold nslcext; simpl;
      list_assoc_r_single;
      bracket_set_up2 D2';
      solve_HSR_except_D3 HSR D2 D3 Hdp';
      solve_D3_weakened D3.
   *)













(* ------------------------------------------------------------------- *)
(* ------------ *)
(* GENERAL DUMP *)
(* ------------ *)
(* ------------------------------------------------------------------- *)

(*
Ltac clear_useless :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         | [H : [?a] = [?a] |- _] => clear H
         | [H : ?a :: ?b = ?a :: ?b |- _] => clear H
         | [H1 : ?a, H2 : ?a |- _] => clear H2
         end.

Ltac inversion_cons :=
  repeat match goal with
         | [ H : ?a :: ?l1 = ?b :: ?l2 |- _] => inversion H; subst; clear_useless
         end.
*)

(*
      Ltac solve_case_G_gen_draft_setup' D2a D2a' D2b D2b' :=
  list_assoc_r_arg_derrec2_spec D2a D2a'; list_assoc_r_single; list_assoc_l;
  list_assoc_r_arg_derrec2_spec D2b D2b'; list_assoc_r_single; list_assoc_l.
  *)    

(*
            Ltac solve_case_G_gen_draft_finish' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb' :=
      econstructor; [ | econstructor; [ | econstructor]];
      unfold nslcext || unfold nslclext ; simpl;
      list_assoc_r_single;
      bracket_set_up2 D1 D2b';
      bracket_set_up2_extra;
      [solve_HSR_except_D3 HSR D2a D3 Hdpa' |
       solve_HSR_except_D3 HSR D2b D3 Hdpb'];
      solve_D3_weakened D3.
*)


      (*
      Ltac solve_case_G_gen_draft3 D1 D2a D2b D2a' D2b' D3 HSR Hdpa' Hdpb' rl fill_tac :=
        solve_case_G_gen_draft_setup D2a D2a' D2b D2b';
        fill_tac D1 D2a' D2b' rl;
        solve_case_G_gen_draft_finish' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
*)

  (*
        Ltac solve_case_F_gen_draft_finish'' D1 D2 D2' D3 HSR Hdp' :=
      econstructor; [ | econstructor];
      unfold nslcext || unfold nslclext ; simpl;
      list_assoc_r_single;
      bracket_set_up2 D1 D2';
      bracket_set_up2_extra;
      solve_HSR_except_D3 HSR D2 D3 Hdp';
      solve_D3_weakened D3.

        Ltac solve_case_F_gen_draft_finish''' D1 D2 D2' D3 HSR Hdp' :=
      econstructor; [ | econstructor];
      unfold nslcext || unfold nslclext ; simpl;
      list_assoc_r_single;
      bracket_set_up2 D1 D2';
      bracket_set_up2_extra;
      solve_HSR_except_D3 HSR D2 D3 Hdp';
      solve_D3_weakened D3.
   *)

(*
Ltac list_assoc_r_arg_derrec  D2 AA :=
  match goal with
  | [ D2 : derrec ?rules ?prems ?concl |- _ ] =>
    let t := fresh in let Heqt := fresh in
                      remember concl as t eqn: Heqt; list_assoc_r_arg Heqt; simpl in Heqt;
                      tac_cons_singleton_hyp Heqt;
                      let D2' := fresh D2 in
                      pose (get_D _ _ _ _ D2 Heqt) as D2'
  end.
*)


(*
Lemma nslclrule_b2lrules : forall V ps L L' seq1 seq2,
    L = L' ->
    b2lrules ps ([seq1;seq2]) ->
    nslclrule (b2lrules (V := V)) (map (nslclext L') ps) ((L ++ [seq1]) ++ [seq2]).
Proof.
  intros.
  list_assoc_r. subst. simpl. econstructor.
  assumption.
Qed.
 *)

(*
Ltac solve_HSR2 HSR D2 D3 Hdp' :=
  eapply HSR;
  [eapply D3 | econstructor 2; eassumption |
   erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
   eapply Hdp' |
   eassumption |
   eassumption |
   simpl; lia].
 *)

(*
Ltac bracket_D2_AA' D2'' AA :=
  match goal with
  | [ D2'' : derrec ?rules ?prems (?H ++ [(?l1,?l2,?d)]) |-
      seqrule ?C ?ps (?L1,?L2)  ] => tac_match l1 AA
  end.
 *)

(*
Ltac bracket_set_up1 D2' :=
  match type of D2' with
  | context [ [Imp ?AA ?BB] ] => bracket_set_up1_pre D2' AA; assoc_mid_loc [Imp AA BB]
  end.
 *)

(*
      Ltac bracket_set_up1_snd D2' :=
  match type of D2' with
  | context [ [Imp ?AA ?BB] ] => bracket_set_up1_pre_snd D2' AA; assoc_mid_loc [Imp AA BB]
  end.
*)
(*
            Ltac bracket_set_up1_sndR D2' :=
  match type of D2' with
  | context [ [Imp ?AA ?BB] ] => bracket_set_up1_pre_sndR D2' AA; assoc_mid_loc [Imp AA BB]
  end.
*)

(*
Ltac bracket_set_up2' D2' :=
  match goal with
  | [ |- derrec _ _ (?H ++ [(?Γ ++ _, _, _)]) ] =>
    idtac 5; bracket_set_up2_pre D2'; repeat rewrite <- (app_assoc Γ)
  | [ |- derrec _ _ (?H ++ [(?Γ ++ _, _, _)] ++ _) ] =>
    idtac 10; bracket_set_up2_pre_snd D2'; repeat rewrite <- (app_assoc Γ)
  | _ => idtac 555
  end.


Ltac list_assoc_r_arg_derrec2  D2 :=
  match goal with
  | [ D2 : derrec ?rules ?prems ?concl |- _ ] =>
    let t := fresh in let Heqt := fresh in
                      remember concl as t eqn: Heqt; list_assoc_r_arg Heqt; simpl in Heqt;
                      tac_cons_singleton_hyp Heqt;
                      let D2' := fresh D2 in
                      pose (get_D D2 Heqt) as D2'
  end.
*)

        (*
      Ltac solve_case_F_gen_draft D2 D2' D3 HSR Hdp' :=
      list_assoc_r_arg_derrec2_spec D2 D2';
      list_assoc_r_single; list_assoc_l;
      eapply derI;
      [eapply prop;
      econstructor;
      list_assoc_r_single ;
      bracket_set_up1 D2' ;
      eapply Sctxt_eq   ;
      [eapply ImpR_pfc | reflexivity ..] | ];
      econstructor; [ | econstructor];
      unfold nslcext; simpl;
      list_assoc_r_single;
      bracket_set_up2 D2';
      solve_HSR_except_D3 HSR D2 D3 Hdp';
      solve_D3_weakened D3.
*)



(* ------------------- *)

(*
(* 
Left it here 28/02/2020
Figure out how to branch and backtrack with ltac. *)
Lemma lem : forall (a b c d e : nat),
    (a = 1) :: (b = 2) :: [(a = 4)] = ((b = 3) :: [(a = c)]) ++ ((c = b) :: [(a = 8)]) -> False.
Proof.
  intros a b c d e H.
  inv_app_hd_tl.  
Admitted.

*)
(*
            Ltac bracket_set_up2_pre_snd D2' :=
        match goal with
        | [ |- context [ WBox ?A ] ] => idtac 21;
            match type of D2' with
            | context [ [WBox A] ] => idtac 22; fail
            | context [ [WBox ?B] ] => idtac 23; bracket_set_up1_pre_snd D2' (WBox B)
            end
        | _ => idtac 24;
            match type of D2' with
            | context [ [WBox ?B] ] => idtac 25; bracket_set_up1_pre_snd D2' (WBox B)
            end
        end.
*)
      (*
               
        match type of D2' with
        | context [ [WBox ?A] ] => idtac 6;
                                   match goal with
                                   | [ |- context [ WBox A ] ] => idtac 7; fail
                                   | _ => idtac 8; bracket_set_up1_pre D2' (WBox A);
                                          repeat rewrite <- (app_assoc Γ)
                                   end
        end.
       *)

            (*
Ltac bracket_set_up2 D2' :=
  match goal with
  | [ |- derrec _ _ (?H ++ [(?Γ ++ _, _, _)]) ] => idtac 5;
    match type of D2' with
    | context [ [WBox ?A] ] => idtac 6;
                               bracket_set_up1_pre D2' (WBox A);
                               repeat rewrite <- (app_assoc Γ)
    end
  | [ |- derrec _ _ (?H ++ [(?Γ ++ _, _, _)] ++ _) ] => idtac 10;
    match type of D2' with
    | context [ [WBox ?A] ] => idtac 12; bracket_set_up1_pre_snd D2' (WBox A);
                               repeat rewrite <- (app_assoc Γ)
    end
  | _ => idtac 555
  end.
*)
(*
Ltac bracket_set_up2 D2' :=
  match goal with
  | [ |- derrec _ _ (?H ++ [(?Γ ++ _, _, _)]) ] =>
    match type of D2' with
    | context [ [WBox ?A] ] => bracket_set_up1_pre D2' (WBox A);
                               repeat rewrite <- (app_assoc Γ)
    end
  | [ |- derrec _ _ (?H ++ [(?Γ ++ _, _, _)] ++ _) ] => idtac 10
  end.
 *)



        (*        match type of D2' with
        | context [WBox ?AA] =>
          lazymatch AA with
          | A => fail
          | _ => bracket_set_up1_pre D2' (WBox AA)
          end
        end
*)

        (*
      | _ =>
        match type of D2' with
        | context [WBox ?AA] => assoc_mid_loc [WBox AA]
        | _ => idtac 123
        end
      end
*)

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
      | context [BBox ?AA] => assoc_mid_loc [BBox AA]
      end
    | BBox2Rs => idtac 678
    | WBox1Ls =>
      match type of D2' with
      | context [WBox ?AA] => assoc_mid_loc [WBox AA]
      | _ => idtac 123
      end
    end.
  *)
  
(*      match type of D2' with
      | context [BBox ?AA] => assoc_mid_loc [BBox AA]
      end
*)
        (*
        match type of D2' with
        | context [WBox AA] => fail
        | context [WBox ?A] => 
          bracket_set_up1_pre_WB2R D2' [WBox A];
        end
*)

(*      eapply merge_step; [reflexivity | reflexivity | reflexivity | eapply merge_nilL; reflexivity | reflexivity | reflexivity | reflexivity] *)

(*
           repeat match goal with
   | [H:merge ?H1 ?H2 ?H3, Hstr : struct_equiv_str ?H1 ?H2
     |- merge (?H1 ++ ?G1) (?H2 ++ ?G2) (?H3 ++ ?G3)] => eapply (merge_app (structu_equiv_str_length _ _ Hstr) H)
   | [H:merge ?H1 ?H2 ?H3 |- merge (?H1 ++ ?G1) (?H2 ++ ?G2) (?H3 ++ ?G3) ] => eapply (merge_app _ H)
   | [ |- merge [(?L1, ?L2, ?d)] [(?M1, ?M2, ?d)] [(?L1 ++ ?M1, ?L2 ++ ?M2, ?d)] ] =>
         eapply merge_step;
          [ reflexivity
          | reflexivity
          | reflexivity
          | eapply merge_nilL; reflexivity
          | reflexivity
          | reflexivity
          | reflexivity ]
   end.

*)

(*
Ltac exact_hyp_brack_nested ns1 ns2 :=
  match ns1 with
  | ?L1 ++ ?L2 =>
    match ns2 with
    | ?L1 ++ ?L3 => exact_hyp_brack_nested L2 L3
    | ?L3 ++ ?L4 => exact_hyp_brack_seq L1 L3; exact_hyp_brack_nested L2 L4
    end
      
  
Ltac solve_exact_hyp_brack D3 :=
  match goal with
  | [D3 : derrec ?rules ?prems ?ns |- derrec ?rules ?prems ?ns2 ] =>
    exact_hyp_nested_brack ns ns2
                    end; exact D3.
 *)

(* False!
Lemma derrec_height_same : forall {T : Type} {rules prems} (l1 l2 : list T)
     (D1 : derrec rules prems l1)
     (D2 : derrec rules prems l2),
    l1 = l2 ->
    derrec_height D1 = derrec_height D2.
Admitted.
*)

  (*
Lemma dp_same_dec_ass : forall {T : Type} {rules prems} (l1 l2 : list T)
                    (deq : forall x y : list T, {x = y} + {x <> y})
     (D1 : derrec rules prems l1)
    (Heq : l1 = l2),
    dp D1 = dp (eq_rect _ (fun l => derrec rules prems l) D1 l2 Heq).
Proof.
  intros until 0. intros deq D1 Heq.
  subst.
  erewrite <- Eqdep_dec.eq_rect_eq_dec.
  reflexivity.
  assumption.
Qed.
*)

(* Left it here 14/02/2020.
Problem: current cut elimination proof uses eq_rect_eq axiom. This is consistent with CIC (see documentation on the logic of Coq), and should be fine for extraction (Coq doesn't complain at extraction time that we need to realize that axiom). We surely can replace this by eq_rect_eq_dec for decidable equalities, which probably depends on decidability of V. Talk with Raj or Jeremy to see whether decidability of V is a reasonable constraint.

I don't know where the occurrence of eq_rec_eq axiom is, but it seems to be used in contexts where e.g. dp D1 = dp (eq_rect  _ _ _ _ _ ... D1). 

See if I can find where it comes up.
*)


(* Proof doesn't go through for the case where WBox A is on the end, and the 
AA formula goes to the right of the WBox A and so the IH doesn't apply on the
premise 
WBox A, AA => AA -> BB, BB
because WBox A isn't on the far right.
Ammend this by putting a context on the right of WBox A so that it doesn't
have to be on the end.
 *)

(*
Lemma Lemma_Sixteen_SR_wb_fwd_ImpR_pfc_old : forall n m
  {V : Set} G Γ Δ H Σ Π I GH A
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  (D1 : derrec (LNSKt_rules (V:=V))
         (fun _ : list (rel (list (PropF V)) * dir) => False)
         (G ++ [(Γ, Δ ++ [WBox A], fwd)])) 
  (Heqconcl : nslcext ctxt d (Φ1 ++ Φ2, Ψ1 ++ Imp AA BB :: Ψ2) =
             H ++ (Σ ++ [WBox A], Π, fwd) :: I)
  (Hprinc : principal_WBox2Rs D1 (WBox A) Γ Δ [])
  (D2s : dersrec (LNSKt_rules (V:=V))
          (fun _ : list (rel (list (PropF V)) * dir) => False)
          [nslcext ctxt d (Φ1 ++ AA :: Φ2, Ψ1 ++ Imp AA BB :: BB :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hme : merge G H GH)
  (Hex : existsT2
          _ : derrec (LNSKt_rules (V:=V))
                (fun _ : list (rel (list (PropF V)) * dir) => False)
                (GH ++ [(Γ ++ Σ, Δ ++ Π, fwd); ([], [A], fwd)]), True)
  (Hsize : fsize A <= n),
  derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
         (GH ++ (Γ ++ Σ, Δ ++ Π, fwd) :: I).
Proof.
Admitted.
*)




(*
  destruct (dersrec_derrec_dp _ D2 eq_refl) as [D1' Hdp1'].
  assert (S (dp D1' + S (dersrec_height D2s)) <= m) as Hass.
  rewrite Hdp1'. assumption.

  clear Hprinc rl Hdp Hdp1' D2.
  inversion D2. subst.
  eapply dersrec_derrec_dp in D2.
  SearchAbout dp.
  eapply dersrec_singleD in D2.
  
SearchAbout dersrec nil.
  SearchAbout  (?l1 ++ [?a] = ?l2 ++ [?b]).

  SearchAbout principal_WBox2Rs.

Admitted.
 *)

(*
Definition get_dpD {X} rules prems G H D pf :=
  (let (D',HD') := ((fun (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (G H : X) (D1 : derrec rules prems G) (H0 : G = H) =>
eq_rect_r
  (fun G0 : X =>
   forall D2 : derrec rules prems G0,
   existsT2 D3 : derrec rules prems H, dp D2 = dp D3)
  (fun D2 : derrec rules prems H =>
     existT (fun D3 : derrec rules prems H => dp D2 = dp D3) D2 eq_refl) H0 D1)
              X rules prems
              G H D pf) in
   (match (fun (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (G H : X) (D1 : derrec rules prems G) (H0 : G = H) =>
eq_rect_r
  (fun G0 : X =>
   forall D2 : derrec rules prems G0,
   existsT2 D3 : derrec rules prems H, dp D2 = dp D3)
  (fun D2 : derrec rules prems H =>
     existT (fun D3 : derrec rules prems H => dp D2 = dp D3) D2 eq_refl) H0 D1)
              X rules prems
              G H D pf return dp D = dp D' with _ => HD' end)).

   HD').
              as _ return 
dp D = dp



Definition get_dpD {X} rules prems G H D pf :=
  (match (fun (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (G H : X) (D1 : derrec rules prems G) (H0 : G = H) =>
eq_rect_r
  (fun G0 : X =>
   forall D2 : derrec rules prems G0,
   existsT2 D3 : derrec rules prems H, dp D2 = dp D3)
  (fun D2 : derrec rules prems H =>
     existT (fun D3 : derrec rules prems H => dp D2 = dp D3) D2 eq_refl) H0 D1)
              X rules prems
              G H D pf
              as y in _  return _




Definition get_dpD {X} rules prems G H D pf :=
  (match (fun (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (G H : X) (D1 : derrec rules prems G) (H0 : G = H) =>
eq_rect_r
  (fun G0 : X =>
   forall D2 : derrec rules prems G0,
   existsT2 D3 : derrec rules prems H, dp D2 = dp D3)
  (fun D2 : derrec rules prems H =>
     existT (fun D3 : derrec rules prems H => dp D2 = dp D3) D2 eq_refl) H0 D1)
              X rules prems
              G H D pf
              as _ return 
dp D = dp
         (match (fun (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (G H : X) (D1 : derrec rules prems G) (H0 : G = H) =>
eq_rect_r
  (fun G0 : X =>
   forall D2 : derrec rules prems G0,
   existsT2 D3 : derrec rules prems H, dp D2 = dp D3)
  (fun D2 : derrec rules prems H =>
     existT (fun D3 : derrec rules prems H => dp D2 = dp D3) D2 eq_refl) H0 D1)
              X rules prems
              G H D pf
              as _ return _
          with existT _ D' HD' => D' end) with
     | existT _ _ HD'' => HD'' end).

      HD' end).

       return True in HD').

  in True). (@LNSKt_rules V))in True).
 *)
  (*
Lemma partition_cons_ns_seqL : forall {T1 T2 T3 : Type} G H I J
    (Γ1 Γ2 : list T1) (Δ : list T2) Σ1 Σ2 Π A B (d1 d2 : T3),
    G ++ [(Γ1 ++ [A] ++ Γ2, Δ, d1)] ++ H =
    I ++ [(Σ1 ++ [B] ++ Σ2, Π, d2)] ++ J ->
    ((G = I) * (H = J) * (Γ1 = Σ1) * (Γ2 = Σ2) * (A = B) * (Δ = Π) * (d1 = d2)).
(*
    +
    ((G = I) * (H = J) *
     (existsT2 Ξ, (I = G ++ [(Γ1 ++ [A] ++ Γ2, Δ, d1)] ++ Ξ) *
                  ()
                  
                  (Γ1 = Σ1) * (Γ2 = Σ2) * (A = B) * (Δ = Π) * (d1 = d2)) +
*)
Admitted.
   *)


(*   
  eapply derI;
    [ eapply b1r; econstructor; list_assoc_r_single | ].
bracket_set_up1_redo_twoprem D2a' D2b' WBox1Rs.
  simpl. eapply WBox1Rs.
  simpl.
  econstructor.
  unfold nslclext.
  bracket_set_up1_pre_sndR D1 D2a' AA.



      fill_tac_case_G_b1r D2a' D2b' WBox1Rs.
      solve_case_G_gen_draft_finish D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
*)
   (*
  eapply derI;
    [ eapply b1r; econstructor; list_assoc_r_single | ].

bracket_set_up1_pre_sndR D2a' AA.
  match WBox1Rs with
  | WBox1Rs =>
      match type of D2b' with
      | context [ ([], [?AA], fwd) ] => idtac 4 ;
          bracket_set_up1_pre_snd D2a' AA; assoc_mid_loc [WBox AA]
      end
  | BBox1Rs =>
      match type of D2b' with
      | context [ ([], [?AA], fwd) ] => assoc_mid_loc [BBox AA]
      end
  | ImpL_pfc =>
      match type of D2b' with
      | context [ Imp ?AA ?BB ] => assoc_mid_loc [Imp AA BB]
      end
  end.
  
      bracket_set_up1_redo_twoprem D2a' D2b' WBox1Rs. ; simpl; 
      eapply rl
   |  ].

      
      fill_tac_case_G_b1r D2a' D2b' WBox1Rs.
(*
      econstructor.
      unfold nslclext. list_assoc_r_single.
      bracket_set_up2 D1 D2b'.
      eapply HSR.
      *)
      solve_case_G_gen_draft_finish D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
   }

  +{  solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.
  eapply derI;
    [ eapply b1r; econstructor; list_assoc_r_single | ].
  rewrite (app_assoc _ L3).
  bracket_set_up1_pre_sndR D2a' [AA].  (L3 ++ [AA] ++ L4) [AA].
      bracket_set_up1_redo_twoprem D2a' D2b' WBox1Rs.  simpl; 
      eapply rl
   |  ]
      
      fill_tac_case_G_b1r D2a' D2b' WBox1Rs.

 econstructor; [  | econstructor; [  | econstructor ] ].
   unfold nslcext || unfold nslclext; simpl; list_assoc_r_single;
   bracket_set_up2 D1 D2b'.
   [ solve_HSR_except_D3 HSR D2a D3 Hdpa' | solve_HSR_except_D3 HSR D2b D3 Hdpb' ];
   solve_D3_weakened D3.
      
      solve_case_G_gen_draft_finish D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
   }
      Unshelve. all : ( subst; solve_eqs ).
      eapply derI.
      eapply b1r.
      econstructor.
      list_assoc_r_single.
      bracket_set_up1_redo_twoprem D2b' WBox1Rs.
        [eapply b1r;
  econstructor;
(*  list_assoc_r_single; *)
  bracket_set_up1_redo_twoprem D2b' WBox1Rs;
  simpl;
  eapply WBox1Rs | ].      
      fill_tac_case_G_b1r D2b' WBox1Rs.

      econstructor; [ | econstructor; [ | econstructor]].
      unfold nslcext || unfold nslclext ; simpl;
      list_assoc_r_single.
      bracket_set_up2 D1 D2b'.

      unfold SR_wb_fwd in HSR.
      unfold SR_wb_fwd_pre in HSR.
      eapply HSR.
      admit.
      econstructor 2. eassumption.
   [ 
   | econstructor 2
   | erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa'
   | eassumption
   | eassumption || merge_solve_primitive
   | simpl; lia ].

      
      solve_HSR_except_D3 HSR D2a D3 Hdpa'.
      [solve_HSR_except_D3 HSR D2a D3 Hdpa' |
       solve_HSR_except_D3 HSR D2b D3 Hdpb'];
       solve_D3_weakened D3.


      solve_case_G_gen_draft_finish D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
   }  econstructor; [  | econstructor; [ | econstructor] ];
    unfold nslcext || unfold nslclext; simpl;
      list_assoc_r_single.

  
  bracket_set_up2 D1 D2a'.
  solve_HSR_except_D3 HSR D2a D3 Hdpa'. 
   solve_D3_weakened D3.

  bracket_set_up2 D1 D2b'.
  solve_HSR_except_D3 HSR D2b D3 Hdpb'. 
  solve_D3_weakened D3.
  
  }
  Unshelve.
 all : (subst;  solve_eqs).


 
  eapply HSR;
    [ 
   | econstructor 2; eassumption
   | erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa'
   | eassumption
   | eassumption || merge_solve_primitive
   | simpl; lia ].
  
  solve_HSR_except_D3 HSR D2 D3 Hdp';
   solve_D3_weakened D3


  
  inv_app_hd_tl_full.

solve_case_F_gen_draft_setup D2 D2'.

  solve_case_F_gen_draft_setup D2 D2'; fill_tac D2' rl;
   solve_case_F_gen_draft_finish D1 D2 D2' D3 HSR Hdp'
  *)
  
  (*
  match goal with
  | [ H : dp ?D1 + S (dersrec_height D2s) <= ?m |- _ ] =>
    assert (dp D1 + (S (dp D2a)) <= m) as Hdpa'';
    [rewrite HdpD2; assumption | ];
    assert (dp D1 + dp D2 <= m - 1) as Hdp';
    [lia | ]; clear HdpD2 D2s Hdp
  end.

  assert (dersrec_height D2s = dersrec_height D2s) as Heq.
  reflexivity.
  destruct (dersrec_derrec2_dp D2s Heq) as [D2a [D2b HdpD2]].
  remember (dersrec_height D2s) as b.  



  epose  (Max.le_max_r _ _).
  epose  (Max.le_max_l _ _).
  rewrite <- HdpD2 in l.
  rewrite <- HdpD2 in l0.

  assert (dp D1 + (S (dp D2a)) <= m) as Hdpa''.

  rewrite <- HdpD2 in H0.
  rewrite <- HdpD2 in H1.
  assert (dp D1 + (S (dp D2a)) <= m) as Hdpa''.
  clear -Hdp H1.
  remember (dp D1) as a.
  remember (dersrec_height D2s) as b.
  rewrite <- Heqb in H1.
lia.
  Lemma lemlem : forall a b c d,
      a + (S b) <= c ->
      d <= b ->
      a + (S d) <= c.
  Proof.
    intros. lia.
  lia.
SearchAbout max.  
  match goal with
  | [ H : dp ?D1 + S (dersrec_height D2s) <= ?m |- _ ] =>
    assert (dp D1 + (S (dp D2a)) <= m) as Hdpa'';
    [rewrite HdpD2; assumption | ];
    assert (dp D1 + dp D2 <= m - 1) as Hdp';
    [lia | ]; clear HdpD2 D2s Hdp
  end.

    
Ltac tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdp'' Hdp' HeqD2s :=  
  destruct (dersrec_derrec2_dp D2s eq_refl) as [D2a [D2b HdpD2]];
  match goal with
  | [ H : dp ?D1 + S (dersrec_height D2s) <= ?m |- _ ] =>
    assert (dp D1 + (S (dp D2)) <= m) as Hdp'';
    [rewrite HdpD2; assumption | ];
    assert (dp D1 + dp D2 <= m - 1) as Hdp';
    [lia | ]; clear HdpD2 D2s Hdp
  end.


  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_lem4 I) as [ | Hl2]; sD; subst; simpl in Heqconcl.
*)
  (*
  intros.
  get_SR_wb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_lem4 I); sD; subst;
  inv_app_hd_tl_full.

  list_assoc_l.
  eapply derI.
  eapply b2r.  econstructor.
  rewrite <- app_assoc. simpl. econstructor 2.

  econstructor; [ | econstructor].
  unfold nslclext. list_assoc_r_single.
  solve_HSR HSR D2 D3 Hdp'.
  Unshelve. solve_eqs. 
   *)

(*
    Ltac solve_derrec_weak_arg D3 :=
  eapply derrec_weakened_nseq; [ | eapply D3];
  list_assoc_r_single;
  weakened_nseq_solve.

 *)

(* Left it here 21/02/2020. Try proving same lemma but include hypothesis that WB2L was the last rule applied in D. *)
(* Problem: need decidability of V to decide whether Σ = Γ or not, for some Σ,Γ. 
Lemma lemlem : forall {V : Set} {G} D A I J Φ1 Φ2 Ξ d
                      (Hwf: np_WB2Ls_wf D A I J Φ1 Φ2 Ξ d)
    (Hex : existsT2 A2 Γ12 Γ22 Δ2 Σ12 Σ22 Π, principal_WBox2Ls D A2 Γ12 Γ22 Δ2 Σ12 Σ22 Π),
  (not_principal_WBox2Ls D A I J Φ1 Φ2 Ξ d) +
  (@not_principal_WBox2Ls V (@LNSKt_rules V) (fun _ => False) G D A I J Φ1 Φ2 Ξ d -> empty).
Proof.
  intros.
  destruct Hex as [A2 [Γ12 [Γ22 [Δ2 [Σ12 [Σ22 [Π Hex]]]]]]].
  inversion Hex. subst.
  clear Hex.
  simpl. inversion rl.
  subst. inversion X.
  simpl in *. destruct ps. discriminate.
  destruct ps. 2 : discriminate.
  simpl in H. inversion H. unfold nslclext in H3.
  inversion H1. subst.
  left. econstructor. assumption.
  Print Coercion Paths class class.
  
  remember D2 as D'.
  destruct D'. contradiction.
  destruct J.
  2:{ left. econstructor. assumption.
     eapply nprinc_WB2Ls_not_last. firstorder. } 
  destruct d.
    left. econstructor. assumption.
     eapply nprinc_WB2Ls_dir. firstorder. 
  destruct (not_wbox_dec A).
    left. econstructor. assumption.
    eapply nprinc_WB2Ls_nwb. assumption.
  
  inversion l. subst ps0 c.
  inversion X. right. intros HH.
  inversion HH.
  inversion X0. contradiction. discriminate. contradiction.
  destruct A; try (apply e; eapply not_wbox__exp; econstructor).
  subst.
  clear_useless.
  Print derI.
  inversion H6.


  remember D as D'.
  destruct D'. contradiction.
  destruct J.
  2:{ left. econstructor. assumption.
     eapply nprinc_WB2Ls_not_last. firstorder. } 
  destruct d.
    left. econstructor. assumption.
     eapply nprinc_WB2Ls_dir. firstorder. 
  destruct (not_wbox_dec A).
    left. econstructor. assumption.
    eapply nprinc_WB2Ls_nwb. assumption.
  
  inversion l. subst ps0 c.
  inversion X. right. intros HH.
  inversion HH.
  inversion X0. contradiction. discriminate. contradiction.
  destruct A; try (apply e; eapply not_wbox__exp; econstructor).
  subst.
  clear_useless.
  Print derI.
  inversion H6.


  Inductive principal_WBox2Ls {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ1 Γ2 Δ Σ1 Σ2 Π : list (PropF V)) :=
| princ_WB2Ls_I G' H B d
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ1 ++ Γ2, Δ, d) ; (Σ1 ++ [A] ++ Σ2, Π, bac)] ->
    A = WBox B ->
    H = (map (nslclext G') [
               [(Γ1 ++ [B] ++ Γ2, Δ, d)]]) ->
    D = derI _ rl D2 ->
    principal_WBox2Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π.
*)

     (*Inductive not_principal_WBox2Ls {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V)
          I J
          (Φ1 Φ2 Ξ : list (PropF V)) (d : dir) : Type :=
| nprinc_WB2Ls_nwb : not_wbox A ->
                     G = I ++ [(Φ1 ++ [A] ++ Φ2, Ξ, d)] ++ J ->
                     not_principal_WBox2Ls D A I J Φ1 Φ2 Ξ d
| nprinc_WB2Ls_dir : d = fwd ->
                     G = I ++ [(Φ1 ++ [A] ++ Φ2, Ξ, d)] ++ J ->
                     not_principal_WBox2Ls D A I J Φ1 Φ2 Ξ d
| nprinc_WB2Ls_not_last : is_bbox A ->
                          d = bac ->
                          J <> [] ->
                          G = I ++ [(Φ1 ++ [A] ++ Φ2, Ξ, d)] ++ J ->
                          not_principal_WBox2Ls D A I J Φ1 Φ2 Ξ d
| nprinc_WB2Ls_last_not_princ G' H B d2 Γ1 Γ2 Σ1 Σ2 Δ Π
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ1 ++ Γ2, Δ, d2) ; (Σ1 ++ [WBox B] ++ Σ2, Π, bac)] ->
    H = (map (nslclext G') [
               [(Γ1 ++ [B] ++ Γ2, Δ, d)]]) ->
    D = derI _ rl D2 ->
    d = bac ->
    J = [] ->
    A <> WBox B ->
    G = I ++ [(Φ1 ++ [A] ++ Φ2, Ξ, d)] ++ J ->
    not_principal_WBox2Ls D A I J Φ1 Φ2 Ξ d.
 *)

(* Not provable, I think, because A might not have been principal and yet it *could have been* in the right form to be principal. Deciding which it is I think would require deciding V. 
Lemma lem : forall {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V)
          I J
          (Φ1 Φ2 Ξ : list (PropF V)) (d : dir),
  np_WB2Ls_wf D A I J Φ1 Φ2 Ξ d ->
(existsT2 Γ1 Γ2 Δ, principal_WBox2Ls D A Γ1 Γ2 Δ Φ1 Φ2 Ξ) +
(not_principal_WBox2Ls D A I J Φ1 Φ2 Ξ d).
Proof.
  intros until 0; intros Hwf.
  inversion Hwf.
  destruct J.
  2:{ right. econstructor. assumption.
      apply nprinc_WB2Ls_not_last. firstorder.
  }

  destruct d. right. econstructor. assumption.
  apply nprinc_WB2Ls_dir. firstorder.

  destruct A;
  try solve [right; econstructor; [assumption|];
  eapply nprinc_WB2Ls_nwb; eapply not_wbox__exp; econstructor].
  simpl in *.
  
  remember D as D'.
  destruct D'. contradiction.
  inversion l. subst ps0 c concl.
  inversion X. subst ps.
  unfold nslclext in H. inversion H1.
  subst c ps0. clear H1 X.
  eapply tail_inv_singleton in H.
  destruct H as [H1 H2].
  inversion H2.
  subst c ps0. clear H1 X.
  eapply tail_inv_singleton in H.
  destruct H as [H1 H2].
  inversion H2. subst I H0 Ξ.
  
  subst c ps0.
  
  
  subst H0 Ξ d.
  Set Printing Implicit.
  SearchAbout LNSKt_rules b2r.
  unfold nslclext.
  
  subst. clear Hwf.
  
*)

  (*
  
  eapply HSR;
   [ 
   | econstructor; eassumption
   | erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa'
   | 
   | repeat eassumption || merge_solve_primitive
   | simpl; lia ].
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

  Unshelve.
  3:{ subst. solve_eqs. }


    unfold nslcext || unfold nslclext; unfold seqext.
  list_assoc_r_single.

  assoc_mid_loc H1. rewrite <- (app_assoc Γ).
  rewrite (app_assoc _ H1).

  eapply HSR;
   [ 
   | econstructor; eassumption
   | erewrite (dp_get_D D2b) in Hdpb'; eapply Hdpb'
   | 
   | repeat eassumption || merge_solve_primitive
   | simpl; lia ].
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

  Unshelve.
  2:{ subst. solve_eqs. }






  
  
    unfold nslcext || unfold nslclext; unfold seqext.
  list_assoc_r_single.

  assoc_mid_loc H1. rewrite <- (app_assoc Γ).


  eapply HSR;
   [ 
   | econstructor; eassumption
   | erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa'
   | 
   | repeat eassumption || merge_solve_primitive
   | simpl; lia ].
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

  Unshelve.
  2:{ subst. solve_eqs. }

  assoc_mid_loc H1. rewrite <- (app_assoc Γ).
  rewrite (app_assoc _ H1).
  eapply HSR.
  2:{
    econstructor 2. eassumption. }
  2:{    erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa'. }
  2:{ eassumption. }
  2:{ eassumption. }
  2:{ simpl. lia. }

  solve_D3_weakened D3. 
  
  Unshelve.
  3:{ subst. solve_eqs. }
  
  eapply HSR;
   [ 
   | econstructor; eassumption
   | erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa'
   | 
   | repeat eassumption || merge_solve_primitive
   | simpl; lia ].
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

    unfold nslcext || unfold nslclext; unfold seqext.
  list_assoc_r_single.
 
  eapply HSR;
   [ 
   | econstructor; eassumption
   | erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa'
   | 
   | repeat eassumption || merge_solve_primitive
   | simpl; lia ].
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

  Unshelve.
  3:{ subst.


  solve_D3_weakened D3. struct_equiv_str_solve_primitive. eassumption.


  eassumption.
  
  solve_HSR_except_D3' HSR D2a D3 Hdpa'.
  solve_HSR_except_D3' HSR D2b D3 Hdpb'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

  Unshelve.
  2:{ subst. admit. }
  2:{ admit. }

  
    solve_case_G_gen_draft_setup' D2a D2a' D2b D2b'.


    eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
     bracket_set_up1_redo_twoprem D1 D2a' D2b' ImpL_pfc; simpl | ].

eapply Sctxt_eq. eapply ImpL_pfc. reflexivity. rewrite app_nil_l. reflexivity. reflexivity.

  econstructor; [  | econstructor; [  | econstructor ] ];
    unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.
  solve_HSR_except_D3' HSR D2a D3 Hdpa'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.
  solve_HSR_except_D3' HSR D2b D3 Hdpb'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.

    Unshelve.
  all : try solve [subst; solve_eqs].


   eapply derI;
   [ eapply prop; econstructor; list_assoc_r_single;
     bracket_set_up1_redo_twoprem D1 D2a' D2b' ImpL_pfc; simpl | ].
  SearchAbout "Sctxt" seqrule.

    eapply derI.
  eapply prop; econstructor; list_assoc_r_single.
   bracket_set_up1_preR D2b' AA; assoc_mid_loc [Imp AA BB].


  econstructor; [  | econstructor; [  | econstructor ] ];
  unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.
  solve_HSR_except_D3' HSR D2a D3 Hdpa'.
  solve_D3_weakened D3. struct_equiv_str_solve_primitive.
  solve_HSR_except_D3' HSR D2b D3 Hdpb'.
  solve_HSR_except_D3' HSR D2b D3 Hdpb'.
  fold app.
   [ solve_HSR_except_D3' HSR D2a D3 Hdpa'
   | solve_HSR_except_D3' HSR D2b D3 Hdpb' ];
   solve_D3_weakened D3 || struct_equiv_str_solve_primitive


  solve_case_G_gen_draft_finish''' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
  
    fill_tac_case_G_b1r D1 D2a' D2b' BBox1Rs;
    try  solve_case_G_gen_draft_finish''' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
      solve_case_G_gen_draft_finish'' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.

    [eapply merge_app_struct_equiv_strR_explicit in Hme; [ | eassumption];
     sD; subst | | ];
    list_assoc_r_single;
    solve_case_G_gen_draft_setup D2a D2a' D2b D2b';
    fill_tac_case_G_b1r D1 D2a' D2b' BBox1Rs;
    try  solve_case_G_gen_draft_finish''' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
      solve_case_G_gen_draft_finish'' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
      Unshelve. all : (subst; solve_eqs).
Qed.
  
  
Admitted.
*)

(*

+{
      list_assoc_r_arg_derrec2_spec  D2 D2'.
      list_assoc_r_single.
      list_assoc_l.
      eapply derI.
      eapply prop.
      econstructor.

      list_assoc_r_single.
      bracket_set_up1 D2'.
      eapply Sctxt_eq. 
      eapply ImpR_pfc.
      reflexivity. reflexivity. reflexivity.
      econstructor; [ | econstructor].
      simpl. unfold nslcext.
      list_assoc_r_single.
      bracket_set_up2 D2'.
      solve_HSR_except_D3 HSR D2 D3 Hdp'.

     (* weakend then apply D3. TODO: generalise. *)
     list_assoc_r_single.
     eapply derrec_weakened_nseq; [ | eapply D3].
     weakened_nseq_solve_nseq.
     list_assoc_r_single.
     weakened_seq_solve.
     all : weakened_multi_solve.

     Unshelve. subst. solve_eqs.
    }

          +{
      list_assoc_r_arg_derrec2_spec  D2 D2'.
      
      (*
      Unshelve. 3: { list_assoc_r_single. reflexivity. }
      *)
      list_assoc_r_single.
      list_assoc_l.
      eapply derI.
      eapply prop.
      econstructor.

      list_assoc_r_single.
      bracket_set_up1 D2'.
      eapply Sctxt_eq. 
      eapply ImpR_pfc.
      reflexivity. reflexivity. reflexivity.
      econstructor; [ | econstructor].
      simpl. unfold nslcext.
      list_assoc_r_single.
      bracket_set_up2 D2'.
      solve_HSR_except_D3 HSR D2 D3 Hdp'.

     (* weakend then apply D3. TODO: generalise. *)
     list_assoc_r_single.
     eapply derrec_weakened_nseq; [ | eapply D3].
     weakened_nseq_solve_nseq.
     list_assoc_r_single.
     weakened_seq_solve.
     all : weakened_multi_solve.

     Unshelve. subst. solve_eqs.
    }



  +{
     
      epose proof Hdp' as Hdp;
      epose proof (get_D D2) as D2';
      eassert (_ = _) as HH;
        [ | specialize (D2' HH)]; [list_assoc_r_single; reflexivity |];
          clear HH.
      (*
      Unshelve. 3: { list_assoc_r_single. reflexivity. }
      *)
      list_assoc_r_single.
      list_assoc_l.
      eapply derI.
      eapply prop.
      econstructor.

      list_assoc_r_single.
      bracket_set_up1 D2'.
      eapply Sctxt_eq. 
      eapply ImpR_pfc.
      reflexivity. reflexivity. reflexivity.
      econstructor; [ | econstructor].
      simpl. unfold nslcext.
      list_assoc_r_single.
      bracket_set_up2 D2'.
      solve_HSR_except_D3 HSR D2 D3 Hdp'.

     (* weakend then apply D3. TODO: generalise. *)
     list_assoc_r_single.
     eapply derrec_weakened_nseq; [ | eapply D3].
     weakened_nseq_solve_nseq.
     list_assoc_r_single.
     weakened_seq_solve.
     all : weakened_multi_solve.

     Unshelve. solve_eqs.
           }

    
  +{
     
      epose proof Hdp' as Hdp;
      epose proof (get_D D2) as D2';
      eassert (_ = _) as HH;
        [ | specialize (D2' HH)]; [list_assoc_r_single; reflexivity |];
          clear HH.
      (*
      Unshelve. 3: { list_assoc_r_single. reflexivity. }
      *)
      list_assoc_r_single.
      list_assoc_l.
      eapply derI.
      eapply prop.
      econstructor.

      list_assoc_r_single.
      bracket_set_up1 D2'.
      eapply Sctxt_eq. 
      eapply ImpR_pfc.
      reflexivity. reflexivity. reflexivity.
      econstructor; [ | econstructor].
      simpl. unfold nslcext.
      list_assoc_r_single.
      bracket_set_up2 D2'.
      solve_HSR_except_D3 HSR D2 D3 Hdp'.

     (* weakend then apply D3. TODO: generalise. *)
     list_assoc_r_single.
     eapply derrec_weakened_nseq; [ | eapply D3].
     weakened_nseq_solve_nseq.
     list_assoc_r_single.
     weakened_seq_solve.
     all : weakened_multi_solve.

     Unshelve. solve_eqs.
           }






    
          +{  epose proof Hdp' as Hdp.
      epose proof (get_D D2 _) as D2'.
      Unshelve. 3 :{ list_assoc_r_single. reflexivity. }
  
      list_assoc_r_single.
      list_assoc_l.
      eapply derI.
      eapply prop.
      econstructor.

      list_assoc_r_single.
      bracket_set_up1 D2'.
      eapply Sctxt_eq. 
      eapply ImpR_pfc.
      reflexivity. reflexivity. reflexivity.
      econstructor; [ | econstructor].
      simpl. unfold nslcext.
      list_assoc_r_single.
      bracket_set_up2 D2'.
      solve_HSR_except_D3 HSR D2 D3 Hdp'.

     (* weakend then apply D3. TODO: generalise. *)
     list_assoc_r_single.
     eapply derrec_weakened_nseq; [ | eapply D3].
     weakened_nseq_solve_nseq.
     list_assoc_r_single.
     weakened_seq_solve.
     all : weakened_multi_solve.

     Unshelve. solve_eqs.
                }
          +{  epose proof Hdp' as Hdp.
      epose proof (get_D D2 _) as D2'.
      Unshelve. 3 :{ list_assoc_r_single. reflexivity. }
  
      list_assoc_r_single.
      list_assoc_l.
      eapply derI.
      eapply prop.
      econstructor.

      list_assoc_r_single.
      bracket_set_up1 D2'.
      eapply Sctxt_eq. 
      eapply ImpR_pfc.
      reflexivity. reflexivity. reflexivity.
      econstructor; [ | econstructor].
      simpl. unfold nslcext.
      list_assoc_r_single.
      bracket_set_up2 D2'.
      solve_HSR_except_D3 HSR D2 D3 Hdp'.

     (* weakend then apply D3. TODO: generalise. *)
     list_assoc_r_single.
     eapply derrec_weakened_nseq; [ | eapply D3].
     weakened_nseq_solve_nseq.
     list_assoc_r_single.
     weakened_seq_solve.
     all : weakened_multi_solve.

     Unshelve. solve_eqs.
     }
Qed.
*)
  (* -- *)


 




(*
  Ltac bracket_set_up1_pre D2' AA :=
  match type of D2' with
  | derrec ?rules ?prems ?H =>
    match get_last_app H with
    | [(?L1,?L2,?d)] =>  tac_match L1 [AA]
    end
  end.

Ltac bracket_set_up1 D2' :=
  match type of D2' with
  | context [ [Imp ?AA ?BB] ] => bracket_set_up1_pre D2' AA; assoc_mid_loc [Imp AA BB]
  end.
*)
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
      | context [ [WBox ?AA] ] =>
        bracket_set_up1_pre D2' AA; assoc_mid_loc [Imp AA BB]
        end
    end.

  Ltac bracket_set_up1_redo_pre D2' princ_conn :=
 *)





(*  
      list_assoc_r_arg_derrec2_spec D2 D2';
      list_assoc_r_single; list_assoc_l;
      eapply derI;
      [eapply b2r ;
      econstructor;
      list_assoc_r_single;
      bracket_set_up1_redo D2' WBox2Rs;
      simpl; eapply WBox2Rs | ];
      econstructor; [ | econstructor];
      unfold nslclext; simpl;
      list_assoc_r_single;
      bracket_set_up2 D2';
      solve_HSR_except_D3 HSR D2 D3 Hdp';
      solve_D3_weakened D3.
 *)
(*
      list_assoc_r_arg_derrec2_spec D2 D2';
      list_assoc_r_single; list_assoc_l;
      eapply derI;
      [eapply b2r ;
      econstructor;
      list_assoc_r_single ;
      assoc_mid_loc [WBox AA] ;
      simpl; eapply WBox2Rs | ];
      econstructor; [ | econstructor];
      unfold nslclext; simpl;
      list_assoc_r_single;
      bracket_set_up2 D2';
      solve_HSR_except_D3 HSR D2 D3 Hdp';
      solve_D3_weakened D3.

      Unshelve. all : (subst; solve_eqs).
Qed.       *)
(*



(*
      Ltac get_snd_last_app H :=
        match H with
          | ?H1 ++ ?H2 ++ ?H3 => get_last_app (H2 ++ H3)
          | ?H1 ++ ?H2 => constr:(H1)
          | _ => constr:(H)
        end.

      Ltac bracket_set_up1_pre_WB2R D2' AA :=
  match type of D2' with
  | derrec ?rules ?prems ?H =>
    match get_snd_last_app H with
    | [(?L1,?L2,?d)] =>  tac_match L1 [AA]
    end
  end.


Ltac bracket_set_up1_WB D2' :=
  match type of D2' with
  | context [ [WBox ?AA] ] =>
      bracket_set_up1_pre_WB2R D2' (WBox AA); assoc_mid_loc [WBox AA]
  end.

 match type of D2' with
  | derrec ?rules ?prems ?H =>
    match get_snd_last_app H with
    | [(?L1,?L2,?d)] =>  tac_match L2 [WBox AA]
    end
  end.

bracket_set_up1_pre_WB2R D2' (WBox AA); assoc_mid_loc [WBox AA].

      bracket_set_up1_WB D2' ; *)

Ltac solve_case_F_gen_draft2 D2 D2' D3 HSR Hdp' :=
      list_assoc_r_arg_derrec2_spec D2 D2';
      list_assoc_r_single; list_assoc_l;
      eapply derI;
      [eapply prop;
      econstructor;
      list_assoc_r_single ;
      bracket_set_up1 D2' ;
      eapply Sctxt_eq   ;
      [eapply ImpR_pfc | reflexivity ..] | ];
      econstructor; [ | econstructor];
      unfold nslcext; simpl;
      list_assoc_r_single;
      bracket_set_up2 D2';
      solve_HSR_except_D3 HSR D2 D3 Hdp';
      solve_D3_weakened D3.



  solve_case_F_gen_draft2 D2 D2' D3 HSR Hdp'.  
  Unshelve. all : (subst ; solve_eqs).
Qed.

  intros.
Admitted.
*)





(* Using size instead of fsize. Came across problems in cut admissibility given that not every formula (e.g. A /\ B) has a size, but every formula has an fsize. 
Definition SR_wb_fwd_pre (n m : nat) := forall {V : Set} 
    G Γ Δ H Σ Π I GH (A : PropF V) sz
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [WBox A],fwd)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [WBox A], Π, fwd)] ++ I)),
        principal_WBR D1 (WBox A) Γ Δ [] fwd ->
        ((dp D1) + (dp D2))%nat <= m ->
        merge G H GH ->
        (existsT2 (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (GH ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++
                           [([],[A],fwd)] )), True) ->
        size (WBox A) sz ->
        sz <= n ->
        existsT2 (D4 : derrec (@LNSKt_rules V) (fun _ => False)
                            (GH ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++ I )), True .
 *)
(* Using size instead of fsize. Came across problems in cut admissibility given that not every formula (e.g. A /\ B) has a size, but every formula has an fsize. 
Definition SR_wb_bac_pre (n m : nat) := forall {V : Set} rules
    G Γ Δ H Σ Π I GH (A : PropF V) sz
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [WBox A],bac)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [WBox A], Π, bac)] ++ I)),
        principal_WBR D1 (WBox A) Γ Δ [] bac ->
        ((dp D1) + (dp D2))%nat <= m ->
        merge G H GH ->
        (existsT2 (D3 : derrec rules (fun _ => False)
                       (GH ++ [(Γ ++ Σ, Δ ++ Π, bac)] ++
                           [([],[A],fwd)] )), True) ->
        size (WBox A) sz ->
        sz <= n ->
        existsT2 (D4 : derrec rules (fun _ => False)
                            (GH ++ [(Γ ++ Σ, Δ ++ Π, bac)] ++ I )), True .
 *)
(* Using size instead of fsize. Came across problems in cut admissibility given that not every formula (e.g. A /\ B) has a size, but every formula has an fsize. 
Definition SR_bb_fwd_pre (n m : nat) := forall {V : Set} 
    G Γ Δ H Σ Π I GH (A : PropF V) sz
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [BBox A],fwd)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [BBox A], Π, fwd)] ++ I)),
        principal_BBR D1 (BBox A) Γ Δ [] fwd ->
        ((dp D1) + (dp D2))%nat <= m ->
        merge G H GH ->
        (existsT2 (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (GH ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++
                           [([],[A],fwd)] )), True) ->
        size (BBox A) sz ->
        sz <= n ->
        existsT2 (D4 : derrec (@LNSKt_rules V) (fun _ => False)
                              (GH ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++ I )), True .
*)

(* Using size instead of fsize. Came across problems in cut admissibility given that not every formula (e.g. A /\ B) has a size, but every formula has an fsize. 
Definition SR_bb_bac_pre (n m : nat) := forall {V : Set} rules
    G Γ Δ H Σ Π I GH (A : PropF V) sz
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [BBox A],bac)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [BBox A], Π, bac)] ++ I)),
        principal_BBR D1 (BBox A) Γ Δ [] bac ->
        ((dp D1) + (dp D2))%nat <= m ->
        merge G H GH ->
        (existsT2 (D3 : derrec rules (fun _ => False)
                       (I ++ [(Γ ++ Σ, Δ ++ Π, bac)] ++
                           [([],[A],fwd)] )), True) ->
        size (BBox A) sz ->
        sz <= n ->
        existsT2 (D4 : derrec rules (fun _ => False)
                            (GH ++ [(Γ ++ Σ, Δ ++ Π, bac)] ++ I )), True .
 *)
(* Using size instead of fsize. Came across problems in cut admissibility given that not every formula (e.g. A /\ B) has a size, but every formula has an fsize. 
Definition SR_wb_pre (n m : nat) := forall {V : Set} 
    G Γ Δ H Σ Π I GH (A : PropF V) sz d
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [WBox A],d)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [WBox A], Π, d)] ++ I)),
        principal_WBR D1 (WBox A) Γ Δ [] d ->
        ((dp D1) + (dp D2))%nat <= m ->
        merge G H GH ->
        (existsT2 (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (GH ++ [(Γ ++ Σ, Δ ++ Π, d)] ++
                           [([],[A],fwd)] )), True) ->
        size (WBox A) sz ->
        sz <= n ->
        existsT2 (D4 : derrec (@LNSKt_rules V) (fun _ => False)
                            (GH ++ [(Γ ++ Σ, Δ ++ Π, d)] ++ I )), True .
 *)

(* Using size instead of fsize. Came across problems in cut admissibility given that not every formula (e.g. A /\ B) has a size, but every formula has an fsize. 
Definition SR_bb_pre (n m : nat) := forall {V : Set} 
    G Γ Δ H Σ Π I GH (A : PropF V) sz d
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [BBox A],d)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [BBox A], Π, d)] ++ I)),
        principal_WBR D1 (BBox A) Γ Δ [] d ->
        ((dp D1) + (dp D2))%nat <= m ->
        merge G H GH ->
        (existsT2 (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (GH ++ [(Γ ++ Σ, Δ ++ Π, d)] ++
                           [([],[A],fwd)] )), True) ->
        size (BBox A) sz ->
        sz <= n ->
        existsT2 (D4 : derrec (@LNSKt_rules V) (fun _ => False)
                            (GH ++ [(Γ ++ Σ, Δ ++ Π, d)] ++ I )), True .
*)
(* Using size instead of fsize. Came across problems in cut admissibility given that not every formula (e.g. A /\ B) has a size, but every formula has an fsize. 
Definition SR_p_pre (n m : nat) := forall {V : Set} 
    G Γ Δ H Σ Π I GH (A : PropF V) d sz
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [A],d)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [A], Π, d)] ++ I)),
        principal_not_box_R D1 A Γ Δ [] d ->
        ((dp D1) + (dp D2))%nat <= m ->
        size A sz ->
        sz <= n ->
        not_box A ->
        merge G H GH ->
        existsT2 (D4 : derrec (@LNSKt_rules V) (fun _ => False)
                            (GH ++ [(Γ ++ Σ, Δ ++ Π, d)] ++ I )), True .
*)
(* Using size instead of fsize. Came across problems in cut admissibility given that not every formula (e.g. A /\ B) has a size, but every formula has an fsize. 
Definition SL_pre (n m : nat) := forall {V : Set} 
    G Γ Δ H Σ Π I GH (A : PropF V) d sz
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [A],d)] ++ I))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [A], Π, d)])),
        ((dp D1) + (dp D2))%nat <= m ->
        size A sz ->
        sz <= n ->
        merge G H GH ->
        existsT2 (D4 : derrec (@LNSKt_rules V) (fun _ => False)
                            (GH ++ [(Γ ++ Σ, Δ ++ Π, d)] ++ I )), True . 
 *)

(*

(* Left it here 10/02/20 
We need to include (rl : rules H G) because of the D = derI _ rl D2 clause. 
It should be provable when rules contains H/G as a rule. 
Consider whether this can be done better.
Keep working on principal_WBL
*)


Inductive principal_ImpR1'_strongR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) G' Γ Δ1 Δ2 d :=
| princ_ImpR1'_str H B C
                   (D2 : dersrec (@LNSKt_rules V) (fun _ => False) H)
                   (data : LNSKt_rules H G)
  :
    G = G' ++ [(Γ,Δ1++[A]++Δ2,d)] ->
    A = Imp B C ->
    (* = (nslcext G' d (seqext Γ1 Γ2 Δ1 Δ2 ([],[A]))) *)
    H =  (map (nslcext G' d) (map (seqext Γ [] Δ1 Δ2)
                                          [([B],[Imp B C; C])])) ->
      D = derI _ data D2 ->
    principal_ImpR1'_strongR D A G' Γ Δ1 Δ2 d. 


Parameter V : Set.
Parameter p q : V.
Definition P := Var p.
Definition Q := Var q.
Print PropF.
Check (dlNil (@LNSKt_rules V) (fun _ => False)).
Definition d0 := (dlNil (@LNSKt_rules V) (fun _ => False)).
Print derI.
Print LNSKt_rules.

Definition d1 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) [([Imp P Q ; Q ; P], [Q], fwd)].
  eapply derI.
  eapply prop.
  rewrite <- app_nil_l.
  rewrite <- nslcext_def.
  eapply NSlcctxt.
  eapply Sctxt_eq;
  [ | rewrite cons_singleton;  rewrite (cons_singleton _ Q);  reflexivity |
    rewrite <- (app_nil_l [Q]); rewrite <- (app_nil_r [Q]); reflexivity | ..].
  eapply Id_pfc.
  reflexivity.
  apply dlNil.
Qed.

Definition d1' : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) (nslcext [] fwd (seqext [Imp P Q] [P] [] [] ([Q],[Q]))). 
  eapply derI.
  eapply prop.
  eapply NSlcctxt.
  eapply Sctxt.
  eapply Id_pfc.
  apply dlNil.
Qed.

Definition d1'' : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) [([Imp P Q ; Q ; P], [Q], fwd)].
  rewrite <- app_nil_l.
  rewrite <- nslcext_def.
  rewrite cons_singleton.
  rewrite <- (app_nil_l [Q]).
  rewrite <- (app_nil_r [Q]).
  rewrite (cons_singleton _ Q).
  rewrite <- seqext_def.
  apply d1'.
Qed.

Definition d2 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) [([Imp P Q ; P], [Q ; P], fwd)].
  eapply derI.
  eapply prop.
  rewrite <- app_nil_l.
  rewrite <- nslcext_def.
  eapply NSlcctxt.
  eapply Sctxt_eq;
  [ | erewrite app_nil_r; rewrite cons_singleton; reflexivity |
    erewrite app_nil_r; rewrite cons_singleton; reflexivity |..].
  eapply Id_pfc.
  reflexivity.
  apply dlNil.
Qed.

Definition d3 : derrec (LNSKt_rules (V:=V)) (fun _ => False) [([Imp P Q; P], [Q], fwd)].
  eapply derI.
  eapply prop.
  rewrite <- app_nil_l.
  rewrite <- nslcext_def.
  eapply NSlcctxt.
  eapply Sctxt_eq.
  eapply ImpL_pfc.
  rewrite cons_singleton.
  rewrite <- (app_nil_l (_ ++ [P])).
  reflexivity.
  simpl. erewrite app_nil_r. reflexivity.
  reflexivity.
  eapply dlCons. eapply d1.
  eapply dlCons. eapply d2.
  eapply dlNil.
Qed.

Print princrule_pfc.
Print seqrule.

Check (ImpR_pfc P Q).
Check princrule_pfc.
Check Sctxt.
Check (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc P Q)).
Check (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc P Q))).
Check (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc P Q)))).
Check (derI _ (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc P Q))))).

Definition is_0 (n:nat) : bool :=
  match n in nat return bool with
  | 0 => true
  | _ => false
  end.

Definition is_nil (T1 T2 : Type) (l : list T1) (f : T1 -> T2) : list T2 :=
  match l in list _ return list T2 with
  | nil => nil
  | a :: l' => (f a) :: nil
  end.

Definition my (T1 T2 : Type) (l : list T1) (pf : T1 = T2) : list T2 :=
  match l in list _ return list T2 with
  | _ => eq_rect _ _ l _ pf
  end.

Print my.
SearchAbout "symmetry".
Print eq.

Inductive principal_ImpR1 {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR1 G2 B C d Φ1 Φ2 Ψ1 Ψ2
             (D2 : dersrec (@LNSKt_rules V) (fun _ => False)
                     (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                       [([B], [Imp B C; C])])))
(*             (D3 : dersrec (@LNSKt_rules V) (fun _ => False)
                     [(G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)])])
             (pf2 : G2 = G)
             (pf3 : nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C])) = G)
             (pf5 : (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                                             [([B], [Imp B C; C])])) =
                    [G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]])
             (pf4 :  G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)] = G)
*)
             (data : LNSKt_rules (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                       [([B], [Imp B C; C])])) G)
  (*           (data2 : LNSKt_rules [G ++ [(Φ1 ++ [B] ++ Φ2,
                       Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]] G)
*)
  :
(*    data2 = (eq_rect _ (fun GG => LNSKt_rules GG  G) data _ pf5)  ->
*)
    D = derI _ data D2
    ->
    principal_ImpR1 D A.

Inductive principal_ImpR1' {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR1' G2 B C d Φ1 Φ2 Ψ1 Ψ2
              (D2 : dersrec (@LNSKt_rules V) (fun _ => False)
                     (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                       [([B], [Imp B C; C])])))
             (data : LNSKt_rules (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                                                          [([B], [Imp B C; C])])) G)
  :
    A = Imp B C -> D = derI _ data D2  ->  principal_ImpR1' D A.


Inductive principal_ImpR1'_strongR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) G' Γ Δ1 Δ2 d :=
| princ_ImpR1'_str H B C
                   (D2 : dersrec (@LNSKt_rules V) (fun _ => False) H)
                   (data : LNSKt_rules H G)
  :
    G = G' ++ [(Γ,Δ1++[A]++Δ2,d)] ->
    A = Imp B C ->
    (* = (nslcext G' d (seqext Γ1 Γ2 Δ1 Δ2 ([],[A]))) *)
    H =  (map (nslcext G' d) (map (seqext Γ [] Δ1 Δ2)
                                          [([B],[Imp B C; C])])) ->
      D = derI _ data D2 ->
    principal_ImpR1'_strongR D A G' Γ Δ1 Δ2 d.


Inductive principal_ImpR2 {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR2 G2 B C d Φ1 Φ2 Ψ1 Ψ2
             (D2 : dersrec (@LNSKt_rules V) (fun _ => False)
                     (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                       [([B], [Imp B C; C])])))
(*             (D3 : dersrec (@LNSKt_rules V) (fun _ => False)
                     [(G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)])])
             (pf2 : G2 = G)
*)
             (pf3 : nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C])) = G)
 (*            (pf5 : (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                                             [([B], [Imp B C; C])])) =
                    [G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]])
             (pf4 :  G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)] = G)
*)
             (data : LNSKt_rules (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                       [([B], [Imp B C; C])])) G)
  (*           (data2 : LNSKt_rules [G ++ [(Φ1 ++ [B] ++ Φ2,
                       Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]] G)
   *)
            (data3 : LNSKt_rules
         (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])]))
         (nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C]))))
  :
(*    data2 = (eq_rect _ (fun GG => LNSKt_rules GG  G) data _ pf5)  ->
 *)
    data3 = (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) ->
    data = (eq_rect _ (fun GG => LNSKt_rules _ GG) data3 _ pf3) ->
    D = derI _ data D2
    ->
    principal_ImpR2 D A.

(* I think go with this definition. *)
Inductive principal_ImpR2' {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR2' G2 B C d Φ1 Φ2 Ψ1 Ψ2  D2 data data3
             (pf3 : nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C])) = G)  :
    data3 = (prop (NSlcctxt _ _ _ _ _
                     (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) ->
    data = (eq_rect _ (fun GG => LNSKt_rules _ GG) data3 _ pf3) ->
    D = derI _ data D2   ->
    A = Imp B C ->
    principal_ImpR2' D A.

Print principal_ImpR2'.

(*
(D2 : dersrec (LNSKt_rules (V:=V))
                             (fun _ : list (rel (list (PropF V)) * dir) => False)
                             (map (nslcext G2 d)
                                (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])])))
*)

Inductive principal_ImpR3 {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR3 G2 B C d Φ1 Φ2 Ψ1 Ψ2
(*             (D2 : dersrec (@LNSKt_rules V) (fun _ => False)
                     (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                       [([B], [Imp B C; C])])))
*)
             (D3 : dersrec (@LNSKt_rules V) (fun _ => False)
                     [(G2 ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)])])
 (*            (pf2 : G2 = G)
*)
             (pf3 : nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C])) = G)
  
             (pf5 :    (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                                                [([B], [Imp B C; C])])) =
                       [G2 ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]])
               
(*
            (pf4 :  G2 ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)] = G)
*)
             (data : LNSKt_rules (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                       [([B], [Imp B C; C])])) G)
 
            (data2 : LNSKt_rules [G2 ++ [(Φ1 ++ [B] ++ Φ2,
                       Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]] G)
  
            (data3 : LNSKt_rules
         (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])]))
         (nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C]))))

  :
(*    data2 = (eq_rect _ (fun GG => LNSKt_rules GG  G) data _ pf5)  ->
 *)
(*    data = (eq_rect _ (fun GG => LNSKt_rules _ GG) data3 _ pf3) ->
*)
    data = (eq_rect _ (fun GG => LNSKt_rules _ GG) data3 _ pf3) ->
    data2 = (eq_rect _ (fun GG => LNSKt_rules GG _) data _ pf5) -> 
     data3 = (prop (NSlcctxt _ _ _ _ _ (Sctxt                                                        (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) ->                      D = derI _ data2 D3
    ->
    principal_ImpR3 D A.

Lemma lem : forall {V : Set} G2 (B C : PropF V) d Φ1 Φ2 Ψ1 Ψ2,
  (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2)
                                                [([B], [Imp B C; C])])) =
                       [G2 ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]].
Proof.
  reflexivity.
Qed.


(*
 (data2 : LNSKt_rules
                               [G2 ++
                                [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]]
                               G)
 *)

Inductive principal_ImpR3' {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR3' G2 B C d Φ1 Φ2 Ψ1 Ψ2  D3 data data2 data3 
               (pf3 : nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C])) = G) :
    data = (eq_rect _ (fun GG => LNSKt_rules _ GG) data3 _ pf3) ->
                                                                                          data2 = (eq_rect _ (fun GG => LNSKt_rules GG _) data
                                                                                                           [G2 ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]]
                                                                                                           eq_refl) ->
                                                                                          data3 = (prop (NSlcctxt _ _ _ _ _ (Sctxt                                                        (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) ->                               D = derI _ data2 D3  ->
     principal_ImpR3' D A.

Print principal_ImpR3.

(*
Inductive principal_ImpR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR G2 B C d Φ1 Φ2 Ψ1 Ψ2
             (D2 : dersrec (@LNSKt_rules V) (fun _ => False) (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])])))
             (D3 : dersrec (@LNSKt_rules V) (fun _ => False) [(G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)])])
(*             (pf :          derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) G = derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
                          (nslcext G' d (seqext Γ1 Γ2 Δ1 Δ2 ([], [Imp B C]))))
*)
             (pf2 : G2 = G)
             (data : LNSKt_rules (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])])) G)
             (pf3 : nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C])) = G)
             (pf5 : (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])])) =  [G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]])
             (pf4 :  G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)] = G)
             (data2 : LNSKt_rules [G ++ [(Φ1 ++ [B] ++ Φ2, Ψ1 ++ [Imp B C] ++ [C] ++ Ψ2, d)]] G)
  :
    data2 = (eq_rect _ (fun GG => LNSKt_rules GG  G) data _ pf5)  ->
    D = derI _ (eq_rect _ (fun GG => LNSKt_rules GG  G)  _ pf5) D3
    ->
    principal_ImpR D A.


(eq_rect _ _ (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) _ pf3 )



Inductive principal_ImpR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR G2 B C d Φ1 Φ2 Ψ1 Ψ2
             (D2 : dersrec (@LNSKt_rules V) (fun _ => False) (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])])))
(*             (pf :          derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) G = derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
                          (nslcext G' d (seqext Γ1 Γ2 Δ1 Δ2 ([], [Imp B C]))))
*)
             (pf2 : G2 = G)
             (data : LNSKt_rules (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])]))
                                 G)
             (pf3 : nslcext G2 d (seqext Φ1 Φ2 Ψ1 Ψ2 ([], [Imp B C])) = G)
  :

    D = derI _ (eq_rect _ _ (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) _ pf3 ) D2
    ->
    principal_ImpR D A.


Inductive principal_ImpR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR G2 B C d Φ1 Φ2 Ψ1 Ψ2
             (D2 : dersrec (@LNSKt_rules V) (fun _ => False) (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])])))
(*             (pf :          derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) G = derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
                          (nslcext G' d (seqext Γ1 Γ2 Δ1 Δ2 ([], [Imp B C]))))
*)
             (pf2 : G2 = G)
             (data : LNSKt_rules (map (nslcext G2 d) (map (seqext Φ1 Φ2 Ψ1 Ψ2) [([B], [Imp B C; C])]))
   G)
  :

    D = derI _ data D2
    ->
    principal_ImpR D A.




D = derI _ data (eq_rect _
                          (fun n => dersrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
    [n]) (D2) _ pf2)

SearchAbout eq_rect.

Inductive principal_ImpR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR G' Γ1 Γ2 Δ1 Δ2 B C d
             (D' : dersrec (@LNSKt_rules V) (fun _ => False)
                           [(G' ++ [(Γ1++[B]++Γ2, Δ1++[Imp B C]++[C]++Δ2, d)])])
(*             (pf :          derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) G = derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
                          (nslcext G' d (seqext Γ1 Γ2 Δ1 Δ2 ([], [Imp B C]))))
*)
(pf2 : (nslcext G' d (seqext Γ1 Γ2 Δ1 Δ2 ([], [Imp B C]))) = G)
  :
    G = G' ++ [(Γ1++Γ2, Δ1++[A]++Δ2, d)] /\
    A = Imp B C /\

    D = derI _ (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) (eq_rect _ _ D' _ pf2)

    ->
    principal_ImpR D A.
    match D in (derrec _ _ _) return Prop with
      | _ =>
      eq_rect _ _ (D = derI _ (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) D') _ pf
    end ->
    principal_ImpR D A.



Inductive principal_test {V1 V2 : Type} (D : list V1) : Type :=
  | pt (pf1 : V1 = V2) (pf2 : V2 = V1) : principal_test (eq_rect _ _ (my V1 V2 D pf1) _ pf2).
| princ_ImpR (V2 : Type) (pf : V = V2) (l : list V) (pf : my V V2 D pf) :
    principal_test D.
    match D in list _ return Prop with
     | _ => D = D
        end ->
    principal_test D.

Inductive principal_ImpR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR G' Γ1 Γ2 Δ1 Δ2 B C d
             (D' : dersrec (@LNSKt_rules V) (fun _ => False)
                           [(G' ++ [(Γ1++[B]++Γ2, Δ1++[Imp B C]++[C]++Δ2, d)])])
             (pf :          derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) G = derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
                          (nslcext G' d (seqext Γ1 Γ2 Δ1 Δ2 ([], [Imp B C]))))
  :
    G = G' ++ [(Γ1++Γ2, Δ1++[A]++Δ2, d)] /\
    A = Imp B C /\
    match D in (derrec _ _ _) return Prop with
      | _ =>
      eq_rect _ _ (D = derI _ (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) D') _ pf
    end ->
    principal_ImpR D A.



Inductive principal_ImpR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G) (A : PropF V) :=
| princ_ImpR G' Γ1 Γ2 Δ1 Δ2 B C d
             (D' : dersrec (@LNSKt_rules V) (fun _ => False)
                          [(G' ++ [(Γ1++[B]++Γ2, Δ1++[Imp B C]++[C]++Δ2, d)])]) :
    G = G' ++ [(Γ1++Γ2, Δ1++[A]++Δ2, d)] /\
    A = Imp B C /\
    D = derI _ (prop (NSlcctxt _ _ _ _ _ (Sctxt (@princrule_pfc V) _ _ _ _ _ _ (ImpR_pfc B C)))) D'.
  D = derI _ (prop (NSlcctxt (Sctxt (ImpR_pfc B C)))) D'.

Inductive principal1 {V : Set} {rules : rlsT (list (rel (list (PropF V)) * dir))}
          {prems} {G} (D : derrec rules prems G) (A : PropF V) :=
| princ_prop  
*)

Definition principal' {V : Set} {rules : rlsT (list (rel (list (PropF V)) * dir))}
           {prems : _ -> Type} {G} (D : @derrec _ rules prems G) (A : PropF V) := True.
  
Definition SR_wb_fwd_pre (n m : nat) := forall {V : Set} 
    G Γ Δ H Σ Π I (A : PropF V)
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [WBox A],fwd)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [WBox A], Π, fwd)] ++ I)),
        principal_ImpR2' D1 (WBox A) ->
        ((ht _ _ _ _ D1) + (ht _ _ _ _ D2))%nat <= m ->
        merge G H I ->
        (exists (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (I ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++
                           [([],[A],fwd)] )), True) ->
        size (WBox A) <= n ->
        exists (D4 : derrec (@LNSKt_rules V) (fun _ => False)
                            (I ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++ I )), True .


Definition SR_testing_ImpR_pre (n m : nat) := forall {V : Set} 
    G Γ Δ H Σ Π I (A : PropF V)
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [A],fwd)]))
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) (H ++ [(Σ ++ [WBox A], Π, fwd)] ++ I)),
        principal_ImpR1'_strongR D1 A G Γ Δ [] fwd ->
        ((ht _ _ _ _ D1) + (ht _ _ _ _ D2))%nat <= m ->
        merge G H I ->
        (exists (D3 : derrec (@LNSKt_rules V) (fun _ => False)
                       (I ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++
                           [([],[A],fwd)] )), True) ->
        size (WBox A) <= n ->
        exists (D4 : derrec (@LNSKt_rules V) (fun _ => False)
                            (I ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++ I )), True .


Definition SR_wb_fwd (nm : nat * nat) :=
  let (n,m) := nm in SR_wb_fwd_pre n m.

Definition SR_testing_ImpR (nm : nat * nat) :=
  let (n,m) := nm in SR_testing_ImpR_pre n m.

Definition SR_wb_bac_pre (n m : nat) := forall {V : Set} rules
    G Γ Δ H Σ Π I (A : PropF V)
  (D1 : derrec rules (fun _ => False) (G ++ [(Γ, Δ ++ [WBox A],bac)]))
  (D2 : derrec rules (fun _ => False) (H ++ [(Σ ++ [WBox A], Π, bac)] ++ I)),
        principal' D1 (WBox A) ->
        ((ht _ _ _ _ D1) + (ht _ _ _ _ D2))%nat <= m ->
        merge G H I ->
        (exists (D3 : derrec rules (fun _ => False)
                       (I ++ [(Γ ++ Σ, Δ ++ Π, bac)] ++
                           [([],[A],fwd)] )), True) ->
        size (WBox A) <= n ->
        exists (D4 : derrec rules (fun _ => False)
                            (I ++ [(Γ ++ Σ, Δ ++ Π, bac)] ++ I )), True .
(*
Lemma dersrec_height_single : forall {V : Set} {rules} {prems} {G}
                                     (D1 : derrec rules prems G)
                                     (D2 : dersrec rules prems [G]),
    dersrec_height D2 = @derrec_height V _ _ _ D1.
Proof.
  intros until 0.
 *)

Require Import Lia.
  
Lemma dersrec_derrec_height : forall n {X : Type} {rules prems G}
                                     (D2 : dersrec rules prems [G]),
    dersrec_height D2 = n ->
    exists (D1 : derrec rules prems G),
      @derrec_height X _ _ _ D1 = n.
Proof.
  intros until 0.
  intros Ht.
  remember D2 as D2'.
  remember [G] as GG.
  destruct D2. discriminate.
  subst. simpl.
  inversion HeqGG. subst.
  exists d.
  remember [] as l.
  destruct D2. simpl.
  lia.
  discriminate.
Qed.

Lemma testing_princ : forall {V : Set} G Γ Δ A n 
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ, Δ ++ [A],fwd)])),
    (ht _ _ _ _ D1) = (S n) ->
  principal_ImpR1'_strongR D1 A G Γ Δ [] fwd ->
  exists B C,
    exists (D2 : derrec (@LNSKt_rules V) (fun _ => False) (G ++ [(Γ ++ [B],Δ ++ [Imp B C; C],fwd)])),
                 ht _ _ _ _ D2 = n.
Proof.
  intros until 0.
  intros Ht Hprinc.
  inversion Hprinc. subst.
  clear H0 Hprinc.
  simpl in Ht. inversion Ht.
  exists B. exists C.
  simpl in D2.
  eapply dersrec_derrec_height in H0.
  destruct H0 as [D3 HD3].
  exists D3.
  unfold ht. inversion Ht. subst. firstorder.
Qed.

  pose proof (dersrec_derrec_height _ D2 H0).
  destruct 

  SearchAbout dersrec derrec.
  pose proof (dersrecD_all D2) as D3.
  apply ForallT_singleD in D3.
  exists D3.
  
  unfold ht.
  

  
  Print dersrec_height.
  destruct D2. simpl in *. 
  inversion D2. subst.
  exists X.
  unfold ht.
  SearchAbout derrec_height dersrec_height.

  simpl.
  Print dersrec.
  exists D2.
  exists D
  , C, D2.
 


Theorem Lemma_Sixteen_test : forall nm,
    SR_testing_ImpR nm.
Proof.
  induction nm using induction_llt.
  destruct nm as [n m].
  unfold SR_testing_ImpR.
  unfold SR_testing_ImpR_pre.
  intros until 0.
  intros Hp Ht Hm [D3 II] Hs.
  clear Ht Hm II Hs D2 D3.
  Print principal_ImpR1'_strongR.
  inversion Hp as [GG B C D2 data Heq ? HGG HD1].
  subst.
  clear Hp. clear Heq.
  
  inversion Hp as [G2 B C d Φ1 Φ2 Ψ1 Ψ2  D4 data data3 pf3 Hd1 Hd2].
Admitted.
*)

(*
(* Case F): single premise, general.
Finished but can be generalised. Notice patterns in proof.
*)
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
  destruct (list_lem4 I); sD; subst;
    inv_app_hd_tl_full.

  app_eq_app_dest3; try contradiction; try discriminate.

  +{ list_assoc_l.
     eapply derI.
     eapply prop.
     econstructor.
     rewrite <- (app_assoc _ [Imp _ _]).
     eapply Sctxt_eq. 
     eapply ImpR_pfc.
     reflexivity. reflexivity. reflexivity.
     econstructor; [ | econstructor].
     simpl. list_assoc_r_single.
     solve_HSR_except_D3 HSR D2 D3 Hdp'.


     (* weakend then apply D3. TODO: generalise. *)
     assoc_mid [AA].
     eapply derrec_weakened_nseq;
       [ |
         eapply derrec_weakened_nseq; 
           [ |
             eapply D3]].
     rewrite <- (app_assoc GH).
     eapply weakened_nseq_app.
     eapply weakened_nseq_refl.
     eapply weakened_nseq_app;
       [ | eapply weakened_nseq_refl].
     econstructor; [ | econstructor].
     eapply weak_seq_baseL.
     econstructor.
     eapply weak_multi_step;
     [ | eapply weak_multi_refl].
     econstructor; reflexivity.

     list_assoc_r_single.
     repeat (try eapply weakened_nseq_app; try
     eapply weakened_nseq_refl).
     econstructor; [ | econstructor].
     eapply weak_seq_baseR.
     econstructor.
     econstructor; [ | econstructor].
     weak_tacX.
   }
   Unshelve. solve_eqs.

     +{ list_assoc_r_single.
     eapply derI.
     eapply prop.
     econstructor.
     list_assoc_l.
     rewrite <- (app_assoc _ H2).
     rewrite <- (app_assoc _ [Imp _ _]).
     eapply Sctxt_eq. 
     eapply ImpR_pfc. simpl.
     reflexivity. reflexivity. reflexivity.
     econstructor; [ | econstructor].
     simpl. list_assoc_r_single.
     rewrite (app_assoc Φ1).
     rewrite (app_assoc (Φ1 ++ _)).
     solve_HSR_except_D3 HSR D2 D3 Hdp'.

     (* weakend then apply D3. TODO: generalise. *)
     eapply derrec_weakened_nseq;
       [ |
         eapply derrec_weakened_nseq; 
           [ |
             eapply D3]].
     assoc_mid [AA].          
     rewrite <- (app_assoc GH).
     eapply weakened_nseq_app.
     eapply weakened_nseq_refl.
     eapply weakened_nseq_app;
       [ | eapply weakened_nseq_refl].
     econstructor; [ | econstructor].
     eapply weak_seq_baseL.
     econstructor.
     eapply weak_multi_step;
     [ | eapply weak_multi_refl].
     econstructor; reflexivity.

     list_assoc_r_single.
     repeat (try eapply weakened_nseq_app; try
     eapply weakened_nseq_refl).
     assoc_mid [BB].
     econstructor; [ | econstructor].
     eapply weak_seq_baseR.
     econstructor.
     econstructor; [ | econstructor].
     weak_tacX.
   }
      Unshelve. solve_eqs.

     +{
         list_assoc_r_single.
        list_assoc_l.
     eapply derI.
     eapply prop.
     econstructor.
     list_assoc_r_single.
     eapply Sctxt_eq. 
     eapply ImpR_pfc. simpl.
     reflexivity. reflexivity. reflexivity.
     unfold nslcext.
     econstructor; [ | econstructor].
     simpl. list_assoc_r_single.
     solve_HSR HSR D2 D3 Hdp'.
       } Unshelve. solve_eqs.
Qed.

 *)
