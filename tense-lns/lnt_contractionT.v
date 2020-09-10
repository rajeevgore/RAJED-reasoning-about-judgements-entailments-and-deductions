Require Import ssreflect.
 
Require Import gen genT.
Require Import ddT.
Require Import List_lemmasT.
Require Import gen_tacs lntT lntacsT lntlsT lntbRT lntmtacsT.
Require Import lntb1LT lntb2LT.
Require Import lnt_weakeningT.
Require Import lntkt_exchT.
Require Import swappedT existsT.
Require Import contractedT.


(* ---------------------------- *)
(* LEFT CONTRACTION DEFINITIONS *)
(* ---------------------------- *)

Definition can_gen_contL {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 a Δ,
  ns = G ++ (seq, d) :: K -> seq = pair (Γ1 ++ [a;a] ++ Γ2) Δ ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ [a] ++ Γ2) Δ, d) :: K).

Definition can_gen_contL_genL {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 a Δ,
    ns = G ++ (seq, d) :: K ->
    (seq = pair (Γ1 ++ [a] ++ Γ2 ++ [a] ++ Γ3) Δ) ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ [a] ++ Γ2 ++ Γ3) Δ, d) :: K) .

Definition can_gen_contL_genR {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 a Δ,
  ns = G ++ (seq, d) :: K -> seq = pair (Γ1 ++ [a] ++ Γ2 ++ [a] ++ Γ3) Δ ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ Γ2 ++ [a] ++ Γ3) Δ, d) :: K).

Definition can_gen_contL_gen {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 a Δ,
    ns = G ++ (seq, d) :: K ->
    (seq = pair (Γ1 ++ [a] ++ Γ2 ++ [a] ++ Γ3) Δ) ->
  (derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ [a] ++ Γ2 ++ Γ3) Δ, d) :: K)) *
  (derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ Γ2 ++ [a] ++ Γ3) Δ, d) :: K)).

Definition gen_contL_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_contL rules) ps -> rsub last_rule rules -> 
  can_gen_contL rules concl.

Definition gen_contL_gen_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_contL_gen rules) ps -> rsub last_rule rules -> 
  can_gen_contL_gen rules concl.

Lemma can_gen_contL_def': forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  iffT (can_gen_contL rules ns) (forall G K seq Γ Δ Γ' (d : dir), 
  contracted Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K)).
Proof.
  intros.  unfold iffT. unfold can_gen_contL.
  split ; intros X; intros until 0;  intros H H0.
  intros H1. inversion H. subst. unfold can_gen_contL in X.
  eapply X. reflexivity.  reflexivity.
  subst. eapply X. 2 : reflexivity. 2 : reflexivity.
  apply contracted_I'.
Qed.

Lemma can_gen_contL_gen_def': forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  iffT (can_gen_contL_gen rules ns) (forall G K seq Γ Δ Γ' (d : dir), 
  contracted_gen Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K)).
Proof.
  intros.  unfold iffT. unfold can_gen_contL_gen.
  split ; intros X; intros until 0; intros H H0. 
  intros H1. destruct H. subst. eapply X. reflexivity.    
  reflexivity. subst. eapply X. reflexivity.
  reflexivity. subst. split. eapply X. 2 : reflexivity.
  2 : reflexivity. apply contracted_genL_I'.
  eapply X. 2 : reflexivity. 2: reflexivity.
  eapply contracted_genR_I'.
Qed.

(* ----------------------------- *)
(* RIGHT CONTRACTION DEFINITIONS *)
(* ----------------------------- *)

Definition can_gen_contR {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 a,
    ns = G ++ (seq, d) :: K -> seq = pair Γ (Δ1 ++ [a;a] ++ Δ2)->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ [a] ++ Δ2), d) :: K).

Definition gen_contR_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_contR rules) ps -> rsub last_rule rules -> 
  can_gen_contR rules concl.

Lemma can_gen_contR_def': forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  iffT (can_gen_contR rules ns) (forall G K seq Γ Δ Δ' (d : dir), 
  contracted Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K)).
Proof.
  intros.  unfold iffT.  unfold can_gen_contR.
  split ; intros X; intros until 0; intros H0 H1.
  intros H2. inversion H0. subst. eapply X.
  reflexivity. reflexivity. subst. eapply X.
  2 : reflexivity. 2 : reflexivity.
  eapply contracted_I'.
Qed.

Definition can_gen_contR_genL {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 Δ3 a,
    ns = G ++ (seq, d) :: K ->
    seq = pair Γ (Δ1 ++ [a] ++ Δ2 ++ [a] ++ Δ3) ->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ [a] ++ Δ2 ++ Δ3), d) :: K) .

Definition can_gen_contR_genR {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 Δ3 a,
    ns = G ++ (seq, d) :: K ->
    seq = pair Γ (Δ1 ++ [a] ++ Δ2 ++ [a] ++ Δ3) ->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ Δ2 ++ [a] ++ Δ3), d) :: K) .

Definition can_gen_contR_gen {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 Δ3 a,
    ns = G ++ (seq, d) :: K ->
    seq = pair Γ (Δ1 ++ [a] ++ Δ2 ++ [a] ++ Δ3) ->
  (derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ [a] ++ Δ2 ++ Δ3), d) :: K)) *
  (derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ Δ2 ++ [a] ++ Δ3), d) :: K)).

Definition gen_contR_gen_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_contR_gen rules) ps -> rsub last_rule rules -> 
  can_gen_contR_gen rules concl.

Lemma can_gen_contR_gen_def': forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  iffT (can_gen_contR_gen rules ns) (forall G K seq Γ Δ Δ' (d : dir), 
  contracted_gen Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K)).
Proof.
  intros.  unfold iffT. unfold can_gen_contR_gen.
  split ; intros X; intros until 0; intros H0 H1.
  intros H2.  destruct H0; subst; eapply X; reflexivity.    
  split; subst; eapply X; auto.
  apply contracted_genL_I'.
  apply contracted_genR_I'.
Qed.

(* --------------- *)
(* SWAPPED TACTICS *)
(* --------------- *)

(*
Move to swapped.v once assoc_mid is moved to List_lemmas.v 
*)

Ltac swapped_gen_tac_pre :=
 match goal with
  | [ |- swapped_gen ?l1 ?l2] =>
    match l1 with
    | ?A ++ ?B =>
      match l2 with
      | ?A ++ ?C => apply swapped_gen_app_L (* strip off front *)
      | _ => let t := fresh "t" in remember l1 as t;
                 assoc_mid A; subst t; apply swapped_gen_front_mid
      end
    end
 end.

Ltac swap_gen_tac :=
  repeat ( try list_assoc_r_single;
   swapped_gen_tac_pre; try apply swapped_gen_refl).

(* ------------------- *)

Ltac nsgen_sw_cont_gen rs sppc c c' acm inps0 swap :=
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


(* -------------------------------------------------- *)
(* HYPOTHESES USED IN LEFT CONTRACTION FOR PRINCRULES *)
(* -------------------------------------------------- *)

Definition premises_fullLT {V} (ps : list (rel (list (PropF V)))) :=
  (non_empty ps -> ForallT (fun p => fst p <> []) ps).

Definition premises_fullL_sT {V} (s : (rel (list (PropF V)))) :=
non_empty (fst s).

Definition premises_fullL_nsT {V} dir (ps : list (list (rel (list (PropF V)) * dir))) :=
  ForallT (fun ns => ForallT (fun s => premises_fullL_sT (fst s)) ns) ps.

Definition rules_L_carryT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps a x Δ, rules ps (a::x, Δ) ->
                   ForallT (fun ps' => a = hd a (fst ps')) ps.

Definition rules_R_carryT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps a x Γ, rules ps (Γ, a::x) ->
                   ForallT (fun ps' => a = hd a (snd ps')) ps.

Definition rules_L_neT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps c,
    rules ps c -> (non_empty ps -> ForallT (fun p => fst p <> []) ps).

Definition rules_R_neT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps c,
    rules ps c -> non_empty ps -> non_empty (snd c) ->ForallT (fun p => snd p <> []) ps.


Definition rules_L_ocT {W : Set} (rules : rlsT (rel (list W))) :=
forall (ps : list (rel (list W))) a (x Δ : list W),
rules ps (a :: x, Δ) -> x = [].

Lemma loe_imp_loc : forall {V} (princrules : rlsT (rel (list (PropF V)))),
  rules_L_oeT princrules -> rules_L_ocT princrules.
Proof.
  intros V princrules Hoe.
  unfold rules_L_oeT in Hoe.
  intros ps a x l Hrules.
  change (a :: x) with ([a] ++ x) in Hrules.
  apply Hoe in Hrules. destruct Hrules.
  discriminate. assumption.
Qed.

Lemma in_nslcext_seqext : forall  V Φ1 Φ2 Ψ1 Ψ2 l l1 ps G d0,
   InT (l, l1) ps ->
  InT (nslcext G d0 (seqext Φ1 Φ2 Ψ1 Ψ2 (l, l1)))
         (map (nslcext G d0) (map (@seqext V Φ1 Φ2 Ψ1 Ψ2) ps)).
Proof. intros. do 2 apply InT_map. auto. Qed.

Lemma in_nslc_seq : forall {V} ns ps G d0 (Γ1 Γ2 Ψ1 Ψ2 : list (PropF V)),
  iffT (InT ns (map (nslcext G d0)
             (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)))
  (existsT2 p, (ns = (nslcext G d0 (seqext Γ1 Γ2 Ψ1 Ψ2 p))) *
            InT p ps).
Proof.
  induction ps; intros.
  +  simpl. split; intros H. inversion H. 
     destruct H as [[p H] [H2 H3]]. inversion H3. 
  + simpl. split; intros H.
    ++ inversion H as [H1 | H2 H3]; subst.
        exists a.  firstorder. econstructor. auto.
        apply IHps in H0. destruct H0 as [p [H0 H1]].
        exists p. split. auto. constructor 2. auto.
    ++ inversion H as [p [H1 H2]].
       inversion H2 as [ | ? ? H3]; subst.  constructor. reflexivity.
       constructor 2. eapply IHps. eexists. split. reflexivity. assumption.
Qed.

Lemma in_rules_L_carry: forall {V} (princrules : rlsT (rel (list (PropF V))))  ps a l l0 Γ1 Γ2,
    rules_L_carryT princrules ->
    rules_L_neT princrules ->
    princrules ps (a::l, l0) ->
    InT (Γ1, Γ2) ps ->
    InT a Γ1.
Proof.
  intros until 0; intros H1 H2 H3 H4.
  unfold rules_L_carryT in H1.
  unfold rules_L_neT in H2.
  pose proof H3 as H3'. pose proof H3 as H3''.
  eapply H1 in H3. eapply H2 in H3'.
  clear H1 H2. 
  eapply ForallT_forall in H3. 2: exact H4.
  eapply ForallT_forall in H3'. 2 : exact H4.
  simpl in H3. destruct Γ1. contradiction.
  simpl in H3. subst. constructor. reflexivity.
  destruct ps. inversion H4. constructor.
Qed.

Lemma in_rules_R_carry: forall {V} (princrules : rlsT (rel (list (PropF V))))  ps a l l0 Γ1 Γ2,
    rules_R_carryT princrules ->
    rules_R_neT princrules -> 
    princrules ps (l0, a::l) ->
    InT (Γ1, Γ2) ps ->
    InT a Γ2.
Proof.
  intros until 0; intros H1 H2 H3 H4.
  unfold rules_R_carryT in H1.
  unfold rules_R_neT in H2.
  pose proof H3 as H3'. pose proof H3 as H3''.
  eapply H1 in H3. eapply H2 in H3'.
  clear H1 H2. 
  eapply ForallT_forall in H3. 2: exact H4.
  eapply ForallT_forall in H3'. 2 : exact H4.
  simpl in H3. destruct Γ2. contradiction.
  simpl in H3. subst. constructor. reflexivity.
  destruct ps. inversion H4. constructor.
  simpl. auto.
Qed.

Lemma rules_L_oe_cons_nil_blind : forall {V} princrules ps a l1 l2,
    @rules_L_oeT V princrules -> 
    princrules ps (a :: l1, l2) ->
    l1 = nil.
Proof.
  intros until 0; intros H1 H2.
  unfold rules_L_oeT in H1.
  change (a :: l1) with ([a] ++ l1) in H2.
  eapply H1 in H2. destruct H2.
  discriminate. assumption.
Qed.

Lemma rules_R_oe_cons_nil_blind : forall {V} princrules ps a l1 l2,
    @rules_R_oeT V princrules -> 
    princrules ps (l1, a :: l2) ->
    l2 = nil.
Proof.
  intros until 0; intros H1 H2.
  unfold rules_R_oe in H1.
  change (a :: l2) with ([a] ++ l2) in H2.
  eapply H1 in H2. destruct H2.
  discriminate. assumption.
Qed.


(* ------------------------------- *)
(* LEFT CONTRACTION FOR PRINCRULES *)
(* ------------------------------- *)

Ltac solve_prop_cont_pr1 :=
  intros until 0; intros Hcarry Hne Hrsub pr HF;
  edestruct Forall_forall as [fwd rev];
  pose proof (fwd HF) as Hcont; clear fwd rev;
  apply dersrec_forall; intros c Hin;
  apply in_nslc_seq in Hin;
  destruct Hin as [[Γ1 Γ2] [Heq Hin]];
  subst; specialize Hin as Hin';
  eapply in_nslcext_seqext in Hin;
  eapply Hcont in Hin;
  (eapply can_gen_contL_gen_def' in Hin ||
   eapply can_gen_contR_gen_def' in Hin);                                    
  [exact Hin | | reflexivity | reflexivity].

Ltac solve_prop_cont_pr1T :=
  intros until 0; intros Hcarry Hne Hrsub pr HF;
  edestruct ForallT_forall as [fwd rev];
  pose proof (fwd HF) as Hcont; clear fwd rev;
  apply dersrec_forall; intros c Hin;
  apply in_nslc_seq in Hin;
  destruct Hin as [[Γ1 Γ2] [Heq Hin]];
  subst; specialize Hin as Hin';
  eapply in_nslcext_seqext in Hin;
  eapply Hcont in Hin;
  (eapply can_gen_contL_gen_def' in Hin ||
   eapply can_gen_contR_gen_def' in Hin);                                    
  [exact Hin | | reflexivity | reflexivity].

Ltac solve_prop_cont :=
  intros until 0; intros HF;
  edestruct Forall_forall as [fwd rev];
  pose proof (fwd HF) as Hcont; clear fwd rev;
  apply dersrec_forall; intros c Hin;
  apply in_nslc_seq in Hin;
  destruct Hin as [[Γ1 Γ2] [Heq Hin]];
  subst; specialize Hin as Hin';
  eapply in_nslcext_seqext in Hin;
  eapply Hcont in Hin;
  (eapply can_gen_contL_gen_def' in Hin ||
   eapply can_gen_contR_gen_def' in Hin);                                    
  [exact Hin | | reflexivity | reflexivity].

Ltac solve_prop_contT :=
  intros until 0; intros HF;
  edestruct ForallT_forall as [fwd rev];
  pose proof (fwd HF) as Hcont; clear fwd rev;
  apply dersrec_forall; intros c Hin;
  apply in_nslc_seq in Hin;
  destruct Hin as [[Γ1 Γ2] [Heq Hin]];
  subst; specialize Hin as Hin';
  eapply in_nslcext_seqext in Hin;
  eapply Hcont in Hin;
  (eapply can_gen_contL_gen_def' in Hin ||
   eapply can_gen_contR_gen_def' in Hin);                                    
  [exact Hin | | reflexivity | reflexivity].

Ltac solve_prop_contL_pr2 thm Hin' Hcarry Hne pr:=
  (eapply in_rules_L_carry in Hin'); [| exact Hcarry | exact Hne | exact pr];
  list_assoc_r_single;  apply thm; exact Hin'.

Ltac solve_prop_contR_pr2 thm Hin' Hcarry Hne pr:=
  (eapply in_rules_R_carry in Hin'); [| exact Hcarry | exact Hne | exact pr];
  list_assoc_r_single;  apply thm; exact Hin'.

Lemma prop_contL_step_pr_L: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
ForallT (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (H5 ++ [a] ++ C) A Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext (H5 ++ C) (A) Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contL_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_R: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
ForallT (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext A (H5 ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext (A) (H5 ++ C) Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contL_pr2 (@contracted_gen_in4 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_L_end: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
 ForallT (can_gen_contL_gen rules)
          (map (nslcext G d0) (map (seqext (A ++ [a]) C Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A) C Ψ1 Ψ2) ps)).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contL_pr2 (@contracted_gen_in2 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_R_start: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
ForallT (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext A ([a] ++ C) Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext A C Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contL_pr2 (@contracted_gen_in3 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step1: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_R_carryT princrules ->
  rules_R_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
ForallT (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (H5 ++ [a] ++ C) A) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (H5 ++ C) A) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contR_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step1_OPP: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_R_carryT princrules ->
  rules_R_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
ForallT (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A (H5 ++ [a] ++ C)) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A (H5 ++ C)) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contR_pr2 (@contracted_gen_in4 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step4: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_R_carryT princrules ->
  rules_R_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
 ForallT (can_gen_contR_gen rules)
          (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a]) C) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A) C) ps)).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contR_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step2: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_R_carryT princrules ->
  rules_R_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
ForallT (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A ([a] ++ C)) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A C) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contR_pr2 (@contracted_gen_in3 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_BL: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 ForallT (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ D) Ψ1 Ψ2) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contL_step_BR: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 ForallT (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contL_step_LL: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 ForallT (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ C) Γ Ψ1 Ψ2) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contL_step_LR: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 ForallT (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contL_step_RL: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 ForallT (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ C) Ψ1 Ψ2) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contL_step_RR: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 ForallT (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Γ (A ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contR_step_BL: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 ForallT (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B) (C ++ [a] ++ D)) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B) (C ++ D)) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contR_step_BR: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 ForallT (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B) (C ++ [a] ++ D)) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ B) (C ++ [a] ++ D)) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contR_step_LL: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 ForallT (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B ++ [a] ++ C) Γ) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B ++ C) Γ) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contR_step_LR: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 ForallT (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B ++ [a] ++ C) Γ) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ B ++ [a] ++ C) Γ) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contR_step_RL: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 ForallT (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 Γ (A ++ [a] ++ B ++ [a] ++ C)) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 Γ (A ++ [a] ++ B ++ C)) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Lemma prop_contR_step_RR: forall {V} (rules : rlsT (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 ForallT (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 Γ (A ++ [a] ++ B ++ [a] ++ C)) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 Γ (A ++ B ++ [a] ++ C)) ps)).
Proof.
  solve_prop_contT.
  apply (@contracted_gen__spec _ a).
  cont_solve.
Qed.

Ltac contL_make_gen_L_hyp :=
  match goal with
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B => add_empty_hyp_L l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | [?a] ++ ?B => add_empty_hyp_L l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contL_make_gen_L_hypT :=
  match goal with
  | [ Hcont :  ForallT (can_gen_contL_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B => add_empty_hyp_L l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | [?a] ++ ?B => add_empty_hyp_L l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contR_make_gen_L_hyp :=
  match goal with
  | [ Hcont :  Forall (can_gen_contR_gen ?rules)
                      (map ?nsl (map (seqext ?Ψ1 ?Ψ2 ?l1 ?l2 ) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?Ψ1 ?Ψ2 ?l1' ?l2') ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B => add_empty_hyp_L l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | [?a] ++ ?B => add_empty_hyp_L l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contR_make_gen_L_hypT :=
  match goal with
  | [ Hcont :  ForallT (can_gen_contR_gen ?rules)
                      (map ?nsl (map (seqext ?Ψ1 ?Ψ2 ?l1 ?l2 ) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?Ψ1 ?Ψ2 ?l1' ?l2') ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B => add_empty_hyp_L l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | [?a] ++ ?B => add_empty_hyp_L l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contL_make_gen_R_hyp :=
  match goal with
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | ?B ++ [?a] => add_empty_hyp_R l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | ?B ++ [?a] => add_empty_hyp_R l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contR_make_gen_R_hyp :=
  match goal with
  | [ Hcont :  Forall (can_gen_contR_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | ?B ++ [?a] => add_empty_hyp_R l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | ?B ++ [?a] => add_empty_hyp_R l1 Hcont
    | _ => idtac 
    end
  end.

Lemma can_gen_swapL_derrec_spec : forall {V} n rules G d0 Γ Ψ Γ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules ns) ->
  swapped_spec n Γ Γ' ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ, Ψ)) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ', Ψ)).
Proof.
  induction n; intros until 0; intros Hcan Hswap Hder.
  inversion Hswap. subst.
  eapply can_gen_swapL_imp. apply Hcan. apply Hder.
  apply H. reflexivity. reflexivity.
  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapL_imp. apply Hcan. apply H0.
  apply H1. reflexivity.
  reflexivity. assumption. assumption.
Qed.

Lemma can_gen_swapR_derrec_spec : forall {V} n rules G d0 Γ Ψ Ψ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapR rules ns) ->
  swapped_spec n Ψ Ψ' ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ, Ψ)) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ, Ψ')).
Proof.
  induction n; intros until 0; intros Hcan Hswap Hder.
  inversion Hswap. subst.
  eapply can_gen_swapR_imp. apply Hcan. apply Hder.
  apply H. reflexivity. reflexivity.
  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapR_imp. apply Hcan. apply H0.
  apply H1. reflexivity.
  reflexivity. assumption. assumption.
Qed.

Lemma can_gen_swapL_derrec_nslcext : forall {V} rules G d0 seq1 seq2 Γ Ψ Γ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules ns) ->
  swapped Γ Γ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ', Ψ) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  intros until 0. intros Hexch Hswap Hs1 Hs2 Hd.
  subst. eapply can_gen_swapL_derrec_spec; auto.
  eapply swapped_spec_I. exact Hswap.
  exact Hd.
Qed.

Lemma can_gen_swapR_derrec_nslcext : forall {V} rules G d0 seq1 seq2 Γ Ψ Ψ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapR rules ns) ->
  swapped Ψ Ψ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ, Ψ') ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  intros until 0. intros Hexch Hswap Hs1 Hs2 Hd.
  subst. eapply can_gen_swapR_derrec_spec; auto.
  eapply swapped_spec_I. exact Hswap.
  exact Hd.
Qed.

Lemma can_gen_swapL_derrec_nslcext_spec : forall {V} n rules G d0 seq1 seq2 Γ Ψ Γ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules ns) ->
  swapped_spec n Γ Γ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ', Ψ) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  induction n; intros until 0; intros Hexch Hswap Hs1 Hs2 Hd.
  subst; eapply can_gen_swapL_derrec_nslcext in Hd.
  exact Hd. exact Hexch. inversion Hswap. exact H.
  reflexivity. reflexivity.

  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapL_derrec_nslcext in H0.
  exact H0. exact Hexch. exact H1.
  reflexivity. reflexivity.
  exact Hexch. reflexivity. reflexivity.
  exact Hd.
Qed.

Lemma can_gen_swapR_derrec_nslcext_spec : forall {V} n rules G d0 seq1 seq2 Ψ Ψ' Γ,
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapR rules ns) ->
  swapped_spec n Ψ Ψ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ, Ψ') ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  induction n; intros until 0; intros Hexch Hswap Hs1 Hs2 Hd.
  subst; eapply can_gen_swapR_derrec_nslcext in Hd.
  exact Hd. exact Hexch. inversion Hswap. exact H.
  reflexivity. reflexivity.

  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapR_derrec_nslcext in H0.
  exact H0. exact Hexch. exact H1.
  reflexivity. reflexivity.
  exact Hexch. reflexivity. reflexivity.
  exact Hd.
Qed.

Lemma can_gen_swapL_derrec_nslcext_gen : forall {V} rules G d0 seq1 seq2 Γ Ψ Γ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules ns) ->
  swapped_gen Γ Γ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ', Ψ) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  intros until 0; intros Hexch Hswap Hs1 Hs2 Hd.
  inversion Hswap as [H]. destruct H as [n H].
  eapply can_gen_swapL_derrec_nslcext_spec in Hd.
  exact Hd. exact Hexch. exact H. exact Hs1. exact Hs2.
Qed.

Lemma can_gen_swapR_derrec_nslcext_gen : forall {V} rules G d0 seq1 seq2 Ψ Ψ' Γ,
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapR rules ns) ->
  swapped_gen Ψ Ψ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ, Ψ') ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  intros until 0; intros Hexch Hswap Hs1 Hs2 Hd.
  inversion Hswap as [H]. destruct H as [n H].
  eapply can_gen_swapR_derrec_nslcext_spec in Hd.
  exact Hd. exact Hexch. exact H. exact Hs1. exact Hs2.
Qed.

Lemma can_gen_swapL_derrec : forall {V} l rules G d0 Γ1 Γ2 Ψ Γ1' Γ2',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules ns) ->
  swapped (Γ1 ++ Γ2) (Γ1' ++ Γ2') ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ1 ++ l ++ Γ2, Ψ)) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ1' ++ l ++ Γ2', Ψ)).
Proof.
  intros until 0. intros Hcan Hswap Hder.
  eapply swapped_spec_I in Hswap.
  eapply swapped__n_mid in Hswap.
  destruct Hswap as [n HH]. 
  eapply can_gen_swapL_derrec_spec.
  apply Hcan. 2 : apply Hder.
  exact HH. 
Qed.

Lemma can_gen_swapR_derrec : forall {V} l rules G d0 Ψ1 Ψ2 Γ Ψ1' Ψ2',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapR rules ns) ->
  swapped (Ψ1 ++ Ψ2) (Ψ1' ++ Ψ2') ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ, Ψ1 ++ l ++ Ψ2)) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ, Ψ1' ++ l ++ Ψ2')).
Proof.
  intros until 0. intros Hcan Hswap Hder.
  eapply swapped_spec_I in Hswap.
  eapply swapped__n_mid in Hswap.
  destruct Hswap as [n HH]. 
  eapply can_gen_swapR_derrec_spec.
  apply Hcan. 2 : apply Hder.
  exact HH. 
Qed.

Lemma can_gen_swapL_dersrec : forall {V} rules G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2' ps,
(forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    swapped (Γ1 ++ Γ2) (Γ1' ++ Γ2') ->
    dersrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
            (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
    dersrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
            (map (nslcext G d0) (map (seqext Γ1' Γ2' Ψ1 Ψ2) ps)).
Proof.
  induction ps; intros Hcan Hswap Hder.
  simpl in *. exact Hder.
  destruct a. simpl in *.
  inversion Hder. subst.
  apply dlCons; auto. 
  unfold nslcext.
  eapply can_gen_swapL_derrec in X.
  exact X. exact Hcan. exact Hswap.
Qed.

Lemma can_gen_swapR_dersrec : forall {V} rules G d0 Γ1 Γ2 Ψ1 Ψ2 Ψ1' Ψ2' ps,
(forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapR rules ns) ->
    swapped (Ψ1 ++ Ψ2) (Ψ1' ++ Ψ2') ->
    dersrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
            (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
    dersrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
            (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1' Ψ2') ps)).
Proof.
  induction ps; intros Hcan Hswap Hder.
  simpl in *. exact Hder.
  destruct a. simpl in *.
  inversion Hder. subst.
  apply dlCons; auto. 
  unfold nslcext.
  eapply can_gen_swapR_derrec in X.
  exact X. exact Hcan. exact Hswap.
Qed.

Ltac look_for_swapL Hexch :=
  match goal with
  | [ Hcont :  dersrec ?rules ?f  (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules ?f (map ?nscl (map (seqext ?Γ1' ?Γ2' ?Ψ1 ?Ψ2) ?ps)) ]
    =>
    match Γ1' with
    | Γ1 => exact Hcont
    | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch|  swap_tac | list_assoc_r_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
    end;
    try 
      match Γ2' with
      | Γ2 => exact Hcont
      | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch | swap_tac | list_assoc_r_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
      end
  end.


Ltac look_for_swapR Hexch :=
  match goal with
  | [ Hcont :  dersrec ?rules ?f  (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules ?f (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1' ?Ψ2') ?ps)) ]
    =>
    match Ψ1' with
    | Ψ1 => exact Hcont
    | _  => eapply (can_gen_swapR_dersrec _ _ _ _ _ Ψ1); [exact Hexch|  swap_tac | list_assoc_r_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
    end;
    try 
      match Ψ2' with
      | Ψ2 => exact Hcont
      | _  => eapply (can_gen_swapR_dersrec _ _ _ _ _ Ψ1); [exact Hexch | swap_tac | list_assoc_r_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
      end
  end.

Ltac breakdownT :=
  repeat (
      repeat (match goal with
              | [ H : ?A ++ ?B = ?x ++ ?y |- _ ] => apply app_eq_appT2 in H; sD; subst
              end) ;
      repeat (match goal with
              | [H2 : [?a] = ?A ++ ?B |- _ ] => apply unit_eq_appT in H2; sD; subst
              end));
  repeat try rewrite app_nil_r; repeat try rewrite app_nil_l;
  repeat (match goal with
          | [ H3 : context[ ?x ++ [] ] |- _ ] => rewrite (app_nil_r x) in H3
          end);
  repeat (match goal with
          | [ H3 : context[ [] ++ ?x ] |- _ ] => rewrite (app_nil_l x) in H3
          end).


Lemma can_gen_contL_gen_Forall_dersrec : forall  {V}  a (rules : rlsT (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2',
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    contracted_gen_spec a (Γ1 ++ Γ2) (Γ1' ++ Γ2')->
  ForallT (can_gen_contL_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  dersrec rules (fun _ => False)
         (map (nslcext G d0) (map (seqext Γ1' Γ2' Ψ1 Ψ2) ps)).
Proof.
  intros until 0. intros Hexch Hcon Hcont.
  inversion  Hcon; subst.
  { breakdownT; clear Hcon;
      contL_make_gen_L_hypT;
      try solve [(eapply prop_contL_step_RL in Hcont; look_for_swapL Hexch)];
      try solve[(eapply prop_contL_step_BL in Hcont;  look_for_swapL Hexch)];
      try solve [eapply prop_contL_step_LL in Hcont; look_for_swapL Hexch].
  }
  { breakdownT; clear Hcon;
      contL_make_gen_L_hypT;
      try solve [(eapply prop_contL_step_RR in Hcont; look_for_swapL Hexch)];
      try solve[(eapply prop_contL_step_BR in Hcont;  look_for_swapL Hexch)];
      try solve [eapply prop_contL_step_LR in Hcont; look_for_swapL Hexch].
  }
Qed.

Lemma can_gen_contR_gen_Forall_dersrec : forall  {V}  a (rules : rlsT (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Ψ1' Ψ2',
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapR rules ns) ->
    contracted_gen_spec a (Ψ1 ++ Ψ2) (Ψ1' ++ Ψ2')->
  ForallT (can_gen_contR_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  dersrec rules (fun _ => False)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1' Ψ2') ps)).
Proof.
  intros until 0. intros Hexch Hcon Hcont.
  inversion  Hcon; subst.
  { breakdownT; clear Hcon;
      contR_make_gen_L_hypT;
      try solve [(eapply prop_contR_step_RL in Hcont; look_for_swapR Hexch)];
      try solve[(eapply prop_contR_step_BL in Hcont;  look_for_swapR Hexch)];
      try solve [eapply prop_contR_step_LL in Hcont; look_for_swapR Hexch].
  }
  { breakdownT; clear Hcon;
      contR_make_gen_L_hypT;
      try solve [(eapply prop_contR_step_RR in Hcont; look_for_swapR Hexch)];
      try solve[(eapply prop_contR_step_BR in Hcont;  look_for_swapR Hexch)];
      try solve [eapply prop_contR_step_LR in Hcont; look_for_swapR Hexch].
  }
Qed.

Ltac derrec_swapL3 acm exch :=
      eapply (can_gen_swapL_derrec_nslcext_gen) in acm;
      [exact acm | exact exch | | reflexivity | reflexivity ]; swap_gen_tac.
Ltac derrec_swapR3 acm exch :=
      eapply (can_gen_swapR_derrec_nslcext_gen) in acm;
      [exact acm | exact exch | | reflexivity | reflexivity ]; swap_gen_tac.

Ltac destruct_princ :=
  match goal with
  | [ |- context[ (nslcext _ _  (seqext _ _ _ _ ?x)) ]] => destruct x
  end.

Lemma Sctxt_e'': forall (W : Type) (pr : rlsT (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) ((Φ1 ++ U) ++ Φ2, (Ψ1 ++ V) ++ Ψ2).
Proof. intros. do 2 rewrite <- app_assoc. apply Sctxt_e. assumption. Qed. 

Ltac nsgen_sw_contL_gen5 rs sppc c c' acm inps0 swap pr inmps exch := 
    derIrs rs  ;
[apply NSlcctxt'; apply Sctxt_e'; exact pr |];
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ;
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 ;
subst;
eapply dersrec_forall in acm;
[| apply inps0];
destruct_princ;
derrec_swapL3 acm exch.


Lemma Sctxt_e''': forall (W : Type) (pr : rlsT (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (Φ1 ++ U ++ Φ2, (Ψ1 ++ V )++ Ψ2).
Proof.
  intros. rewrite <- app_assoc.
  rewrite <- seqext_def. apply Sctxt. assumption.
Qed.  

Ltac nsgen_sw_contR_gen5 rs sppc c c' acm inps0 swap pr inmps exch := 
    derIrs rs  ;
[apply NSlcctxt'; apply Sctxt_e''; exact pr |];
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ;
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 ;
subst;
eapply dersrec_forall in acm;
[| apply inps0];
destruct_princ;
derrec_swapR3 acm exch.

(* Makes progress on princrules ps (l1, l2) goals *)
Ltac lt1 a acm Hexch :=
  list_assoc_r_single;
  eapply (can_gen_contL_gen_Forall_dersrec a) in acm;
  [| exact Hexch | cont_solve].

Ltac lt2 a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : Forall (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Γ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contL_step_pr_L in acm
    | ?A ++ [?a] => eapply prop_contL_step_pr_L_end in acm
    | _ => match Γ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contL_step_pr_R in acm
           | [?a] ++ ?A => eapply prop_contL_step_pr_R_start in acm
           end
    end
  end.


Ltac lt3 a Hexch rs carry psfull loe :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      acm : Forall (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match l1 with
    | context[ a :: [] ] =>
      lt2 a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | context[ a :: ?l2 ] =>
      pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;
      lt2 a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | _ => lt1 a acm Hexch
    end
  end.

Ltac check_nil_contradiction :=
  repeat (try discriminate;
  match goal with
  | [ H : ?l1 ++ ?l2 = [] |- _ ] =>
    apply app_eq_nil_iff in H; destruct H as [H HH]
  end).

Ltac check_contradiction_prL_pre :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Δ : list (PropF ?V)),
            ?princrules ps (x ++ y, Δ) -> x = [] \/ y = [] |- _ ] =>
    match l1 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr; try rewrite app_nil_r in pr
    end
  end.

Ltac check_contradiction_prL_preT :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Δ : list (PropF ?V)),
            ?princrules ps (x ++ y, Δ) -> (x = []) + (y = []) |- _ ] =>
    match l1 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr; try rewrite app_nil_r in pr
    end
  end.

Ltac check_contradiction_prR_pre :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Γ : list (PropF ?V)),
            ?princrules ps (Γ, x ++ y) -> x = [] \/ y = [] |- _ ] =>
    match l2 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr; try rewrite app_nil_r in pr
    end
  end.

Ltac check_contradiction_prR_preT :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Γ : list (PropF ?V)),
            ?princrules ps (Γ, x ++ y) -> (x = []) + (y = []) |- _ ] =>
    match l2 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr; try rewrite app_nil_r in pr
    end
  end.

Ltac check_contradiction_pr :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    repeat (list_assoc_r_singleton_hyp2 pr;
            try check_contradiction_prL_pre;
            try check_contradiction_prR_pre)
  end.

Ltac check_contradiction_prT :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    repeat (list_assoc_r_singleton_hyp2 pr;
            try check_contradiction_prL_preT;
            try check_contradiction_prR_preT)
  end.

Ltac contL_setup_nil :=
  match goal with
    | [ acm : dersrec _ _ (map _ (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
       add_empty_goal_R l1 || (rewrite app_assoc;  add_empty_goal_R l1)
  end.

Ltac contR_setup_nil :=
  match goal with
    | [ acm : dersrec _ _ (map _ (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
       add_empty_goal_R Ψ1 || (rewrite app_assoc;  add_empty_goal_R Ψ1)
  end.


Ltac contL_setup  :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
            rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    match l1 with
    | nil => contL_setup_nil
    | _ => assoc_mid l1; rewrite app_assoc
    end
  end.

Ltac contR_setup  :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
            rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    match l2 with
    | nil => contR_setup_nil
    | _ => assoc_mid l2; rewrite app_assoc
    end
  end.

Ltac contR_setup_extra_pre  :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, []),
            rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    rewrite (app_assoc _ l1)
  end.

Ltac contR_setup_extra :=
  contR_setup; try contR_setup_extra_pre.

Ltac nsgen_sw_cont_genT rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ; subst q ;
rename_last inps0 ;
eapply ForallT_forall in acm ;
[ | eapply InT_map in inps0; exact inps0 ]];
try eapply can_gen_contL_gen_def' in acm ;
  try eapply can_gen_contR_gen_def' in acm ;
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  assoc_single_mid' c' ;
[ eapply acm | exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | (reflexivity || assumption) ].

Ltac tac_cons_singleton_arg_hyp a l H :=
    match l with
    | nil => idtac
    | _ => rewrite (cons_singleton l a) in H
    end.

Ltac tac_cons_singleton_hyps :=
  repeat
  match goal with
   | [ H : context [?a :: ?l] |- _] => progress (tac_cons_singleton_arg_hyp a l H)
  end.

Ltac lt2T a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : ForallT (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Γ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contL_step_pr_L in acm
    | ?A ++ [?a] => eapply prop_contL_step_pr_L_end in acm
    | _ => match Γ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contL_step_pr_R in acm
           | [?a] ++ ?A => eapply prop_contL_step_pr_R_start in acm
           end
    end
  end.

Ltac lt3T a Hexch rs carry psfull loe :=
  lazymatch goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      acm : ForallT (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
   lazymatch l1 with
    | context[ a :: [] ] =>  tac_cons_singleton_hyps;
      lt2T a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | context[ a :: _ ] =>  tac_cons_singleton_hyps ;
                           let H := fresh in 
                           pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr) as H; rewrite H in pr;
                           try rewrite app_nil_r in H; subst ;
      lt2T a Hexch; [| exact carry | exact psfull| exact rs| exact pr] 
    | _ => tac_cons_singleton_hyps; lt1 a acm Hexch
    end
  end.

 Ltac nsgen_sw_contL_gen5T rs sppc c c' acm inps0 swap pr inmps exch := 
    derIrs rs  ;
[apply NSlcctxt'; apply Sctxt_e'; exact pr |];
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ; 
rename_last inmps ;
eapply InT_map_iffT in inmps ; cD ;
rename_last inps0 ;  eapply InT_map in inps0 ;
  eapply InT_map in inps0 ;
subst;
eapply dersrec_forall in acm;
[| apply inps0];
destruct_princ;
derrec_swapL3 acm exch.

Lemma gen_contL_gen_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  rules_L_oeT princrules -> 
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  (forall ns : list (rel (list (PropF V)) * dir),
      derrec rules (fun _ => False) ns ->
      can_gen_swapL rules ns) ->
  last_rule = nslcrule (seqrule princrules) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contL_step.
intros loe carry psfull exch lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
eapply can_gen_contL_gen_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2T in pp.

destruct c.
sD ; subst.

{ nsgen_sw_cont_genT rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{ inversion pp1. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oeT in loe.
inversion_clear swap ; subst.
{
  (* do as much as possible for all rules at once *)
acacD'T2 ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_ncT || (pose pr as Qpr ; apply loe in Qpr)) ;
        sD ; subst  ; simpl in pr);
rem_nil;
try solve [check_contradiction_prT];
try solve [
 lt3T a exch rs carry psfull loe;
 repeat rewrite app_nil_l; contL_setup;
 nsgen_sw_contL_gen5T rs sppc c c' acm inps0 swap pr inmps exch].

}

{
(* do as much as possible for all rules at once *)
acacD'T2 ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_ncT || (pose pr as Qpr ; apply loe in Qpr)) ;
        sD ; subst  ; simpl in pr);
rem_nil;
try solve [check_contradiction_prT];
try (lt3T a exch rs carry psfull loe; repeat rewrite app_nil_l; contL_setup; 
    nsgen_sw_contL_gen5T rs sppc c c' acm inps0 swap pr inmps exch).
}
}
{ list_eq_nc. contradiction. }

Qed.

Lemma princrule_pfc_L_carry : forall {V : Set} ps a x Δ,
  princrule_pfc ps (a :: x, Δ) ->
  ForallT (fun ps' : list (PropF V) * list (PropF V) => a = hd a (fst ps')) ps.
Proof.
  intros until 0; intros H; inversion H; subst;
    repeat constructor; reflexivity.
Qed.

Lemma princrule_pfc_R_carry : forall {V : Set} ps a x Γ,
  princrule_pfc ps (Γ, a :: x) ->
  ForallT (fun ps' : list (PropF V) * list (PropF V) => a = hd a (snd ps')) ps.
Proof.
  intros until 0; intros H; inversion H; subst;
    repeat constructor; reflexivity.
Qed.

Lemma princrule_pfc_L_carry' : forall V,
    rules_L_carryT (@princrule_pfc V).
Proof.
  unfold rules_L_carryT.  intros until 0; intros H.
  eapply princrule_pfc_L_carry.  exact H.
Qed.

Lemma princrule_pfc_R_carry' : forall V,
    rules_R_carryT (@princrule_pfc V).
Proof.
  unfold rules_R_carryT.  intros until 0; intros H.
  eapply princrule_pfc_R_carry.  exact H.
Qed.


Lemma princrule_pfc_L_ne : forall {V : Set} ps C,
  princrule_pfc ps C ->
  non_empty ps ->
  ForallT (fun p : list (PropF V) * list (PropF V) => fst p <> []) ps.
Proof.
  intros until 0; intros H1 H2; inversion H1; subst;
    repeat constructor; discriminate.
Qed.

Lemma princrule_pfc_L_ne' : forall V, rules_L_neT (@princrule_pfc V).
Proof.
  unfold rules_L_neT. intros until 0; intros H1 H2.
  eapply princrule_pfc_L_ne. exact H1. exact H2. 
Qed.

Lemma princrule_pfc_R_ne : forall {V : Set} ps C,
  princrule_pfc ps C ->
  non_empty ps ->
  non_empty (snd C) ->
  ForallT (fun p : list (PropF V) * list (PropF V) => snd p <> []) ps.
Proof.
  intros until 0; intros H1 H2.
  inversion H1; subst;
    repeat constructor.
  discriminate. inversion H. discriminate.
Qed.
  
Lemma princrule_pfc_R_ne' : forall V, rules_R_neT (@princrule_pfc V).
Proof.
  intros until 0; intros H1 H2.
  eapply princrule_pfc_R_ne. 
Qed.

(* New pr rules. *)
Lemma gen_contL_gen_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hswap Hl H2 H3 H4 H5.
  subst.
  eapply gen_contL_gen_step_loe_lc.
  apply princrule_pfc_L_oe'T.
  apply princrule_pfc_L_carry'. 
  apply princrule_pfc_L_ne'.
  exact Hswap.
  reflexivity.
  exact H2.
  all : assumption.
Qed.

Lemma rsub_princrule_pfc_LNSKt_rules : forall V,
  rsub (nslcrule (seqrule (princrule_pfc (V:=V)))) (LNSKt_rules (V:=V)).
Proof. 
  unfold rsub. intros V u v H. 
  eapply prop. exact H.
Qed.


(* ------------------------------ *)
(* RIGHT WEAKENING FOR PRINCRULES *)
(* ------------------------------ *)

(* Makes progress on princrules ps (l1, l2) goals *)
Ltac lt1R a acm Hexch :=
  list_assoc_r_single;
  eapply (can_gen_contR_gen_Forall_dersrec a) in acm; [| exact Hexch | cont_solve].

Ltac lt2R a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : Forall (can_gen_contR_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Ψ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contR_step1 in acm
    | ?A ++ [?a] => eapply prop_contR_step4 in acm
    | _ => match Ψ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contR_step1_OPP in acm
           | [?a] ++ ?A => eapply prop_contR_step2 in acm
           end
    end
  end.

Ltac lt2RT a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : ForallT (can_gen_contR_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Ψ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contR_step1 in acm
    | ?A ++ [?a] => eapply prop_contR_step4 in acm
    | _ => match Ψ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contR_step1_OPP in acm
           | [?a] ++ ?A => eapply prop_contR_step2 in acm
           end
    end
  end.

Ltac lt3R a Hexch rs carry psfull loe :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      acm : Forall (can_gen_contR_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match l2 with
    | context[ a :: [] ] =>
      lt2R a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | context[ a :: ?l2 ] =>
      pose proof (rules_R_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;
      lt2R a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | _ => lt1R a acm Hexch
    end
  end.

Ltac lt3RT a Hexch rs carry psfull loe :=
  lazymatch goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      acm : ForallT (can_gen_contR_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    lazymatch l2 with
    | context[ a :: [] ] =>
      lt2RT a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | context[ a :: _ ] => tac_cons_singleton_hyps ;
                           let H := fresh in 
                           pose proof (rules_R_oe_cons_nil_blind _ _ _ _ _ loe pr) as H; rewrite H in pr;
                           try rewrite app_nil_r in H; subst ;
      lt2RT a Hexch; [| exact carry | exact psfull| exact rs| exact pr] 
    | _ => tac_cons_singleton_hyps; lt1R a acm Hexch
    end
  end.

Ltac nsgen_sw_contR_gen5T rs sppc c c' acm inps0 swap pr inmps exch := 
    derIrs rs  ;
[apply NSlcctxt'; apply Sctxt_e''; exact pr |];
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ; 
rename_last inmps ;
eapply InT_map_iffT in inmps ; cD ;
rename_last inps0 ;  eapply InT_map in inps0 ;
  eapply InT_map in inps0 ;
subst;
eapply dersrec_forall in acm;
[| apply inps0];
destruct_princ;
derrec_swapR3 acm exch.

Lemma gen_contR_gen_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  rules_R_oeT princrules -> 
  rules_R_carryT princrules ->
  rules_R_neT princrules -> 
  (forall ns : list (rel (list (PropF V)) * dir),
      derrec rules (fun _ => False) ns ->
      can_gen_swapR rules ns) ->
  last_rule = nslcrule (seqrule princrules) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contR_step.
intros loe carry psfull exch lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
eapply can_gen_contR_gen_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2T in pp.

destruct c.
sD ; subst.

{ nsgen_sw_cont_genT rs sppc (l, l0, d) (Γ, Δ', d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection pp1 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oeT in loe.
inversion_clear swap ; subst.
{
unfold rules_R_oeT in loe.
(* do as much as possible for all rules at once *)



acacD'T2 ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
        sD ; subst  ; simpl in pr);
rem_nil;
try solve [check_contradiction_prT];
try (lt3RT a exch rs carry psfull loe; rem_nil; contR_setup_extra;
nsgen_sw_contR_gen5T rs sppc c c' acm inps0 swap pr inmps exch).
}

{
  unfold rules_R_oeT in loe.
(* do as much as possible for all rules at once *)
acacD'T2 ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_ncT || (pose pr as Qpr ; apply loe in Qpr)) ;
        sD ; subst  ; simpl in pr);
rem_nil;
try solve [check_contradiction_prT];
try (lt3RT a exch rs carry psfull loe; rem_nil; contR_setup_extra;
     nsgen_sw_contR_gen5T rs sppc c c' acm inps0 swap pr inmps exch).
}
}
{ list_eq_nc. contradiction. }
Qed.

(* New pr rules. *)
Lemma gen_contR_gen_step_pr_lc: forall V ps concl 
                                       (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapR rules ns) ->
    last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hswap Hl H2 H3 H4 H5.
  subst.
  eapply gen_contR_gen_step_loe_lc.
  apply princrule_pfc_R_oe'T.
  apply princrule_pfc_R_carry'. 
  apply princrule_pfc_R_ne'. 
  exact Hswap.
  reflexivity.
  exact H2.
  all : assumption.
Qed.
