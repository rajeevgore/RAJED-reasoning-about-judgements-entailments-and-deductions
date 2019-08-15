Require Import ssreflect.
 
Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt lntacs lntls lntbR lntmtacs.
Require Import lntb1L lntb2L.
Require Import lnt_weakening.
Require Import lntkt_exch.
Require Import swapped.


Inductive contracted {T} : list T -> list T -> Prop :=
  | contracted_I : forall a (X Y A B : list T), X = (A ++ [a;a] ++ B) -> 
    Y = (A ++ [a] ++ B) -> contracted X Y.

Lemma contracted_I': forall T a (A B : list T),
   contracted (A ++ [a;a] ++ B) (A ++ [a] ++ B).
Proof.  intros.  eapply contracted_I ; reflexivity. Qed.

Inductive contracted_gen {T} : list T -> list T -> Prop :=
| contracted_genL_I : forall a (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ [a] ++ B ++ C) -> contracted_gen X Y
| contracted_genR_I : forall a (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ B ++ [a] ++ C) -> contracted_gen X Y.

Inductive contracted_gen_spec {T} (a : T) : list T -> list T -> Prop :=
| contracted_genL_spec_I : forall (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ [a] ++ B ++ C) -> contracted_gen_spec a X Y
| contracted_genR_spec_I : forall (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ B ++ [a] ++ C) -> contracted_gen_spec a X Y.

Lemma contracted_genL_I': forall T a (A B C : list T),
   contracted_gen (A ++ [a] ++ B ++ [a] ++ C) (A ++ [a] ++ B ++ C).
Proof.  intros.  eapply contracted_genL_I ; reflexivity. Qed.

Lemma contracted_genR_I': forall T a (A B C : list T),
   contracted_gen (A ++ [a] ++ B ++ [a] ++ C) (A ++ B ++ [a] ++ C).
Proof.  intros.  eapply contracted_genR_I ; reflexivity. Qed.

Lemma contracted_genR_spec_I': forall T a (A B C : list T),
   contracted_gen_spec a (A ++ [a] ++ B ++ [a] ++ C) (A ++ B ++ [a] ++ C).
Proof.  intros.  eapply contracted_genR_spec_I ; reflexivity. Qed.

Lemma contracted_genL_spec_I': forall T a (A B C : list T),
   contracted_gen_spec a (A ++ [a] ++ B ++ [a] ++ C) (A ++ [a] ++ B ++ C).
Proof.  intros.  eapply contracted_genL_spec_I ; reflexivity. Qed.

Lemma contracted_gen__spec : forall {T} (a : T) l1 l2,
    contracted_gen_spec a l1 l2 -> contracted_gen l1 l2.
Proof.
  intros until 0; intros H. inversion H;
  [eapply contracted_genL_I |
   eapply contracted_genR_I].
  1,3 : apply H0.
  all : apply H1.
Qed.

(* ---------------------------- *)
(* LEFT CONTRACTION DEFINITIONS *)
(* ---------------------------- *)

Definition can_gen_contL {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 a Δ,
  ns = G ++ (seq, d) :: K -> seq = pair (Γ1 ++ [a;a] ++ Γ2) Δ ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ [a] ++ Γ2) Δ, d) :: K).

Definition can_gen_contL_genL {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 a Δ,
    ns = G ++ (seq, d) :: K ->
    (seq = pair (Γ1 ++ [a] ++ Γ2 ++ [a] ++ Γ3) Δ) ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ [a] ++ Γ2 ++ Γ3) Δ, d) :: K) .

Definition can_gen_contL_genR {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 a Δ,
  ns = G ++ (seq, d) :: K -> seq = pair (Γ1 ++ [a] ++ Γ2 ++ [a] ++ Γ3) Δ ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ Γ2 ++ [a] ++ Γ3) Δ, d) :: K).

Definition can_gen_contL_gen {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 a Δ,
    ns = G ++ (seq, d) :: K ->
    (seq = pair (Γ1 ++ [a] ++ Γ2 ++ [a] ++ Γ3) Δ) ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ [a] ++ Γ2 ++ Γ3) Δ, d) :: K) /\
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ Γ2 ++ [a] ++ Γ3) Δ, d) :: K).

Definition gen_contL_step {V : Set}
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  Forall (can_gen_contL rules) ps -> rsub last_rule rules -> 
  can_gen_contL rules concl.

Definition gen_contL_gen_step {V : Set}
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  Forall (can_gen_contL_gen rules) ps -> rsub last_rule rules -> 
  can_gen_contL_gen rules concl.

Lemma can_gen_contL_def': forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_contL rules ns <-> forall G K seq Γ Δ Γ' (d : dir), 
  contracted Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros.  unfold iff.  split ; intros. 
  destruct H0. subst. unfold can_gen_contL in H.
  eapply H. reflexivity.  reflexivity.
  unfold can_gen_contL. intros. eapply H.
  2: exact H0.  2: exact H1. apply contracted_I'. Qed.

Lemma can_gen_contL_gen_def': forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_contL_gen rules ns <-> forall G K seq Γ Δ Γ' (d : dir), 
  contracted_gen Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros.  unfold iff.  split ; intros. 
  destruct H0; subst; unfold can_gen_contL_gen in H;
  eapply H; reflexivity.    
  unfold can_gen_contL_gen. intros.
  apply conj; subst; eapply H; auto.
  apply contracted_genL_I'.
  apply contracted_genR_I'.
Qed.

(* ----------------------------- *)
(* RIGHT CONTRACTION DEFINITIONS *)
(* ----------------------------- *)

Definition can_gen_contR {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 a,
    ns = G ++ (seq, d) :: K -> seq = pair Γ (Δ1 ++ [a;a] ++ Δ2)->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ [a] ++ Δ2), d) :: K).

Definition gen_contR_step {V : Set}
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  Forall (can_gen_contR rules) ps -> rsub last_rule rules -> 
  can_gen_contR rules concl.

Lemma can_gen_contR_def': forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_contR rules ns <-> forall G K seq Γ Δ Δ' (d : dir), 
  contracted Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K).
Proof.  intros.  unfold iff.  split ; intros. 
  destruct H0. subst. unfold can_gen_contR in H.
  eapply H. reflexivity.  reflexivity.
  unfold can_gen_contR. intros. eapply H.
  2: exact H0.  2: exact H1. apply contracted_I'. Qed.

Definition can_gen_contR_genL {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 Δ3 a,
    ns = G ++ (seq, d) :: K ->
    seq = pair Γ (Δ1 ++ [a] ++ Δ2 ++ [a] ++ Δ3) ->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ [a] ++ Δ2 ++ Δ3), d) :: K) .

Definition can_gen_contR_genR {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 Δ3 a,
    ns = G ++ (seq, d) :: K ->
    seq = pair Γ (Δ1 ++ [a] ++ Δ2 ++ [a] ++ Δ3) ->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ Δ2 ++ [a] ++ Δ3), d) :: K) .

Definition can_gen_contR_gen {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 Δ3 a,
    ns = G ++ (seq, d) :: K ->
    seq = pair Γ (Δ1 ++ [a] ++ Δ2 ++ [a] ++ Δ3) ->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ [a] ++ Δ2 ++ Δ3), d) :: K) /\
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ Δ2 ++ [a] ++ Δ3), d) :: K).

Definition gen_contR_gen_step {V : Set}
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  Forall (can_gen_contR_gen rules) ps -> rsub last_rule rules -> 
  can_gen_contR_gen rules concl.

Lemma can_gen_contR_gen_def': forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_contR_gen rules ns <-> forall G K seq Γ Δ Δ' (d : dir), 
  contracted_gen Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K).
Proof.  intros.  unfold iff.  split ; intros. 
  destruct H0; subst; unfold can_gen_contL_gen in H;
  eapply H; reflexivity.    
  unfold can_gen_contR_gen. intros.
  apply conj; subst; eapply H; auto.
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
(* CONTRACTION TACTICS *)
(* ------------------- *)

Lemma cont_L: forall T X Y Z,
  contracted X (Y : list T) -> contracted (Z ++ X) (Z ++ Y).
Proof.  intros. destruct H. subst. 
  rewrite !(app_assoc Z). apply contracted_I'. Qed.

Lemma cont_R: forall T X Y Z,
  contracted X (Y : list T) -> contracted (X ++ Z) (Y ++ Z).
Proof.
  intros. destruct H. subst. rewrite <- !app_assoc.
  apply contracted_I'. 
Qed.

Lemma cont_gen_L: forall T X Y Z,
  contracted_gen X (Y : list T) -> contracted_gen (Z ++ X) (Z ++ Y).
Proof.
  intros. destruct H; subst; rewrite !(app_assoc Z).
  apply contracted_genL_I'.
  apply contracted_genR_I'.
Qed.

Lemma cont_gen_R: forall T X Y Z,
  contracted_gen X (Y : list T) -> contracted_gen (X ++ Z) (Y ++ Z).
Proof.
  intros. destruct H; subst; rewrite <- !app_assoc.
  apply contracted_genL_I'. 
  apply contracted_genR_I'. 
Qed.

Lemma cont_gen_spec_basic : forall T (a : T),
    contracted_gen_spec a ([a]++[a]) [a].
Proof.
  intros. change ([a] ++ [a]) with ([] ++ [a] ++ [] ++ [a] ++ []).
  change ([a]) with ([] ++ [a] ++ [] ++ []) at 3.
  apply contracted_genL_spec_I'.
Qed.
  
Lemma cont_gen_spec_L: forall T a X Y Z,
  contracted_gen_spec a X (Y : list T) -> contracted_gen_spec a (Z ++ X) (Z ++ Y).
Proof.
  intros. destruct H; subst; rewrite !(app_assoc Z).
  apply contracted_genL_spec_I'.
  apply contracted_genR_spec_I'.
Qed.

Lemma cont_gen_spec_R: forall T a X Y Z,
  contracted_gen_spec a X (Y : list T) -> contracted_gen_spec a (X ++ Z) (Y ++ Z).
Proof.
  intros. destruct H; subst; rewrite <- !app_assoc.
  apply contracted_genL_spec_I'. 
  apply contracted_genR_spec_I'. 
Qed.

Lemma cont_gen_spec_rem_sml_L : forall T (a : T) Z,
    contracted_gen_spec a ([a] ++ Z ++ [a]) ([a] ++ Z).
Proof.
  intros.
  change ([a] ++ Z ++ [a]) with ([] ++ [a] ++ Z ++ [a] ++ []).
  change ([a] ++ Z) with ([] ++ [a] ++ Z).
  rewrite <- (app_nil_r Z) at 2.
  apply contracted_genL_spec_I'.
Qed.

Lemma cont_gen_spec_rem_sml_R : forall T (a : T) Z,
    contracted_gen_spec a ([a] ++ Z ++ [a]) (Z ++ [a]).
Proof.
  intros.
  change ([a] ++ Z ++ [a]) with ([] ++ [a] ++ Z ++ [a] ++ []).
  change (Z ++ [a]) with (Z ++ [a] ++ []).
  rewrite <- (app_nil_l Z) at 2.
  apply contracted_genR_spec_I'.
Qed.

Lemma cont_cons: forall T (x : T) Y Z,
  contracted Y Z -> contracted (x :: Y) (x :: Z).
Proof.  intros. destruct H. subst. list_assoc_l.
        rewrite <- !app_assoc. apply contracted_I'.
Qed.

Lemma contracted_gen_in1: forall {T} (a : T) A Γ1 C H5,
    In a C ->
 contracted_gen (A ++ [a] ++ Γ1 ++ C ++ H5) (A ++ Γ1 ++ C ++ H5).
Proof.
  intros. apply in_split in H.
  destruct H as [l1 [l2 H]].
  subst.   list_assoc_r'.
  simpl.
  do 2 change (a :: (?x ++ ?y)) with ([a] ++ (x ++ y)).
  eapply contracted_genR_I.
  do 2 apply applI.
  rewrite app_assoc.  reflexivity.
  list_assoc_r'. reflexivity.
Qed.

Lemma contracted_gen_in2: forall {T} (a : T) A Γ1 C,
    In a Γ1 ->
 contracted_gen (A ++ [a] ++ Γ1 ++ C) (A ++ Γ1 ++ C).
Proof.
  intros. apply in_split in H.
  destruct H as [l1 [l2 H]].
  subst.   list_assoc_r'.
  simpl.
  change (a :: ?x) with ([a] ++ x).
  eapply contracted_genR_I.
  do 3 apply applI.
  2 : do 3 apply applI.
  all : reflexivity.
Qed.

Lemma contracted_gen_in3: forall {T} (a : T) A Γ1 C,
    In a Γ1 ->
contracted_gen (A ++ Γ1 ++ [a] ++ C) (A ++ Γ1 ++ C).
Proof.
  intros. apply in_split in H.
  destruct H as [l1 [l2 H]].
  subst.   list_assoc_r'.
  simpl.
  change (a :: ?x) with ([a] ++ x).
  eapply contracted_genL_I.
  rewrite app_assoc.
  do 3 apply applI. reflexivity.
  apps_eq_tac.
Qed.

Lemma contracted_gen_in4: forall {T} (a : T) A Γ1 H5 C,
    In a Γ1 ->
    contracted_gen (A ++ Γ1 ++ H5 ++ [a] ++ C) (A ++ Γ1 ++ H5 ++ C).
Proof.
  intros. apply in_split in H.
  destruct H as [l1 [l2 H]].
  subst.
  change (a :: ?x) with ([a] ++ x).
  assoc_mid [a].
  eapply contracted_genL_I.
  do 2 apply applI.
  assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

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

Ltac cont_rem_head :=
  list_assoc_r'; rewrite ?app_comm_cons;
  repeat match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    (tryif check_app_head l1 [a] then idtac else apply cont_gen_spec_L)
  end.

Ltac cont_rem_tail :=
  list_assoc_l'; rewrite ?app_comm_cons;
  repeat match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    (tryif check_app_tail l1 [a] then idtac else apply cont_gen_spec_R)
         end.

Ltac cont_rem_mid_simp :=
  apply cont_gen_spec_basic || apply cont_gen_spec_rem_sml_L
|| apply cont_gen_spec_rem_sml_R.

Ltac cont_gen_spec_app_brac_mid_L :=
  match goal with
  | [ |- contracted_gen_spec _ ?l1 ?l2 ] => app_bracket_middle_arg l1
  end.

Ltac cont_gen_spec_app_brac_mid_R :=
  match goal with
  | [ |- contracted_gen_spec _ ?l1 ?l2 ] => app_bracket_middle_arg l2
  end.

Ltac cont_gen_spec_app_brac_mid :=
  cont_gen_spec_app_brac_mid_L; cont_gen_spec_app_brac_mid_R.

(* Use this one *)
Ltac cont_solve :=
  cont_rem_head; cont_rem_tail;
  list_assoc_r_single; repeat cont_gen_spec_app_brac_mid;
  cont_rem_mid_simp.

Ltac cont_solve' :=
  cont_rem_head; cont_rem_tail;
  list_assoc_r_single; cont_gen_spec_app_brac_mid;
  cont_rem_mid_simp.



(* -------------------------------------------------- *)
(* HYPOTHESES USED IN LEFT CONTRACTION FOR PRINCRULES *)
(* -------------------------------------------------- *)

Definition premises_fullL {V} (ps : list (rel (list (PropF V)))) :=
  (non_empty ps -> Forall (fun p => fst p <> []) ps).

Definition premises_fullL_s {V} (s : (rel (list (PropF V)))) :=
non_empty (fst s).

Definition premises_fullL_ns {V} dir (ps : list (list (rel (list (PropF V)) * dir))) :=
  Forall (fun ns => Forall (fun s => premises_fullL_s (fst s)) ns) ps.

Definition rules_L_carry {W : Set} (rules : rls (rel (list W))) := 
  forall ps a x Δ, rules ps (a::x, Δ) ->
                   Forall (fun ps' => a = hd a (fst ps')) ps.

Definition rules_R_carry {W : Set} (rules : rls (rel (list W))) := 
  forall ps a x Γ, rules ps (Γ, a::x) ->
                   Forall (fun ps' => a = hd a (snd ps')) ps.

Definition rules_L_ne {W : Set} (rules : rls (rel (list W))) := 
  forall ps c,
    rules ps c -> (non_empty ps -> Forall (fun p => fst p <> []) ps).

Definition rules_R_ne {W : Set} (rules : rls (rel (list W))) := 
  forall ps c,
    rules ps c -> non_empty ps -> non_empty (snd c) ->Forall (fun p => snd p <> []) ps.


Definition rules_L_oc {W : Set} (rules : rls (rel (list W))) :=
forall (ps : list (rel (list W))) a (x Δ : list W),
rules ps (a :: x, Δ) -> x = [].

Lemma loe_imp_loc : forall {V} (princrules : rls (rel (list (PropF V)))),
  rules_L_oe princrules -> rules_L_oc princrules.
Proof.
  intros V princrules Hoe.
  unfold rules_L_oe in Hoe.
  intros ps a x l Hrules.
  change (a :: x) with ([a] ++ x) in Hrules.
  apply Hoe in Hrules. destruct Hrules.
  discriminate. assumption.
Qed.

Lemma in_nslcext_seqext : forall  V Φ1 Φ2 Ψ1 Ψ2 l l1 ps G d0,
   In (l, l1) ps ->
  In (nslcext G d0 (seqext Φ1 Φ2 Ψ1 Ψ2 (l, l1)))
         (map (nslcext G d0) (map (@seqext V Φ1 Φ2 Ψ1 Ψ2) ps)).
Proof. intros. do 2 apply in_map. auto. Qed.

Lemma in_nslc_seq : forall {V} ns ps G d0 (Γ1 Γ2 Ψ1 Ψ2 : list (PropF V)),
  In ns (map (nslcext G d0)
             (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) <->
  exists p, ns = (nslcext G d0 (seqext Γ1 Γ2 Ψ1 Ψ2 p)) /\
            In p ps.
Proof.
  induction ps; intros.
  +  simpl. split; intros H. contradiction.
     destruct H as [[p H] H2]. 
     firstorder.
  + simpl. split; intros H.
    ++  destruct H as [H1 | H2].
        exists a. firstorder.
        apply IHps in H2. firstorder.
    ++ destruct H as [ [p H] [H2 [H3 | H4]]].
       subst. firstorder.
       subst. right. apply IHps. firstorder.
Qed.

Lemma in_rules_L_carry: forall {V} (princrules : rls (rel (list (PropF V))))  ps a l l0 Γ1 Γ2,
    rules_L_carry princrules ->
    rules_L_ne princrules ->
    princrules ps (a::l, l0) ->
    In (Γ1, Γ2) ps ->
    In a Γ1.
Proof.
  intros. unfold rules_L_carry in H.
  pose proof H1 as H1'.
  apply H in H1. eapply Forall_forall in H1.
  2 : exact H2. simpl in *.
  destruct Γ1.
  + apply H0 in H1'.
    destruct ps. contradiction.
    simpl in H1'. pose proof (H1' I).
    eapply Forall_forall in H3. 2:exact H2.
    contradiction.
  + simpl in *. firstorder.
Qed.

Lemma in_rules_R_carry: forall {V} (princrules : rls (rel (list (PropF V))))  ps a l l0 Γ1 Γ2,
    rules_R_carry princrules ->
    rules_R_ne princrules -> 
    princrules ps (l0, a::l) ->
    In (Γ1, Γ2) ps ->
    In a Γ2.
Proof.
  intros. unfold rules_R_carry in H.
  pose proof H1 as H1'.
  pose proof H1 as H1''.
  apply H in H1. eapply H0 in H1'.
  simpl in *. destruct ps. contradiction.
  specialize (H1' I I).
  remember (r :: ps) as ps'.
  eapply Forall_forall in H1'.
  2 : exact H2. simpl in H1'.
  eapply Forall_forall in H1.
  2 : exact H2. simpl in H1.
  destruct Γ2. contradiction.
  simpl in *. subst. auto.
Qed.

Lemma rules_L_oe_cons_nil_blind : forall {V} princrules ps a l1 l2,
    @rules_L_oe V princrules -> 
    princrules ps (a :: l1, l2) ->
    l1 = nil.
Proof.
  intros until 0; intros H1 H2.
  unfold rules_L_oe in H1.
  change (a :: l1) with ([a] ++ l1) in H2.
  eapply H1 in H2. destruct H2.
  discriminate. assumption.
Qed.

Lemma rules_R_oe_cons_nil_blind : forall {V} princrules ps a l1 l2,
    @rules_R_oe V princrules -> 
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

Ltac solve_prop_contL_pr2 thm Hin' Hcarry Hne pr:=
  (eapply in_rules_L_carry in Hin'); [| exact Hcarry | exact Hne | exact pr];
  list_assoc_r_single;  apply thm; exact Hin'.

Ltac solve_prop_contR_pr2 thm Hin' Hcarry Hne pr:=
  (eapply in_rules_R_carry in Hin'); [| exact Hcarry | exact Hne | exact pr];
  list_assoc_r_single;  apply thm; exact Hin'.

Lemma prop_contL_step_pr_L: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_L_carry princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (H5 ++ [a] ++ C) A Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext (H5 ++ C) (A) Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1.
  solve_prop_contL_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_R: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_L_carry princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext A (H5 ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext (A) (H5 ++ C) Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1.
  solve_prop_contL_pr2 (@contracted_gen_in4 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_L_end: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_L_carry princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
 Forall (can_gen_contL_gen rules)
          (map (nslcext G d0) (map (seqext (A ++ [a]) C Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A) C Ψ1 Ψ2) ps)).
Proof.
  solve_prop_cont_pr1.
  solve_prop_contL_pr2 (@contracted_gen_in2 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_R_start: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_L_carry princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext A ([a] ++ C) Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext A C Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1.
  solve_prop_contL_pr2 (@contracted_gen_in3 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step1: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_R_carry princrules ->
  rules_R_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
Forall (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (H5 ++ [a] ++ C) A) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (H5 ++ C) A) ps))).
Proof.
  solve_prop_cont_pr1.
  solve_prop_contR_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step1_OPP: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_R_carry princrules ->
  rules_R_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
Forall (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A (H5 ++ [a] ++ C)) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A (H5 ++ C)) ps))).
Proof.
  solve_prop_cont_pr1.
  solve_prop_contR_pr2 (@contracted_gen_in4 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step4: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_R_carry princrules ->
  rules_R_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
 Forall (can_gen_contR_gen rules)
          (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a]) C) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A) C) ps)).
Proof.
  solve_prop_cont_pr1.
  solve_prop_contR_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step2: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_R_carry princrules ->
  rules_R_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
Forall (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A ([a] ++ C)) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A C) ps))).
Proof.
  solve_prop_cont_pr1.
  solve_prop_contR_pr2 (@contracted_gen_in3 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_BL: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ D) Ψ1 Ψ2) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contL_step_BR: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contL_step_LL: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ C) Γ Ψ1 Ψ2) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contL_step_LR: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contL_step_RL: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ C) Ψ1 Ψ2) ps)).
Proof.
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contL_step_RR: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Γ (A ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contR_step_BL: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 Forall (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B) (C ++ [a] ++ D)) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B) (C ++ D)) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contR_step_BR: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 Forall (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B) (C ++ [a] ++ D)) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ B) (C ++ [a] ++ D)) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contR_step_LL: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B ++ [a] ++ C) Γ) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B ++ C) Γ) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contR_step_LR: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a] ++ B ++ [a] ++ C) Γ) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ B ++ [a] ++ C) Γ) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contR_step_RL: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 Γ (A ++ [a] ++ B ++ [a] ++ C)) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 Γ (A ++ [a] ++ B ++ C)) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
  cont_solve.
Qed.

Lemma prop_contR_step_RR: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contR_gen rules)
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 Γ (A ++ [a] ++ B ++ [a] ++ C)) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 Γ (A ++ B ++ [a] ++ C)) ps)).
Proof.
  solve_prop_cont.
  apply (contracted_gen__spec a).
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
  eapply can_gen_swapL_derrec in H1.
  exact H1. exact Hcan. exact Hswap.
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
  eapply can_gen_swapR_derrec in H1.
  exact H1. exact Hcan. exact Hswap.
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

Lemma can_gen_contL_gen_Forall_dersrec : forall  {V}  a (rules : rls (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2',
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    contracted_gen_spec a (Γ1 ++ Γ2) (Γ1' ++ Γ2')->
  Forall (can_gen_contL_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  dersrec rules (fun _ => False)
         (map (nslcext G d0) (map (seqext Γ1' Γ2' Ψ1 Ψ2) ps)).
Proof.
  intros until 0. intros Hexch Hcon Hcont.
  inversion  Hcon; subst.
  { breakdown; clear Hcon;
      contL_make_gen_L_hyp;
      try solve [(eapply prop_contL_step_RL in Hcont; look_for_swapL Hexch)];
      try solve[(eapply prop_contL_step_BL in Hcont;  look_for_swapL Hexch)];
      try solve [eapply prop_contL_step_LL in Hcont; look_for_swapL Hexch].
  }
  { breakdown; clear Hcon;
      contL_make_gen_L_hyp;
      try solve [(eapply prop_contL_step_RR in Hcont; look_for_swapL Hexch)];
      try solve[(eapply prop_contL_step_BR in Hcont;  look_for_swapL Hexch)];
      try solve [eapply prop_contL_step_LR in Hcont; look_for_swapL Hexch].
  }
Qed.

Lemma can_gen_contR_gen_Forall_dersrec : forall  {V}  a (rules : rls (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Ψ1' Ψ2',
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapR rules ns) ->
    contracted_gen_spec a (Ψ1 ++ Ψ2) (Ψ1' ++ Ψ2')->
  Forall (can_gen_contR_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  dersrec rules (fun _ => False)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1' Ψ2') ps)).
Proof.
  intros until 0. intros Hexch Hcon Hcont.
  inversion  Hcon; subst.
  { breakdown; clear Hcon;
      contR_make_gen_L_hyp;
      try solve [(eapply prop_contR_step_RL in Hcont; look_for_swapR Hexch)];
      try solve[(eapply prop_contR_step_BL in Hcont;  look_for_swapR Hexch)];
      try solve [eapply prop_contR_step_LL in Hcont; look_for_swapR Hexch].
  }
  { breakdown; clear Hcon;
      contR_make_gen_L_hyp;
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

Lemma Sctxt_e'': forall (W : Type) (pr : rls (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) ((Φ1 ++ U) ++ Φ2, (Ψ1 ++ V) ++ Ψ2).
Proof. intros. do 2 rewrite <- app_assoc. apply Sctxt_e. exact H. Qed. 

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

Lemma Sctxt_e''': forall (W : Type) (pr : rls (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (Φ1 ++ U ++ Φ2, (Ψ1 ++ V )++ Ψ2).
Proof.
  intros. rewrite <- app_assoc.
  rewrite <- seqext_def. apply Sctxt. exact H.
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

Ltac check_contradiction_pr :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    repeat (list_assoc_r_singleton_hyp2 pr;
            try check_contradiction_prL_pre;
            try check_contradiction_prR_pre)
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

Lemma gen_contL_gen_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_L_oe princrules -> 
  rules_L_carry princrules ->
  rules_L_ne princrules ->
  (forall ns : list (rel (list (PropF V)) * dir),
      derrec rules (fun _ => False) ns ->
      can_gen_swapL rules ns) ->
  last_rule = nslcrule (seqrule princrules) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contL_step.
intros loe carry psfull exch lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
rewrite can_gen_contL_gen_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw_cont_gen rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection H0 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oe in loe.
inversion_clear swap ; subst.
{
(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
        sD ; subst  ; simpl in pr);
rem_nil;
try solve [check_contradiction_pr];
try (lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; contL_setup; 
     nsgen_sw_contL_gen5 rs sppc c c' acm inps0 swap pr inmps exch).
}

{
(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
        sD ; subst  ; simpl in pr);
rem_nil;
try solve [check_contradiction_pr];
try (lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; contL_setup; 
    nsgen_sw_contL_gen5 rs sppc c c' acm inps0 swap pr inmps exch).
}
}
{ list_eq_nc. contradiction. }

Qed.

Lemma princrule_pfc_L_carry : forall {V : Set} ps a x Δ,
  princrule_pfc ps (a :: x, Δ) ->
  Forall (fun ps' : list (PropF V) * list (PropF V) => a = hd a (fst ps')) ps.
Proof.  intros. inversion H; subst; auto. Qed.

Lemma princrule_pfc_R_carry : forall {V : Set} ps a x Γ,
  princrule_pfc ps (Γ, a :: x) ->
  Forall (fun ps' : list (PropF V) * list (PropF V) => a = hd a (snd ps')) ps.
Proof.  intros. inversion H; subst; auto. Qed.

Lemma princrule_pfc_L_carry' : forall V,
    rules_L_carry (@princrule_pfc V).
Proof.
  unfold rules_L_carry.  intros.
  eapply princrule_pfc_L_carry.  exact H.
Qed.

Lemma princrule_pfc_R_carry' : forall V,
    rules_R_carry (@princrule_pfc V).
Proof.
  unfold rules_R_carry.  intros.
  eapply princrule_pfc_R_carry.  exact H.
Qed.


Lemma princrule_pfc_L_ne : forall {V : Set} ps C,
  princrule_pfc ps C ->
  non_empty ps ->
  Forall (fun p : list (PropF V) * list (PropF V) => fst p <> []) ps.
Proof.
  intros. inversion H; subst; auto;
  apply Forall_forall; intros [l1 l2] Hxx;
    simpl in *; destruct Hxx as [H1 | H1].
  2 : contradiction.
  inversion H1; subst; intros HH; discriminate.
  inversion H1; subst; intros HH; discriminate.
  destruct H1.
  inversion H1; subst; intros HH; discriminate.
  contradiction.
Qed.
  
Lemma princrule_pfc_L_ne' : forall V, rules_L_ne (@princrule_pfc V).
Proof.
  unfold rules_L_ne. intros until 0; intros H1 H2.
  eapply princrule_pfc_L_ne. exact H1. exact H2. 
Qed.

Lemma princrule_pfc_R_ne : forall {V : Set} ps C,
  princrule_pfc ps C ->
  non_empty ps ->
  non_empty (snd C) ->
  Forall (fun p : list (PropF V) * list (PropF V) => snd p <> []) ps.
Proof.
  intros. inversion H; subst; auto;
  apply Forall_forall; intros [l1 l2] Hxx;
    simpl in *; destruct Hxx as [HH1 | HH1].
  2 : contradiction.
  inversion HH1; subst; intros HH; discriminate.
Qed.
  
Lemma princrule_pfc_R_ne' : forall V, rules_R_ne (@princrule_pfc V).
Proof.
  intros until 0; intros H1 H2.
  eapply princrule_pfc_R_ne. 
Qed.

(* New pr rules. *)
Lemma gen_contL_gen_step_pr_lc: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hswap Hl H2 H3 H4 H5.
  subst.
  eapply gen_contL_gen_step_loe_lc.
  apply princrule_pfc_L_oe'.
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


Lemma gen_contR_gen_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_R_oe princrules -> 
  rules_R_carry princrules ->
  rules_R_ne princrules -> 
  (forall ns : list (rel (list (PropF V)) * dir),
      derrec rules (fun _ => False) ns ->
      can_gen_swapR rules ns) ->
  last_rule = nslcrule (seqrule princrules) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contR_step.
intros loe carry psfull exch lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
rewrite can_gen_contR_gen_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw_cont_gen rs sppc (l, l0, d) (Γ, Δ', d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection H0 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oe in loe.
inversion_clear swap ; subst.
{
unfold rules_R_oe in loe.
(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
        sD ; subst  ; simpl in pr);
rem_nil;
try solve [check_contradiction_pr];
try (lt3R a exch rs carry psfull loe; rem_nil; contR_setup_extra;
nsgen_sw_contR_gen5 rs sppc c c' acm inps0 swap pr inmps exch).
}

{
  unfold rules_R_oe in loe.
(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
        sD ; subst  ; simpl in pr);
rem_nil;
try solve [check_contradiction_pr];
try (lt3R a exch rs carry psfull loe; rem_nil; contR_setup_extra;
     nsgen_sw_contR_gen5 rs sppc c c' acm inps0 swap pr inmps exch).
}
}
{ list_eq_nc. contradiction. }

Qed.

(* New pr rules. *)
Lemma gen_contR_gen_step_pr_lc: forall V ps concl 
                                       (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapR rules ns) ->
    last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hswap Hl H2 H3 H4 H5.
  subst.
  eapply gen_contR_gen_step_loe_lc.
  apply princrule_pfc_R_oe'.
  apply princrule_pfc_R_carry'. 
  apply princrule_pfc_R_ne'. 
  exact Hswap.
  reflexivity.
  exact H2.
  all : assumption.
Qed.