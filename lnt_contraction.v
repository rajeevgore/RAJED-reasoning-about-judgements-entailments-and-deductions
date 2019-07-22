Require Import ssreflect.
 
Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt lntacs lntls lntbR lntmtacs.
Require Import lntb1L lntb2L.
Require Import lnt_weakening.
Require Import lntkt_exch.


Inductive contracted {T} : list T -> list T -> Prop :=
  | contracted_I : forall a (X Y A B : list T), X = (A ++ [a;a] ++ B) -> 
    Y = (A ++ [a] ++ B) -> contracted X Y.

Lemma contracted_I': forall T a (A B : list T),
   contracted (A ++ [a;a] ++ B) (A ++ [a] ++ B).
Proof.  intros.  eapply contracted_I ; reflexivity. Qed.

Inductive contracted_gen {T} : list T -> list T -> Prop :=
  | contracted_genL_I : forall a (X Y A B C : list T), X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ [a] ++ B ++ C) -> contracted_gen X Y
  | contracted_genR_I : forall a (X Y A B C : list T), X = (A ++ [a] ++ B ++ [a] ++ C) -> 
                                                       Y = (A ++ B ++ [a] ++ C) -> contracted_gen X Y.

Inductive contracted_gen_spec {T} (a : T) : list T -> list T -> Prop :=
  | contracted_genL_spec_I : forall (X Y A B C : list T), X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ [a] ++ B ++ C) -> contracted_gen_spec a X Y
  | contracted_genR_spec_I : forall (X Y A B C : list T), X = (A ++ [a] ++ B ++ [a] ++ C) -> 
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

(* ------------------- *)
(* CONTRACTION TACTICS *)
(* ------------------- *)

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
rewrite -> ?can_gen_contL_def' in inps0 ;
rewrite -> ?can_gen_contR_def' in inps0 ; 
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply inps0 ; [> exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | reflexivity ]].

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
rewrite -> ?can_gen_contR_def' in inps0 ; 
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply inps0 ; [> exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | reflexivity ]].

(*
Lemma cont_same: forall T X, contracted X (X : list T).
Proof.
  intros. apply (weakened_I _ _ [] [] X); reflexivity.
Qed.
*)
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
(*
Lemma cont_gen_spec_mid: forall T a X1 X2 Y1 Y2 Z,
  contracted_gen_spec a (X1 ++ X2) (Y1 ++ Y2 : list T) -> contracted_gen_spec a (X1 ++ Z ++ X2) (Y1 ++ Z ++ Y2).
Proof.
Admitted.
*)
(*
Lemma cont_gen_spec_sml : forall T a Z,
    contracted_gen_spec a ([a] ++ [a]) ([a] : list T)
    contracted_gen_spec a ([a] ++ Z ++ [a]) ([a] ++ Z).
Admitted. 
*)
Lemma cont_gen_spec_rem_sml_L : forall T (a : T) Z,
    contracted_gen_spec a ([a] ++ Z ++ [a]) ([a] ++ Z).
Proof.
  intros.
  change ([a] ++ Z ++ [a]) with ([] ++ [a] ++ Z ++ [a] ++ []).
  change ([a] ++ Z) with ([] ++ [a] ++ Z).
  rewrite <- (app_nil_r Z) at 2.
  apply contracted_genL_spec_I'.
Qed.

(*
Lemma cont_gen_spec_rem_lge_L : forall T a Y1 Y2 Z,
    contracted_gen_spec a ([a] ++ Y1) ([a] ++ Y2 : list T) ->
    contracted_gen_spec a ([a] ++ Z ++ Y1) ([a] ++ Z ++ Y2).
Admitted.  
 *)
(*
Lemma cont_gen_spec_rem_sml_R : forall T a Z,
    contracted_gen_spec a ([a] ++ [a]) ([a] : list T) ->
    contracted_gen_spec a ([a] ++ Z ++ [a]) (Z ++ [a]).
Admitted.
*)
(*
  intros. inversion H. subst.
  eapply contracted_genL_spec_I.
  
  destruct H. subst.
  destruct H; subst. ; rewrite !(app_assoc Z).
  apply contracted_genL_spec_I'.
  apply contracted_genR_spec_I'.
Qed.
 *)

Lemma cont_cons: forall T (x : T) Y Z,
  contracted Y Z -> contracted (x :: Y) (x :: Z).
Proof.  intros. destruct H. subst. list_assoc_l.
        rewrite <- !app_assoc. apply contracted_I'.
Qed.
(*
Lemma weak_simpleRX : forall T (A B : list T),
    weakened A (A ++ B).
Proof.
  intros. apply (weakened_I _ _ A B []);
            list_app_nil; reflexivity.
Qed.

Lemma weak_simpleLX : forall T (A B : list T),
    weakened A (B ++ A).
Proof.
  intros. apply (weakened_I _ _ [] B A);
            list_app_nil; reflexivity.
Qed.
 *)
Ltac cont_tacX :=
  list_assoc_r ; try discriminate;
    repeat (apply cont_L || apply cont_cons) ;  
    list_assoc_l ; repeat (apply cont_R).

Ltac nsprsame_cont rs pr q qin inmps acm inps0 x0 :=
  try solve [discriminate];
derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
  apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ; 
rewrite -> Forall_forall in acm ;
rename_last inps0 ;  eapply in_map in inps0 ;
eapply in_map in inps0 ;
eapply acm in inps0 ;
clear acm ;
rewrite -> ?can_gen_contL_def' in inps0 ;
rewrite -> ?can_gen_contR_def' in inps0 ;
subst ;
destruct x0 ;
unfold seqext ;
unfold nsext ; unfold nslcext ;
eapply inps0 ;
  [> | unfold nsext ; unfold nslcext ; reflexivity |
    unfold seqext ; reflexivity ] ;
  cont_tacX.

Ltac nsprsameL_cont princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (?x :: ?x :: ?l, _) |- _ ] => assoc_mid (x :: l) end ;
nsprsame_cont rs pr q qin inmps acm inps0 x0.


(* ------------------------------- *)
(* LEFT CONTRACTION FOR PRINCRULES *)
(* ------------------------------- *)

Definition rules_L_carry {W : Set} (rules : rls (rel (list W))) := 
  forall ps a x Δ, rules ps (a::x, Δ) ->
                   Forall (fun ps' => (In a (fst ps'))) ps.

Definition rules_L_carry2 {W : Set} (rules : rls (rel (list W))) := 
  forall ps a x Δ, rules ps (a::x, Δ) ->
                   Forall (fun ps' => a = hd a (fst ps')) ps.

Definition non_empty {A : Type} (l : list A) :=
  match l with
  | nil => False
  | _ => True
  end.

Definition rules_L_ne {W : Set} (rules : rls (rel (list W))) := 
  forall ps c, rules ps c ->
               (non_empty ps -> Forall (fun p => fst p <> []) ps).
                   
Definition rem_hd {A : Type} (l : list A) :=
  match l with
  | nil => nil
  | a::l' => l'
  end.

Definition premises_fullL {V} (ps : list (rel (list (PropF V)))) :=
  (non_empty ps -> Forall (fun p => fst p <> []) ps).

Definition premises_fullL_s {V} (s : (rel (list (PropF V)))) :=
non_empty (fst s).

Definition premises_fullL_ns {V} dir (ps : list (list (rel (list (PropF V)) * dir))) :=
  Forall (fun ns => Forall (fun s => premises_fullL_s (fst s)) ns) ps.
(*
(non_empty ps -> Forall (fun p => fst p <> []) ps).
 *)
(*
Lemma lem : forall V ps A a Φ2 Ψ1 Ψ2,
(Forall (fun ps' : list (PropF V) * list (PropF V) =>
           a = hd a (fst ps')) ps) ->
premises_fullL ps ->
     (map (seqext (A ++ [a]) Φ2 Ψ1 Ψ2) ps) =
     (map (seqext (A ++ [a;a]) Φ2 Ψ1 Ψ2)
          (map (fun p =>(rem_hd (fst p), snd p)) ps)).
Proof.
  intros V. induction ps; intros until 0; intros HF HN; auto.
  simpl.  apply Forall_cons_inv in HF. destruct HF as [HF1 HF2].
  simpl in HN. specialize (HN I).
  apply Forall_cons_inv in HN. destruct HN as [HN1 HN2].
  unfold premises_fullL in *.
  rewrite IHps; auto. 
  destruct a as [Γ1 Γ2]. simpl in *.
  destruct Γ1. contradiction.
  simpl in *. subst. apps_eq_tac.
Qed.
*)
Lemma lem : forall V ps A a Φ2 Ψ1 Ψ2,
(Forall (fun ps' : list (PropF V) * list (PropF V) =>
           a = hd a (fst ps')) ps) ->
premises_fullL ps ->
     (map (seqext (A) Φ2 Ψ1 Ψ2) ps) =
     (map (seqext (A ++ [a]) Φ2 Ψ1 Ψ2)
          (map (fun p =>(rem_hd (fst p), snd p)) ps)).
Proof.
  intros V. induction ps; intros until 0; intros HF HN; auto.
  simpl.  apply Forall_cons_inv in HF. destruct HF as [HF1 HF2].
  simpl in HN. specialize (HN I).
  apply Forall_cons_inv in HN. destruct HN as [HN1 HN2].
  unfold premises_fullL in *.
  rewrite <- IHps; auto. 
  destruct a as [Γ1 Γ2]. simpl in *.
  destruct Γ1. contradiction.
  simpl in *. subst. apps_eq_tac.
Qed.
(*
Lemma lem' : forall V ps A a Φ2 Ψ1 Ψ2,
(Forall (fun ps' : list (PropF V) * list (PropF V) =>
           a = hd a (fst ps')) ps) ->
premises_fullL ps ->
     (map (seqext A ([a] ++ Φ2) Ψ1 Ψ2) ps) =
     (map (seqext A Φ2 Ψ1 Ψ2)
          (map (fun p =>(rem_hd (fst p), snd p)) ps)).
Proof.
  intros V. induction ps; intros until 0; intros HF HN; auto.
  simpl.  apply Forall_cons_inv in HF. destruct HF as [HF1 HF2].
  simpl in HN. specialize (HN I).
  apply Forall_cons_inv in HN. destruct HN as [HN1 HN2].
  unfold premises_fullL in *.
  rewrite <- IHps; auto. 
  destruct a as [Γ1 Γ2]. simpl in *.
  destruct Γ1. contradiction.
  simpl in *. subst. apps_eq_tac.
Qed.
*)

Lemma  lem4 : forall {V} Γ1 Γ2 A a0 Φ2 Ψ1 Ψ2,
    fst (@seqext V (A ++ [a0]) Φ2 Ψ1 Ψ2 (Γ1, Γ2)) <> [] ->
    Γ1 <> [].
  Admitted.

  Lemma lem5 : forall {V} G d0 s,
    Forall (fun s => premises_fullL_s (fst s))
           (nslcext G d0 s) ->
    @premises_fullL_s V s.
  Admitted.
  
Lemma  lem3 : forall {V} G d0 Γ1 Γ2 A a0 Φ2 Ψ1 Ψ2,
    Forall
      (fun s : rel (list (PropF V)) * dir =>
         premises_fullL_s (fst s))
      (nslcext G d0 (seqext (A ++ [a0]) Φ2 Ψ1 Ψ2 (Γ1, Γ2))) ->
    Γ1 <> [].
Proof.
  intros until 0. intros H.
  apply lem5 in H.
  unfold premises_fullL_s in H.
  simpl in *.
Admitted.
  
Lemma lem2 : forall {V} ps (G : list (rel (list (PropF V)) * dir)) d0 A a Φ2 Ψ1 Ψ2,
    premises_fullL_ns dir
                      (map (nslcext G d0)
                           (map (seqext (A ++ [a]) Φ2 Ψ1 Ψ2) ps)) ->
    premises_fullL ps.
Proof.
  induction ps; intros until 0; intros Hprems;
  unfold premises_fullL. simpl. auto.
  intros Hnon.
  unfold premises_fullL_ns in Hprems.
  destruct a as [Γ1 Γ2].
  do 2 rewrite map_cons in Hprems.
  apply Forall_cons_inv in Hprems.
  destruct Hprems as [H1 H2].
  apply IHps in H2. apply lem3 in H1.
  destruct ps. 
  apply Forall_cons.  auto. auto.
  apply Forall_cons.  auto. auto.
Qed.  

Lemma lem7 : forall {V} rules G d0 A (a : PropF V) Φ2 Ψ1 Ψ2 seq,
  Forall (can_gen_contL rules)
         (map (nslcext G d0)
              (map (seqext (A ++ [a;a]) Φ2 Ψ1 Ψ2) seq)) ->
  Forall (derrec rules (fun _ => False)) (map (nslcext G d0) (map (seqext (A ++ [a]) Φ2 Ψ1 Ψ2) seq)).
(*
  Forall (@can_gen_contL V rules)
         (map (nslcext G d0)
              (map (seqext (A ++ [a]) Φ2 Ψ1 Ψ2) seq))  .
 *)
Proof.
  induction seq; intros Hcont.
  simpl. auto.
  simpl in *. apply Forall_cons_inv in Hcont.
  destruct Hcont as [cont Hcont]. apply Forall_cons.
  + unfold can_gen_contL in cont.
    unfold nslcext. destruct a0 as [b1 b2].
    simpl. rewrite <- app_assoc.
    simpl. eapply cont.
    reflexivity. unfold seqext. solve_eqs.
  + apply IHseq. apply Hcont.
Qed.

Lemma lem7' : forall {V} rules G d0 A (a : PropF V) Φ2 Ψ1 Ψ2 seq,
  Forall (can_gen_contL rules)
         (map (nslcext G d0)
              (map (seqext A ([a;a] ++ Φ2) Ψ1 Ψ2) seq)) ->
    Forall (derrec rules (fun _ => False)) (map (nslcext G d0) (map (seqext A ([a] ++ Φ2) Ψ1 Ψ2) seq)).
(*  Forall (@can_gen_contL V rules)
         (map (nslcext G d0)
              (map (seqext (A) ([a] ++ Φ2) Ψ1 Ψ2) seq))  . *)
Proof.
  induction seq; intros Hcont.
  simpl. auto.
  simpl in *. apply Forall_cons_inv in Hcont.
  destruct Hcont as [cont Hcont]. apply Forall_cons.
  + unfold can_gen_contL in cont.
    unfold nslcext. destruct a0 as [b1 b2].
    simpl. rewrite app_assoc. 
    eapply cont.
    reflexivity. unfold seqext. solve_eqs.
  + apply IHseq. apply Hcont.
Qed.

Lemma lem9 : forall  V Φ1 Φ2 Ψ1 Ψ2 l l1 ps G d0,
  In (nslcext G d0 (seqext Φ1 Φ2 Ψ1 Ψ2 (l, l1)))
     (map (nslcext G d0) (map (@seqext V Φ1 Φ2 Ψ1 Ψ2) ps)) ->
     In (l, l1) ps.
Proof.
  induction ps; intros. auto.
  simpl in *. destruct H.
  unfold nslcext in H. left.
  apply app_inv_head in H.
  destruct a. simpl in *.
  inversion H as [[H1 H2]].
  apply app_inv_head in H1. apply app_inv_tail in H1.
  apply app_inv_head in H2. apply app_inv_tail in H2.
  subst. auto.

  right. apply IHps in H. auto.
Qed.
  
Lemma lem8 : forall  V Φ1 Φ2 Ψ1 Ψ2 l l1 ps G d0,
   In (l, l1) ps ->
  In (nslcext G d0 (seqext Φ1 Φ2 Ψ1 Ψ2 (l, l1)))
         (map (nslcext G d0) (map (@seqext V Φ1 Φ2 Ψ1 Ψ2) ps)).
Proof. intros. do 2 apply in_map. auto. Qed.

Ltac nsprsame_cont2 rs pr q qin inmps acm inps0 x0 := 
derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
  apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ; 
rewrite -> Forall_forall in acm ;
rename_last inps0 ;  eapply in_map in inps0 ;
eapply in_map in inps0 ;
pose proof inps0 as HH;
eapply acm in inps0 ;
clear acm ;
rewrite -> ?can_gen_contL_def' in inps0 ;
rewrite -> ?can_gen_contR_def' in inps0 ;
subst ;
destruct x0 ;
unfold seqext ;
unfold nsext ; unfold nslcext ;
eapply inps0 ;
  [> | unfold nsext ; unfold nslcext ; reflexivity |
   unfold seqext ; reflexivity ].
(*;
  cont_tacX.
 *)

Ltac nsprsame_cont2_gen rs pr q qin inmps acm inps0 x0 := 
derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
  apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ; 
rewrite -> Forall_forall in acm ;
rename_last inps0 ;  eapply in_map in inps0 ;
eapply in_map in inps0 ;
pose proof inps0 as HH;
eapply acm in inps0 ;
clear acm ;
rewrite -> ?can_gen_contL_gen_def' in inps0 ;
rewrite -> ?can_gen_contR_def' in inps0 ;
subst ;
destruct x0 ;
unfold seqext ;
unfold nsext ; unfold nslcext ;
eapply inps0 ;
  [> | unfold nsext ; unfold nslcext ; reflexivity |
   unfold seqext ; reflexivity ].
(*;
  cont_tacX.
 *)

Lemma cont_small : forall {T} (a : T),
    contracted [a;a] [a].
Proof.
  intros. eapply (contracted_I _ _ _ [][]);
  solve_eqs. 
Qed.

Lemma lem10 : forall {V} princrules (rules : rls (list (rel (list (PropF V)) * dir))) ps p G d0 l0 A B Ψ1 Ψ2,
                    rules_L_carry2 princrules ->
                    rules_L_ne princrules ->
                     rsub (nslcrule (seqrule princrules)) rules ->
princrules ps ([p], l0) ->
Forall (can_gen_contL rules)
          (map (nslcext G d0)
               (map (seqext (A) ([p] ++ B) Ψ1 Ψ2) ps))
  ->
Forall (can_gen_contL rules)
          (map (nslcext G d0)
               (map (seqext A ([p;p] ++ B) Ψ1 Ψ2) (map (fun p =>(rem_hd (fst p), snd p)) ps))).
Proof.
  intros until 0; intros carry ne rsub pr cont.
Admitted.

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

Lemma in_rem_hd : forall {V} ps (seq : rel (list (PropF V))),
    In seq (map (fun p => (rem_hd (fst p), snd p)) ps) <->
    exists seq2, seq = (rem_hd (fst seq2), snd seq2) /\
                 In seq2 ps.
Proof.
  induction ps; intros.
  simpl. firstorder.
  simpl. split; intros H.
  destruct H as [H1 | H1].
  subst. exists a. firstorder.
  apply IHps in H1.
  firstorder.
  destruct H as [seq2 [H1 [H2 | H2]]].
  subst. firstorder.
  right. apply IHps. firstorder.
Qed.


Lemma can_gen_contL_imp: forall {V : Set} 
                                (rules : rls (list (rel (list (PropF V)) * dir))) ns,
    can_gen_contL rules ns -> forall G K seq Γ Δ Γ' (d : dir), 
      contracted Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
      derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros until 0. intro.
        rewrite -> can_gen_contL_def' in H. exact H. Qed.

Lemma can_gen_contL_gen_imp: forall {V : Set} 
                                (rules : rls (list (rel (list (PropF V)) * dir))) ns,
    can_gen_contL_gen rules ns -> forall G K seq Γ Δ Γ' (d : dir), 
      contracted_gen Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
      derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros until 0. intro.
        rewrite -> can_gen_contL_gen_def' in H. exact H. Qed.

Lemma can_gen_contL_imp': forall {V : Set} 
                                (rules : rls (list (rel (list (PropF V)) * dir))) ns,
    can_gen_contL rules ns ->
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
                can_gen_swapL rules ns) ->
    forall G K seq Γ Δ Γ' Γ'' (d : dir), 
      contracted Γ Γ' ->
      swapped Γ' Γ'' ->
      ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
      derrec rules (fun _ => False) (G ++ (pair Γ'' Δ, d) :: K).
Proof.
  intros until 0. intros Hcont Hswap. intros. subst.
  rewrite -> can_gen_contL_def' in Hcont.
  eapply Hcont in H; try reflexivity.
  apply Hswap in H.
  eapply can_gen_swapL_def' in H.
  apply H. apply H0. reflexivity. reflexivity.
Qed. 

Lemma can_gen_contL_swapL_pre' : forall {V} rules G d0 Γ Γ' Ψ,
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    swapped Γ Γ' ->
    can_gen_contL_gen rules
                  (nslcext G d0 (Γ, Ψ)) ->
    can_gen_contL_gen rules
                  (nslcext G d0 (Γ', Ψ)).
Proof.
  intros. rewrite can_gen_contL_gen_def'. intros.
  subst. unfold nslcext in *.
  apply partition_2_2 in H3.

sE ; subst.
  + inversion H2.
    ++ subst.
    eapply can_gen_contL_gen_imp in H1.
    2 : exact H2. 2 : rewrite <- app_assoc. 2 : reflexivity.
    2 : reflexivity.
    fold (app x [(Γ, Ψ, d0)]) in H1.
    apply H in H1.
    rewrite app_cons_single.
    rewrite app_assoc. 
    eapply can_gen_swapL_imp. apply H1. apply H0.
    2 : reflexivity. solve_eqs.
    ++ subst.
    eapply can_gen_contL_gen_imp in H1.
    2 : exact H2. 2 : rewrite <- app_assoc. 2 : reflexivity.
    2 : reflexivity.
    fold (app x [(Γ, Ψ, d0)]) in H1.
    apply H in H1.
    rewrite app_cons_single.
    rewrite app_assoc. 
    eapply can_gen_swapL_imp. apply H1. apply H0.
    2 : reflexivity. solve_eqs.
  +     inversion H3. subst.
        inversion H2. subst.
        clear H3 H2.
        
(*        edestruct (@can_gen_contL_def' V) as [fwd rev].
        clear rev.  pose proof (fwd H1) as H2. clear fwd.
 *)
        
        
        eapply can_gen_contL_gen_imp in H1.
        apply H1. 2: reflexivity. 2 : reflexivity.

    
Admitted.


Lemma can_gen_contL_swapL_pre : forall {V} rules G d0 Γ Γ' Ψ,
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    swapped Γ Γ' ->
    can_gen_contL rules
                  (nslcext G d0 (Γ, Ψ)) ->
    can_gen_contL rules
                  (nslcext G d0 (Γ', Ψ)).
Proof.
  intros. rewrite can_gen_contL_def'. intros.
  subst. unfold nslcext in *.
  apply partition_2_2 in H3.

sE ; subst.
  + inversion H2. subst.
    eapply can_gen_contL_imp in H1.
    2 : exact H2. 2 : rewrite <- app_assoc. 2 : reflexivity.
    2 : reflexivity.
    fold (app x [(Γ, Ψ, d0)]) in H1.
    apply H in H1.
    rewrite app_cons_single.
    rewrite app_assoc. 
    eapply can_gen_swapL_imp. apply H1. apply H0.
    2 : reflexivity. solve_eqs.
  +     inversion H3. subst.
        inversion H2. subst.
        clear H3 H2.
(*        edestruct (@can_gen_contL_def' V) as [fwd rev].
        clear rev.  pose proof (fwd H1) as H2. clear fwd.
 *)
        
        
        eapply can_gen_contL_imp in H1.
        apply H1. 2: reflexivity. 2 : reflexivity.
        
    
Admitted.

Lemma can_gen_contL_swapL : forall {V} rules G d0 Γ1 p0 ss1 Γ2 Ψ1 ss2 Ψ2,
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) -> 
    can_gen_contL rules
                  (nslcext G d0 (Γ1 ++ p0 :: ss1 ++ Γ2, Ψ1 ++ ss2 ++ Ψ2)) ->
    can_gen_contL rules
                  (nslcext G d0 (Γ1 ++ ss1 ++ p0 :: Γ2, Ψ1 ++ ss2 ++ Ψ2)).
Proof.
  intros until 0. intros ?. apply can_gen_contL_swapL_pre. auto.
  swap_tac. change (p0 :: ss1 ++ Γ2) with ([p0] ++ ss1 ++ Γ2).
  rewrite app_cons_single. swap_tac.
Qed.

Lemma lem11 : forall {V} princrules rules ps p l0 G d0 (Γ1 Γ2 Ψ1 Ψ2 : list (PropF V)),
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  princrules ps ([p], l0) ->
(forall ns
  (D : derrec rules (fun _ => False) ns),
      can_gen_swapL rules ns) -> 
rsub (nslcrule (seqrule princrules)) rules ->
Forall (can_gen_contL rules) (map (nslcext G d0)
   (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
Forall (can_gen_contL rules) (map (nslcext G d0)
   (map (seqext Γ1 ([p] ++ Γ2) Ψ1 Ψ2)
        (map (fun p =>(rem_hd (fst p), snd p)) ps))).
Proof.
  intros. apply Forall_forall.
  intros x Hin.
  pose proof Hin as Hin'.
  apply in_nslc_seq in Hin.
  destruct Hin as [seq [Heq Hin]].
  subst. apply in_rem_hd in Hin.
  destruct Hin as [seq2 [Heq2 Hin2]].
  subst.
  pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  specialize (fwd H3 (nslcext G d0
       (seqext Γ1 Γ2 Ψ1 Ψ2 seq2))). clear rev.
  assert ( In (nslcext G d0 (seqext Γ1 Γ2 Ψ1 Ψ2 seq2))
              (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps))) as Hass.
  apply in_map. apply in_map. auto.
  apply fwd in Hass. clear fwd.
  unfold rules_L_carry2 in H.
  pose proof H1 as H1'.
  apply H in H1.
  edestruct Forall_forall as [fwd rev].
  pose proof (fwd H1 seq2 Hin2) as H5.
  destruct seq2 as [ss1 ss2]. simpl in *.
  destruct ss1.
  unfold rules_L_ne in H0. apply H0 in H1'.
  clear fwd rev.
  edestruct Forall_forall as [fwd rev].
  pose proof (fwd H1' ([], ss2) Hin2).
  simpl in H6. contradiction.
  destruct ps. contradiction. simpl. auto.
  simpl in *. subst.  clear rev fwd.
  apply can_gen_contL_swapL; auto.
Qed.

Lemma lem11' : forall {V} princrules ps P p l0 G d0 (Γ1 Γ2 Ψ1 Ψ2 : list (PropF V)),
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  princrules ps ([p], l0) ->
Forall P (map (nslcext G d0)
   (map (seqext Γ1 ([p] ++ Γ2) Ψ1 Ψ2)
        (map (fun p =>(rem_hd (fst p), snd p)) ps))) ->
Forall P (map (nslcext G d0)
   (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)).
Admitted.

Lemma lem13: forall {T} (a : T) A Γ1 H5 C,
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

Lemma lem13b: forall {T} (a : T) A Γ1 C,
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

Lemma lem13b2: forall {T} (a : T) A Γ1 C H5,
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

  Lemma lem13c: forall {T} (a : T) A Γ1 C,
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

Lemma lem14: forall {V} (princrules : rls (rel (list (PropF V))))  ps a l l0 Γ1 Γ2,
    rules_L_carry2 princrules ->
    rules_L_ne princrules ->
    princrules ps (a::l, l0) ->
    In (Γ1, Γ2) ps ->
    In a Γ1.
Proof.
  intros. unfold rules_L_carry2 in H.
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


Lemma prop_contL_step1_OPP: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext A (H5 ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext (A) (H5 ++ C) Ψ1 Ψ2) ps))).
Proof.
  intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (A) (H5 ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H3.
  apply lem13.
  eapply lem14; auto.
  apply H. apply H0. apply H1. apply Hin.
Qed.

Ltac cont_partial_solve_old a :=
list_assoc_r'; 
(eapply contracted_genL_spec_I; reflexivity) ||
(eapply contracted_genR_spec_I; reflexivity).

Ltac check_head l1 l2 :=
  match l1 with
  | l2 ++ ?l3 => idtac
  | _ => fail
  end.

Ltac check_tail l1 l2 :=
  match l1 with
  | ?l3 ++ l2 => idtac
  | _ => fail
  end.

Ltac cont_rem_head :=
  list_assoc_r'; rewrite ?app_comm_cons;
  repeat match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    (tryif check_head l1 [a] then idtac else apply cont_gen_spec_L)
  end.

Ltac cont_rem_tail :=
  list_assoc_l'; rewrite ?app_comm_cons;
  repeat match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    (tryif check_tail l1 [a] then idtac else apply cont_gen_spec_R)
         end.

Ltac cont_rem_mid_simp :=
  apply cont_gen_spec_basic || apply cont_gen_spec_rem_sml_L.

(*
Ltac cont_rem_mid :=
  list_assoc_r'; rewrite ?app_comm_cons;
  match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] => 
   repeat match l1 with
    | [a] ++ ?A => once idtac 500
    | ?A ++ ?B => do 2 rewrite (app_assoc A); apply cont_gen_spec_mid;
                  do 2 rewrite <- (app_assoc A)
    end
  end.
*)
Ltac single_app :=
repeat match goal with
| [ |- context[ ?a :: [] ++ ?B ] ] => rewrite (app_comm_cons _ _ a)
end.

Ltac rem_nil_goal := repeat rewrite app_nil_l; repeat rewrite app_nil_l.
Ltac rem_nil_hyp_arg H := repeat rewrite app_nil_l in H; repeat rewrite app_nil_l in H.
Ltac rem_nil_hyp :=
  match goal with
  | [ H : context[ [] ++ ?A ] |- _ ] => rem_nil_hyp_arg H
  | [ H : context[ ?A ++ [] ] |- _ ] => rem_nil_hyp_arg H
  | _ => idtac
  end.

Ltac rem_nil := rem_nil_hyp; rem_nil_goal.

Ltac list_assoc_r'_single :=
  list_assoc_r'; tac_cons_singleton; rem_nil.

  Ltac app_bracket_middle_arg l :=
    repeat match l with
           | ?l1 ++ ?l2 ++ ?l3 ++ ?l4 => rewrite (app_assoc l2)
           end.

  Ltac app_bracket_middle_L :=
    match goal with
    | [ |- contracted_gen_spec _ ?l1 ?l2 ] => app_bracket_middle_arg l1
    end.

    Ltac app_bracket_middle_R :=
    match goal with
    | [ |- contracted_gen_spec _ ?l1 ?l2 ] => app_bracket_middle_arg l2
    end.

    Ltac app_bracket_middle :=
      app_bracket_middle_L; app_bracket_middle_R.

    
(* Use this one *)
Ltac cont_solve :=
  cont_rem_head; cont_rem_tail;
  list_assoc_r'_single; app_bracket_middle;
  cont_rem_mid_simp.

Ltac cont_solve2 a :=
  cont_rem_head; cont_rem_tail;
  list_assoc_r'_single; cont_rem_mid_simp.

(*
Ltac cont_rem_mid_solve :=
  repeat match goal with
         | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
           repeat match l1 with
           | [a] ++ ?A ++ ?B => apply cont_gen_spec_rem_sml_L || apply cont_gen_spec_rem_lge_L
           end
         end.
 *)


Lemma prop_contL_step1: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (H5 ++ [a] ++ C) A Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext (H5 ++ C) (A) Ψ1 Ψ2) ps))).
Proof.
  intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (H5 ++ [a] ++ C) A Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H3.
  list_assoc_r'_single.
  apply lem13b2.
  eapply lem14; auto.
  apply H. apply H0. apply H1. apply Hin.
Qed.

Lemma prop_contL_step2: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext A ([a] ++ C) Ψ1 Ψ2) ps)) ->
(dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext A C Ψ1 Ψ2) ps))).
Proof.
  intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (A) ([a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H3.
  apply lem13c.
  eapply lem14; auto.
  apply H. apply H0. apply H1. apply Hin.
Qed.



 Lemma prop_contL_step4: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
 Forall (can_gen_contL_gen rules)
          (map (nslcext G d0) (map (seqext (A ++ [a]) C Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A) C Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (A ++ [a]) C Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H3.
  rewrite <- app_assoc.
  apply lem13b.
  eapply lem14; auto.
  apply H. apply H0.
  apply H1.  apply Hin.
Qed.

 Lemma prop_contL_step4': forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l l0 G d0 A C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (a::l, l0) ->
 Forall (can_gen_contL_gen rules)
          (map (nslcext G d0) (map (seqext (A ++ [a]) C Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A) C Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (A ++ [a]) C Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H3.
  rewrite <- app_assoc.
  apply lem13b.
  eapply lem14; auto.
  apply H. apply H0.
  apply H1.  apply Hin.
Qed.

Lemma prop_contL_step5: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A l C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l, l0) ->
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (A ++ [a]) ( [a] ++ C) Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a]) C Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (A ++ [a]) ([a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H3.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.




Lemma prop_contL_step6: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A B l C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l, l0) ->
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext A ([a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext A ([a] ++ B ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext  A ([a] ++ B ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H3.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step6': forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext A ([a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext A ([a] ++ B ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext  A ([a] ++ B ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.


Lemma prop_contL_step7': forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A B l C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l, l0) ->
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) ([a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) C Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext  (A ++ [a] ++ B) ([a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H3.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.



Lemma prop_contL_step9: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext  (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genR_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.



Lemma prop_contL_step11: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Γ (A ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genR_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step3: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A H5 C Ψ1 Ψ2,
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (A ++ [a]) (H5 ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a]) (H5 ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (A ++ [a]) (H5 ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step_OPP: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A H5 C Ψ1 Ψ2,
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (A ++ [a]) (H5 ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A) (H5 ++ [a] ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (A ++ [a]) (H5 ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H.
  eapply contracted_genR_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step3_OPP2: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A H5 C Ψ1 Ψ2,
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (H5 ++ [a] ++ C) (A ++ [a]) Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (H5 ++ C) (A ++ [a]) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (H5 ++ [a] ++ C) (A ++ [a]) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genR_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step7: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ D) Ψ1 Ψ2) ps)).
Proof.
  intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext  (A ++ [a] ++ B) (C ++ [a] ++ D) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step7_OPP: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ B) (C ++ [a] ++ D) Ψ1 Ψ2) ps)).
Proof.
  intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext  (A ++ [a] ++ B) (C ++ [a] ++ D) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H.
  eapply contracted_genR_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step7_OPP2: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C D Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (C ++ [a] ++ D) (A ++ [a] ++ B) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (C ++ D) (A ++ [a] ++ B) Ψ1 Ψ2) ps)).
Proof.
  intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (C ++ [a] ++ D) (A ++ [a] ++ B) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H.
  eapply contracted_genR_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step8: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ C) Γ Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext  (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step8_OPP: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext  (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genR_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step8_OPP2: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext Γ  (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step10: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step10_OPP: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext Γ (A ++ B ++ [a] ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext Γ (A ++ [a] ++ B ++ [a] ++ C) Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genR_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Lemma prop_contL_step10_OPP2: forall {V} (rules : rls (list (rel (list (PropF V)) * dir))) ps a G d0 A B C Γ Ψ1 Ψ2,
 Forall (can_gen_contL_gen rules)
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2) ps)) ->
 dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a] ++ B ++ C) Γ Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H) as H3. clear fwd rev.
  apply dersrec_forall.
  intros c Hin.
  apply in_nslc_seq in Hin.
  destruct Hin as [[Γ1 Γ2] [Heq Hin]].
  subst.
  specialize (H3 (nslcext G d0 (seqext (A ++ [a] ++ B ++ [a] ++ C) Γ Ψ1 Ψ2 (Γ1, Γ2)))).
  pose proof (H3 (lem8 _ _ _ _ _ _ _ _ _ _ Hin)) as H6.
  clear H3.
  clear H4.
  eapply can_gen_contL_gen_def' in H6; try reflexivity.
  apply H6.
  clear H0.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.


Lemma lem20_l : forall  {V}  (rules : rls (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1',
  contracted_gen Γ1 Γ1' ->
  Forall (can_gen_contL_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  dersrec rules (fun _ => False)
         (map (nslcext G d0) (map (seqext Γ1' Γ2 Ψ1 Ψ2) ps)).
Proof.
  intros until 0. intros Hcon Hcont.
  inversion  Hcon; subst.
  { eapply prop_contL_step8 in Hcont.
      exact Hcont. }
  { eapply prop_contL_step9 in Hcont.
      exact Hcont. }
Qed.

Lemma lem20_r : forall  {V}  (rules : rls (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ2',
  contracted_gen Γ2 Γ2' ->
  Forall (can_gen_contL_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  dersrec rules (fun _ => False)
         (map (nslcext G d0) (map (seqext Γ1 Γ2' Ψ1 Ψ2) ps)).
Proof.
  intros until 0. intros Hcon Hcont.
  inversion  Hcon; subst.
  { eapply prop_contL_step10 in Hcont.
      exact Hcont. }
  { eapply prop_contL_step11 in Hcont.
      exact Hcont. }
Qed.

Lemma cons_single : forall {T} a (l2 : list T),
   a :: l2 = [a] ++ l2.
Proof. auto. Qed.

Ltac add_empty_hyp_L l H :=  rewrite <- (app_nil_l l) in H.
Ltac add_empty_goal_L l :=  rewrite <- (app_nil_l l).
Ltac add_empty_hyp_R l H :=  rewrite <- (app_nil_r l) in H.
Ltac add_empty_goal_R l :=  rewrite <- (app_nil_r l).
Ltac rem_empty_hyp_L l H :=  rewrite (app_nil_l l) in H.
Ltac rem_empty_goal_L l :=  rewrite (app_nil_l l).
Ltac rem_empty_hyp_R l H :=  rewrite (app_nil_r l) in H.
Ltac rem_empty_goal_R l :=  rewrite (app_nil_r l).



Ltac breakdown :=
  repeat (
      repeat (match goal with
              | [ H : ?A ++ ?B = ?x ++ ?y |- _ ] => apply app_eq_app in H; sE; subst
              end) ;
      repeat (match goal with
              | [H2 : [?a] = ?A ++ ?B |- _ ] => apply unit_eq_app in H2; sE; subst
              end));
  repeat try rewrite app_nil_r; repeat try rewrite app_nil_l;
  repeat (match goal with
          | [ H3 : context[ ?x ++ [] ] |- _ ] => rewrite (app_nil_r x) in H3
          end);
  repeat (match goal with
          | [ H3 : context[ [] ++ ?x ] |- _ ] => rewrite (app_nil_l x) in H3
          end).


Ltac cont_make_gen_L :=
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
    end;
    match l1' with
    | [?a] ++ ?B => add_empty_goal_L l1'
    | _ => idtac 
    end;
    match l2' with
    | [?a] ++ ?B => add_empty_goal_L l2'
    | _ => idtac 
    end      
  end.

Ltac cont_make_gen_L_hyp :=
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


Ltac cont_make_gen_L'' :=
  match goal with
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B ++ [?a] ++ ?C => add_empty_hyp_L l2 Hcont;
      match l2' with
      | B ++ [a] ++ C => apply prop_contL_step11 in Hcont; exact Hcont
      | [a] ++ B ++ C => apply prop_contL_step10 in Hcont; exact Hcont
      end
    end
  end.
      
(*

    
    add_empty_hyp_L ([a] ++ B ++ [a] ++ C) Hcont;
    eapply prop_contL_step10 in Hcont; exact Hcont
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                      (map (nslcext ?G ?d0) (map (seqext ?A ([?a] ++ ?B ++ [?a] ++ ?C) ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map (nslcext ?G ?d0) (map (seqext ?A (?B ++ [?a] ++ ?C) ?Ψ1 ?Ψ2) ?ps)) ] => add_empty_hyp_L ([a] ++ B ++ [a] ++ C) Hcont; eapply prop_contL_step11 in Hcont; exact Hcont
  end.      
*)
Ltac cont_make_gen_L' :=
  match goal with
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                      (map (nslcext ?G ?d0) (map (seqext ?A
                           ([?a] ++ ?B ++ [?a] ++ ?C) ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map (nslcext ?G ?d0) (map (seqext ?A ([?a] ++ ?B ++ ?C)
                                                 ?Ψ1 ?Ψ2) ?ps)) ] =>
    add_empty_hyp_L ([a] ++ B ++ [a] ++ C) Hcont;
    eapply prop_contL_step10 in Hcont; exact Hcont
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                      (map (nslcext ?G ?d0) (map (seqext ?A ([?a] ++ ?B ++ [?a] ++ ?C) ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map (nslcext ?G ?d0) (map (seqext ?A (?B ++ [?a] ++ ?C) ?Ψ1 ?Ψ2) ?ps)) ] => add_empty_hyp_L ([a] ++ B ++ [a] ++ C) Hcont; eapply prop_contL_step11 in Hcont; exact Hcont
  end.      

Ltac cont_solve_gen1 :=
  match goal with
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                          (map (nslcext ?G ?d0) (map (seqext ?A (?D ++ [?a] ++ ?B ++ [?a] ++ ?C) ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    (eapply prop_contL_step10 in Hcont; exact Hcont) || (eapply prop_contL_step11 in Hcont; exact Hcont) || idtac 200
  end.


(*
  
Lemma swapped_single_rearr : forall {T} (A1 A2 B : list T) a,
    swapped (a :: A1 ++ A2) (a :: B) ->
    swapped (A1 ++ a :: A2) (a :: B).
Proof.
  induction A1;
    intros until 0; intros Hswap.
  simpl in *. auto.
  simpl in *.
  inversion Hswap; subst.
  apply cons_eq_app in H.
  apply cons_eq_app in H0.
  sE; subst.
  apply app_eq_cons in H2.
  apply app_eq_cons in H3.
  sE; simpl in *; subst.
  simpl in *. subst. rewrite H4.
  


Lemma swapped_mid_single : forall {T} (A1 A2 B1 B2 : list T) a,
    swapped (A1 ++ A2) (B1 ++ B2) ->
    swapped (A1 ++ [a] ++ A2) (B1 ++ [a] ++ B2).
Proof.
  intros until 0; intros Hswap.
  inversion Hswap. subst.
  apply app_eq_app in H; apply app_eq_app in H0; sE; subst.
  apply app_eq_app in H2; sE; subst.
  *)

Inductive swapped_n {T} : nat -> list T -> list T -> Prop :=
  swapped_n_I X Y : swapped X Y -> swapped_n 0 X Y
| swapped_n_step n A B C : swapped_n n A B -> swapped B C -> swapped_n (S n) A C.
(*
Lemma can_gen_swapL_swapped_n : forall {V} rules G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2' ps,
(forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
 *)
(*

Lemma can_gen_swapL_derrec : forall {V} l rules d0 Γ1 Γ2 Ψ Γ1' Γ2',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules ns) ->
  swapped (Γ1 ++ Γ2) (Γ1' ++ Γ2') ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         [(Γ1 ++ l ++ Γ2, Ψ, d0)] ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         [(Γ1' ++ l ++ Γ2', Ψ, d0)].
Proof.
Admitted.
 *)
Inductive swapped_gen {T} Γ Δ  :=
  swapped_gen_I : (exists n, @swapped_n T n Γ Δ) -> swapped_gen Γ Δ.

(*
Lemma swapped_n_front_mid : forall {T} n (A B C D : list T),
    swapped_n n B C ->
    exists m, swapped_n m (A ++ B ++ C) ().
 *)

Lemma swapped_app_L : forall {T} n (l A B : list T),
    swapped_n n A B ->
    swapped_n n (l ++ A) (l ++ B).
Proof.
  induction n; intros until 0; intros Hswap.
  constructor. apply swapped_L. inversion Hswap. auto.
  inversion Hswap. subst.
  econstructor. eapply IHn. exact H0.
  apply swapped_L. assumption.
Qed.

Lemma swapped_n_trans : forall {T} n1 n2 (l1 l2 l3 : list T),
    swapped_n n1 l1 l2 ->
    swapped_n n2 l2 l3 ->
    exists m, swapped_n m l1 l3.
Proof.
  induction n2; intros until 0; intros H1 H2.
  inversion H2. subst. exists (S n1).
  econstructor. apply H1. apply H.
  inversion H2. subst.
  eapply IHn2 in H1. destruct H1 as [m H1].
  exists (S m). econstructor.
  apply H1. apply H3. apply H0.
Qed.

Lemma swapped_comm : forall {T} (A B : list T),
    swapped A B ->
    swapped B A.
Proof.
  intros T A B H.
  inversion H. subst.
  eapply swapped_I'.
Qed.

Lemma swapped_n_refl : forall {T} n (A : list T),
    swapped_n n A A.
Proof.
  induction n; intros. econstructor. apply swapped_same.
  econstructor. apply IHn.
  apply swapped_same.
Qed.  

Lemma swapped_n_trans_exact : forall {T} n1 n2 (l1 l2 l3 : list T),
    swapped_n n1 l1 l2 ->
    swapped_n n2 l2 l3 ->
    swapped_n (S (n1 + n2)) l1 l3.
Proof.
  induction n2; intros until 0; intros H1 H2.
  inversion H2. subst. rewrite PeanoNat.Nat.add_0_r. 
  econstructor. apply H1. apply H.
  inversion H2. subst.
  eapply IHn2 in H1. simpl.  econstructor.
  rewrite <- PeanoNat.Nat.add_succ_comm.
  apply H1. apply H3. assumption.
Qed.

Lemma swapped_n_comm : forall {T} n (A B : list T),
    swapped_n n A B ->
    swapped_n n B A.
Proof.
  induction n; intros until 0; intros H.
  constructor. inversion H. subst.
  eapply swapped_comm. assumption.
  inversion H. subst.
  eapply swapped_comm in H2.
  eapply swapped_n_I in H2.
  apply IHn in H1. 
  pose proof (swapped_n_trans_exact _ _ _ _ _ H2 H1) as H3.
  apply H3.
Qed.

Lemma swapped_n_conv : forall {T} n m (A B : list T),
  n = m ->
  swapped_n n A B ->
  swapped_n m A B.
Proof.
  intros. subst. auto.
Qed.

Lemma swapped_app_mid_L : forall {T} n (A B C D E : list T),
    swapped_n n (A ++ B ++ C ++ D) E ->
    swapped_n (S n) (A ++ C ++ B ++ D) E.
Proof.
  intros until 0; intros Hswap.
  assert (S n = S (0 + n)) as Hass.
  reflexivity.
  eapply swapped_n_conv. symmetry. apply Hass.
  eapply swapped_n_trans_exact.
  constructor. apply swapped_I'.
  apply Hswap.
Qed.


Lemma swapped_app_mid_R : forall {T} n (A B C D E : list T),
    swapped_n n E (A ++ B ++ C ++ D) ->
    swapped_n (S n) E (A ++ C ++ B ++ D).
Proof.
  intros until 0; intros H.
  eapply swapped_n_comm in H.
  eapply swapped_n_comm.
  eapply swapped_app_mid_L.
  apply H.
Qed.


Lemma swapped_n_front_mid : forall {T} n (A B C D : list T),
    swapped_n n B (C ++ D) ->
    exists m, swapped_n m (A ++ B) (C ++ A ++ D).
Proof.
  intros T n A B C D Hswap.
  eapply swapped_app_L in Hswap.
  eapply swapped_n_trans. exact Hswap.
  rewrite <- app_nil_l.
  eapply swapped_app_mid_R.
  apply swapped_n_refl.
  Unshelve. apply 0.
Qed.

Lemma swapped_gen_front_mid : forall {T} (A B C D : list T),
    swapped_gen B (C ++ D) ->
    swapped_gen (A ++ B) (C ++ A ++ D).
Proof.
  intros T A B C D Hswap. inversion Hswap as [Hs].
  destruct Hs as [n Hs].
  constructor.
  eapply swapped_n_front_mid. exact Hs.
Qed.




(*
Lemma swapped_app_mid_L : forall {T} n (A B C D E : list T),
    swapped_n n (A ++ B ++ C ++ D) E ->
    exists m,
      swapped_n m (A ++ C ++ B ++ D) E.
Proof.
  intros until 0; intros Hswap.
  eapply swapped_n_trans in Hswap.
  destruct Hswap as [m Hswap].
  exists m. apply Hswap.
  constructor. econstructor; reflexivity.
Qed.
*)

Lemma swapped_n_opp : forall {T} n (A B C : list T),
    swapped_n n B C ->
    swapped A B ->
    swapped_n (S n) A C.
Proof.
  intros until 0; intros H1 H2.
  eapply swapped_n_I in H2.
  eapply swapped_n_trans_exact in H1.
  2 : eapply H2. auto.
Qed.


Lemma swapped__n_mid : forall {T} m (l Γ1 Γ2 Γ1' Γ2' : list T),
    swapped_n m (Γ1 ++ Γ2) (Γ1' ++ Γ2') ->
    exists n, swapped_n n (Γ1 ++ l ++ Γ2) (Γ1' ++ l ++ Γ2').
Proof.
  intros until 0.
  intros H. eapply swapped_app_L in H.
  rewrite <- app_nil_l in H.
  rewrite <- app_nil_l in H at 1.
  apply swapped_app_mid_L in H.
  eapply swapped_app_mid_R in H.
  do 2 rewrite app_nil_l in H.
  exists (S (S m)). exact H.
Qed.

Ltac swap_tac_n :=
  try solve [apply swapped_n_I; swap_tac]; idtac.

Lemma swapped__gen : forall {T} (A B : list T),
  swapped A B ->
  swapped_gen A B.
Proof.
  intros T A B H.
  constructor.
  exists 0. constructor. exact H.
Qed.

Ltac swap_tac_gen :=
  try solve [apply swapped__gen; swap_tac]; idtac.

(*
  list_assoc_r ; try (apply swapped_same) ; 
    repeat (apply swapped_L || apply swapped_cons) ;  
  list_assoc_l ; repeat (apply swapped_R) ; show_swapped_1.
*)


Lemma can_gen_swapL_derrec_n : forall {V} n rules G d0 Γ Ψ Γ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules ns) ->
  swapped_n n Γ Γ' ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ, Ψ)) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ', Ψ)).
Proof.
  induction n;
    intros until 0; intros Hcan Hswap Hder.
  inversion Hswap. subst.
  eapply can_gen_swapL_imp. apply Hcan. apply Hder.
  apply H. reflexivity. reflexivity.
  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapL_imp. apply Hcan. apply H0.
  apply H1. reflexivity.
  reflexivity. assumption. assumption.
Qed.

Lemma can_gen_swapL_derrec_n_RLS : forall {V} n (rules : list (list (rel (list (PropF V)) * dir)) ->
  list (rel (list (PropF V)) * dir) -> Prop) rules0 G d0 Γ Ψ Γ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules0 (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules0 ns) ->
  rsub rules0 rules ->
  swapped_n n Γ Γ' ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ, Ψ)) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 (Γ', Ψ)).
Proof.
Admitted.
(*
  induction n;
    intros until 0; intros Hcan Hsub Hswap Hder.
  inversion Hswap. subst. 
  eapply can_gen_swapL_derrec.
  eapply can_gen_swapL_imp.
  2 : exact H. 2-3: reflexivity.
  2 : exact Hder.
  eapply can_gen_swapL_mono. exact Hsub. apply Hcan.

  apply Hder.
  apply H. reflexivity. reflexivity.
  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapL_imp. apply Hcan. apply H0.
  apply H1. reflexivity.
  reflexivity. assumption. assumption.
Qed.
*)

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
  subst. eapply can_gen_swapL_derrec_n; auto.
  eapply swapped_n_I. exact Hswap.
  exact Hd.
Qed.

Lemma can_gen_swapL_derrec_nslcext_RLS : forall {V} (rules : list (list (rel (list (PropF V)) * dir)) -> list (rel (list (PropF V)) * dir) -> Prop) rules0 G d0 seq1 seq2 Γ Ψ Γ',
  (forall (ns : list (rel (list (PropF V)) * dir)),
         derrec rules0 (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules0 ns) ->
  rsub rules0 rules ->
  swapped Γ Γ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ', Ψ) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  intros until 0. intros Hexch Hswap Hs1 Hs2 Hd.
  subst. eapply can_gen_swapL_derrec_n_RLS; auto.
  eapply swapped_n_I. exact Hs1.
Qed.

Lemma can_gen_swapL_derrec_nslcext_n : forall {V} n rules G d0 seq1 seq2 Γ Ψ Γ',
  (forall ns : list (rel (list (PropF V)) * dir),
         derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules ns) ->
  swapped_n n Γ Γ' ->
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

Lemma can_gen_swapL_derrec_nslcext_n_RLS : forall {V} n (rules : list (list (rel (list (PropF V)) * dir)) -> list (rel (list (PropF V)) * dir) -> Prop) rules0 G d0 seq1 seq2 Γ Ψ Γ',
  (forall (ns : list (rel (list (PropF V)) * dir)),
         derrec rules0 (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules0 ns) ->
  rsub rules0 rules ->
  swapped_n n Γ Γ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ', Ψ) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  induction n; intros until 0; intros Hexch Hrsub Hswap Hs1 Hs2 Hd.
  subst; eapply can_gen_swapL_derrec_nslcext_RLS in Hd.
  exact Hd. exact Hexch. exact Hrsub. inversion Hswap. exact H.
  reflexivity. reflexivity.

  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapL_derrec_nslcext_RLS in H0.
  exact H0. exact Hexch. exact Hrsub. exact H1.
  reflexivity. reflexivity.
  exact Hexch. exact Hrsub. reflexivity. reflexivity.
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
  eapply can_gen_swapL_derrec_nslcext_n in Hd.
  exact Hd. exact Hexch. exact H. exact Hs1. exact Hs2.
Qed.

Lemma can_gen_swapL_derrec_nslcext_gen_RLS : forall {V} (rules : list (list (rel (list (PropF V)) * dir)) ->
  list (rel (list (PropF V)) * dir) -> Prop) rules0 G d0 seq1 seq2 Γ Ψ Γ',
  (forall (ns : list (rel (list (PropF V)) * dir)),
         derrec rules0 (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
         can_gen_swapL rules0 ns) ->
  rsub rules0 rules ->
  swapped_gen Γ Γ' ->
  seq1 = (Γ, Ψ) ->
  seq2 = (Γ', Ψ) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq1) ->
  derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False)
         (nslcext G d0 seq2).
Proof.
  intros until 0; intros Hexch Hrsub Hswap Hs1 Hs2 Hd.
  inversion Hswap as [H]. destruct H as [n H].
  eapply can_gen_swapL_derrec_nslcext_n_RLS in Hd.
  exact Hd. exact Hexch. exact Hrsub. exact H. exact Hs1. exact Hs2.
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
  eapply swapped_n_I in Hswap.
  eapply swapped__n_mid in Hswap.
  destruct Hswap as [n HH]. 
  eapply can_gen_swapL_derrec_n.
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

(*
  SearchAbout can_gen_swapL.
  eapply Hcan.
  
  SearchAbout dersrec cons.

  intros Hcan H
  apply dersrec_forall.
  intros c Hin.
  eapply Hcan.
  destruct c. destruct ps. simpl in *. contradiction.
  
  eapply dersrec_forall in Hder.
  eapply Hcan.
  apply Hder.
  SearchAbout dersrec derrec.
 *)

Ltac list_assoc_l'_arg H := repeat (rewrite !app_assoc in H || rewrite !app_comm_cons in H).
Ltac list_assoc_r'_arg H :=
  repeat (rewrite - !app_assoc in H || rewrite - !app_comm_cons in H).
Ltac list_assoc_l'_arg_conc H := list_assoc_l'; list_assoc_l'_arg H.
Ltac list_assoc_r'_arg_conc H := list_assoc_r'; list_assoc_r'_arg H.

Ltac tac_cons_singleton_arg_hyp H a l :=
    match l with
    | nil => idtac
    | _ => rewrite (cons_singleton l a) in H
    end.


Ltac tac_cons_singleton_hyp H :=
  repeat
  match goal with
   | [ H : context [?a :: ?l] |- _] => progress (tac_cons_singleton_arg_hyp H a l)
  end.

Ltac list_assoc_r'_singleton_hyp H :=
  list_assoc_r'_arg H; tac_cons_singleton_hyp H.
  

    Ltac look_for_swap Hexch :=
      match goal with
      | [ Hcont :  dersrec ?rules ?f  (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |-
          dersrec ?rules ?f (map ?nscl (map (seqext ?Γ1' ?Γ2' ?Ψ1 ?Ψ2) ?ps)) ]
        =>
        match Γ1' with
        | Γ1 => exact Hcont
        | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch|  swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
        end;
        try 
        match Γ2' with
        | Γ2 => exact Hcont
        | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch | swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
        end
      end
    .

        Ltac look_for_swap2 Hexch :=
      match goal with
      | [ Hcont :  dersrec ?rules ?f  (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |-
          dersrec ?rules ?f (map ?nscl (map (seqext ?Γ1' ?Γ2' ?Ψ1 ?Ψ2) ?ps)) ]
        =>
        match Γ1' with
        | Γ1 => exact Hcont
        | Γ1 ++ ?A => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch|  swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
        | _ => idtac
        end;
        match Γ1 with
        | Γ1' => exact Hcont
        | Γ1' ++ ?A => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch | swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
        | _ => idtac
        end
      end
    .

Lemma can_gen_contL_gen_Forall_dersrec : forall  {V}  a (rules : rls (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2',
    (*    In a Γ1 -> In a Γ2 -> *)
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
  intros until 0. intros (* Hin1 Hin2 *) Hexch Hcon Hcont.
  inversion  Hcon; subst.
  { breakdown; clear Hcon;     cont_make_gen_L_hyp;

      try cont_solve_gen1;
      try solve [(eapply prop_contL_step10 in Hcont; look_for_swap Hexch)];
      try solve[(eapply prop_contL_step3 in Hcont; look_for_swap Hexch)];
      try solve[(eapply prop_contL_step7 in Hcont;  look_for_swap Hexch)];
      try solve [eapply prop_contL_step8 in Hcont; look_for_swap Hexch].
  }
  { breakdown; clear Hcon;     cont_make_gen_L_hyp;

      try cont_solve_gen1;
      try solve [(eapply prop_contL_step10_OPP in Hcont; look_for_swap Hexch)];
      try solve[(eapply prop_contL_step3_OPP in Hcont; look_for_swap Hexch)];
      try solve[(eapply prop_contL_step7_OPP in Hcont;  look_for_swap Hexch)];
      try solve [eapply prop_contL_step8_OPP in Hcont; look_for_swap Hexch].
  }
Qed.

Lemma can_gen_contL_gen_Forall_dersrec_RLS : forall  {V}  a rules0 (rules : rls (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2',
    (*    In a Γ1 -> In a Γ2 -> *)
    (forall (ns : list (rel (list (PropF V)) * dir)),
        derrec rules0
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules0 ns) ->
    rsub rules0 rules ->
    contracted_gen_spec a (Γ1 ++ Γ2) (Γ1' ++ Γ2')->
  Forall (can_gen_contL_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  dersrec rules (fun _ => False)
         (map (nslcext G d0) (map (seqext Γ1' Γ2' Ψ1 Ψ2) ps)).
Proof.
Admitted.
(*
intros until 0. intros (* Hin1 Hin2 *) Hexch Hcon Hcont.
  inversion  Hcon; subst.
  { breakdown; clear Hcon;     cont_make_gen_L_hyp;

      try cont_solve_gen1;
      try solve [(eapply prop_contL_step10 in Hcont; look_for_swap Hexch)];
      try solve[(eapply prop_contL_step3 in Hcont; look_for_swap Hexch)];
      try solve[(eapply prop_contL_step7 in Hcont;  look_for_swap Hexch)];
      try solve [eapply prop_contL_step8 in Hcont; look_for_swap Hexch].
  }
  { breakdown; clear Hcon;     cont_make_gen_L_hyp;

      try cont_solve_gen1;
      try solve [(eapply prop_contL_step10_OPP in Hcont; look_for_swap Hexch)];
      try solve[(eapply prop_contL_step3_OPP in Hcont; look_for_swap Hexch)];
      try solve[(eapply prop_contL_step7_OPP in Hcont;  look_for_swap Hexch)];
      try solve [eapply prop_contL_step8_OPP in Hcont; look_for_swap Hexch].
  }
Qed.
*)
Ltac cont_np_old pr :=
  match type of pr with
  | ?princrules ?ps ([], ?l) =>
  match goal with
  | [ H2 : Forall (can_gen_contL_gen ?rules)
                  (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps))|- _] =>
    match Γ1 with
    | context[ [?a] ] =>
      match Γ2 with
      | context[ [?a] ] => idtac 6
      | _ => (eapply lem20_l in H2; [ | idtac 0])
      end
    | _ =>
      match Γ2 with
      | context[ [?a] ] => (eapply lem20_r in H2; [ | idtac 1])
      | _ => idtac 5
      end
    | _ => idtac 5
    end
  | _ => idtac 2 
  end
  | _ => idtac 3
  end.

Ltac cont_np :=
  match goal with
  | [ H2 : Forall (can_gen_contL_gen ?rules)
                  (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps))|- _] =>
    match Γ1 with
    | context[ [?a] ++ ?A ] =>
      match A with
      | context[ [a] ] =>
        (* two lots of [a] in Γ1 *)
        (eapply lem20_l in H2; [ | idtac 0])
      | _ =>
        match Γ2 with
        | context[ [?a] ] =>
          (* one [a] in Γ1, one [a] in Γ2 *)
          idtac 6
        | _ =>
          (* one [a] in Γ1, no [a] in Γ2 *)
          idtac 2
        end
      end
    | context[ [?a] ] =>
      match Γ2 with
      | context[ [?a] ] =>
        (* one [a] at the end of Γ1, one [a] in Γ2 *)
        idtac 7
      | _ =>
        (* one [a] at the end of Γ1, no [a] in Γ2 *)
        idtac 3
      end
    | _ => 
      match Γ2 with
      | context[ [?a] ++ ?A ] =>
        match A with
        | context[ [a] ] =>
          (* no [a] in Γ1, two [a] in Γ2 *)
          (eapply lem20_r in H2; [ | idtac 1])
        | _ =>
          (* no [a] in Γ1, one [a] in Γ2 *)
          idtac 4
        end
      | context[ [?a] ] =>
        (* no [a] in Γ1, one [a] at end of Γ2 *)
        idtac 5
      | _ =>
        (* no [a] in either Γ1 or Γ2 *)
        idtac 8
      end
    end
  end.

Ltac app_r C :=
list_assoc_l';
 match goal with
  | [ |- context[ [(?l, ?B, ?dir)] ] ] =>
    match l with
    | ((?l1 ++ ?l2) ++ ?l3) ++ C => idtac 02; rewrite - (app_assoc l1)
    | _ => idtac 10
    end
 end.

Ltac app_nil_r_give C :=
  match goal with
  | [ |- context[ ?l ++ C ] ] => rewrite <- (app_nil_r l)
  end.

Ltac list_assoc_l'_conc_rs :=
  match goal with
  | [ |- context[ (?p1, ((?l1 ++ ?l2) ++ ?l3), ?dir) ] ] => rewrite <- (app_assoc l1)
  | _ => idtac 200
  end.

Ltac cont_np_gen :=
  list_assoc_l'_conc_rs;
  match goal with
  | [ H2 : Forall (can_gen_contL_gen ?rules)
                  (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)),
      Hexch : (forall ns : list (rel (list (PropF ?V)) * dir),
        derrec ?rules
               (fun _ : list (rel (list (PropF ?V)) * dir) => False) ns  ->
        can_gen_swapL ?rules ns),
              pr : ?princrules ?ps (?l1, ?l2),
                   rs : rsub (nslcrule (seqrule ?princrules)) ?rules |- _] =>
    match Γ1 with
    | context[ [?a] ++ ?A ] =>
      match A with
      | context[ [a] ] =>
        (* two lots of [a] in Γ1 *)
        match l1 with
        | [] => eapply (can_gen_contL_gen_Forall_dersrec a) in H2; [app_r Γ2; app_nil_r_give Γ2;
                                          list_assoc_l'_conc_rs
                                        |exact Hexch | idtac 11]
        | _  => (eapply (can_gen_contL_gen_Forall_dersrec a) in H2; [assoc_mid l1; rewrite app_assoc
                                         | exact Hexch | idtac 01])
        end
      | _ =>
        match Γ2 with
        | context[ [?a] ] =>
          (* one [a] in Γ1, one [a] in Γ2 *)
        match l1 with
        | [] => idtac 001
        | _  => (eapply (can_gen_contL_gen_Forall_dersrec a) in H2; [assoc_mid l1; rewrite app_assoc
                                         | exact Hexch | idtac 02])
        end        | _ =>
          (* one [a] in Γ1, no [a] in Γ2 *)
          idtac 2
        end
      end
    | context[ [?a] ] =>
      match Γ2 with
      | context[ [?a] ] =>
        (* one [a] at the end of Γ1, one [a] in Γ2 *)
        match l1 with
        | [] => idtac 001
        | _  => (eapply (can_gen_contL_gen_Forall_dersrec a) in H2; [assoc_mid l1; rewrite app_assoc
                                         | exact Hexch | idtac 03])
        end      | _ =>
        (* one [a] at the end of Γ1, no [a] in Γ2 *)
        idtac 3
      end
    | _ => 
      match Γ2 with
      | context[ [?a] ++ ?A ] =>
        match A with
        | context[ [a] ] =>
          (* no [a] in Γ1, two [a] in Γ2 *)
        match l1 with
        | [] => eapply (can_gen_contL_gen_Forall_dersrec a) in H2;
                [rewrite <- (app_nil_r Γ1)
                                         | exact Hexch | idtac 04]
        | _  => (eapply (can_gen_contL_gen_Forall_dersrec a) in H2; [assoc_mid l1; rewrite app_assoc
                                         | exact Hexch | idtac 04])
        end
        | _ =>
          (* no [a] in Γ1, one [a] in Γ2 *)
          idtac 4
        end
      | context[ [?a] ] =>
        (* no [a] in Γ1, one [a] at end of Γ2 *)
        idtac 5
      | _ =>
        (* no [a] in either Γ1 or Γ2 *)
        idtac 8
      end
    end
  end.



Ltac cont_tacX2 :=
  match goal with
  | [ |- contracted_gen ([?a] ++ ?B ++ [?a] ++ ?C) ([?a] ++ ?B ++ ?C)] =>
    rewrite <- app_nil_l at 1; apply contracted_genL_I'
  end.
  
Ltac nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps := 
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
try rewrite app_nil_r in acm; exact acm.



(*
Ltac list_assoc_l'_single_arg H :=
  list_assoc_l'_arg H; tac_cons_singleton H; rem_nil.
  repeat (rewrite !app_assoc in H || rewrite !app_comm_cons in H).
Ltac list_assoc_r'_arg H :=
  repeat (rewrite - !app_assoc in H || rewrite - !app_comm_cons in H).
Ltac list_assoc_l'_arg_conc H := list_assoc_l'; list_assoc_l'_arg H.
Ltac list_assoc_r'_arg_conc H := list_assoc_r'; list_assoc_r'_arg H.
 *)




(* eapply (can_gen_swapL_dersrec _ _ _ Γ1) *)
(* Left it here 17/07/19
. This is the problem ^ *)

    Ltac look_for_swap3 Hexch :=
      match goal with
      | [ Hcont :  dersrec ?rules ?f  (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |-
          dersrec ?rules ?f (map ?nscl (map (seqext ?Γ1' ?Γ2' ?Ψ1 ?Ψ2) ?ps)) ]
        =>
        match Γ1' with
        | Γ1 => exact Hcont
        | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1) in Hcont
                (*[exact Hexch|  swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont] *)
        end;
        try 
        match Γ2' with
        | Γ2 => exact Hcont
        | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1) in Hcont
                (*[exact Hexch | swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont] *)
        end
      end
    .

(*    Ltac look_for_swap3 Hexch :=
      match goal with
      | [ Hcont :  dersrec ?rules ?f  (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |-
          dersrec ?rules ?f (map ?nscl (map (seqext ?Γ1' ?Γ2' ?Ψ1 ?Ψ2) ?ps)) ]
        =>
        match Γ1' with
        | Γ1 => exact Hcont
        | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch|  swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
        end;
        try 
        match Γ2' with
        | Γ2 => exact Hcont
        | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch | swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
        end
      end
    .
 *)

    

Lemma swapped_gen_app_L : forall {T} (l A B : list T),
    swapped_gen A B ->
    swapped_gen (l ++ A) (l ++ B).
Proof.
  intros T l A B H. inversion H as [H2].
  destruct H2 as [n H2]. constructor.
  eapply swapped_app_L in H2. exists n. exact H2.
Qed.

Lemma swapped_gen_refl : forall {T} (A : list T),
    swapped_gen A A.
Proof.
  intros T A. constructor.
  exists 0. apply swapped_n_refl.
Qed.  



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
  repeat ( try list_assoc_r'_single;
   swapped_gen_tac_pre; try apply swapped_gen_refl).

Ltac derrec_swapL acm exch :=
      eapply (can_gen_swapL_derrec_nslcext) in acm;
      [exact acm | exact exch | | reflexivity | reflexivity ]; swap_tac.

Ltac derrec_swapL2 acm exch :=
      eapply (can_gen_swapL_derrec_nslcext_gen) in acm;
      [exact acm | exact exch | | reflexivity | reflexivity ]; swap_tac_n.

Ltac derrec_swapL3 acm exch :=
      eapply (can_gen_swapL_derrec_nslcext_gen) in acm;
      [exact acm | exact exch | | reflexivity | reflexivity ]; swap_gen_tac.

Ltac derrec_swapL3_RLS acm exch :=
      eapply (can_gen_swapL_derrec_nslcext_gen_RLS) in acm;
      [exact acm | exact exch | | reflexivity | reflexivity ]; swap_gen_tac.

Ltac destruct_princ :=
  match goal with
  | [ |- context[ (nslcext _ _  (seqext _ _ _ _ ?x)) ]] => destruct x
  end.

    Ltac nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch := 
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
derrec_swapL acm exch.

Ltac nsgen_sw_cont_gen4 rs sppc c c' acm inps0 swap pr inmps exch := 
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
derrec_swapL2 acm exch.

Ltac nsgen_sw_cont_gen5 rs sppc c c' acm inps0 swap pr inmps exch := 
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

Ltac nsgen_sw_cont_gen5_RLS rs sppc c c' acm inps0 swap pr inmps exch := 
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
derrec_swapL3_RLS acm exch.


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

(* Makes progress on princrules ps (l1, l2) goals *)
Ltac lt1 a acm Hexch :=
  list_assoc_r'_single;
  eapply (can_gen_contL_gen_Forall_dersrec a) in acm; [| exact Hexch | cont_solve].


Ltac lt1_RLS a acm Hexch :=
  list_assoc_r'_single;
  eapply (can_gen_contL_gen_Forall_dersrec_RLS a) in acm; [| exact Hexch | cont_solve].

Ltac lt2 a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : Forall (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Γ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contL_step1 in acm
    | ?A ++ [?a] => eapply prop_contL_step4 in acm
    | _ => match Γ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contL_step1_OPP in acm
           | [?a] ++ ?A => eapply prop_contL_step2 in acm
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

Ltac lt3_RLS a Hexch rs carry psfull loe :=
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
    | _ => lt1_RLS a acm Hexch
    end
  end.


(* Makes progress on princrules ps (l1, l2) goals *)
Ltac lt1' a Hexch :=
  list_assoc_r'_single;
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : Forall (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match l1 with
    | context[ [a] ] => idtac
    | _ => eapply (can_gen_contL_gen_Forall_dersrec a) in acm; [| exact Hexch | cont_solve]
    end
  end.

Ltac lt2' Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : Forall (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Γ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contL_step1 in acm
    | ?A ++ [?a] => eapply prop_contL_step4 in acm
    | _ => match Γ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contL_step1_OPP in acm
           | [?a] ++ ?A => eapply prop_contL_step2 in acm
           end
    end
  end.

(* Makes progress on princrules ps ([a], l2) goals *)
Ltac lt3' a Hexch :=
  list_assoc_r'_single;
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : Forall (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)),
      carry : rules_L_carry2 ?princrules,
      psfull : rules_L_ne ?princrules |- _ ] =>
    match l1 with
    | context[ [a] ] => lt2 a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | _ => idtac
    end
  end.

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

Ltac check_nil_contradiction :=
  repeat (try discriminate;
  match goal with
  | [ H : ?l1 ++ ?l2 = [] |- _ ] =>
    apply app_eq_nil_iff in H; destruct H as [H HH]
  end).

Ltac check_contradiction_pr_pre :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Δ : list (PropF ?V)),
            ?princrules ps (x ++ y, Δ) -> x = [] \/ y = [] |- _ ] =>
    match l1 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr
    end
  end.

Ltac check_contradiction_pr :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    repeat (list_assoc_r'_singleton_hyp pr; check_contradiction_pr_pre)
  end.

Ltac cont_setup_nil :=
  match goal with
    | [ acm : dersrec _ _ (map _ (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
       add_empty_goal_R l1 || (rewrite app_assoc;  add_empty_goal_R l1)
  end.

Ltac cont_setup  :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
            rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    match l1 with
    | nil => cont_setup_nil
    | _ => assoc_mid l1; rewrite app_assoc
    end
  end.

(*
(nslcrule (seqrule (@princrule_pfc V)))
*)
Lemma gen_contL_gen_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_L_oe princrules -> 
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
      (forall (ns : list (rel (list (PropF V)) * dir)),
        derrec last_rule
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL last_rule ns) ->

(*   premises_fullL_ns dir ps -> *)
(*  Forall (fun ps' => premises_fullL (fst ps')) ps -> *)
(*   premises_fullL ps -> *)
  last_rule = nslcrule (seqrule princrules) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.
Admitted.
(*
  intros until 0.  unfold gen_contL_step.
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
(* unfold rules_L_carry2 in carry. *)



(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst  ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr);
  try rewrite app_nil_r in acm;
  try rewrite app_nil_l in acm);
try solve [check_contradiction_pr];
try (lt3_RLS a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen5_RLS rs sppc c c' acm inps0 swap pr inmps exch).

}

{
(* unfold rules_L_carry2 in carry. *)



(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst  ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr);
  try rewrite app_nil_r in acm;
  try rewrite app_nil_l in acm);
try solve [check_contradiction_pr];
try (lt3_RLS a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen5_RLS rs sppc c c' acm inps0 swap pr inmps exch).
}
}
{ list_eq_nc. contradiction. }

Qed.
*)
Lemma gen_contL_gen_step_loe_lc_old: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_L_oe princrules -> 
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
      (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->

(*   premises_fullL_ns dir ps -> *)
(*  Forall (fun ps' => premises_fullL (fst ps')) ps -> *)
(*   premises_fullL ps -> *)
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
(* unfold rules_L_carry2 in carry. *)



(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst  ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr);
  try rewrite app_nil_r in acm;
  try rewrite app_nil_l in acm);
try solve [check_contradiction_pr];
try (lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen5 rs sppc c c' acm inps0 swap pr inmps exch).
}

{
(* unfold rules_L_carry2 in carry. *)



(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst  ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr);
  try rewrite app_nil_r in acm;
  try rewrite app_nil_l in acm);
try solve [check_contradiction_pr];
try (lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen5 rs sppc c c' acm inps0 swap pr inmps exch).
}
}
{ list_eq_nc. contradiction. }

Qed.

Lemma princrule_pfc_L_carry2 : forall {V : Set} ps a x Δ,
  princrule_pfc ps (a :: x, Δ) ->
  Forall (fun ps' : list (PropF V) * list (PropF V) => a = hd a (fst ps')) ps.
Proof.  intros. inversion H; subst; auto. Qed.
  
Lemma princrule_pfc_L_carry2' : forall V, rules_L_carry2 (@princrule_pfc V).
Proof. unfold rules_L_carry2.  intros.
       eapply princrule_pfc_L_carry2.  exact H.
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

Lemma gen_contL_gen_step_loe_lc_FAKE: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_L_oe princrules -> 
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
      (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->

(*   premises_fullL_ns dir ps -> *)
(*  Forall (fun ps' => premises_fullL (fst ps')) ps -> *)
(*   premises_fullL ps -> *)
  last_rule = nslcrule (seqrule princrules) ->
  gen_contL_gen_step last_rule rules ps concl.
Admitted.


(* New pr rules. *)
Lemma gen_contL_gen_step_pr_lc: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
    last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hl Hswap H2 H3 H4 H5.
  subst.
  eapply gen_contL_gen_step_loe_lc_old.
  apply princrule_pfc_L_oe'.
  apply princrule_pfc_L_carry2'. 
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

Lemma LNSKt_contL: forall (V : Set) ns
  (D : derrec (@LNSKt_rules V) (fun _ => False) ns),
      can_gen_contL_gen (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H ; subst.
admit.
admit.
admit.
admit.
admit.
eapply gen_contL_gen_step_pr_lc; try reflexivity; try assumption.
eapply LNSKt_exchL.
exact H2.
assumption.
assumption.
apply rsub_princrule_pfc_LNSKt_rules.
Qed.


all : assumption.
pose proof gen_contL_gen_step_pr_lc as HH.
unfold gen_contL_gen_step in HH.
eapply HH.
eapply gen_contL_gen_step_pr_lc.
; [> pose gen_weakL_step_b2R_lc 
  | pose gen_weakL_step_b1R_lc
  | pose gen_weakL_step_b2L_lc
  | pose gen_weakL_step_b1L_lc
  | pose gen_weakL_step_EW_lc
  | pose gen_weakL_step_pr_lc ] ; 
unfold gen_weakL_step in g ; egx g ;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.
  2 : reflexivity.
  2 : exact H2.
  2 : exact H3.
  2 : exact H4.
  2 : exact H5.
  intros ns Hder.
  unfold can_gen_swapL.
  
  eapply can_gen_swapL_mono. exact H5.
  eapply gen_swapL_lc.
  exact Hder.
  Search can_gen_swapL.
  eapply gen_swapL_lc.
  subst. 2 : exact H2.
  admit.
  subst. apply gen_swapL_lc.
  exact H.
Qed.



Lemma gen_contL_gen_step_pr_lc: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.


  eapply derrec_rmono in H. exact H.
  rsub
  SearchAbout derrec "mono".
  exact H.
  
  subst. apply gen_swapL_lc.
  exact H.


  intros. eapply gen_contL_gen_step_loe_lc_FAKE.
  apply princrule_pfc_L_oe'.
  apply princrule_pfc_L_carry2'. 
  apply princrule_pfc_L_ne'.
  subst. apply gen_swapL_lc.
  exact H.
Qed.

Lemma gen_weakL_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule_pfc V))) (fun _ => False) ns),
  can_gen_weakL (nslcrule (seqrule (@princrule_pfc V))) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_weakL_step_pr_lc.
unfold gen_weakL_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

(* ------------------------------ *)
(* RIGHT WEAKENING FOR PRINCRULES *)
(* ------------------------------ *)

Lemma gen_weakR_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_R_oe princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw_weak rs sppc (l, l0, d) (Γ, Δ, d0) acm inps0 swap. }

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

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameR_weak princrules rs pr q qin inmps acm inps0 x0.
}

{ list_eq_nc. contradiction. }

Qed.

Lemma gen_weakR_step_pr_lc: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule V)) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros. eapply gen_weakR_step_loe_lc.
        apply princrule_R_oe'. exact H. Qed.

Lemma gen_weakR_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_weakR (nslcrule (seqrule (@princrule V))) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_weakR_step_pr_lc.
unfold gen_weakR_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

(* ---------------------- *)
(* WEAKENING FOR B2RRULES *)
(* ---------------------- *)

Ltac ms_cgs_weak acm := 
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_weakL_def' in acm ;
rewrite -> ?can_gen_weakR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac use_acm1_weak acm rs ith :=
derIrs rs; [> 
apply NSlctxt2 || apply NSlclctxt' ;
assoc_single_mid ;
apply ith | 
ms_cgs acm ;
  list_assoc_r' ; simpl];
(* unfold can_gen_weakR in acm. *)
   (*   assoc_mid B; *)

   first [eapply acm | list_assoc_l'; rewrite <- app_assoc; eapply acm];
   unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl; reflexivity.


Ltac use_acm_os_weak acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith |
ms_cgs_weak acm ;
eapply acm in swap ] ;
[> eapply swap |
  unfold nslext ; unfold nslclext ; reflexivity |
  reflexivity ].

Lemma gen_weakL_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
   + use_acm_os_weak acm rs weak WBox2Rs.
   + use_acm_os_weak acm rs weak BBox2Rs. }
(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_weak rs sppc c (Γ', Δ, d) acm inps0 weak. }
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
    * use_acm_os_weak acm rs weak WBox2Rs.
    * { list_eq_nc. contradiction. }
    }
  +{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
    * use_acm_os_weak acm rs weak BBox2Rs.
    * { list_eq_nc. contradiction. }
    }
  }
Qed.

Lemma gen_weakR_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak; subst;
   acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)

   use_acm1_weak acm rs WBox2Rs. }
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs BBox2Rs. }
  }
-{ nsgen_sw_weak rs sppc c (Γ, Δ', d) acm inps0 weak. }
-{ inversion sppc ; subst ; clear sppc.  (* 2 subgoals *)
(* WBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1_weak acm rs WBox2Rs. }
*{ list_eq_nc. contradiction. }
}
(* BBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1_weak acm rs BBox2Rs. }
*{ list_eq_nc. contradiction. }
} }
Qed.

(* ---------------------- *)
(* WEAKENING FOR B1LRULES *)
(* ---------------------- *)

Ltac use_acm2s_weak acm rs ith rw:=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
apply ith |
ms_cgs_weak acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22 ; eapply acm ] ; [> | 
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; weak_tacX.

Ltac use_acm_sw_sep_weak acm rs weak ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs_weak acm ;
eapply acm in weak ] ;
[> (rewrite - list_rearr21 ; eapply weak) || 
  (list_assoc_r' ; simpl ; eapply weak) |
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ].

Lemma gen_weakL_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* swap in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs WBox1Ls. }
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs BBox1Ls. }
  }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_weak rs sppc c (Γ', Δ, d) acm inps0 weak. }

(* here, weak in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs WBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s_weak acm rs WBox1Ls ltac: (do 2 rewrite app_assoc). }

  use_acm2s_weak acm rs WBox1Ls ltac: (assoc_mid H). }
(* { use_acm2s_weak acm rs WBox1Ls ltac: (assoc_mid H). } } *)

*{ list_eq_nc. contradiction. }
}

(* BBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs BBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s_weak acm rs BBox1Ls ltac: (do 2 rewrite app_assoc). }
{ use_acm2s_weak acm rs BBox1Ls ltac: (assoc_mid H). } }

*{ list_eq_nc. contradiction. }
}
}
Qed.

Lemma gen_weakR_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; [> 
  use_acm_sw_sep_weak acm rs weak WBox1Ls |
  use_acm_sw_sep_weak acm rs weak BBox1Ls ]. }
-{ nsgen_sw_weak rs sppc c (Γ, Δ', d) acm inps0 weak. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ use_acm_sw_sep_weak acm rs weak WBox1Ls. }
*{ use_acm_sw_sep_weak acm rs weak WBox1Ls. }
*{ list_eq_nc. contradiction. }
}
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ use_acm_sw_sep_weak acm rs weak BBox1Ls. }
*{ use_acm_sw_sep_weak acm rs weak BBox1Ls. }
*{ list_eq_nc. contradiction. }
}
}  

Qed.

(* ---------------------- *)
(* WEAKENING FOR B2LRULES *)
(* ---------------------- *)

Lemma gen_weakL_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. (* no clear drs. *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* weak in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2s_weak acm rs WBox2Ls ltac: (do 2 rewrite app_assoc). 
  * use_acm2s_weak acm rs WBox2Ls ltac: (assoc_mid H). 
  }
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2s_weak acm rs BBox2Ls ltac: (do 2 rewrite app_assoc). 
  * use_acm2s_weak acm rs BBox2Ls ltac: (assoc_mid H).
  } }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_weak rs sppc c (Γ', Δ, d) acm inps0 weak. }

(* here, swap in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2s_weak acm rs WBox2Ls ltac: (do 2 rewrite app_assoc). 
  ** use_acm2s_weak acm rs WBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst. 
acacD' ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs WBox2Ls. }
*{ list_eq_nc. contradiction. }
}

(* BBox *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2s_weak acm rs BBox2Ls ltac: (do 2 rewrite app_assoc). 
  ** use_acm2s_weak acm rs BBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst. 
acacD' ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs BBox2Ls. }
*{ list_eq_nc. contradiction. }
}
}
Qed.

Lemma gen_weakR_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros lreq nsr drs acm rs. (* no clear drs! *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; 
  [> use_acm_sw_sep_weak acm rs weak WBox2Ls |
     use_acm_sw_sep_weak acm rs weak BBox2Ls ]. }
-{ nsgen_sw_weak rs sppc c (Γ, Δ', d) acm inps0 weak. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ use_acm_sw_sep_weak acm rs weak WBox2Ls. }
*{ use_drs rs drs WBox2Ls. }
*{ list_eq_nc. contradiction. }
}
+{ acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 3 subgoals *)
*{ use_acm_sw_sep_weak acm rs weak BBox2Ls. }
*{ use_drs rs drs BBox2Ls. }
*{ list_eq_nc. contradiction. }
}
}  
Qed.




(* ---------------------------------------------------------------- *)
(* -------- *)
(* OLD CODE *)
(* -------- *)



(*
Ltac cont_choose a :=
  list_assoc_r'.
match goal with
| [ |- contracted_gen_spec a ?l1 ?l2 ] =>
  match l1 with
  | [a] ++ ?A => 
  | ?A ++ [a] ++ (
  | [a] ++ ?A =>
  | ?A ++ (?B ++ ?C) => rewrite (app_assoc A)
  | ?A ++ [a] ++ ?B ++ [a] ++ ?C =>
  | [a] ++ [a] ++ ?A =>
list_assoc_r'.
 *)


(*
Ltac app_r C :=
list_assoc_l';
 match goal with
  | [ |- context[ [(?l, ?B)] ] ] =>
    match l with
    | ((?l1 ++ ?l2) ++ ?l3) ++ C => idtac 02; rewrite - (app_assoc l1)
    | _ => idtac 10
    end
 end.
*)

(*
Ltac app_r3 C :=
list_assoc_l';
 match goal with
 | [ |- context[ ( pair (((?l1 ++ ?l2) ++ ?l3) ++ C) ?B ) :: nil ] ] =>
   rewrite - (app_assoc l1)
 | _ => idtac 10
 end
   .
(*    match l with
    | ((?l1 ++ ?l2) ++ ?l3) ++ C => idtac 02; rewrite - (app_assoc l1)
    | _ => idtac 10
    end
 end.
*)
Ltac app_r2 C l1 l2 l3 :=
  list_assoc_l';
  match goal with
         |[ |- context[ ((l1 ++ l2) ++ l3) ++ C ] ] =>  rewrite - (app_assoc l1)
            end.
*)
  (* repeat  match l with
    | ((?l1 ++ ?l2) ++ ?l3) ++ C => rewrite - (app_assoc l1)
    | _ => idtac 10
    end. *)
(*
  match goal with
  | [ |- context[ ?l ] ] =>
    match l with
    | ?l1 ++ C => idtac 100
    | ?l1 ++ (?l2 ++ C) =>
    | ?l1 ++ (?l2 ++ (?l3 ++ ?l4))
 *)
(*
+
eapply prop_contL_step1 in acm; [|exact carry | exact psfull | exact rs | exact pr];
rewrite (app_cons_single _ _ a);
nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .

+
eapply prop_contL_step3 in acm; [|exact carry | exact psfull | exact rs | exact pr];
rewrite (app_cons_single _ _ a); assoc_mid H3; rewrite app_assoc;
nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .

+
eapply prop_contL_step2 in acm; [|exact carry | exact psfull | exact rs | exact pr];
rewrite (app_cons_single _ _ a);
nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .

+
eapply prop_contL_step5 in acm; [|exact carry | exact psfull | exact rs | exact pr];
rewrite (app_cons_single _ _ a); rewrite app_assoc;
nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .

+ admit.

+ 
eapply prop_contL_step4' in acm; [|exact carry | exact psfull | exact rs | exact pr];
rewrite (app_cons_single _ _ a);
nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .

+
eapply prop_contL_step4' in acm; [|exact carry | exact psfull | exact rs | exact pr];
 rewrite app_comm_cons; rewrite app_assoc;
   nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .

+

  Forall 

  
eapply prop_contL_step6 in acm; [|exact carry | exact psfull | exact rs | exact pr];
  change (A ++ a :: ?x) with (A ++ [] ++ [a] ++ x);
  rewrite app_assoc;
   nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .


+
 eapply prop_contL_step1 in acm; [|exact carry | exact psfull | exact rs | exact pr];
  rewrite (app_cons_single _ _ a);
   nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .

+
eapply prop_contL_step3 in acm; [|exact carry | exact psfull | exact rs | exact pr];
  rewrite (app_cons_single _ _ a); rewrite <- (app_nil_r (A ++ [a]));
nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .


+ 
  eapply prop_contL_step7 in acm; [|exact carry | exact psfull | exact rs | exact pr];
  rewrite app_comm_cons; rewrite app_assoc;
  rewrite <- (app_nil_r (A ++ _));
nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps .

  +

*)


(*
(eapply lem15 in acm; [|exact carry | exact psfull | exact rs | exact pr]) ||
(eapply lem12 in acm; [|exact carry | exact psfull | exact rs | exact pr]) ||
(eapply lem16 in acm; [|exact carry | exact psfull | exact rs | exact pr]) ||                    
(change ([a]++C) with ([] ++ [a] ++ C) in acm;
  eapply lem12 in acm; [|exact carry | exact psfull | exact rs | exact pr]) ||
(rewrite (app_cons_single _ _ a); rewrite app_assoc;
   change ([a]++C) with ([] ++ [a] ++ C) in acm;
   eapply lem15 in acm; [|exact carry | exact psfull | exact rs | exact pr]) ||
(rewrite app_comm_cons;  rewrite app_assoc;
  eapply lem16 in acm; [|exact carry | exact psfull | exact rs | exact pr]) ||

idtac;

nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps ||
(rewrite (app_cons_single _ _ a);
  nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps) || idtac.
*)
(*
+
  rewrite (app_cons_single _ _ a). 

nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps.

*)
        (*
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
try rewrite app_nil_r in acm; exact acm.
 *)
    (*
  +   
  rewrite (app_cons_single _ _ a). 

  nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps.
*)
(*
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
try rewrite app_nil_r in acm; exact acm.
*)
(*
  +
nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps. 
*)
(*    
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
try rewrite app_nil_r in acm; exact acm.
 *)


(*
Lemma can_gen_contL_imp'': forall {V : Set} 
                                (rules : rls (list (rel (list (PropF V)) * dir))) ns,
    can_gen_contL rules ns ->
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
                can_gen_swapL rules ns) ->
    forall G K seq Γ Δ Γ' Γ'' (d : dir), 
      contracted Γ' Γ'' ->
      swapped Γ Γ' ->
      ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
      derrec rules (fun _ => False) (G ++ (pair Γ'' Δ, d) :: K).
Proof.
  intros until 0. intros Hcont Hswap. intros. subst.
  rewrite -> can_gen_contL_def' in Hcont.
  eapply Hcont in H; try reflexivity.
  apply Hswap in H.
  eapply can_gen_swapL_def' in H.
  apply H. apply H0. reflexivity. reflexivity.
Qed.

*)
  
(*
Lemma can_gen_contL_swapL_pre : forall {V} rules G d0 Γ Γ' Ψ1 ss2 Ψ2,
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    swapped Γ Γ' ->
    can_gen_contL rules
                  (nslcext G d0 (Γ, Ψ1 ++ ss2 ++ Ψ2)) ->
    can_gen_contL_genL rules
                  (nslcext G d0 (Γ', Ψ1 ++ ss2 ++ Ψ2)).
Proof.
  intros. rewrite can_gen_contL_genL_def'. intros.
  subst. unfold nslcext in *.
  apply partition_2_2 in H3.

sE ; subst.
  + inversion H2. subst.
    eapply can_gen_contL_imp in H1.
    2 : exact H2. 2 : rewrite <- app_assoc. 2 : reflexivity.
    2 : reflexivity.
    fold (app x [(Γ, Ψ1 ++ ss2 ++ Ψ2, d0)]) in H1.
    apply H in H1.
    rewrite app_cons_single.
    rewrite app_assoc. 
    eapply can_gen_swapL_imp. apply H1. apply H0.
    2 : reflexivity. solve_eqs.
  +     inversion H3. subst.
        inversion H2. subst.
    eapply can_gen_contL_imp in H1.
    3 : reflexivity. 3 : reflexivity.
 *)
(*
Lemma can_gen_contL_swapL_pre : forall {V} rules d0 Γ Γ' Ψ,
    (forall ns : list (rel (list (PropF V)) * dir),
        derrec rules
               (fun _ : list (rel (list (PropF V)) * dir) => False) ns ->
        can_gen_swapL rules ns) ->
    swapped Γ Γ' ->
    can_gen_contL rules
                  (nslcext [] d0 (Γ, Ψ)) ->
    can_gen_contL rules
                  (nslcext [] d0 (Γ', Ψ)).
Proof.
  intros. rewrite can_gen_contL_def'. intros.
  subst. unfold nslcext in *. simpl in *.
  destruct G.
  + simpl in *. inversion H3. subst.
    clear H3.
    eapply can_gen_contL_def' in H1.
    4 : reflexivity.
    rewrite <- app_nil_r.    rewrite <- app_nil_l.
    eapply can_gen_swapL_imp.
    2 : exact H0.
    apply H.
    3 : reflexivity.
  admit.
  +  simpl in *. destruct G; simpl in *; discriminate.
Qed.

  apply partition_2_2 in H3.

sE ; subst.
  + inversion H2. subst.
    eapply can_gen_contL_imp in H1.
    2 : exact H2. 2 : rewrite <- app_assoc. 2 : reflexivity.
    2 : reflexivity.
    fold (app x [(Γ, Ψ, d0)]) in H1.
    apply H in H1.
    rewrite app_cons_single.
    rewrite app_assoc. 
    eapply can_gen_swapL_imp. apply H1. apply H0.
    2 : reflexivity. solve_eqs.
  +     inversion H3. subst.
        inversion H2. subst.
    eapply can_gen_contL_imp in H1.
    3 : reflexivity. 3 : reflexivity.
    
Admitted.
 *)

(*
Lemma contracted_gen_swapped : forall {T} Γ A B C (a : T),
    swapped Γ (A ++ [a] ++ B ++ [a] ++ C) ->
    contracted_gen Γ (A ++ [a] ++ B ++ C).
Proof.
  intros.
  inversion H. subst.
  apply app_eq_app in H1.
  destruct H1 as [m [[H2 H3] | [H2 H3]]].
  subst. rewrite <- app_assoc.
  apply cont_gen_L.
  


  contracted_genL.
  SearchAbout list app ex.
*)

(*
    apply H1. 
    apply H.  eapply H1.
    rewrite <- app_assoc. reflexivity. reflexivity.
    2 : fold (app x [(Γ, Ψ1 ++ ss2 ++ Ψ2, d0)]).
    apply swapped_same. 2 : reflexivity.
    
    apply swapped_refl.
    3 : reflexivity. 
  inversion H2. subst X Y. subst Γ0. reflexivity. subst. reflexivity.
  unfold nslcext. reflexivity.
  reflexivity.
  5 : reflexivity.
SearchAbout can_gen_swapL swapped.
  unfold can_gen_swapL in H.
  
  eapply H.
Admitted.
*)



(* Left it here 10/07 *)
(* For can_gen_contL_swapL, see whether there is a way to prove it.
If not, see if there is a different lemma to be proved by checking out where it's used.
If not, consider:
- changing contracted to be anywhere
- just proving for princrule_pfc, not the general princrules that satisfy certain constraints. Will this come across the same problems?
- try restating the conditions (probs won't help)
 *)


  (*
  can_gen_contL rules
           (nslcext G d0 (seqext Γ1 Γ2 Ψ1 Ψ2 seq2)) ->
  can_gen_contL rules
    (nslcext G d0
       (seqext Γ1 ([p] ++ Γ2) Ψ1 Ψ2 (rem_hd (fst seq2), snd seq2))).
  unfold can_gen_contL in *.
  intros. subst. eapply Hass.
  destruct seq2 as [seq2' d'].
  simpl. unfold nslcext. simpl.[
  simpl. reflexivity.

  inversion Hass.
SearchAbout In map.
  eapply H4 in H3.
  Print can_gen_contL.
  eapply Forall_forall in H3.
  instantiate (1 := (nslcext G d0
       (seqext Γ1 Γ2 Ψ1 Ψ2 seq2))). in H3.


  SearchAbout Forall nslcext.
  apply (Forall_forall
  eapply Forall_forall in H3.
  unfold can_gen_contL.
  unfold can_gen_contL in H3.
  intros. subst.
  eapply H3. simpl.
  Focus 2. reflexivity.
  
  


  apply H3.

  
  induction ps; intros until 0; intros carry ne pr Hswap Hrs Hseq .
  simpl in *. auto.
  simpl in *. destruct a as [A B].
  simpl. apply Forall_cons_inv in Hseq.
  destruct Hseq as [HP Hseq].
  pose proof pr as Qpr. pose proof pr as Ppr.
  apply Forall_cons.
  +  unfold rules_L_carry2 in carry.
     apply carry in Qpr. apply Forall_cons_inv in Qpr.
     destruct Qpr as [Hhd Qpr].
     simpl in Hhd. destruct A.
     ++ unfold rules_L_ne in ne. apply ne in Ppr.
        apply Forall_cons_inv in Ppr. simpl in *.
        destruct Ppr. contradiction. simpl. auto.
     ++ simpl in *. subst.
        unfold can_gen_contL.
        intros until 0. intros Heq1 Heq2.
        subst. unfold nslcext in Heq1.
Admitted.
*)


(*
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.
*)
(*
  3 : reflexivity. 2 : reflexivity.
  SearchAbout In map.
  SearchAbout dersrec.
  unfold can_gen_contL_gen.
  intros.
  Check (dersrec rules (fun _ => False) (map (nslcext G d0) (map (seqext (A ++ []) (H5 ++ C) Ψ1 Ψ2) ps))).

  specialize (fwd H3 (nslcext G d0
       (seqext Γ1 Γ2 Ψ1 Ψ2 seq2))). clear rev.
  assert ( In (nslcext G d0 (seqext Γ1 Γ2 Ψ1 Ψ2 seq2))
              (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps))) as Hass.
  apply in_map. apply in_map. auto.
  apply fwd in Hass. clear fwd.
  unfold rules_L_carry2 in H.
  pose proof H1 as H1'.
  apply H in H1.
  edestruct Forall_forall as [fwd rev].
  pose proof (fwd H1 seq2 Hin2) as H5.
  destruct seq2 as [ss1 ss2]. simpl in *.
  destruct ss1.
  unfold rules_L_ne in H0. apply H0 in H1'.
  clear fwd rev.
  edestruct Forall_forall as [fwd rev].
  pose proof (fwd H1' ([], ss2) Hin2).
  simpl in H6. contradiction.
  destruct ps. contradiction. simpl. auto.
  simpl in *. subst.  clear rev fwd.
  apply can_gen_contL_swapL; auto.    
 *)

(*
Lemma lem21 : forall  {V}  (rules : rls (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2' a,
    In a Γ1 -> In a Γ2 ->
    contracted_gen (Γ1 ++ Γ2) (Γ1' ++ Γ2')->
  Forall (can_gen_contL_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  dersrec rules (fun _ => False)
         (map (nslcext G d0) (map (seqext Γ1' Γ2' Ψ1 Ψ2) ps)).
Proof.
  intros until 0. intros Hin1 Hin2 Hcon Hcont.
  inversion  Hcon; subst.
  { apply app_eq_app in H.
    destruct H as [m [[H1 H2] | [H1 H2]]]; subst.
    + destruct m.
      ++ simpl in H2. subst.   apply app_eq_app in H2.
       destruct H2 as [m2 [[H21 H22] | [H21 H22]]]; subst.
       
    eapply prop_contL_step10 in Hcont.
      exact Hcont. }
  { eapply prop_contL_step11 in Hcont.
      exact Hcont. }
Qed.
*)
(*
    simpl in *. apply cons_eq_app in H2.
  destruct H2 as [[ H2 H3] | [y' [H2 H3]]]; subst.
++ rewrite app_nil_r in Hcon Hcont.
  apply app_eq_app in H0.
  destruct H0 as [m' [ [H1' H2'] | [H1' H2']]]; subst.
  +++ apply cons_eq_app in H2'.
      destruct H2' as [[ H2' H3'] | [y'' [H2' H3']]]; subst.
      ++++ simpl in *.
           eapply prop_contL_step6' in Hcont.
           rewrite app_nil_r. exact Hcont.
      ++++ apply app_eq_app in H3'.
           destruct H3' as [m' [ [H1' H2'] | [H1' H2']]]; subst.
           eapply prop_contL_step6' in Hcont.
  
  symmetry in H0. apply partition_2_2 in H0.
  SearchAbout list ex app.
  apply partition_2_3 in H.
 *)

(*   { breakdown; clear Hcon;     cont_make_gen_L_hyp ;

      try cont_solve_gen1;
      try solve [(eapply prop_contL_step10 in Hcont; look_for_swap Hexch)].

    eapply prop_contL_step10_OPP in Hcont; look_for_swap Hexch.

eapply prop_contL_step11 in Hcont; look_for_swap Hexch.


try solve[(eapply prop_contL_step3 in Hcont; look_for_swap Hexch)].
      try solve[(eapply prop_contL_step7 in Hcont;  look_for_swap Hexch)].
      try solve [eapply prop_contL_step8 in Hcont; look_for_swap Hexch].
  { 
    eapply prop_contL_step10 in Hcont.
    eapply (can_gen_swapL_dersrec _ _ _ A); [exact Hexch | swap_tac |
                                            list_assoc_r'; tac_cons_singleton; rem_nil].
    ; look_for_swap Hexch.
    eapply (can_gen_swapL_dersrec _ _ _ (A ++ [a] ++ x2));
      [exact Hexch | swap_tac | list_assoc_r'; tac_cons_singleton; rem_nil; apply Hcont].
                                               
try solve [eapply prop_contL_step7 in Hcont;
    eapply (can_gen_swapL_dersrec _ _ _ (A ++ [a] ++ x2)); [exact Hexch | swap_tac | list_assoc_r'; tac_cons_singleton; rem_nil; look_for_swap Hexch] ].

    eapply prop_contL_step7 in Hcont.
list_assoc_r'; tac_cons_singleton; repeat (rewrite 
       eapply prop_contL_step7 in Hcont; look_for_swap Hexch.

look_for_swap Hexch.
    eapply prop_contL_step10 in Hcont.
    rewrite app_nil_l in Hcont.


look_for_swap Hexch.    


    eapply can_gen_swapL_dersrec;
      try assumption.
    admit.
    

    eapply prop_contL_step10 in Hcont.

    SearchAbout swapped.
    
admit.

(*    
    apply app_eq_app in H.
    apply app_eq_app in H0.    
    sE; subst.
    apply app_eq_app in H2.
    apply app_eq_app in H3.
    sE; subst.
    apply unit_eq_app in H.
    apply unit_eq_app in H0.
    sE; subst.
    rewrite app_nil_r in Hcont.
    rewrite app_nil_r.
*)    


    admit.
    admit.
    admit.
    admit.

    cont_make_gen_L.

    apply Hcont.
    
    eapply prop_contL_step2 in Hcont.                    
    
    
    SearchAbout ([?a] = ?x ++ ?y).
    
    destruct H as [m [[H1 H2] | [H1 H2]]]; subst.
    + destruct m.
      ++ rewrite app_nil_l in H2. subst.   apply app_eq_app in H0.
         destruct H0 as [m0 [[H01 H02] | [H01 H02]]]; subst.
         +++ rewrite <- (app_nil_l ([a] ++ _)) in Hcont.
             destruct m0.
             * rewrite app_nil_l in H02. subst.
               eapply prop_contL_step10 in Hcont.                    
               exact Hcont.
             * simpl in H02. inversion H02.
               subst. apply app_eq_app in H1.
               destruct H1 as [m1 [[H11 H12] | [H11 H12]]]; subst.
               ** apply dersrec_forall.
                  intros c Hc.
                  unfold can_gen_swapL in Hexch.
                  apply in_nslc_seq in Hc.
                  destruct Hc as [[p2 p1] [Hc Hcin]].

                  subst. unfold nslcext. unfold seqext.
                  rewrite <- app_assoc.
                  eapply Hexch. 3 : reflexivity.
                  2 : reflexivity.
                  eapply prop_contL_step10 in Hcont.
                  eapply lem8 in Hcin.
                  eapply dersrec_forall in Hcin.
                  simpl in Hcin. apply Hcin.
                  simpl in *. rewrite app_nil_r in Hcont.
                  rewrite <- app_assoc in Hcont.
                  exact Hcont.
               ** apply dersrec_forall.
                  intros c Hc.
                  unfold can_gen_swapL in Hexch.
                  apply in_nslc_seq in Hc.
                  destruct Hc as [[p2 p1] [Hc Hcin]].
                  subst. unfold nslcext. unfold seqext.
                  rewrite <- app_assoc.
                  eapply Hexch. 3 : reflexivity.
                  2 : reflexivity.
                  eapply prop_contL_step10 in Hcont.
                  eapply lem8 in Hcin.
                  eapply dersrec_forall in Hcin.
                  simpl in Hcin. apply Hcin.
                  simpl in *. rewrite app_nil_r in Hcont.
                  rewrite app_assoc in Hcont.
                  exact Hcont.
         +++ rewrite <- (app_nil_l ([a] ++ _)) in Hcont.
             eapply prop_contL_step10 in Hcont.                    
             apply dersrec_forall.
             intros c Hc.
             unfold can_gen_swapL in Hexch.
             apply in_nslc_seq in Hc.
             destruct Hc as [[p2 p1] [Hc Hcin]].
             subst. unfold nslcext. unfold seqext.
             eapply Hexch. 3 : reflexivity.
             2 : reflexivity.
             eapply lem8 in Hcin.
             eapply dersrec_forall in Hcin.
             simpl in Hcin.
             assoc_mid p2. apply Hcin.
             simpl in *. rewrite app_nil_r in Hcont.
             exact Hcont.
    ++ inversion H2. subst.
       apply app_eq_app in H3.
       destruct H3 as [m3 [[H31 H32] | [H31 H32]]]; subst.      
Admitted.
 *)


(*


swapped_gen_tac.
swapped_gen_tac.
swapped_gen_tac.

Search swapped_gen.
swapped_gen (l ++ A) (B ++ l ++ C)
Ltac lntacs.assoc_mid l :=
  list_assoc_r'; rewrite ?app_comm_cons;
   repeat (rewrite -(app_assoc _ l _); fail 1) || rewrite app_assoc; rewrite
   -(app_assoc _ l _)



(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen4 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
 nsgen_sw_cont_gen4 rs sppc c c' acm inps0 swap pr inmps exch).

(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
 nsgen_sw_cont_gen4 rs sppc c c' acm inps0 swap pr inmps exch).

lt3 a exch rs carry psfull loe. repeat rewrite app_nil_l. cont_setup.
derrec_swapL.
can_gen_swapL_derrec_nslcext.
 nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.




admit.

(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
 nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).


admit.

(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
 nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).

admit.
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
(lt3 a exch rs carry psfull loe; repeat rewrite app_nil_l; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).




}

{


lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
  nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
  nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
  nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;  
lt2 a Hexch; [| exact carry | exact psfull| exact rs| exact pr];
rewrite app_nil_l; cont_setup;
  nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

lt3 a exch rs carry psfull loe; cont_setup; 
  nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;  
lt2 a Hexch; [| exact carry | exact psfull| exact rs| exact pr];
rewrite app_nil_l; cont_setup;
  nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
lt3 a exch rs carry psfull loe; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.


pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;
lt3 a exch rs carry psfull; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit.
admit.

pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;
lt3 a exch rs carry psfull; cont_setup;
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;
lt3 a exch rs carry psfull; cont_setup;
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.


admit.

pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;
lt3 a exch rs carry psfull; cont_setup; 
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.


try ( lt1 a exch ; cont_setup;
    nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).
try ( lt3 a exch ; cont_setup;
      nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).

lt1 a acm exch.


try (lt2 a exch; [| exact carry | exact psfull| exact rs| exact pr];
cont_setup;
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch).

eapply prop_contL_step1_OPP in acm; [| exact carry | exact psfull| exact rs| exact pr].
cont_setup.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

eapply prop_contL_step2 in acm; [| exact carry | exact psfull| exact rs| exact pr].
cont_setup.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

eapply prop_contL_step4 in acm; [| exact carry | exact psfull| exact rs| exact pr].
cont_setup.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit.

eapply prop_contL_step1_OPP in acm; [| exact carry | exact psfull| exact rs| exact pr].
cont_setup.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

eapply prop_contL_step1 in acm; [| exact carry | exact psfull| exact rs| exact pr].
cont_setup.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit.

eapply prop_contL_step1 in acm; [| exact carry | exact psfull| exact rs| exact pr].
cont_setup.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
admit.

eapply prop_contL_step1 in acm; [| exact carry | exact psfull| exact rs| exact pr].
cont_setup.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

eapply prop_contL_step1_OPP in acm; [| exact carry | exact psfull| exact rs| exact pr].
cont_setup.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit.
admit.



(* Left it here 18/07/19 *)
(* 
Keep going! Finished all the goals except those with a in pr. 
Work on those, clean up, then work on the second (and last) 
major goal which should be a mirror of sorts.
*)





(* 
Work on the best way to use can_gen_contL_gen_Forall_dersrec, cont_solve, etc.
In particular, consider

cont_np_gen;
try nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps;
try cont_solve a.


 *)

admit.
admit.
admit.

admit.

admit.
admit.

admit.

admit.
admit.
admit.

admit.
admit.





admit. (* [a] in pr *)



assoc_mid H3; rewrite app_assoc.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit. (* [a] in pr *)

assoc_mid B; rewrite app_assoc.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.


admit. (* [a] in pr *)
admit. (* [a] in pr && *)

rewrite app_assoc;  add_empty_goal_R (A ++ [a]).
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit. (* [a] in pr *)

rewrite app_assoc;  add_empty_goal_R (A ++ [a]).
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

rewrite app_assoc;  add_empty_goal_R (A ++ [a]).
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

assoc_mid H3; rewrite app_assoc.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit. (* [a] in pr *)
admit. (* [a] in pr && *)
assoc_mid l; rewrite app_assoc.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit. (* [a] in pr *)

assoc_mid H7; rewrite app_assoc.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

rewrite app_assoc;  add_empty_goal_R (A ++ [a]).
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit. (* [a] in pr *)

rewrite app_assoc;  add_empty_goal_R (A ++ [a]).
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

assoc_mid l; rewrite app_assoc.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

rewrite app_assoc;  add_empty_goal_R (Φ1 ++ [a]).
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

assoc_mid H; rewrite app_assoc.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.

admit. (* [a] in pr *)
admit. (* [a] in pr && *)
admit. (* [a] in pr && *)

assoc_mid l; rewrite app_assoc.
nsgen_sw_cont_gen3 rs sppc c c' acm inps0 swap pr inmps exch.
}


assoc_mid H3; rewrite app_assoc;
    derIrs rs  ; [apply NSlcctxt'; apply Sctxt_e'; exact pr |];
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
destruct_princ.

derrec_swapL acm exch.


swap_tac.

SearchAbout derrec nslcext can_gen_swapL.
eapply (can_gen_swapL_dersrec _ _ _ A). in acm. ; [exact Hexch|  swap_tac | list_assoc_r'_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont].
list_assoc_r'_singleton_hyp acm; rem_nil.
look_for_swap exch.
list_assoc_r'_arg_single_hyp acm. look_for_swap exch.
eapply can_gen_swapL_derrec_n.
exact exch. 2 : exact acm.
constructor. look_for_swap exch.
Search derrec swapped_n.
try rewrite app_nil_r in acm; exact acm.


admit.
assoc_mid H3.
try nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps.



eapply (can_gen_contL_gen_Forall_dersrec a) in acm; [| exact exch | ].
2 : 

  list_assoc_r'_single;
  apply cont_gen_spec_basic.
  apply cont_gen_spec_rem_sml_L.
  2 : (cont_rem_head; cont_rem_tail; cont_rem_mid_simp;
  list_assoc_r'_single; apply cont_gen_spec_basic).



2 : cont_solve a.
try lt1 a exch.
eapply (can_gen_contL_gen_Forall_dersrec a) in acm; [| exact exch|].
2 : cont_solve a.
2 : cont_rem_head.
2 : cont_rem_tail.

2 : apply cont_gen_spec_rem_sml_L.


  cont_rem_head; cont_rem_tail; cont_rem_mid_simp;
  apply cont_gen_spec_basic.


Focus 2.
  cont_rem_head; cont_rem_tail; cont_rem_mid_simp;
  apply cont_gen_spec_basic.

try lt1 a exch.



admit.
admit.
cont_solve a.
Ltac cont_gen_spec_solve :=
  list_assoc_r'; tac_cons_singleton; rem_nil;
  match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    match l1 with
    | 
Search cont_gen_spec.
admit.
eapply (can_gen_contL_gen_Forall_dersrec a) in acm; [ | exact exch | ].

cont_np_gen;
try nsgen_sw_cont_gen2 rs sppc c c' acm inps0 swap pr inmps;
try cont_solve a.


(* Left it here 13/07/19 *)
(* Keep working on 
cont_np_gen to solve the following goals.
Then clean it up and make the tactic simpler.
Along the way I may need to add to cont_solve, 
but I think it should be good.
*)

admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
}
destruct x; discriminate.
Admitted.


  + admit.
  + rewrite app_comm_cons;  rewrite app_assoc.
eapply lem16 in acm.
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
try rewrite app_nil_r in acm; exact acm.



 *)



(* GOOD STUFF
+ eapply lem12 in acm.
  2 : exact carry.
  2 : exact psfull.
  2 : exact rs.
  2 : exact pr.

  rewrite (app_cons_single _ _ a).
  derIrs rs  .
apply NSlcctxt'; apply Sctxt_e'; exact pr.
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ;
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 .
subst.
eapply dersrec_forall in acm.
2 : apply inps0.
rewrite app_nil_r in acm. auto.

+ eapply lem15 in acm.
    2 : exact carry.
  2 : exact psfull.
  2 : exact rs.
  2 : exact pr.


  rewrite (app_cons_single _ _ a).
    assoc_mid H3.
    rewrite app_assoc.
    derIrs rs  .
apply NSlcctxt'; apply Sctxt_e'; exact pr.
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ;
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 .
subst.
eapply dersrec_forall in acm.
2 : apply inps0. auto.
+
  rewrite app_nil_r in acm.
  change ([a]++C) with ([] ++ [a] ++ C) in acm.
  eapply lem12 in acm.
  2 : exact carry.
  2 : exact psfull.
  2 : exact rs.
  2 : exact pr.

  rewrite (app_cons_single _ _ a).
  derIrs rs  .
apply NSlcctxt'; apply Sctxt_e'; exact pr.
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ;
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 .
subst.
eapply dersrec_forall in acm.
2 : apply inps0.
auto.
  
+
    change ([a]++C) with ([] ++ [a] ++ C) in acm.
 eapply lem15 in acm.
    2 : exact carry.
  2 : exact psfull.
  2 : exact rs.
  2 : exact pr.


  rewrite (app_cons_single _ _ a).
    assoc_mid B.
    rewrite app_assoc.
    derIrs rs  .
apply NSlcctxt'; apply Sctxt_e'; exact pr.
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ;
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 .
subst.
eapply dersrec_forall in acm.
2 : apply inps0. auto.
 *)


(*
+ admit.

+
  

  rewrite (app_cons_single _ _ a).

nsprsame_cont2 rs pr q qin inmps acm inps0 x0.
cont_tacX.

unfold rules_L_ne in psfull.
assert ( In (l, l1) ps) as Hin.
apply lem9 in HH. auto.
pose proof pr as Cpr.
apply carry in Cpr.
assert (a = hd a (fst (l,l1))).
eapply Forall_forall in Cpr; [exact Cpr|]; auto.
pose proof pr as Fpr. apply psfull in Fpr.
assert (fst (l,l1) <> []).
eapply Forall_forall in Fpr; [exact Fpr|]; auto.
destruct l. simpl in *. contradiction.
simpl in *. subst.
eapply (contracted_I _ _ _ [] l);
apps_eq_tac.
destruct ps; simpl; auto. 

+ 
rewrite (app_cons_single _ _ a).

nsprsame_cont2 rs pr q qin inmps acm inps0 x0.

apply cont_R. apply cont_L.
apply cont_small.

+
change ([a] ++ B) with ([] ++ [a] ++ B).  
destruct l. simpl in H4. subst.
nsprsame_cont2 rs pr q qin inmps acm inps0 x0.
admit.
simpl in H4. inversion H4 as [[H6 H5]].
destruct l.
simpl in H5. subst.
simpl.
rewrite (app_cons_single _ _ p).



eapply lem11 in acm. simpl in acm.
apply lem7' in acm.
eapply lem11' in acm.

derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
             apply Sctxt_e || apply Sctxt_e' ; exact pr |] .
apply dersrec_all. rewrite app_nil_r in acm. auto.
unfold rules_L_carry2. apply carry.
apply psfull. apply pr.
unfold rules_L_carry2. eapply carry.
apply psfull. apply pr.
admit. apply rs.
subst. change (p :: p0 :: l) with ([p] ++ [p0] ++ l) in pr.
apply loe in pr. destruct pr; discriminate.

Lemma gen_contL_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_L_oe princrules -> 
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
(*   premises_fullL_ns dir ps -> *)
(*  Forall (fun ps' => premises_fullL (fst ps')) ps -> *)
(*   premises_fullL ps -> *)
  last_rule = nslcrule (seqrule princrules) ->
  gen_contL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_contL_step.
intros loe carry psfull lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
rewrite can_gen_contL_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw_cont rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

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

unfold rules_L_carry2 in carry.

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)).

+ change ([a;a]) with ([a] ++ [a]) in pr.
  apply loe in pr; destruct pr; discriminate.
+ 
rewrite (app_cons_single _ _ a).

nsprsame_cont2 rs pr q qin inmps acm inps0 x0.
cont_tacX.

unfold rules_L_ne in psfull.
assert ( In (l, l1) ps) as Hin.
apply lem9 in HH. auto.
pose proof pr as Cpr.
apply carry in Cpr.
assert (a = hd a (fst (l,l1))).
eapply Forall_forall in Cpr; [exact Cpr|]; auto.
pose proof pr as Fpr. apply psfull in Fpr.
assert (fst (l,l1) <> []).
eapply Forall_forall in Fpr; [exact Fpr|]; auto.
destruct l. simpl in *. contradiction.
simpl in *. subst.
eapply (contracted_I _ _ _ [] l);
apps_eq_tac.
destruct ps; simpl; auto. 

+ 
rewrite (app_cons_single _ _ a).

nsprsame_cont2 rs pr q qin inmps acm inps0 x0.

apply cont_R. apply cont_L.
apply cont_small.

+
change ([a] ++ B) with ([] ++ [a] ++ B).  
destruct l. simpl in H4. subst.
nsprsame_cont2 rs pr q qin inmps acm inps0 x0.
admit.
simpl in H4. inversion H4 as [[H6 H5]].
destruct l.
simpl in H5. subst.
simpl.
rewrite (app_cons_single _ _ p).



eapply lem11 in acm. simpl in acm.
apply lem7' in acm.
eapply lem11' in acm.

derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
             apply Sctxt_e || apply Sctxt_e' ; exact pr |] .
apply dersrec_all. rewrite app_nil_r in acm. auto.
unfold rules_L_carry2. apply carry.
apply psfull. apply pr.
unfold rules_L_carry2. eapply carry.
apply psfull. apply pr.
admit. apply rs.
subst. change (p :: p0 :: l) with ([p] ++ [p0] ++ l) in pr.
apply loe in pr. destruct pr; discriminate.




simpl in *.inversion H5. subst.
apply loe in pr.

rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ; 
rewrite -> Forall_forall in acm ;
rename_last inps0 ;  eapply in_map in inps0 ;
eapply in_map in inps0 ;
pose proof inps0 as HH .
eapply acm in inps0 .
clear acm .
subst.
rewrite -> ?can_gen_contL_def' in inps0 ;
rewrite -> ?can_gen_contR_def' in inps0 ;
subst ;
destruct x0 ;
unfold seqext ;
unfold nsext ; unfold nslcext .
eapply inps0 ;
  [> | unfold nsext ; unfold nslcext ; reflexivity |
   unfold seqext ; reflexivity ].
Print can_gen_contL.
Print contracted.

nsprsame_cont2 rs pr q qin inmps acm inps0 x0.



eapply lem10 in acm.
apply lem7' in acm.
eapply lem10 in acm.


SearchAbout Forall can_gen_contL.

  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
Forall P (map (nslcext G d0
   (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps))) ->
Forall P (map (nslcext G d0
   (map (seqext Γ1 ([p] ++ Γ2) Ψ1 Ψ2)
      (map (fun p =>(rem_hd (fst p), snd p)) ps)))).


(* Left it here, try to write the above lemma. *)
(* Not really sure how to incorporate the 
exchange lemmas. *)

nsprsame_cont2 rs pr q qin inmps acm inps0 x0.
admit.
(*
rewrite (app_cons_single _ _ a).
*)
destruct l.
- simpl in *.
subst. rewrite <- app_assoc.

nsprsame_cont2 rs pr q qin inmps acm inps0 x0.
cont_tacX.
simpl.
apply cont_L. apply cont_small.
- simpl in *. inversion H4. subst.
  destruct l. simpl in *.
  subst.

rewrite <- app_assoc.
nsprsame_cont2 rs pr q qin inmps acm inps0 x0.
admit.
admit.

unfold rules_L_ne in psfull.
assert ( In (l, l1) ps) as Hin.
apply lem9 in HH. auto.
pose proof pr as Cpr.
apply carry in Cpr.
assert (a = hd a (fst (l,l1))).
eapply Forall_forall in Cpr; [exact Cpr|]; auto.
pose proof pr as Fpr. apply psfull in Fpr.
assert (fst (l,l1) <> []).
eapply Forall_forall in Fpr; [exact Fpr|]; auto.
destruct l. simpl in *. contradiction.
simpl in *. subst.
eapply (contracted_I _ _ _ [] l);
apps_eq_tac.
destruct ps; simpl; auto. 

cont_tacX.
simpl.
apply cont_L. apply cont_small.
  
unfold rules_L_ne in psfull.

assert ( In (l, l1) ps) as Hin.
apply lem9 in HH. auto.
pose proof pr as Cpr.
apply carry in Cpr.
assert (a = hd a (fst (l,l1))).
eapply Forall_forall in Cpr; [exact Cpr|]; auto.
pose proof pr as Fpr. apply psfull in Fpr.
assert (fst (l,l1) <> []).
eapply Forall_forall in Fpr; [exact Fpr|]; auto.
destruct l. simpl in *. contradiction.
simpl in *. subst.
eapply (contracted_I _ _ _ [] l);
apps_eq_tac.
destruct ps; simpl; auto. 

  
Search contracted.


(*
derIrs rs ; [> eapply NSctxt' || eapply NSlcctxt' ;
  apply Sctxt_e || apply Sctxt_e' ; exact pr |] .
rewrite dersrec_forall .
intros q qin .
rewrite -> in_map_iff in qin ; cE .
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE . 
rewrite -> Forall_forall in acm .
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 .
pose proof inps0 as HH.
eapply acm in inps0 .
(*clear acm ; *)
rewrite -> ?can_gen_contL_def' in inps0 ;
rewrite -> ?can_gen_contR_def' in inps0 .
subst .
destruct x0 .
unfold seqext .
unfold nsext ; unfold nslcext .
eapply inps0 .
2 : reflexivity.
2 : reflexivity. 
unfold can_gen_contL in acm.
clear acm. *)


cont_tacX.

apply in_map_iff in HH. destruct HH as [xx [HH HH2]].

SearchAbout In map.
SearchAbout Forall .
Check Forall_forall.

Print contracted.

cont_tacX.


[> | unfold nsext ; unfold nslcext ; reflexivity |
    unfold seqext ; reflexivity ] ;
  cont_tacX.

Print contracted.
apply (contracted_I _ _ _ nil (a :: l)).
econstructor.

(*
  pose pr as Qpr ; apply carry in Qpr.
  unfold rules_L_ne in psfull.
  pose pr as Qpr2 ; apply psfull in Qpr2.
  rewrite (lem _ _ _ a) in acm; auto.
  intros HH. auto.
  rewrite <- app_assoc in acm.
  apply lem7 in acm.
  rewrite <- lem in acm; auto.
  *)

unfold contracted.
admit.
 nsprsame_cont2  rs pr q qin inmps acm inps0 x0.

  Search derrec.

  unfold rsub in rs.
  eapply derI.
  apply rs.
  apply NSlcctxt.
  rewrite app_cons_single.
  apply Sctxt_e'. apply pr.
  SearchAbout dersrec.
  rewrite <- app_assoc.
  
  Search seqrule.
  Search derrec.
  admit.
  intros HH. auto.
  admit.
  
  apply Qpr. unfold premises_fullL. auto.
  admit.
  Qpr2.
  unfold premises_fullL. intros. auto.
  SearchAbout Forall map.
Print can_gen_contL.
  Lemma lem6 : forall G d0 seq P,
    Forall (can_gen_contL rules)
          (map (nslcext G d0)
             (map (seqext (A ++ [a; a]) Φ2 Ψ1 Ψ2)
                (map
                   (fun p : list (PropF V) * list (PropF V) =>
                      (rem_hd (fst p), snd p)) ps))) ->
    
  
  Definition rem_hd {A : Type} (l : list A) :=
    match l with
    | nil => nil
    | [a] => nil
    | a::l' => l'
    end.

(Forall (fun ps' : list (PropF V) * list (PropF V) =>
             a = hd a (fst ps')) ps) ->
     (map (seqext (A ++ [a]) Φ2 Ψ1 Ψ2) ps) =
     (map (seqext (A ++ [a;a]) Φ2 Ψ1 Ψ2)
          (map (fun p => rem_hd (fst p)) ps)).


  
  admit.
+
  SearchAbout Forall can_gen_swapL.
SearchAbout Forall can_gen_contL.
  admit.
destruct l. simpl in *. subst.
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameL_cont princrules rs pr q qin inmps acm inps0 x0.
}

{ list_eq_nc. contradiction. }

Qed.







Proof.  intros until 0.  unfold gen_contL_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
rewrite can_gen_contL_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw_cont rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

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

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
  subst.


  repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)). 
(* above produces 20 subgoals, following solves all of them!! *)
change [a;a] with ([a] ++ [a]) in *. apply loe in pr.


nsprsameL_cont princrules rs pr q qin inmps acm inps0 x0.
}


((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)).
nsprsame_cont rs pr q qin inmps acm inps0 x0.


(* above produces 20 subgoals, following solves all of them!! *)
nsprsameL_cont princrules rs pr q qin inmps acm inps0 x0.
}


repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameL_cont princrules rs pr q qin inmps acm inps0 x0.
}

{ list_eq_nc. contradiction. }

Qed.

*)