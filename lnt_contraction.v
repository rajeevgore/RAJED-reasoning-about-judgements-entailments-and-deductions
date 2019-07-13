Require Import ssreflect.
 
Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt lntacs lntls lntbR lntmtacs.
Require Import lntb1L lntb2L.


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


Lemma prop_contL_step1: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 C Ψ1 Ψ2,
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

Lemma prop_contL_step3: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A H5 l C Ψ1 Ψ2,
  rules_L_carry2 princrules ->
  rules_L_ne princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l, l0) ->
Forall (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (A ++ [a]) (H5 ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
dersrec rules (fun _ => False) 
        (map (nslcext G d0) (map (seqext (A ++ [a]) (H5 ++ C) Ψ1 Ψ2) ps)).
Proof.
    intros. pose proof Forall_forall as H4.
  edestruct H4 as [fwd rev].
  pose proof (fwd H2) as H3. clear fwd rev.
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
  clear H3.
  eapply contracted_genL_I.
  assoc_mid [a]. apply applI.
  apply applI. assoc_mid [a]. reflexivity.
  apps_eq_tac.
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


Lemma prop_contL_step7: forall {V} (princrules : rls (rel (list (PropF V)))) (rules : rls (list (rel (list (PropF V)) * dir))) ps a l0 G d0 A B l C Ψ1 Ψ2,
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

Lemma lem21 : forall  {V}  a (rules : rls (list (rel (list (PropF V)) * dir))) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2',
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
  { apply app_eq_app in H.
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
        | [] => eapply (lem21 a) in H2; [app_r Γ2; app_nil_r_give Γ2;
                                          list_assoc_l'_conc_rs
                                        |exact Hexch | idtac 11]
        | _  => (eapply (lem21 a) in H2; [assoc_mid l1; rewrite app_assoc
                                         | exact Hexch | idtac 01])
        end
      | _ =>
        match Γ2 with
        | context[ [?a] ] =>
          (* one [a] in Γ1, one [a] in Γ2 *)
        match l1 with
        | [] => idtac 001
        | _  => (eapply (lem21 a) in H2; [assoc_mid l1; rewrite app_assoc
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
        | _  => (eapply (lem21 a) in H2; [assoc_mid l1; rewrite app_assoc
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
        | [] => eapply (lem21 a) in H2;
                [rewrite <- (app_nil_r Γ1)
                                         | exact Hexch | idtac 04]
        | _  => (eapply (lem21 a) in H2; [assoc_mid l1; rewrite app_assoc
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

Ltac cont_partial_solve_old a :=
list_assoc_r'; 
(eapply contracted_genL_spec_I; reflexivity) ||
(eapply contracted_genR_spec_I; reflexivity).

Ltac check_head l1 l2 :=
  match l1 with
  | l2 ++ ?l3 => idtac 100
  | _ => fail
  end.

Ltac check_tail l1 l2 :=
  match l1 with
  | ?l3 ++ l2 => idtac 100
  | _ => fail
  end.

Ltac cont_rem_head :=
  list_assoc_r'; rewrite ?app_comm_cons;
  repeat match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    (tryif check_head l1 [a] then idtac 200 else apply cont_gen_spec_L)
  end.

Ltac cont_rem_tail :=
  list_assoc_l'; rewrite ?app_comm_cons;
  repeat match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    (tryif check_tail l1 [a] then idtac 200 else apply cont_gen_spec_R)
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

(* Use this one *)
Ltac cont_solve a :=
  cont_rem_head; cont_rem_tail; cont_rem_mid_simp;
  apply cont_gen_spec_basic.

(*
Ltac cont_rem_mid_solve :=
  repeat match goal with
         | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
           repeat match l1 with
           | [a] ++ ?A ++ ?B => apply cont_gen_spec_rem_sml_L || apply cont_gen_spec_rem_lge_L
           end
         end.
*)
Lemma gen_contL_gen_step_loe_lc: forall V ps concl princrules
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

unfold rules_L_carry2 in carry.

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst  ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr);
  try rewrite app_nil_r in acm;
  try rewrite app_nil_l in acm);
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

Lemma gen_weakL_step_pr_lc: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule V)) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros. eapply gen_weakL_step_loe_lc.
  apply princrule_L_oe'. exact H. Qed.

Lemma gen_weakL_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_weakL (nslcrule (seqrule (@princrule V))) ns.

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