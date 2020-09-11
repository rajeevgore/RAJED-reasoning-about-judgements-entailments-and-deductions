Add LoadPath "../general".
Require Import List.
Require Import existsT.
Require Import List_lemmasT.
Require Import gen genT lntacsT.
Require Import gen_tacs lntT.

Set Implicit Arguments.
Import ListNotations.

(* Contains definitions and lemmas for ... *)

Inductive contracted {T} : list T -> list T -> Type :=
  | contracted_I : forall a (X Y A B : list T), X = (A ++ [a;a] ++ B) -> 
    Y = (A ++ [a] ++ B) -> contracted X Y.

Lemma contracted_I': forall T a (A B : list T),
   contracted (A ++ [a;a] ++ B) (A ++ [a] ++ B).
Proof.  intros.  eapply contracted_I ; reflexivity. Qed.

Inductive contracted_gen {T} : list T -> list T -> Type :=
| contracted_genL_I : forall a (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ [a] ++ B ++ C) -> contracted_gen X Y
| contracted_genR_I : forall a (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ B ++ [a] ++ C) -> contracted_gen X Y.

Inductive contracted_gen_spec {T} (a : T) : list T -> list T -> Type :=
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

(* ------------------- *)
(* CONTRACTION TACTICS *)
(* ------------------- *)

Lemma cont_L: forall T X Y Z,
  contracted X (Y : list T) -> contracted (Z ++ X) (Z ++ Y).
Proof.
  intros until 0; intros H. destruct H. subst. 
  rewrite !(app_assoc Z). apply contracted_I'.
Qed.

Lemma cont_R: forall T X Y Z,
  contracted X (Y : list T) -> contracted (X ++ Z) (Y ++ Z).
Proof.
  intros until 0; intros H. destruct H. subst.
  rewrite <- !app_assoc. apply contracted_I'. 
Qed.

Lemma cont_gen_L: forall T X Y Z,
  contracted_gen X (Y : list T) -> contracted_gen (Z ++ X) (Z ++ Y).
Proof.
  intros until 0; intros H. destruct H; subst; rewrite !(app_assoc Z).
  apply contracted_genL_I'.
  apply contracted_genR_I'.
Qed.

Lemma cont_gen_R: forall T X Y Z,
  contracted_gen X (Y : list T) -> contracted_gen (X ++ Z) (Y ++ Z).
Proof.
  intros until 0; intros H. destruct H; subst; rewrite <- !app_assoc.
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
  intros until 0; intros H. destruct H; subst; rewrite !(app_assoc Z).
  apply contracted_genL_spec_I'.
  apply contracted_genR_spec_I'.
Qed.

Lemma cont_gen_spec_R: forall T a X Y Z,
  contracted_gen_spec a X (Y : list T) -> contracted_gen_spec a (X ++ Z) (Y ++ Z).
Proof.
  intros until 0; intros H. destruct H; subst; rewrite <- !app_assoc.
  apply contracted_genL_spec_I'. 
  apply contracted_genR_spec_I'. 
Qed.

Lemma cont_gen_spec_rem_sml_L : forall T (a : T) Z,
    contracted_gen_spec a ([a] ++ Z ++ [a]) ([a] ++ Z).
Proof.
  intros.
  change ([a] ++ Z ++ [a]) with ([] ++ [a] ++ Z ++ [a] ++ []).
  replace ([a] ++ Z) with ([] ++ [a] ++ Z ++ []).
  apply contracted_genL_spec_I'. rewrite app_nil_r. reflexivity.
Qed.

Lemma cont_gen_spec_rem_sml_R : forall T (a : T) Z,
    contracted_gen_spec a ([a] ++ Z ++ [a]) (Z ++ [a]).
Proof.
  intros.
  change ([a] ++ Z ++ [a]) with ([] ++ [a] ++ Z ++ [a] ++ []).
  change (Z ++ [a]) with ([] ++ Z ++ [a] ++ []).
  apply contracted_genR_spec_I'.
Qed.

Lemma cont_cons: forall T (x : T) Y Z,
  contracted Y Z -> contracted (x :: Y) (x :: Z).
Proof.
  intros until 0; intros H. inversion H.
  subst. list_assoc_l.
  rewrite <- !app_assoc. apply contracted_I'.
Qed.

Lemma contracted_gen_in1: forall {T} (a : T) A Γ1 C H5,
    InT a C ->
 contracted_gen (A ++ [a] ++ Γ1 ++ C ++ H5) (A ++ Γ1 ++ C ++ H5).
Proof.
  intros until 0; intros H. apply InT_split in H.
  destruct H as [l1 [l2 H]].
  subst.  list_assoc_r'.
  simpl.
  do 2 change (a :: (?x ++ ?y)) with ([a] ++ (x ++ y)).
  eapply contracted_genR_I.
  do 2 apply applI.
  rewrite app_assoc.  reflexivity.
  list_assoc_r'. reflexivity.
Qed.

Lemma contracted_gen_in2: forall {T} (a : T) A Γ1 C,
    InT a Γ1 ->
 contracted_gen (A ++ [a] ++ Γ1 ++ C) (A ++ Γ1 ++ C).
Proof.
  intros until 0; intros H. apply InT_split in H.
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
    InT a Γ1 ->
contracted_gen (A ++ Γ1 ++ [a] ++ C) (A ++ Γ1 ++ C).
Proof.
  intros until 0; intros H. apply InT_split in H.
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
    InT a Γ1 ->
    contracted_gen (A ++ Γ1 ++ H5 ++ [a] ++ C) (A ++ Γ1 ++ H5 ++ C).
Proof.
  intros until 0; intros H. apply InT_split in H.
  destruct H as [l1 [l2 H]].
  subst.
  change (a :: ?x) with ([a] ++ x).
  assoc_mid [a].
  eapply contracted_genL_I.
  do 2 apply applI.
  assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

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

Inductive contracted_multi {T : Type} : list T -> list T -> Type :=
| cont_multi_refl X : @contracted_multi T X X
(*| cont_multi_base X Y   : @contracted_gen T X Y -> contracted_multi X Y *)
| cont_multi_step X Y Z : @contracted_gen T X Y -> contracted_multi Y Z -> contracted_multi X Z.

Inductive contracted_multi_enum {T : Type} : list T -> list T -> nat -> Type :=
| cont_multi_enum_refl X : @contracted_multi_enum T X X 0
(*| cont_multi_base X Y   : @contracted_gen T X Y -> contracted_multi X Y *)
| cont_multi_enum_step X Y Z n : @contracted_gen T X Y -> contracted_multi_enum Y Z n -> contracted_multi_enum X Z (S n).

Lemma cont_multi__enum : forall {T : Type} (X Y : list T),
    contracted_multi X Y -> existsT2 n, contracted_multi_enum X Y n.
Proof.
  intros T X Y Hc.
  induction Hc. exists 0. eapply cont_multi_enum_refl.
  destruct IHHc as [n IH].
  exists (S n). eapply cont_multi_enum_step.
  eapply c. apply IH.
Qed.

Lemma cont_multi__enum_rev : forall {T : Type} (X Y : list T) n,
    contracted_multi_enum X Y n -> contracted_multi X Y.
Proof.
  intros T X Y n Hc.
  induction Hc. eapply cont_multi_refl.
  eapply cont_multi_step. eapply c.
  assumption.
Qed.

Inductive contracted_seqL {T : Type} : ((list T) * (list T) * dir) -> ((list T) * (list T) * dir) -> Type :=
| cont_seqL X Y Δ d : contracted_multi X Y -> contracted_seqL (X,Δ,d) (Y,Δ,d).

Inductive contracted_seqR {T : Type} : ((list T) * (list T) * dir) -> ((list T) * (list T) * dir) -> Type :=
| cont_seqR X Y Γ d : contracted_multi X Y -> contracted_seqR (Γ,X,d) (Γ,Y,d).

Inductive contracted_seq {T : Type} : ((list T) * (list T) * dir) -> ((list T) * (list T) * dir) -> Type :=
| cont_seq_baseL s1 s2 : contracted_seqL s1 s2 -> contracted_seq s1 s2
| cont_seq_baseR s1 s2  : contracted_seqR s1 s2 -> contracted_seq s1 s2
| cont_seq_stepL s1 s2 s3 : contracted_seqL s1 s2 -> contracted_seq s2 s3 -> contracted_seq s1 s3
| cont_seq_stepR s1 s2 s3 : contracted_seqR s1 s2 -> contracted_seq s2 s3 -> contracted_seq s1 s3.

Inductive contracted_nseq {T : Type} : list ((list T) * (list T) * dir) -> list ((list T) * (list T) * dir) -> Type :=
| cont_nseq_nil  : contracted_nseq [] []
| cont_nseq_cons s1 s2 ns1 ns2 : contracted_seq s1 s2 -> contracted_nseq ns1 ns2 ->
                                 contracted_nseq (s1::ns1) (s2::ns2).

Lemma contracted_gen_cons : forall {T : Type} Y Z (a : T),
    contracted_gen Y Z ->
    contracted_gen (a :: Y) (a :: Z).
Proof.
  intros until 0; intros Hc; inversion Hc; subst.
  rewrite ?app_comm_cons.
  eapply contracted_genL_I.
  reflexivity. reflexivity.
  rewrite ?app_comm_cons.
  eapply contracted_genR_I.
  reflexivity. reflexivity.
Qed.

Lemma contracted_multi_cons : forall {T : Type} Y Z (a : T),
    contracted_multi Y Z ->
    contracted_multi (a :: Y) (a :: Z).
Proof.
  intros until 0; intros Hc.
  induction Hc. subst. eapply cont_multi_refl.
  subst.
  eapply cont_multi_step. eapply contracted_gen_cons.
  eapply c.
  assumption.
Qed.

Lemma contracted_multi_cons_tl : forall {T : Type} Y Z (a : T),
    contracted_multi Y Z ->
    contracted_multi (Y ++ [a]) (Z ++ [a]).
Proof.
  intros until 0; intros Hc.
  induction Hc. eapply cont_multi_refl.
  inversion c. subst. 
  eapply cont_multi_step.
  list_assoc_r'. simpl. eapply contracted_genL_I.
  reflexivity. reflexivity.
  do 3 rewrite <- app_assoc in IHHc. assumption.

  subst. eapply cont_multi_step.
  list_assoc_r'. simpl. eapply contracted_genR_I.
  reflexivity. reflexivity.
  do 3 rewrite <- app_assoc in IHHc. assumption.
Qed.

Lemma contracted_multi_L : forall {T : Type} (X Y Z : list T),
    contracted_multi Y Z ->
    contracted_multi (X ++ Y) (X ++ Z).
Proof.
  induction X; intros Y Z Hc. assumption.
  simpl. eapply contracted_multi_cons.
  apply IHX. apply Hc.
Qed.

Lemma contracted_multi_R : forall {T : Type} (X Y Z : list T),
    contracted_multi Y Z ->
    contracted_multi (Y ++ X) (Z ++ X).
Proof.
  induction X; intros Y Z Hc. do 2 rewrite app_nil_r. assumption.
  rewrite cons_singleton. do 2 rewrite app_assoc.
  eapply IHX. eapply contracted_multi_cons_tl. assumption.
Qed.

Lemma contracted_multi_multi : forall {T : Type} Γ X Y Z,
    @contracted_multi T (X ++ Γ ++ Y ++ Γ ++ Z) (X ++ Γ ++ Y ++ Z).
Proof.
  induction X; intros.
  simpl.
  list_assoc_l'. eapply contracted_multi_R.
  list_assoc_r'.
  revert Y Z.
  induction Γ; intros Y Z.
  simpl. rewrite app_nil_r. apply cont_multi_refl.
  simpl. eapply cont_multi_step.
  2 :{ eapply contracted_multi_cons. eapply IHΓ. auto. }
  eapply (@contracted_gen__spec _ a).
  rewrite (cons_singleton Γ a).
  do 2 rewrite (cons_singleton (Γ ++ _) a).
  cont_solve.

  simpl. eapply contracted_multi_cons. apply IHX.
Qed.

Lemma contracted_multi_double : forall {T : Type} Γ,
    @contracted_multi T (Γ ++ Γ) Γ.
Proof.
  intros T Γ.
  assert (    @contracted_multi T ([] ++ Γ ++ [] ++ Γ ++ []) ([] ++ Γ ++ [] ++ [])) as Hass.
  eapply contracted_multi_multi. 
  repeat rewrite app_nil_r in Hass.  assumption. 
Qed.

Lemma contracted_seq_double : forall {T : Type} Γ Δ d,
    @contracted_seq T (Γ ++ Γ, Δ ++ Δ, d) (Γ, Δ, d).
Proof.
  intros. econstructor 3.
  econstructor. eapply contracted_multi_double.
  econstructor 2. econstructor.
  eapply contracted_multi_double.
Qed.
  
Lemma contracted_seq_refl : forall {T : Type} s,
    @contracted_seq T s s.
Proof.
  intros T [[Γ Δ] d].
  econstructor. econstructor.
  eapply cont_multi_refl.
Qed.

Lemma contracted_multi_seq : forall {T} G1 G2 H1 H2 d,
    contracted_multi G1 G2 ->
    contracted_multi H1 H2 ->
    @contracted_seq T (G1, H1, d) (G2, H2, d).
  Proof.
    intros.
    eapply cont_seq_stepL.
    econstructor. eassumption.
    eapply cont_seq_baseR.
    econstructor. eassumption.
  Qed.


Lemma contracted_nseq_refl : forall {T : Type} ns,
    @contracted_nseq T ns ns.
Proof.
  induction ns. constructor.
  constructor. apply contracted_seq_refl.
  assumption.
Qed.


Lemma contracted_nseq_app : forall {T : Type} l1 l2 l3 l4,
  @contracted_nseq T l1 l3 ->
  contracted_nseq l2 l4 ->
  contracted_nseq (l1 ++ l2) (l3 ++ l4).
Proof.
  induction l1; intros l2 l3 l4 H1 H2.
  inversion H1. assumption.
  inversion H1. subst. simpl.
  econstructor. assumption.
  apply IHl1; assumption.
Qed.

Lemma contracted_seqL_consL : forall {T : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seqL T (l1, l2, d1) (l3, l4, d2) ->
    contracted_seqL (a :: l1, l2, d1) (a :: l3, l4, d2).
Proof.
  intros until 0; intros H.
  inversion H. subst.
  econstructor.
  eapply contracted_multi_cons.
  assumption.
Qed.

Lemma contracted_seqR_consL : forall {T : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seqR T (l1, l2, d1) (l3, l4, d2) ->
    contracted_seqR (a :: l1, l2, d1) (a :: l3, l4, d2).
Proof.
  intros until 0; intros H.
  inversion H. subst.
  econstructor.
  assumption.
Qed.

Lemma contracted_seqL_consR : forall {T : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seqL T (l1, l2, d1) (l3, l4, d2) ->
    contracted_seqL (l1, a :: l2, d1) (l3, a :: l4, d2).
Proof.
  intros until 0; intros H.
  inversion H. subst.
  econstructor.
  assumption.
Qed.

Lemma contracted_seqR_consR : forall {T : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seqR T (l1, l2, d1) (l3, l4, d2) ->
    contracted_seqR (l1, a :: l2, d1) (l3, a :: l4, d2).
Proof.
  intros until 0; intros H.
  inversion H. subst.
  econstructor.
  eapply contracted_multi_cons.
  assumption.
Qed.

Lemma contracted_seqL_dir : forall {T : Type} (l1 l2 l3 l4 : list T) d1 d2,
    contracted_seqL (l1, l2, d1) (l3, l4, d2) -> d1 = d2.
Proof.
  intros until 0; intros Hc.
  inversion Hc. subst. reflexivity.
Qed.

Lemma contracted_seqR_dir : forall {T : Type} (l1 l2 l3 l4 : list T) d1 d2,
    contracted_seqR (l1, l2, d1) (l3, l4, d2) -> d1 = d2.
Proof.
  intros until 0; intros Hc.
  inversion Hc. subst. reflexivity.
Qed.
  
Lemma contracted_seq_consL : forall {T : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seq T (l1, l2, d1) (l3, l4, d2) ->
    contracted_seq (a :: l1, l2, d1) (a :: l3, l4, d2).
Proof.
  intros until 0; intros H.
  remember (l1,l2,d1) as s1.
  remember (l3,l4,d2) as s2.
  revert l1 l2 l3 l4 Heqs1 Heqs2. 
  induction H as [ [[? ?] ?] [[? ?] ?] X | ? ? X | ? ? ? X X2| ? ? ? X X2];
    intros ll1 ll2 ll3 ll4 Heqs1 Heqs2;
    inversion Heqs1; inversion Heqs2; subst.

  eapply contracted_seqL_consL in X.
  econstructor. eassumption.

  eapply contracted_seqR_consL in X.
  econstructor 2. eassumption.

  destruct s2 as [[? ?] ?].
  econstructor 3.
  eapply contracted_seqL_consL.
  eassumption.
  eapply contracted_seqL_dir in X.  subst.
  eapply IHX2; reflexivity.

  destruct s2 as [[? ?] ?].
  econstructor 4.
  eapply contracted_seqR_consL.
  eassumption.
  eapply contracted_seqR_dir in X.  subst.
  eapply IHX2; reflexivity.
Qed.

Lemma contracted_seq_consR : forall {T : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seq T (l1, l2, d1) (l3, l4, d2) ->
    contracted_seq (l1, a :: l2, d1) (l3, a :: l4, d2).
Proof.
  intros until 0; intros H.
  remember (l1,l2,d1) as s1.
  remember (l3,l4,d2) as s2.
  revert l1 l2 l3 l4 Heqs1 Heqs2. 
  induction H as [ [[? ?] ?] [[? ?] ?] X | ? ? X | ? ? ? X X2| ? ? ? X X2];
    intros ll1 ll2 ll3 ll4 Heqs1 Heqs2;
    inversion Heqs1; inversion Heqs2; subst.

  eapply contracted_seqL_consR in X.
  econstructor. eassumption.

  eapply contracted_seqR_consR in X.
  econstructor 2. eassumption.

  destruct s2 as [[? ?] ?].
  econstructor 3.
  eapply contracted_seqL_consR.
  eassumption.
  eapply contracted_seqL_dir in X.  subst.
  eapply IHX2; reflexivity.

  destruct s2 as [[? ?] ?].
  econstructor 4.
  eapply contracted_seqR_consR.
  eassumption.
  eapply contracted_seqR_dir in X.  subst.
  eapply IHX2; reflexivity.
Qed.

Lemma contracted_seq_app_sameL : forall {T : Type} l1 l2 d,
    @contracted_seq T (l1 ++ l1, l2, d) (l1, l2, d).
Proof.
  intros.
  econstructor.
  econstructor.
  eapply contracted_multi_double.
Qed.

Lemma contracted_seq_app_sameR : forall {T : Type} l1 l2 d,
    @contracted_seq T (l1, l2 ++ l2, d) (l1, l2, d).
Proof.
  intros.
  econstructor 2.
  econstructor.
  eapply contracted_multi_double.
Qed.
  
Lemma contracted_nseq_singleL : forall {T : Type} l1 l2 d,
    @contracted_nseq T [(l1 ++ l1, l2, d)] [(l1, l2, d)].
Proof.
  intros. econstructor.
  eapply contracted_seq_app_sameL.
  econstructor.
Qed.

Lemma contracted_nseq_singleR : forall {T : Type} l1 l2 d,
    @contracted_nseq T [(l1, l2 ++ l2, d)] [(l1, l2, d)].
Proof.
  intros. econstructor.
  eapply contracted_seq_app_sameR.
  econstructor.
Qed.

Lemma contracted_nseq_single : forall {T : Type} l1 l2 d,
    @contracted_nseq T [(l1 ++ l1, l2 ++ l2, d)] [(l1, l2, d)].
Proof.
  intros. econstructor.
  apply contracted_seq_double.
  econstructor.
Qed.
