
(* doing stuff like in Frank Pfenning.  Structural cut elimination.
  well, not exactly, because I can't find his code, so looking at
  http://twelf.org/wiki/Admissibility_of_cut 
*)

(* at present this file requires ljt.v only for the definition of PropF *)
Require Export List.
Export ListNotations.
Set Implicit Arguments.
From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import ljt.

Parameter hyp : forall V, PropF V -> Type.

Inductive conc V : PropF V -> Type :=
  | init : forall (A : PropF V), (hyp A -> conc A) (* axiom in Pfenning *)
  | impL : forall (A B C : PropF V),
    conc A -> (hyp B -> conc C) -> (hyp (Imp A B) -> conc C)
  | impR : forall (A B : PropF V), (hyp A -> conc B) -> conc (Imp A B)
  | andL : forall (A B C : PropF V), 
    (hyp A -> hyp B -> conc C) -> (hyp (And A B) -> conc C)
  | andR : forall (A B : PropF V), conc A -> conc B -> conc (And A B)
  .

(* sample proofs *)
Lemma sample1 V A B : hyp (And A (Imp A B)) -> @conc V B.
Proof. apply andL. intro.  apply impL.
apply (init X).  apply init. Qed.

Lemma sample2 V A B : hyp (And (Imp A B) A) -> @conc V B.
Proof. apply andL. (* apply impL. fails, must switch args *)
intros. revert X. apply impL.
apply (init X0).  apply init. Qed.

Print Implicit init.
Print Implicit andR.

Definition cancut V (A C : PropF V) (D: conc A) (E: hyp A -> conc C) :=
  sigT (fun F : conc C => True).

Definition iscad V (A C : PropF V) 
  (D: conc A) (E: hyp A -> conc C) (F : conc C) := True.

Print Implicit cancut.
Print Implicit iscad.

Lemma initD V (A C : PropF V) Ha (E: hyp A -> conc C) :
  iscad (init Ha) E (E Ha).
Proof. exact I. Qed.

Lemma initE V (A : PropF V) (D : conc A) : @iscad V A A D (@init _ _) D.
Proof. exact I. Qed.

Lemma closed V (A C : PropF V) D E' : @iscad V A C D (fun _ => E') E'.
Proof. exact I. Qed.

Notation "B <- A" := (forall _ : A, B)
  (only parsing, at level 90, left associativity).

Lemma andC V (A B C : PropF V) D1 D2 E' F1 F2 F : 
  @iscad _ (And A B) C (andR D1 D2) 
    (fun (Hab : hyp (And A B)) => andL (E' Hab) Hab) F
    <- (forall Ha Hb, @iscad V (And A B) C (andR D1 D2) 
      (fun Hab => E' Hab Ha Hb) (F1 Ha Hb))
    <- (forall Hb, @iscad V A C D1 (fun Ha => F1 Ha Hb) (F2 Hb))
    <- @iscad V B C D2 F2 F.
Proof. intros. exact I. Qed.

Lemma impC V (A B C : PropF V) D' E1 E2 F1 F2 F3 F :
  @iscad V (Imp A B) _ (impR D')
     (fun Hab => impL (E1 Hab : conc A) (E2 Hab : hyp B -> conc C) Hab) F
    <- @iscad V (Imp A B) _ (impR D') E1 (F1 : conc A)
    <- (forall Hb : hyp B, @iscad V (Imp A B) _ (impR D')
      (fun Hab => E2 Hab Hb) (F2 Hb : conc C))
    <- @iscad V A _ F1 D' (F3 : conc B)
    <- @iscad V B _ F3 F2 F.
Proof. intros. exact I. Qed.

Lemma andLLC V (A B A1 B1 : PropF V) D' E F' (Hab : hyp (And A1 B1)) :
  @iscad V A B (andL D' Hab) E (andL F' Hab)
      <- (forall Ha Hb, @iscad V A B (D' Ha Hb) E (F' Ha Hb)).
Proof. intros. exact I. Qed.

Lemma impLLC V (A B A1 B1 : PropF V) D1 D2 E F2 (Hi : hyp (Imp A1 B1)) :
  @iscad V A B (impL D1 D2 Hi) E (impL D1 F2 Hi)
      <- (forall Hb, @iscad V A B (D2 Hb) E (F2 Hb)).
Proof. intros. exact I. Qed.

Lemma andRRC V A B C D E1 E2 F1 F2 :
  @iscad V A (And B C) D (fun Ha => andR (E1 Ha) (E2 Ha)) (andR F1 F2)
      <- iscad D E1 F1 <- iscad D E2 F2.
Proof. intros. exact I. Qed.

Lemma impRRC V A B C D E1 F1 :
  @iscad V A (Imp B C) D (fun Ha => impR (E1 Ha)) (impR F1)
      <- (forall H1, iscad D (fun Ha => E1 Ha H1) (F1 H1)).
Proof. intros. exact I. Qed.

Print Implicit andL.
Print Implicit impL.

Lemma andLRC V A B D A1 B1 E' F' (Hp : hyp (And A1 B1)) :
  @iscad V A B D (fun Ha => andL (E' Ha) Hp) (andL F' Hp)
      <- (forall H1 H2, iscad D (fun Ha => E' Ha H1 H2) (F' H1 H2)).
Proof. intros. exact I. Qed.

Lemma impLRC V A B D A1 B1 E1 E2 F1 F2 (Hi : hyp (Imp A1 B1)) :
  @iscad V A B D (fun Ha => impL (E1 Ha) (E2 Ha) Hi) (impL F1 F2 Hi)
      <- iscad D E1 F1
      <- (forall Hb, iscad D (fun Ha => E2 Ha Hb) (F2 Hb)).
Proof. intros. exact I. Qed.


