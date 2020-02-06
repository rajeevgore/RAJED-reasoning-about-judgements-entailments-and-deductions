Require Import List.
Export ListNotations.

Require Import lntT.


(* Equality that ignores the first, irrelevant direction. *)
Inductive LNS_eq {V : Set} : (list (rel (list (PropF V)) * dir)) -> (list (rel (list (PropF V)) * dir)) -> Type :=
| LNS_eq_nil n1 n2 : n1 = [] -> n2 = [] -> LNS_eq n1 n2
| LNS_eq_hd n1 n2 ns1 ns2 nseq1 nseq2 seq d1 d2 : n1 = nseq1 :: ns1 -> n2 = nseq2 :: ns2 ->
                      ns1 = ns2 -> nseq1 = (seq, d1) -> nseq2 = (seq, d2) ->
                      LNS_eq n1 n2.

Lemma LNS_eq_eq {V : Set} : forall n1 n2,
    n1 = n2 -> @LNS_eq V n1 n2.
Proof.
  intros n1 n2 H. subst.
  destruct n2. apply LNS_eq_nil; reflexivity.
  destruct p.
  eapply LNS_eq_hd; reflexivity.
Qed.

Lemma LNS_eq_cons_tl : forall {V : Set} l1 l2 a,
    LNS_eq (a :: l1) (a :: l2) -> @LNS_eq V l1 l2.
Proof.
  intros V l1 l2 a H.
  inversion H. discriminate.
  inversion H0. inversion H1. subst.
  apply LNS_eq_eq. reflexivity.
Qed.

Lemma LNS_eq_cons : forall {V : Set} l seq1 seq2 d1 d2,
    @LNS_eq V ((seq1,d1) :: l) ((seq2,d2) :: l) -> seq1 = seq2.
Proof.
  intros until 0; intros H.
  inversion H. discriminate.
  subst. inversion H0. inversion H1.
  reflexivity.
Qed.

Lemma LNS_eq_refl : forall (V : Set) n, @LNS_eq V n n.
Proof.
  intros V n. apply LNS_eq_eq. reflexivity.
Qed.
