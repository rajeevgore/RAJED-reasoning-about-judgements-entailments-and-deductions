Require Import utils.

Require Import Arith.
Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import String.
Open Scope string_scope.


Set Implicit Arguments.

Inductive nnf : Type :=
  | var (p : string)
  | neg (p : string)
  | and (phi psi : nnf)
  | or (phi psi : nnf)
  | box (phi : nnf)
  | dia (phi : nnf).

Lemma nnf_eqdec : forall phi psi : nnf, {phi = psi} + {phi <> psi}.
Proof. decide equality; apply string_dec. Defined.

Fixpoint neg_nnf (xi : nnf) : nnf :=
  match xi with
  | var p       => neg p
  | neg p       => var p
  | and phi psi => or (neg_nnf phi) (neg_nnf psi)
  | or phi psi  => and (neg_nnf phi) (neg_nnf psi)
  | box phi     => dia (neg_nnf phi)
  | dia phi     => box (neg_nnf phi)
  end.



Class no_literals (G : list nnf) :=
{ nl_no_var : forall {p}, ~ In (var p) G;
  nl_no_neg : forall {p}, ~ In (neg p) G }.

Class saturated (G : list nnf) :=
{ sa_no_and : forall {phi psi}, ~ (In (and phi psi) G);
  sa_no_or : forall {phi psi}, ~ (In (or phi psi) G)}.

Class box_only (G : list nnf) :=
{ bo_no_literals :: no_literals G;
  bo_saturated :: saturated G;
  bo_no_dia : forall {phi}, ~ (In (dia phi) G) }.

#[export] Instance box_only_nil : box_only [].
Proof.
constructor; try ((constructor || idtac); intros; apply in_nil).
Qed.

Theorem cons_no_literals {phi} {G} (h : no_literals G) : no_literals (box phi :: G).
Proof.
constructor; intros p Hin; elim Hin; (discriminate || apply h).
Qed.

Theorem cons_saturated {phi} {G} (h : saturated G) : saturated (box phi :: G).
Proof.
constructor; intros psi1 psi2 Hin; elim Hin; (discriminate || apply h).
Qed.

Theorem cons_box_only {phi} {G} (h : box_only G) : box_only (box phi :: G).
Proof.
constructor; try ((apply cons_no_literals || apply cons_saturated); apply h).
intros psi Hin; elim Hin; (discriminate || apply h).
Qed.



Record kripke :=
{ world : Type;
  rel   : world -> world -> Prop;
  val   : world -> string -> Prop; }.

Definition inhabited_kripke : kripke :=
{| world := nat; val := fun _ _ => True; rel := fun _ _ => True |}.



Definition erase_nnf := set_remove nnf_eqdec.
Definition inter_nnf := set_inter nnf_eqdec.
Definition remove_nnf := remove nnf_eqdec.
Definition diff_nnf := diff nnf_eqdec.
Definition hd_nnf := hd (var "").



Inductive close_instance (G : list nnf) :=
  | ci_cons : forall {p}, In (var p) G -> In (neg p) G -> close_instance G.

Inductive and_instance (G : list nnf) : list nnf -> Type :=
  | ai_cons : forall {phi} {psi}, In (and phi psi) G ->
         and_instance G (phi :: psi :: remove_nnf (and phi psi) G).

Inductive or_instance (G : list nnf) : list nnf -> list nnf -> Type :=
  | oi_cons : forall {phi psi}, In (or phi psi) G ->
         or_instance G (phi :: remove_nnf (or phi psi) G)
                       (psi :: remove_nnf (or phi psi) G).

Arguments ci_cons {G p}.
Arguments ai_cons {G phi psi}.
Arguments oi_cons {G phi psi}.

Definition left_prcp {G1 G2 D : list nnf} (i : or_instance D G1 G2) : nnf :=
  match i with
  | @oi_cons _ phi psi _ => phi
  end.

