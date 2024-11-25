(*Require Import Ensembles.*)
Require Import List.
Import ListNotations.
Require Import ListSetNotations.


Ltac all_rewrite :=
  repeat match goal with
    | [H : _ = _ |- _] => rewrite H; revert H
    end; intros.

Ltac injection_iff :=
  split; [let H := fresh in intro H; now injection H |
           try apply and_ind; intros; now all_rewrite].


Ltac find_if_inside :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X; try tauto
  end.

Ltac subst_disagree_destruct :=
  match goal with
  | [ H : {_ | _ & _} |- _ ] => destruct H as [a Hain Hneq]
  end.

Ltac auto_ind_tauto := repeat (constructor; try tauto).

Ltac eauto_ind_tauto := repeat (constructor; try (tauto || eassumption)).




Ltac clean_dcl a :=
  match goal with
  | [ H : ?x <> a |- _ ] => clear H
  | _ => idtac
  end.

Ltac dcl_rec Aeq_dec a l :=
  match l with
  | ?x :: ?xs => let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
    destruct (Aeq_dec a x) as [Heq|Hneq];
    [ repeat clean_dcl a | apply not_eq_sym in Hneq; dcl_rec Aeq_dec a xs]
  | []        => try (match goal with | [ H : List.In a ?l' |- _ ] => simpl in H; exfalso; tauto end)
  end.

Ltac dec_destruct_List_In Aeq_dec a :=
  try (match goal with | H : List.In a ?l |- _ => unfold l in H end);
  match goal with
  | [ H : List.In a ?l |- _ ] => dcl_rec Aeq_dec a l
  end.

Ltac destruct_list_easy l u :=
  repeat let a := fresh u in destruct l as [|a l]; try (discriminate || tauto).




Ltac destruct_or :=
  match goal with
    | [ H : ?P \/ ?Q |- _ ]  => destruct H; [idtac | destruct_or]; try tauto
    | _ => idtac
  end.

Ltac destruct_List_In :=
  match goal with
    | [ H : List.In ?x (?a :: ?l) |- _ ] => simpl in H; destruct_or
  end.

Ltac destruct_or_name H :=
  match type of H with
  | False       => contradiction
  | ?P \/ ?Q => let H' := fresh H in
              destruct H as [H' | H]; [  | destruct_or_name H ]; try tauto
  end.

Ltac destruct_List_In_name H := simpl in H; destruct_or_name H.


Ltac forall_list_tauto_name H :=
  try contradiction; try (rewrite <- H); try (simpl; tauto);
  try (let Hx := fresh H in destruct H as [Hx|Hx]; forall_list_tauto_name Hx).

Ltac forall_list_tauto :=
  let x := fresh "x" in let Hx := fresh "H" x in
  intros x Hx; forall_list_tauto_name Hx.



Ltac rewrite_discriminate a :=
  match goal with
  | [ H : a = _ |- _ ] =>
      match reverse goal with
      | [ H0 : a = _ |- _ ] => rewrite H0 in H; discriminate
      end
  end.

Ltac rewrite_by_name a :=
  match goal with
  | [ Ha : a = _ |- _ ] => rewrite Ha in *
  end.


Ltac auto_in := repeat (try (left; reflexivity); right).

Ltac auto_incl :=
  match goal with
    |- incl ?l ?l' =>
      let x := fresh "x" in let Hx := fresh "H" x in
      intros x Hx; destruct_List_In_name Hx;
      match goal with H : _ = x |- _ => rewrite <- H; simpl; tauto end
  end.

Ltac auto_Forall :=
  match goal with
    |- Forall ?P ?l =>
        match l with
        | _ :: _ => apply Forall_cons; [try (simpl; tauto)|auto_Forall]
        | []     => apply Forall_nil
        end
  end.


Ltac in_list :=
  simpl; try (match goal with |- List.In _ ?l => unfold l end);
    simpl; tauto.
