
Require Export List.
Set Implicit Arguments.
Export ListNotations.

Require Import genT gen.
Require Import List_lemmasT.

Definition rel (W : Type) : Type := prod W W.
Definition trf (W : Type) : Type := W -> W.  

Ltac acacE :=
  repeat match goal with
    | [ H : _ |- _ ] => apply app_eq_app in H ; sE
    | [ H : _ |- _ ] => apply cons_eq_app in H ; sE
    | [ H : _ |- _ ] => apply app_eq_cons in H ; sE
    end.

Ltac acacD :=
  repeat match goal with
    | [ H : _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    end.

Ltac acacD' :=
  repeat match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
         end.

Ltac acacD'T2 :=
  repeat match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_appT2 in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_appT2 in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_consT2 in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
         end.

Ltac acacDe' :=
  match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
    | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
    | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_app in H
    end.

Ltac acacDe'T2 :=
  match goal with
    | [ H : _ ++ _ = _ ++ _ |- _ ] => apply app_eq_appT2 in H ; sD
    | [ H : _ :: _ = _ ++ _ |- _ ] => apply cons_eq_appT2 in H ; sD
    | [ H : _ ++ _ = _ :: _ |- _ ] => apply app_eq_consT2 in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    | [ H : (_, _) = (_, _) |- _ ] => injection H as ?H ?H 
    | [ H : _ :: _ = [] |- _ ] => discriminate H
    | [ H : [] = _ :: _ |- _ ] => discriminate H
    | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nilT in H
    | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_appT in H
  end.

Ltac acacDe := repeat (sD' || acacDe').
Ltac acacDeT2 := repeat (sD' || acacDe'T2).

Theorem app_eq_unitT :
    forall {A : Type } (x y:list A) (a:A),
      x ++ y = [a] -> (x = [] /\ y = [a]) + (x = [a] /\ y = []).
Proof.
  intros until 0; intros H; destruct x; auto.
  simpl in H; inversion H as [[H1 H2]]; subst.
  apply app_eq_nil in H2. destruct H2. subst. auto.
Qed.

Theorem unit_eq_appT :
    forall {A : Type } (x y:list A) (a:A),
      [a] = x ++ y -> (x = [] /\ y = [a]) + (x = [a] /\ y = []).
Proof.
  intros until 0; intros H. 
  apply app_eq_unitT. auto.
Qed.

Ltac list_eq_nc :=
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : [] = _ ++ _ :: _  |- _ ] => apply nil_eq_list in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nil in H
     | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_app in H
     | [ H : _ ++ _ = [_] |- _ ] => apply app_eq_unit in H
     | [ H : [_] = _ ++ _ |- _ ] => apply unit_eq_app in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_single in H
     | [ H : [_] = _ ++ _ :: _ |- _ ] => apply single_eq_list in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.

(* Type version of list_eq_nc *)
Ltac list_eq_ncT :=
   match goal with
     | [ H : _ ++ _ :: _ = [] |- _ ] => apply list_eq_nil in H
     | [ H : [] = _ ++ _ :: _  |- _ ] => apply nil_eq_list in H
     | [ H : _ ++ _ = [] |- _ ] => apply app_eq_nilT in H
     | [ H : [] = _ ++ _ |- _ ] => apply nil_eq_appT in H
     | [ H : _ ++ _ = [_] |- _ ] => apply app_eq_unitT in H
     | [ H : [_] = _ ++ _ |- _ ] => apply unit_eq_appT in H
     | [ H : _ ++ _ :: _ = [_] |- _ ] => apply list_eq_singleT in H
     | [ H : [_] = _ ++ _ :: _ |- _ ] => apply single_eq_listT in H
     | [ H : _ :: _ = [] |- _ ] => discriminate H
     | [ H : _ :: _ = _ :: _ |- _ ] => injection H as
     end.

