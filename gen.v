
(* lemmas which shouldn't be necessary at all! *)

Lemma or_false: forall P : Prop, iff (or P False) P. Proof. tauto. Qed.
Lemma false_or: forall P : Prop, iff (or False P) P. Proof. tauto. Qed.
Lemma and_true: forall P : Prop, iff (and P True) P. Proof. tauto. Qed.
Lemma true_and: forall P : Prop, iff (and True P) P. Proof. tauto. Qed.

Lemma rappl: forall (A B : Prop), A -> (A -> B) -> B.
Proof.  tauto.  Qed.

Lemma appl: forall (A B : Prop), (A -> B) -> A -> B.
Proof.  tauto.  Qed.

Lemma gen_cong: forall T U f g, f = g -> 
  forall x y, x = y -> (f (x : U) : T) = g y.
Proof. intros. subst. reflexivity. Qed.

Lemma fun_cong: forall T U f g, f = g -> 
  forall x, (f (x : U) : T) = g x.
Proof. intros. subst. reflexivity. Qed.

Lemma arg_cong: forall T U f x y, x = y -> (f (x : U) : T) = f y.
Proof. intros. subst. reflexivity. Qed.

(* see also eq_refl, eq_trans, eq_sym, eq_ind, eq_ind_r *)

Lemma pair_eqI: forall T U (u v : T) (x y : U),
  u = v -> x = y -> (u,x) = (v,y).
Proof. intros. subst. reflexivity. Qed.

Ltac rename_last name :=
  match goal with
    | [ K : _ |- _ ] => rename K into name
    end.

Ltac clear_one :=
  match goal with
    | [ K : _ |- _ ] => clear K
    end.

Ltac cE :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => inversion_clear H
    | [ H : ex _ |- _ ] => inversion_clear H
    | [ H : False |- _ ] => contradiction H
    end.

(* one step of cD *)
Ltac cD' :=
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H as [?H ?H]
    | [ H : ex _ |- _ ] => destruct H as [?H ?H]
    | [ H : False |- _ ] => contradiction H
    end.

(*
Ltac cD :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => destruct H as [?H ?H]
    | [ H : ex _ |- _ ] => destruct H as [?H ?H]
    | [ H : False |- _ ] => contradiction H
    end.
    *)

Ltac cD := repeat cD'.

Ltac sE :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => inversion_clear H
    | [ H : _ \/ _ |- _ ] => inversion_clear H
    | [ H : ex _ |- _ ] => inversion_clear H
    | [ H : False |- _ ] => contradiction H
    end.

Ltac sD' :=
  match goal with
    | [ H : _ /\ _ |- _ ] => destruct H as [?H ?H]
    | [ H : _ \/ _ |- _ ] => destruct H as [?H | ?H]
    | [ H : ex _ |- _ ] => destruct H as [?H ?H]
    | [ H : False |- _ ] => contradiction H
    end.

(* extra stuff used in sD, not in cD *)
Ltac sDx :=
  match goal with
    | [ H : _ \/ _ |- _ ] => destruct H as [?H | ?H]
    end.

(*
Ltac sD :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => destruct H as [?H ?H]
    | [ H : _ \/ _ |- _ ] => destruct H as [?H | ?H]
    | [ H : ex _ |- _ ] => destruct H as [?H ?H]
    | [ H : False |- _ ] => contradiction H
    end.

Ltac sD := repeat sD'.
*)
Ltac sD := repeat (cD' || sDx).

(* various solutions to dealing with hypothesis forall x, A x -> B x 
  see emails 8-9 Jan 
evar (z : list (rel (list (PropF V)) * dir)).
specialize (H1 z).
subst z. (* subst. alone doesn't work *)

match type of H1 with
| ?A -> _ =>
  assert (I : A); [| apply H1 in I ]
  end. 

apply (fun G2 G1 => G1 (H1 G2)). 

eassert _ as I%H1.

or 
eassert _ ; [ apply H1 | ].
eassert _ as I ; [ | apply H1 in I ].

all : cycle 1. Show. 
Undo. Show. 
*)

(* tactics from Lily Chung <ikdc@mit.edu> Tue, 8 Jan 2019
  https://gist.github.com/ichung/032b849da0c3c5e3987c83f835d111ee *) 

(* [require], when called on a hypothesis [H : P -> Q],
   asserts that P actually holds,
   and thus that H's type can be replaced with Q *)
Ltac require H :=
  match type of H with
  | forall _  : ?H1, _ =>
    let x := fresh in
    let y := x in
    assert H1 as x; [| specialize (H x); clear y]
  end.

(* [erequire H], when called on a hypothesis [H : forall x, Q x],
   specializes [H] to a new evar to be filled in later *)
Ltac erequire H :=
  match type of H with
  | forall _  : ?H1, _ =>
    let x := fresh in
    evar (x : H1); specialize (H x); subst x
end.

(* solution from  Marko Doko <mdoko@mpi-sws.org> Tue, 8 Jan 2019
  solves question for quantified implication, changed to use Ltac

Tactic Notation "specialize_full" ident(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1;
  [eapply H|try clear H; intro H].
*)

Ltac specialize_full H := 
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1;
  [eapply H|try clear H; intro H].

