
(* lemmas which shouldn't be necessary at all! *)

Lemma or_false: forall P : Prop, iff (or P False) P. Proof. tauto. Qed.
Lemma false_or: forall P : Prop, iff (or False P) P. Proof. tauto. Qed.
Lemma and_true: forall P : Prop, iff (and P True) P. Proof. tauto. Qed.
Lemma true_and: forall P : Prop, iff (and True P) P. Proof. tauto. Qed.

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

