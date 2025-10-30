From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.

From KTsat Require Import defs.
From KTsat Require Import ops.
From KTsat Require Import semantics.


Require Import List.
Import ListNotations.


Inductive node (G : seqt) : Type :=
| closed : unsatable_KT (main G ++ hdld G) -> node G
| open   : {s | sat builder s (main G ++ hdld G)} -> node G.

Arguments closed {G}.
Arguments open {G}.

Definition contra_rule_seqt {D n} : In (var n) (main D) /\ In (neg n) (main D) -> node D.
Proof.
refine (fun H => closed _).
apply (@unsat_contra_seqt _ n); tauto.
Defined.

Definition and_rule_seqt {G D} (i : and_instance_seqt G D) (mu : node D) : node G.
Proof.
refine (
match mu with
| closed H               => closed _
| open (exist _ m Hsat) => open (exist _ m _)
end).
- apply (@unsat_of_closed_and_seqt G D); repeat assumption.
- destruct i. simpl in Hsat.
  apply (@sat_and_of_sat_split_seqt phi psi). assumption.
Defined.

Definition or_rule_seqt {G1 G2 D} (i : or_instance_seqt D G1 G2)
  (mu : node G1) (nu : node G2) : node D.
Proof.
refine (
match mu, nu with
| open (exist _ m Hsat), _ => open (exist _ m _)
| _, open (exist _ m Hsat) => open (exist _ m _)
| closed H1, closed H2      => closed _
end).
- apply (@unsat_of_closed_or_seqt G1 G2 D); assumption.
- destruct i. simpl main in Hsat. simpl hdld in Hsat.
  apply (@sat_or_of_sat_split_right _ _ _ phi psi).
  eapply sat_subset; try apply Hsat.
  unfold remove_nnf. rewrite remove_app.
  rewrite app_comm_cons. apply incl_app.
  * apply incl_appl, incl_refl.
  * apply incl_appr, remove_subset.
- destruct i. simpl main in Hsat. simpl hdld in Hsat.
  apply (@sat_or_of_sat_split_left _ _ _ phi psi).
  eapply sat_subset; try apply Hsat.
  unfold remove_nnf. rewrite remove_app.
  rewrite app_comm_cons. apply incl_app.
  * apply incl_appl, incl_refl.
  * apply incl_appr, remove_subset.
Defined.

Definition open_rule_seqt {G1 G2 D} {s} (i : or_instance_seqt D G1 G2) :
  sat builder s (main G1 ++ hdld G1) -> node D.
Proof.
refine (fun H => open _).
exists s. destruct i as [phi psi Hin].
apply (@sat_or_of_sat_split_left _ _ _ phi psi).
eapply sat_subset; try apply H.
unfold remove_nnf. rewrite remove_app.
rewrite app_comm_cons. apply incl_app.
  * apply incl_appl, incl_refl.
  * apply incl_appr, remove_subset.
Defined.

Definition copy_rule_seqt {G D : seqt} (i : copy_instance_seqt G D) (mu : node D) : node G.
Proof.
refine (
match mu with
| closed H => closed _
| open w  => open _
end).
- destruct i. apply (@unsat_copy_of_unsat_box phi); assumption.
- destruct i. destruct w as [s Hsat]. exists s.
  apply (@sat_copy_of_sat_box phi); assumption.
Defined.

Definition dia_rule_seqt_return (L : list seqt) : Set :=
  {i | In i L /\ unsatable_KT (main i ++ hdld i)} +
  {x | batch_sat_seqt x L}.

Fixpoint dia_rule_seqt {p : seqt -> Prop} (f : forall G, p G -> node G) (L : list seqt)
  (H : forall i, In i L -> p i) {struct L} : dia_rule_seqt_return L.
Proof.
refine ((
match L as L' return L = L' -> dia_rule_seqt_return L' with
| []         => fun HeqL => inr (exist _ [] bs_nil)
| (G :: Ltl) => fun HeqL =>
    match f G (H G _) with
    | closed Hunsat       => inl (exist _ G _)
    | open (exist _ m Hm) =>
        match dia_rule_seqt p f Ltl (fun x Hx => _) with
        | inl (exist _ w Hw) => inl (exist _ w _)
        | inr (exist _ l Hl) => inr (exist _ (m::l) (bs_cons Hm Hl))
        end
    end
end) (eq_refl L)
);
try (simpl; tauto).
- rewrite HeqL. left. reflexivity.
- apply H. rewrite HeqL. right. assumption.
Defined.
