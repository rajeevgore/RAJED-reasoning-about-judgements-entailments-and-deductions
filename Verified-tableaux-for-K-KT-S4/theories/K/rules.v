From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.
From Ksat Require Import model.
From Ksat Require Import marking.

Require Import List.
Import ListNotations.


Inductive node (G : list nnf) : Type :=
  | closed : forall m, unsatable G -> pmark G m -> node G
  | open   : {s | sat builder s G} -> node G.


Definition and_rule {G D} (i : and_instance G D) (mu : node D) : node G.
Proof.
refine (
  match mu with
  | closed _ m h p => _
  | open _ w       => _
  end).
- pose proof (pmark_of_closed_and i m h p) as Hsig.
  destruct Hsig as [m' HpGm'].
  eleft.
  * apply (unsat_of_closed_and i). assumption.
  * apply HpGm'.
- right. destruct w as [m Hsat]. destruct i as [phi psi Hin].
  exists m. apply (sat_and_of_sat_split Hsat).
Defined.

Definition jump_rule {G1 G2 D : list nnf} (i : or_instance D G1 G2) (m : list nnf) :
  unsatable G1 -> pmark G1 m -> ~ In (left_prcp i) m -> node D.
Proof.
intros Hunsat HpG1m Hnin.
pose proof (pmark_of_jump i m Hunsat HpG1m Hnin) as Hsig.
destruct Hsig as [l HpDl].
eleft.
- apply (unsat_of_jump i m); assumption.
- apply HpDl.
Defined.

Definition or_rule {G1 G2 D} (i : or_instance D G1 G2) (mu : node G1) (nu : node G2) :
  node D.
Proof.
refine (
  match mu, nu with
  | open _ w, _                          => _
  | _, open _ w                          => _
  | closed _ m1 h1 p1, closed _ m2 h2 p2 => _
  end
).
- destruct (pmark_of_closed_or i h1 p1 h2 p2) as [x px].
  eleft.
  * apply (unsat_of_closed_or i); assumption.
  * exact px.
- right. destruct i as [phi psi h].
  destruct w as [t satt].
  exists t. apply (sat_or_of_sat_split_right _ satt).
- right. destruct i as [phi psi h].
  destruct w as [t satt].
  exists t. apply (sat_or_of_sat_split_left _ satt).
Defined.

Definition open_rule {G1 G2 D} {s} (i : or_instance D G1 G2) :
  sat builder s G1 -> node D.
Proof.
intro H. right. destruct i as [phi psi Hin].
exists s. apply (sat_or_of_sat_split_left _ H).
Defined.

Definition contra_rule {D n} : In (var n) D /\ In (neg n) D -> node D.
Proof.
intro Hin. destruct Hin as [Hinvar Hinneg]. left with (m:=[var n; neg n]).
- apply (unsat_contra Hinvar Hinneg).
- intros D' HD' Hsub. apply (@unsat_contra _ n);
  apply mem_diff_of_mem;
  (assumption || (intro HinD'; apply (HD' _ HinD'); simpl; tauto)).
Defined.



(*  This is essentially the modal rule. *)

Definition tmap_return (G : list (list nnf)) : Set :=
{c : list nnf * list nnf | In (fst c) G /\ unsatable (fst c) /\ pmark (fst c) (snd c)}
+ {x | batch_sat x G}.

Fixpoint tmap {p : list nnf -> Prop} (f : forall G, p G -> node G)
  (G : list (list nnf)) (hp : forall i, In i G -> p i) {struct G} : tmap_return G.
Proof.
refine (
 (match G as G' return G = G' -> tmap_return G' with
  | []       => fun HeqG => inr (exist _ _ bs_nil)
  | l :: Gtl => fun HeqG =>
      match f l (hp l _) with
      | closed _ m pr pm       => inl (exist _ (l,m) _)
      | open  _ (exist _ s Hs) =>
          match tmap p f Gtl (fun x hx => _) with
          | inl (exist _ w Hw) => inl (exist _ w _)
          | inr (exist _ w Hw) => inr (exist _ (s :: w) _)
          end
      end
  end) (eq_refl G)
).
- rewrite HeqG. apply in_eq.
- split; try split; simpl.
  * left. reflexivity.
  * assumption.
  * assumption.
- apply hp. rewrite HeqG. simpl. right. assumption.
- destruct Hw as (Hw1 & Hw2 & Hw3).
  split; try split; try assumption.
  simpl. right. assumption.
- apply bs_cons; assumption.
Defined.