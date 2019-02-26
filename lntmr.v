
(* modal rules *)

Set Implicit Arguments.

(* context of a nested sequent *)
Definition nslext (W : Type) (G H seqs : list W) := G ++ seqs ++ H.

Lemma nslext_def: forall (W : Type) G H seqs,
@nslext W G H seqs = G ++ seqs ++ H.
Proof.  unfold nslext. reflexivity.  Qed.

Inductive nslrule (W : Type) (sr : rls (list W)) : rls (list W) :=
  | NSlctxt : forall ps c G H, sr ps c ->
    nslrule sr (map (nslext G H) ps) (nslext G H c).

Inductive drules (V : Set) : rls (list (rel (list (PropF V)) * dir)) :=
  | WDiaR : forall A d, drules [[(pair [] [WDia A], d); (pair [] [A], fwd)]]
      [(pair [] [WDia A], d); (pair [] [], fwd)]
  | BDiaR : forall A d, drules [[(pair [] [BDia A], d); (pair [] [A], bac)]]
      [(pair [] [WDia A], d); (pair [] [], bac)].
      


