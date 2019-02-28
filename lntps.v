
(* try non-adjacent exchange, for system with princrule and seqrule *)

(* this doesn't work for

Γ1 B Γ2 |- Δ1 Δ2    Γ1 Γ2 |- Δ1 A Δ2
----------------------------------------
Γ1 A->B Γ2 |- Δ1 Δ2

because in this case, interchanging A->B with some Q
in either Γ1 or Γ2 requires, in the right premise, moving that Q
to in between Γ1 and Γ2, ie

Γ1 B Γ2' Q Γ2'' |- Δ1 Δ2    Γ1 Γ2' Q Γ2'' |- Δ1 A Δ2
------------------------------------------------------
Γ1 A->B Γ2' Q Γ2'' |- Δ1 Δ2

becomes

Γ1 B Γ2' Q Γ2'' |- Δ1 Δ2    Γ1 Γ2' Q Γ2'' |- Δ1 A Δ2
------------------------------------------------------
Γ1 A->B Γ2' Q Γ2'' |- Δ1 Δ2

Γ1 Q Γ2' B Γ2'' |- Δ1 Δ2    Γ1 Q Γ2' Γ2'' |- Δ1 A Δ2
------------------------------------------------------
Γ1 Q Γ2' A->B Γ2'' |- Δ1 Δ2

that is, in the right premise, we have to just move Q,
not swap it with something else.
*)

