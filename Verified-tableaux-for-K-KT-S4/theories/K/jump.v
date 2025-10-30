From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import size.
From Ksat Require Import ops.
From Ksat Require Import semantics.
From Ksat Require Import model.
From Ksat Require Import marking.
From Ksat Require Import rules.

Require Import List.
Import ListNotations.
Require Import Program.


Program Fixpoint tableau (G : list nnf) {measure (node_size G)} : node G :=
match get_contra G with
| inleft (exist _ n contra_n) => contra_rule contra_n
| inright no_contra =>
    match get_and G with
    | inleft (exist _ (phi, psi) pinG) =>
        let D := phi :: psi :: remove_nnf (and phi psi) G in
        let inst := ai_cons pinG in
        and_rule inst (tableau D)
    | inright no_and =>
        match get_or G with
        | inleft (exist _ (phi, psi) pinG) =>
            let G1 := phi :: remove_nnf (or phi psi) G in
            let G2 := psi :: remove_nnf (or phi psi) G in
            let inst := oi_cons pinG in
            match tableau G1 with
            | closed _ m hunsat pm =>
                match in_dec nnf_eqdec (left_prcp inst) m with
                | left _      => or_rule inst (closed G1 m hunsat pm) (tableau G2)
                | right hprcp => jump_rule inst m hunsat pm hprcp
                end
            | open _ (exist _ _ hsat) => open_rule inst hsat
            end
        | inright no_or =>
            let sa : saturated G :=
              {|sa_no_and := no_and;
                sa_no_or  := no_or|} in
            let vc : @val_constructible G sa :=
              {|vc_no_contra   := no_contra;
                vc_atoms    := get_var G;
                vc_hypatoms := fun n => @get_var_iff G n|} in
            match get_dia G with
            | inleft (exist _ p pinG) =>
                let ma : @modal_applicable G sa vc :=
                  {|ma_dia    := p;
                    ma_dia_ex := pinG|} in
                let l := @tmap (fun D => node_size D < node_size G)
                (fun x h => tableau x) (unmodal G) (unmodal_size G) in
                match l with
                | inl (exist _ c (conj pc1 (conj pc2 pc3))) =>
                    closed G (mark_modal G (fst c) (snd c))
                    (unsat_of_unsat_unmodal ma (fst c) (conj pc1 pc2))
                    (modal_pmark ma (fst c) (snd c) (conj pc1 pc2) pc3)
                | inr (exist _ x px) =>
                    open G (exist _ (mcons vc.(vc_atoms) x) (sat_of_batch_sat x G ma px))
                end
            | inright no_dia =>
                let mc : @model_constructible G sa vc :=
                  {|mc_no_dia := no_dia|} in
                open G (exist _ (mcons vc.(vc_atoms) []) (build_model G mc))
            end
        end
    end
end.
Next Obligation.
repeat (rewrite node_size_cons). apply split_lt_and. assumption.
Qed.
Next Obligation.
rewrite node_size_cons. apply split_lt_or_left. assumption.
Qed.
Next Obligation.
rewrite node_size_cons. apply split_lt_or_right. assumption.
Qed.




Definition is_sat (G : list nnf) : bool :=
match tableau G with
| closed _ _ _ _ => false
| open _ _       => true
end.

Theorem correctness (G : list nnf) :
  is_sat G = true <-> exists (k : kripke) s, sat k s G.
Proof.
unfold is_sat.
destruct (tableau G) as [m Hunsat pm | sigsat].
- split.
  * discriminate.
  * intro H. contradict Hunsat. unfold unsatable.
    intro H0. destruct H as (k & s & Hsat).
    specialize (H0 k s). contradiction.
- split.
  * intro tt. destruct sigsat as [s sats].
    exists builder, s. assumption.
  * tauto.
Qed.


(*
Definition is_sat_model (G : list nnf) : bool * (option model) :=
match tableau G with
| closed _ _ _ _        => (false, None)
| open_ _ (exist _ m _) => (true, Some m)
end.

(* The negation of the defining formula of K is unsatisfiable *)

Definition phi_ex : nnf :=
and (box (or (neg 1) (var 2))) (and (box (var 1)) (dia (neg 2))).

Compute (is_sat [phi_ex]).

Definition psi_ex : nnf := and (box (var 1)) (dia (dia (neg 1))).

Compute (is_sat [psi_ex]).

Definition nnf_exm : nnf := or (var 1) (neg 1).

Compute (is_sat [nnf_exm]).

Definition complex_ex : nnf :=
  and (box (box (dia (var 0))))
  (or (dia (box (box (neg 0)))) (and (dia (box (dia (dia (var 0))))) (box (neg 0)))).

Compute (is_sat_model [complex_ex]).
*)