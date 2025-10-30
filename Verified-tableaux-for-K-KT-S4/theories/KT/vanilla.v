From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import ops.
From Ksat Require Import semantics.

From KTsat Require Import defs.
From KTsat Require Import size.
From KTsat Require Import ops.
From KTsat Require Import semantics.
From KTsat Require Import rules.


Require Import List.
Import ListNotations.

Require Import Program.



Program Fixpoint tableau (G : seqt) {wf (measure_lex seqt_size) G} : node G :=
match get_contra_seqt G with
| inleft (exist _ n contra_n) => contra_rule_seqt contra_n
| inright no_contra =>
    match get_and_seqt G with
    | inleft (exist _ (phi, psi) Hin) =>
        let inst := ais_cons Hin in
        and_rule_seqt inst (tableau (and_child G Hin))
    | inright no_and =>
        match get_or_seqt G with
        | inleft (exist _ (phi, psi) Hin) =>
            let inst := ois_cons Hin in
            match tableau (or_child_left G Hin) with
            | closed pr => or_rule_seqt inst (closed pr) (tableau (or_child_right G Hin))
            | open (exist _ s Hsat) => open_rule_seqt inst Hsat
            end
        | inright no_or =>
            match get_box_seqt G with
            | inleft (exist _ phi Hin) =>
                let inst := cis_cons Hin in
                copy_rule_seqt inst (tableau (box_child G Hin))
            | inright no_box =>
                let sa : saturated (main G) :=
                  {|sa_no_and := no_and;
                    sa_no_or  := no_or|} in
                let vc : @val_constructible G sa :=
                  {|vc_no_box    := no_box;
                    vc_no_contra := no_contra;
                    vc_atoms     := get_var (main G);
                    vc_hypatoms  := fun n => @get_var_iff (main G) n|} in
                match get_dia_seqt G with
                | inleft (exist _ phi Hin) =>
                    let ma : @modal_applicable G sa vc :=
                      {|ma_dia    := phi;
                        ma_dia_ex := Hin|} in
                    match @dia_rule_seqt (fun i => measure_lex seqt_size i G)
                    (fun x _ => tableau x) (unmodal_seqt G) (unmodal_seqt_size G) with
                    | inl (exist _ w Hw) => closed (unsat_of_unsat_unmodal ma w Hw)
                    | inr (exist _ w Hw) => open (exist _ (mcons vc_atoms w)
                                                           (sat_of_batch_sat w G ma Hw))
                    end
                | inright no_dia =>
                    let mc : @model_constructible G sa vc :=
                      {|mc_no_dia := no_dia|} in
                    open (exist _ (mcons vc_atoms []) (build_model_seqt G mc))
                end
            end
        end
    end
end.
Next Obligation. apply split_lt_and_seqt. Qed.
Next Obligation. apply split_lt_or_seqt_left. Qed.
Next Obligation. apply split_lt_or_seqt_right. Qed.
Next Obligation. apply copy_lt_seqt. Qed.
Next Obligation. apply measure_lex_wf. Qed.



Definition mk_seqt (G : list nnf) : seqt.
Proof.
refine (
{|main := G;
  hdld := [];
  pmain := _;
  phdld := box_only_nil|}).
unfold srefl. simpl. tauto.
Defined.

Definition is_sat (G : list nnf) : bool :=
match tableau (mk_seqt G) with
| closed _ => false
| open _   => true
end.

Theorem correctness (G : list nnf) :
  is_sat G = true <-> exists (M : KT) w, sat M w G.
Proof.
assert (main (mk_seqt G) ++ hdld (mk_seqt G) = G) as Heq.
unfold mk_seqt. simpl. apply app_nil_r.
split.
- unfold is_sat. destruct (tableau (mk_seqt G)) as [|x]; try discriminate.
  intro Htt. clear Htt. destruct x as [s Hs]. rewrite Heq in Hs.
  exists builder, s. assumption.
- unfold is_sat. destruct (tableau (mk_seqt G)) as [Hunsat|]; try trivial.
  rewrite Heq in Hunsat. intro H. destruct H as [M [w Hsat]].
  contradict Hsat. apply Hunsat.
Qed.