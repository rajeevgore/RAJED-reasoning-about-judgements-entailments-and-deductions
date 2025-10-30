From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.
From Ksat Require Import full_language.

From S4sat Require Import closure.
From S4sat Require Import data.
From S4sat Require Import hintikka.
From S4sat Require Import defs.
From S4sat Require Import size.
From S4sat Require Import ops.
From S4sat Require Import semantics.
From S4sat Require Import rules.

Require Import List.
Import ListNotations.
Require Import Program.



Program Fixpoint tableau (ss : sseqt) {measure (seqt_size ss) lexnat3} : node ss :=
match get_contra_seqt ss with
| inleft (exist _ n contra_n) => contra_rule_seqt contra_n (* apply (id) rule *)
| inright no_contra =>
    match get_and_seqt ss with
    | inleft (exist _ (phi, psi) Hin) => (* apply (/\) rule *)
        and_rule_seqt Hin (tableau (and_child_sseqt Hin))
    | inright no_and =>
        match get_or_seqt ss with
        | inleft (exist _ (phi, psi) Hin) => (* apply (\/) rule *)
            match tableau (or_child_left_sseqt Hin) with
            | open w         => open_rule_seqt Hin w
            (* only traverse right branch if left branch is closed *)
            | closed Hunsatl =>
                or_rule_seqt Hin Hunsatl
                (tableau (or_child_right_sseqt Hin))
            end
        | inright no_or =>
            match get_box_seqt ss with
            | inleft (exist _ phi Hin1) =>
                (* check if box phi already appears in Sigma component *)
                match in_dec nnf_eqdec (box phi) (s_S ss) with
                | left Hin2 => (* if yes, apply (box, dup) rule *)
                    box_dup_rule_seqt Hin1 Hin2
                    (tableau (box_child_dup_sseqt Hin1 Hin2))
                | right Hin2 => (* if no, apply (box, new) rule *)
                    box_new_rule_seqt Hin1 Hin2
                    (tableau (box_child_new_sseqt Hin1 Hin2))
                end
            | inright no_box =>
                (* gather negative responses of get functions to show the current
                sequent only contains dia formulae and literals without contradiction *)
                let sc := Build_state_conditions _
                no_contra no_and no_or no_box in
                (* apply (S4) rule *)
                match dia_rule (fun x => MR lexnat3 seqt_size x ss)
                (fun x _ => tableau x) (unmodal_seqt ss)
                (unmodal_pseqt ss) (unmodal_seqt_size ss) with
                | inl bl => (* if all children are open, construct tree model *)
                    open (unmodal_batch_to_treem ss sc bl)
                | inr (exist _ i Hi) => (* if not, prove unsatisfiability *)
                    closed (unsat_of_unsat_unmodal ss i Hi)
                end
            end
        end
    end
end.
Next Obligation. apply split_lt_and_seqt. assumption. Qed.
Next Obligation. apply split_lt_or_seqt_left. assumption. Qed.
Next Obligation. apply split_lt_or_seqt_right. assumption. Qed.
Next Obligation. apply split_lt_box_seqt_dup; assumption. Qed.
Next Obligation. apply split_lt_box_seqt_new; assumption. Qed.
Next Obligation. apply lexnat3_wf. Qed.


Definition mk_root (G : list nnf) : seqt :=
{|s_G := G;
  s_S := [];
  s_H := [];
  s_d := 0;
  s_c := false;
  s_R  := G;|}.

Theorem mk_root_pseqt (G : list nnf) : pseqt (mk_root G).
Proof.
constructor; simpl.
- constructor.
- constructor.
- apply incl_nil_l.
- apply incl_nil_l.
- apply mem_closure_self.
- apply box_only_nil.
- contradiction.
- discriminate.
- discriminate.
Qed.

Definition mk_root_sseqt (G : list nnf) : sseqt :=
  exist _ (mk_root G) (mk_root_pseqt G).

Definition tableau_sat (G : list nnf) : bool :=
match tableau (mk_root_sseqt G) with
| open _   => true
| closed _ => false
end.

Theorem completeness : forall G,
  satable_S4 G -> tableau_sat G = true.
Proof.
intros G H. destruct (tableau_sat G) eqn:Htab; try reflexivity.
unfold tableau_sat in Htab.
destruct (tableau (mk_root_sseqt G)) as [|c]; try discriminate.
simpl in c. unfold unsatable_S4_seqt, mk_root in c. simpl in c.
rewrite app_nil_r in c.
destruct H as [M [w H]]. contradict H. apply c.
Qed.

Definition tableau_treem_from_G (G : list nnf) :
  tableau_sat G = true -> {tt : tableau_treem | G = tm_G (tt_root tt)}.
Proof.
intro H. unfold tableau_sat in H.
destruct (tableau (mk_root_sseqt G)) as [o|]; try discriminate.
destruct o as [rt [prt [gprt Heqsert]]].
assert (tm_d rt = 0) as Hd0.
{ unfold tm_d. rewrite Heqsert. simpl. reflexivity. }
exists (
{|
  tt_root := rt;
  tt_proot := prt;
  tt_gproot := gprt;
  tt_depth0 := Hd0;
|}).
simpl. unfold tm_G. rewrite Heqsert. simpl. reflexivity.
Defined.

Theorem soundness : forall G,
  tableau_sat G = true -> satable_S4 G.
Proof.
intros G H. destruct (tableau_treem_from_G G H) as [tt HeqG].
rewrite HeqG. apply model_existence.
Qed.

Theorem correctness : forall G,
  tableau_sat G = true <-> satable_S4 G.
Proof.
intro G. split; [apply soundness|apply completeness].
Qed.

Definition fml_tableau_sat (G : list fml) := tableau_sat (map to_nnf G).

Theorem fml_correctness : forall G,
  fml_tableau_sat G = true <-> fml_satable_S4 G.
Proof.
unfold fml_tableau_sat. unfold fml_satable_S4.
setoid_rewrite sat_fml_nnf_iff.
intro G. apply correctness.
Qed.
