From Ksat Require Import utils.
From Ksat Require Import defs.
From Ksat Require Import semantics.

From S4sat Require Import closure.
From S4sat Require Import data.
From S4sat Require Import hintikka.
From S4sat Require Import defs.
From S4sat Require Import semantics.

Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Arith.
Require Import Relations.
Require Import Program.
Require Import Lia.

Set Implicit Arguments.


Definition tm_info (x : treem) (s : seqt) :=
  ptreem x /\ gptreem x /\ tm_se x = s.

Definition open_info (s : seqt) := {x | tm_info x s}.

Inductive node (s : seqt) : Type :=
  | open   : open_info s -> node s
  | closed : unsatable_S4_seqt s -> node s.

Arguments closed [s].
Arguments open [s].

Definition contra_rule_seqt [s n] :
  In (var n) (s_G s) /\ In (neg n) (s_G s) -> node s.
Proof.
refine (fun H => closed _).
apply (@unsat_contra_seqt _ n); tauto.
Defined.



Definition and_rule_seqt [phi psi] [ss : sseqt]
  (Hin : In (and phi psi) (s_G (`ss)))
  (nu : node (and_child phi psi (`ss))) : node (`ss).
Proof.
refine (
match nu with
| open w        => open _
| closed Hunsat => closed (unsat_of_closed_and_seqt Hin Hunsat)
end).
clear nu. destruct w as [c [pc [gpc Heqsec]]].
destruct ss as [s ps]. simpl in Hin, Heqsec |- *.
set (x := mcons (tm_children c) s (tm_req c) (and phi psi :: tm_htk c)).

assert (tm_d x = tm_d c) as Heqd.
{ unfold tm_d. rewrite Heqsec. simpl. reflexivity. }
assert (tm_H x = tm_H c) as HeqH.
{ unfold tm_H. rewrite Heqsec. simpl. reflexivity. }
assert (tm_S x = tm_S c) as HeqB.
{ unfold tm_S. rewrite Heqsec. simpl. reflexivity. }
assert (forall y, is_child y x <-> is_child y c) as Hiffch.
{ unfold is_child. intro y. apply iff_refl. }
assert (forall y, desc y x <-> desc y c) as Hiffdesc.
{ intro y. apply eq_desc_of_eq_children. reflexivity. }

exists x. split.
{
constructor.
- assumption.
- intros xi Hxi.
  destruct (nnf_eqdec xi (and phi psi)) as [Heq|Hneq].
  + rewrite Heq. now left.
  + right. apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec.
    right. right. apply in_in_remove; try assumption.
- apply pre_hintikka_and_htk.
  + apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec. now left.
  + apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec. right. now left.
  + apply (ptphhtk pc).
- setoid_rewrite Hiffch. rewrite HeqB. apply (ptmsboxS pc).
- setoid_rewrite Hiffch. intros y Hy xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptmsbox pc); assumption.
- setoid_rewrite Hiffch. intros xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptmdia pc xi); assumption.
- rewrite Heqd, HeqH. setoid_rewrite Hiffdesc. apply (ptdcomH pc).
- rewrite HeqH. apply (ptreqH pc).
- rewrite Heqd, HeqB. setoid_rewrite Hiffdesc. apply (ptdcomS pc).
- rewrite HeqB. intros H xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptboxhtkS pc); assumption.
- rewrite Heqd. setoid_rewrite Hiffdesc. apply (ptfulfill pc).
- setoid_rewrite Hiffdesc. apply (ptadtran pc).
}

split; try reflexivity.
unfold gptreem. setoid_rewrite Hiffdesc. assumption.
Defined.




Definition open_rule_seqt [phi psi] [ss : sseqt]
  (Hin : In (or phi psi) (s_G (`ss)))
  (w : open_info (or_child_left phi psi (`ss))) : node (`ss).
Proof.
refine (open _).

destruct w as [c [pc [gpc Heqsec]]].
destruct ss as [s ps]. simpl in Hin, Heqsec |- *.
set (x := mcons (tm_children c) s (tm_req c) (or phi psi :: tm_htk c)).

assert (tm_d x = tm_d c) as Heqd.
{ unfold tm_d. rewrite Heqsec. simpl. reflexivity. }
assert (tm_H x = tm_H c) as HeqH.
{ unfold tm_H. rewrite Heqsec. simpl. reflexivity. }
assert (tm_S x = tm_S c) as HeqB.
{ unfold tm_S. rewrite Heqsec. simpl. reflexivity. }
assert (forall y, is_child y x <-> is_child y c) as Hiffch.
{ unfold is_child. intro y. apply iff_refl. }
assert (forall y, desc y x <-> desc y c) as Hiffdesc.
{ intro y. apply eq_desc_of_eq_children. reflexivity. }

exists x. split.
{
constructor.
- assumption.
- intros xi Hxi.
  destruct (nnf_eqdec xi (or phi psi)) as [Heq|Hneq].
  + rewrite Heq. now left.
  + right. apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec.
    right. apply in_in_remove; try assumption.
- apply pre_hintikka_or_left_htk.
  + apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec. now left.
  + apply (ptphhtk pc).
- setoid_rewrite Hiffch. rewrite HeqB. apply (ptmsboxS pc).
- setoid_rewrite Hiffch. intros y Hy xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptmsbox pc); assumption.
- setoid_rewrite Hiffch. intros xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptmdia pc xi); assumption.
- rewrite Heqd, HeqH. setoid_rewrite Hiffdesc. apply (ptdcomH pc).
- rewrite HeqH. apply (ptreqH pc).
- rewrite Heqd, HeqB. setoid_rewrite Hiffdesc. apply (ptdcomS pc).
- rewrite HeqB. intros H xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptboxhtkS pc); assumption.
- rewrite Heqd. setoid_rewrite Hiffdesc. apply (ptfulfill pc).
- setoid_rewrite Hiffdesc. apply (ptadtran pc).
}

split; try reflexivity.
unfold gptreem. setoid_rewrite Hiffdesc. assumption.
Defined.




Definition or_rule_seqt [phi psi] [ss : sseqt]
  (Hin : In (or phi psi) (s_G (`ss)))
  (Hunsatl : unsatable_S4_seqt (or_child_left phi psi (`ss)))
  (nu : node (or_child_right phi psi (`ss))) : node (`ss).
Proof.
refine (
match nu with
| closed Hunsatr => closed (unsat_of_closed_or_seqt Hin Hunsatl Hunsatr)
| open w    => open _
end
).
clear nu. destruct w as [c [pc [gpc Heqsec]]].
destruct ss as [s ps]. simpl in Hin, Hunsatl, Heqsec |- *.
set (x := mcons (tm_children c) s (tm_req c) (or phi psi :: tm_htk c)).

assert (tm_d x = tm_d c) as Heqd.
{ unfold tm_d. rewrite Heqsec. simpl. reflexivity. }
assert (tm_H x = tm_H c) as HeqH.
{ unfold tm_H. rewrite Heqsec. simpl. reflexivity. }
assert (tm_S x = tm_S c) as HeqB.
{ unfold tm_S. rewrite Heqsec. simpl. reflexivity. }
assert (forall y, is_child y x <-> is_child y c) as Hiffch.
{ unfold is_child. intro y. apply iff_refl. }
assert (forall y, desc y x <-> desc y c) as Hiffdesc.
{ intro y. apply eq_desc_of_eq_children. reflexivity. }

exists x. split.
{
constructor.
- assumption.
- intros xi Hxi.
  destruct (nnf_eqdec xi (or phi psi)) as [Heq|Hneq].
  + rewrite Heq. now left.
  + right. apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec.
    right. apply in_in_remove; try assumption.
- apply pre_hintikka_or_right_htk.
  + apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec. now left.
  + apply (ptphhtk pc).
- setoid_rewrite Hiffch. rewrite HeqB. apply (ptmsboxS pc).
- setoid_rewrite Hiffch. intros y Hy xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptmsbox pc); assumption.
- setoid_rewrite Hiffch. intros xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptmdia pc xi); assumption.
- rewrite Heqd, HeqH. setoid_rewrite Hiffdesc. apply (ptdcomH pc).
- rewrite HeqH. apply (ptreqH pc).
- rewrite Heqd, HeqB. setoid_rewrite Hiffdesc. apply (ptdcomS pc).
- rewrite HeqB. intros H xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptboxhtkS pc); assumption.
- rewrite Heqd. setoid_rewrite Hiffdesc. apply (ptfulfill pc).
- setoid_rewrite Hiffdesc. apply (ptadtran pc).
}

split; try reflexivity.
unfold gptreem. setoid_rewrite Hiffdesc. assumption.
Defined.




Definition box_dup_rule_seqt [phi] [ss : sseqt]
  (Hin1 : In (box phi) (s_G (`ss))) (Hin2 : In (box phi) (s_S (`ss)))
  (nu : node (box_child_dup phi (`ss))) : node (`ss).
Proof.
refine (
match nu with
| open w        => open _
| closed Hunsat => closed (unsat_of_closed_box_dup_seqt Hin1 Hunsat)
end).
clear nu. destruct w as [c [pc [gpc Heqsec]]].
destruct ss as [s ps]. simpl in Hin1, Hin2, Heqsec |- *.
set (x := mcons (tm_children c) s (tm_req c) (box phi :: tm_htk c)).

assert (tm_d x = tm_d c) as Heqd.
{ unfold tm_d. rewrite Heqsec. simpl. reflexivity. }
assert (tm_H x = tm_H c) as HeqH.
{ unfold tm_H. rewrite Heqsec. simpl. reflexivity. }
assert (tm_S x = tm_S c) as HeqB.
{ unfold tm_S. rewrite Heqsec. simpl. reflexivity. }
assert (forall y, is_child y x <-> is_child y c) as Hiffch.
{ unfold is_child. intro y. apply iff_refl. }
assert (forall y, desc y x <-> desc y c) as Hiffdesc.
{ intro y. apply eq_desc_of_eq_children. reflexivity. }

exists x. split.
{
constructor.
- assumption.
- intros xi Hxi.
  destruct (nnf_eqdec xi (box phi)) as [Heq|Hneq].
  + rewrite Heq. now left.
  + right. apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec.
    right. apply in_in_remove; try assumption.
- apply pre_hintikka_box_htk.
  + apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec. now left.
  + apply (ptphhtk pc).
- setoid_rewrite Hiffch. rewrite HeqB. apply (ptmsboxS pc).
- setoid_rewrite Hiffch. intros y Hy xi Hxi.
  destruct Hxi as [Hxi|Hxi].
  + injection Hxi. intro Heqphi. rewrite <- Heqphi.
    apply (ptmsboxS pc); try assumption.
    rewrite <- HeqB. assumption.
  + apply (ptmsbox pc); assumption.
- setoid_rewrite Hiffch. intros xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptmdia pc xi); assumption.
- rewrite Heqd, HeqH. setoid_rewrite Hiffdesc. apply (ptdcomH pc).
- rewrite HeqH. apply (ptreqH pc).
- rewrite Heqd, HeqB. setoid_rewrite Hiffdesc. apply (ptdcomS pc).
- intros H xi Hxi. destruct Hxi as [Hxi|Hxi].
  + injection Hxi. intro Heqphi. rewrite <- Heqphi. assumption.
  + rewrite HeqB. apply (ptboxhtkS pc); assumption.
- rewrite Heqd. setoid_rewrite Hiffdesc. apply (ptfulfill pc).
- setoid_rewrite Hiffdesc. apply (ptadtran pc).
} 

split; try reflexivity.
unfold gptreem. setoid_rewrite Hiffdesc. assumption.
Defined.




Definition box_new_rule_seqt [phi] [ss : sseqt]
  (Hin1 : In (box phi) (s_G (`ss))) (Hin2 : ~ In (box phi) (s_S (`ss)))
  (nu : node (box_child_new phi (`ss))) : node (`ss).
Proof.
refine (
match nu with
| open w        => open _
| closed Hunsat => closed (unsat_of_closed_box_new_seqt Hin1 Hunsat)
end).
clear nu. destruct w as [c [pc [gpc Heqsec]]].
destruct ss as [s ps]. simpl in Hin1, Hin2, Heqsec |- *.
set (x := mcons (tm_children c) s (tm_req c) (box phi :: tm_htk c)).

assert (tm_d x = tm_d c) as Heqd.
{ unfold tm_d. rewrite Heqsec. simpl. reflexivity. }
assert (tm_H c = []) as HeqH.
{ unfold tm_H. rewrite Heqsec. simpl. reflexivity. }
assert (tm_S c = box phi :: tm_S x) as HeqB.
{ unfold tm_S. rewrite Heqsec. simpl. reflexivity. }
assert (forall y, is_child y x <-> is_child y c) as Hiffch.
{ unfold is_child. intro y. apply iff_refl. }
assert (forall y, desc y x <-> desc y c) as Hiffdesc.
{ intro y. apply eq_desc_of_eq_children. reflexivity. }

exists x. split.
{
constructor.
- assumption.
- intros xi Hxi.
  destruct (nnf_eqdec xi (box phi)) as [Heq|Hneq].
  + rewrite Heq. now left.
  + right. apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec.
    right. apply in_in_remove; try assumption.
- apply pre_hintikka_box_htk.
  + apply (ptGinhtk pc). unfold tm_G. rewrite Heqsec. now left.
  + apply (ptphhtk pc).
- setoid_rewrite Hiffch. intros y Hy xi Hxi.
  apply (ptmsboxS pc); try assumption. rewrite HeqB. now right.
- setoid_rewrite Hiffch. intros y Hy xi Hxi.
  destruct Hxi as [Hxi|Hxi].
  + injection Hxi. intro Heqphi. rewrite <- Heqphi.
    apply (ptmsboxS pc); try assumption.
    rewrite HeqB. now left.
  + apply (ptmsbox pc); assumption.
- setoid_rewrite Hiffch. intros xi Hxi.
  destruct Hxi as [|Hxi]; try discriminate.
  apply (ptmdia pc xi); assumption.
- rewrite Heqd. setoid_rewrite Hiffdesc. intros y Hy h Hh1 Hh2.
  apply False_ind. fold (In h []). rewrite <- HeqH.
  apply (ptdcomH pc Hy); assumption.
- intros rq Hrq. apply False_ind. fold (In rq []).
  rewrite <- HeqH. apply (ptreqH pc). assumption.
- rewrite Heqd. setoid_rewrite Hiffdesc.
  intros y Hy [rq [Hrq1 Hrq2]].
  apply False_ind. fold (In rq []). rewrite <- HeqH.
  apply (ptdcomH pc Hy); try assumption.
  pose proof (gpc y Hy) as py. apply (ptreqH py). assumption.
- intro H. destruct (not_nil_ex H) as [rq Hrq].
  apply False_ind. fold (In rq []). rewrite <- HeqH.
  apply (ptreqH pc). assumption.
- rewrite Heqd. setoid_rewrite Hiffdesc. apply (ptfulfill pc).
- setoid_rewrite Hiffdesc. apply (ptadtran pc).
} 

split; try reflexivity.
unfold gptreem. setoid_rewrite Hiffdesc. assumption.
Defined.




Inductive batch_eq : list treem -> list seqt -> Prop :=
  | bs_nil : batch_eq [] []
  | bs_cons (x : treem) (s : seqt)
      (lx : list treem) (ls : list seqt) :
      tm_info x s -> batch_eq lx ls ->
      batch_eq (x :: lx) (s :: ls).

Theorem be_ex [lx ls] : 
  batch_eq lx ls -> forall (x : treem), In x lx ->
  exists s, In s ls /\ tm_info x s.
Proof.
intro be. induction be.
- simpl. tauto.
- intros y Hy. destruct Hy as [Hy|Hy]. 
  + rewrite <- Hy. exists s. split; try (now left).
    assumption.
  + apply IHbe in Hy. destruct Hy as [sy Hsy].
    exists sy. split; try (now right). tauto.
Qed.

Theorem be_forall [lx ls] :
  batch_eq lx ls -> forall (s : seqt), In s ls ->
  exists x, In x lx /\ tm_info x s.
Proof.
intro be. induction be.
- simpl. tauto.
- intros t Ht. destruct Ht as [Ht|Ht].
  + exists x. split; try (simpl; tauto).
    rewrite <- Ht. assumption.
  + apply IHbe in Ht. destruct Ht as [y [Hin Heq]].
    exists y. split; try (now right). assumption.
Qed.


Definition dia_rule_return (L : list seqt) : Type :=
  {lx | batch_eq lx L} + {s | In s L /\ unsatable_S4_seqt s}.

Fixpoint dia_rule (pm : seqt -> Prop)
  (f : forall (ss : sseqt), pm (`ss) -> node (`ss)) (L : list seqt)
  (pL : forall s, In s L -> pseqt s) (hpm : forall s, In s L -> pm s)
  {struct L} : dia_rule_return L.
Proof.
refine ((
match L as L' return L = L' -> dia_rule_return L' with
| []         => fun HeqL => inl (exist _ [] bs_nil)
| (G :: Ltl) => fun HeqL =>
    match f (exist _ G (pL G _)) (hpm G _) with
    | open (exist _ m be_m) => 
        match dia_rule pm f Ltl _ _ with
        | inl (exist _ lm Hlm) => inl (exist _ (m::lm) _)
        | inr (exist _ w Hw)   => inr (exist _ w _)
        end
    | closed Hunsat         => inr (exist _ G _)
    end
end) (eq_refl L)); 
try ((simpl; tauto) || (rewrite HeqL; simpl; tauto)).
- intros s Hs. apply pL. rewrite HeqL. now right.
- intros s Hs. apply hpm. rewrite HeqL. now right.
- constructor; assumption.
Unshelve. rewrite HeqL. now left.
Defined.



(* Definition models_to_tmodels : list model -> list tmodel :=
  map (@proj1_sig tmodel _). *)


Definition nnf_eqsnd (phi : nnf) (p : nat*nnf) : bool :=
  if nnf_eqdec (snd p) phi then true else false.

Fixpoint dia_rule_loop (H : list (nat*nnf)) (B G : list nnf) :
  list (nat*nnf) :=
  match G with
  | [] => []
  | (dia phi :: Gtl) =>
      match find (nnf_eqsnd phi) H with
      | Some p => p :: dia_rule_loop H B Gtl
      | None   => dia_rule_loop H B Gtl
      end
  | _ :: Gtl => dia_rule_loop H B Gtl
  end.

Theorem mem_loop_left [phi H B G] : In phi (map snd H) ->
  In (dia phi) G -> exists n, In (n, phi) (dia_rule_loop H B G).
Proof.
intros HphiH HphiG.
induction G as [|psi].
- simpl in HphiG. contradiction.
- destruct HphiG as [HphiG|HphiG].
  + rewrite HphiG. simpl.
    destruct (find (nnf_eqsnd phi) H) eqn:Heqfind.
    * apply find_some in Heqfind. exists (fst p).
      left. rewrite surjective_pairing at 1.
      rewrite pair_equal_spec. split; try reflexivity.
      destruct Heqfind as [Heqfind1 Heqfind2].
      unfold nnf_eqsnd in Heqfind2.
      destruct (nnf_eqdec (snd p) phi) as [Heq|Hneq] in Heqfind2;
      try discriminate. assumption.
    * pose proof (find_none _ _ Heqfind) as H0.
      apply in_map_iff in HphiH.
      destruct HphiH as [h [Hh1 Hh2]].
      specialize (H0 h Hh2). unfold nnf_eqsnd in H0.
      destruct (nnf_eqdec (snd h) phi) in H0; try discriminate.
      contradiction.
  + specialize (IHG HphiG). destruct IHG as [n Hn].
    exists n. destruct psi; try (simpl; assumption). simpl.
    destruct (find (nnf_eqsnd psi) H); try assumption. now right.
Qed.

Theorem mem_loop_dia [H B G rq] :
  In rq (dia_rule_loop H B G) -> In rq H.
Proof.
induction G as [|phi].
- simpl. tauto.
- destruct phi; try (apply IHG).
  simpl. destruct (find (nnf_eqsnd phi) H) as [p|] eqn:Heqfd.
  + intro Hrq. destruct Hrq as [Heq|Hin].
    * rewrite <- Heq. apply (find_some _ _ Heqfd).
    * apply IHG. assumption.
  + apply IHG.
Qed.


Definition unmodal_batch_to_treem (ss : sseqt)
  (sc : state_conditions (`ss)) :
  {lx : list treem | batch_eq lx (unmodal_seqt (`ss))} ->
  open_info (`ss).
Proof.
destruct ss as [s ps]. simpl in sc |- *. intros [lx Hlx].
set (x := mcons lx s (dia_rule_loop (s_H s) (s_S s) (s_G s)) (s_G s)).

assert (forall y, is_child y x -> exists phi : nnf,
  In phi (filter_undia (map snd (s_H s)) (s_G s)) /\
  tm_se y = dia_child phi s) as Hunch.
{
intros y ychx. destruct (be_ex Hlx _ ychx) as [t [Htin Hiyt]].
apply in_map_iff in Htin. destruct Htin as [phi [Hphi1 Hphi2]].
exists phi. split; try assumption. rewrite Hphi1. apply Hiyt.
}

assert (forall y, is_child y x -> tm_S x = tm_S y) as HeqB.
{
intros y H. apply Hunch in H.
destruct H as [phi [Hphi1 Hphi2]].
unfold tm_S. rewrite Hphi2. unfold dia_child.
simpl. reflexivity.
}

assert (forall y, is_child y x -> tm_d y = S (tm_d x)) as Heqd.
{
intros y H. apply Hunch in H.
destruct H as [phi [Hphi1 Hphi2]].
unfold tm_d. rewrite Hphi2. unfold dia_child.
simpl. reflexivity.
}

assert (forall y, is_child y x -> tm_c y = true) as Heqc.
{
intros y H. apply Hunch in H.
destruct H as [phi [Hphi1 Hphi2]].
unfold tm_c. rewrite Hphi2. unfold dia_child.
simpl. reflexivity.
}

exists x. split.
{
constructor.
- assumption.
- apply incl_refl.
- apply pre_hintikka_sc. assumption.
- intros y ychx. pose proof (be_ex Hlx _ ychx) as [_ [_ [py _]]].
  eapply incl_tran.
  2:{ apply (ptGinhtk py). }
  eapply incl_tran.
  2:{ apply (S_incl_G (ptpseq py)). apply Heqc. assumption. }
  fold (tm_S y). rewrite HeqB with y; [apply incl_refl|assumption].
- intros y Hy phi Hphi. contradict Hphi. apply (sc_no_box sc).
- intros phi Hphi.
  destruct (in_dec nnf_eqdec phi (map snd (s_H s))) as [Hin|Hnin].
  + right.
    pose proof (@mem_loop_left _ _ (s_S s) (s_G s) Hin Hphi) as Hex.
    destruct Hex as [n Hn]. exists (n, phi). split; try assumption.
    simpl. reflexivity.
  + left. pose proof (mem_filter_undia_left Hphi Hnin) as H.
    apply (in_map (fun d => dia_child d s) _ _) in H.
    fold (unmodal_seqt s) in H. apply (be_forall Hlx) in H.
    destruct H as [y [Hyin [_ [_ Heqsey]]]].
    exists y. split; try assumption.
    pose proof (be_ex Hlx _ Hyin) as [_ [_ [py _]]].
    apply (ptGinhtk py). unfold tm_G.
    rewrite Heqsey. simpl. now left.
- intros y yltx h Hinh Hfsth. unfold tm_d in Hfsth. simpl in Hfsth.
  apply clos_trans_tn1 in yltx. inversion yltx.
  + clear H0 y0. apply Hunch in H.
    destruct H as [phi [Hphi1 Hphi2]].
    unfold tm_H in Hinh. rewrite Hphi2 in Hinh.
    simpl in Hinh. destruct Hinh as [Heqh|Hinh].
    * rewrite <- Heqh in Hfsth. simpl in Hfsth. lia.
    * unfold tm_H. simpl. assumption.
  + clear H1 z. apply clos_tn1_trans in H0. fold desc in H0.
    pose proof (Hunch _ H) as H1.
    destruct H1 as [phi [Hphi1 Hphi2]].
    pose proof (be_ex Hlx _ H) as [_ [_ [py0 _]]].
    assert (In h (tm_H y0)) as Hiny0.
    { apply (ptdcomH py0 H0 h Hinh). unfold tm_d. rewrite Hphi2.
    simpl. lia. }
    unfold tm_H in Hiny0.
    rewrite Hphi2 in Hiny0. unfold dia_child in Hiny0.
    simpl in Hiny0. destruct Hiny0 as [Heq|Hin].
    * rewrite <- Heq in Hfsth. simpl in Hfsth. lia.
    * unfold tm_H. simpl. assumption.
- intros rq Hrq. simpl. apply mem_loop_dia in Hrq.
  unfold tm_H. simpl. assumption.
- intros y yltx Hex.
  apply clos_trans_tn1 in yltx. inversion yltx.
  + clear H0 y0. apply Hunch in H.
    destruct H as [phi [Hphi1 Hphi2]].
    unfold tm_S. rewrite Hphi2. simpl. reflexivity.
  + clear H1 z. apply clos_tn1_trans in H0. fold desc in H0.
    apply eq_trans with (tm_S y0); try (apply (HeqB y0 H)).
    pose proof (be_ex Hlx _ H) as [_ [_ [py0 _]]].
    apply (ptdcomS py0); try assumption.
    destruct Hex as [rq [Hrq1 Hrq2]].
    exists rq. split; try assumption.
    rewrite (Heqd y0 H). lia.
- intros H phi Hphi. contradict Hphi. apply (sc_no_box sc).
- intros y yltx n Hn.
  apply clos_trans_tn1 in yltx. inversion yltx.
  + clear H0 y0. rewrite (Heqd _ H) in Hn. lia.
  + clear H1 z. apply clos_tn1_trans in H0. fold desc in H0.
    assert (S (tm_d x) <= n) as Hlen. { lia. }
    rewrite <- (Heqd _ H) in Hlen.
    apply Nat.le_lteq in Hlen. destruct Hlen as [Hlt|Heq].
    * assert (tm_d y0 < n < tm_d y) as H1. { tauto. }
      pose proof (be_ex Hlx _ H) as [_ [_ [py0 _]]].
      apply (ptfulfill py0 H0) in H1.
      destruct H1 as [z [Hz1 [Hz2 Hz3]]].
      exists z. split; try assumption. split; try assumption.
      apply clos_tn1_trans. constructor 2 with y0; try assumption.
      apply clos_trans_tn1. assumption.
    * exists y0. split; try assumption. apply eq_sym in Heq.
      split; try assumption. constructor 1. assumption.
- intros y yltx.
  apply clos_trans_tn1 in yltx. inversion yltx.
  + clear H0 y0. apply Heqc. assumption.
  + clear H1 z. apply clos_tn1_trans in H0. fold desc in H0.
    pose proof (be_ex Hlx _ H) as [_ [_ [py0 _]]].
    apply (ptadtran py0 H0).
}

split; try reflexivity.
intros y yltx. apply clos_trans_tn1 in yltx. inversion yltx.
- pose proof (be_ex Hlx _ H) as [_ [_ [py _]]]. assumption.
- apply clos_tn1_trans in yltx, H0. fold (desc y y0) in H0.
  pose proof (be_ex Hlx _ H) as [_ [_ [_ [gpy0 _]]]].
  apply gpy0. assumption.
Defined.
