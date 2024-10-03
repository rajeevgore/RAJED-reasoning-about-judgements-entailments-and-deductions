Require Import utils.
Require Import nnf.
Require Import seqt.

Require Import Compare_dec.
Require Import String.
Open Scope string_scope.
Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Lia.

Require Import Classical.

Set Implicit Arguments.


Record kripke :=
{ world : Type;
  kseq  : nat -> world;
  val   : world -> string -> Prop }.


Fixpoint force (M : kripke) (i : nat) (xi : nnf) : Prop :=
  match xi with
  | var p       => val M (kseq M i) p
  | neg p       => ~ val M (kseq M i) p
  | and phi psi => (force M i phi) /\ (force M i psi)
  | or phi psi  => (force M i phi) \/ (force M i psi)
  | bef phi psi => forall k, k >= i -> force M k psi ->
      exists j, i <= j < k /\ force M j phi
  | unt phi psi => exists k, k >= i /\ force M k psi /\
      forall j, i <= j < k -> force M j phi
  | next phi    => force M (S i) phi
  end.

Definition sat (M : kripke) (i : nat) (G : list nnf) : Prop :=
  forall phi, In phi G -> force M i phi.

Definition satable (G : list nnf) : Prop := exists M i, sat M i G.

Definition unsatable (G : list nnf) : Prop := forall M i, ~ sat M i G.


Section SemanticsMore.

  Variable M : kripke.

  (* Requires XM *)
  Lemma nnf_true_is_true : forall i, force M i nnf_true.
  Proof.
  intro i. simpl. apply classic.
  Qed.
  
  Lemma nnf_false_is_false : forall i, ~ force M i nnf_false.
  Proof.
  intros i H. destruct H. contradiction.
  Qed.
  
  (* Requires XM *)
  Lemma force_not_neg :
    forall [i phi], ~ force M i phi -> force M i (neg_nnf phi).
  Proof.
  intros i phi; revert i.
  induction phi; intros i H; simpl in H |- *.
  - assumption.
  - apply NNPP. assumption.
  - apply not_and_or in H. destruct H as [H|H].
    + left. apply IHphi1. assumption.
    + right. apply IHphi2. assumption.
  - apply not_or_and in H. destruct H as [H1 H2]. split.
    + apply IHphi1. assumption.
    + apply IHphi2. assumption.
  - apply not_all_ex_not in H. destruct H as [k H].
    apply imply_to_and in H. destruct H as [ilek H].
    apply imply_to_and in H. destruct H as [forphi2 H].
    exists k. repeat (split; try assumption). intro j.
    apply not_ex_all_not with (n:=j) in H.
    apply not_and_or in H. intro H0.
    destruct H as [H|H]; try contradiction.
    apply IHphi1. assumption.
  - intros k ilek forphi2.
    apply not_ex_all_not with (n:=k) in H.
    repeat (apply not_and_or in H; destruct H; try contradiction).
    apply not_all_ex_not in H. destruct H as [j H].
    exists j. apply imply_to_and in H. split; try tauto.
    apply IHphi1. tauto.
  - apply IHphi. assumption.
  Qed.

  (* Does not require XM *)
  Lemma force_neg_not :
    forall [i phi], force M i (neg_nnf phi) -> ~ force M i phi.
  Proof.
  intros i phi; revert i.
  induction phi; intros i H; simpl in H |- *.
  - assumption.
  - intro Hctr. contradiction.
  - intro Hctr. destruct H as [H|H].
    + apply (IHphi1 _ H). tauto.
    + apply (IHphi2 _ H). tauto.
  - intro Hctr. destruct Hctr as [Hctr|Hctr].
    + contradict Hctr. apply IHphi1. tauto.
    + contradict Hctr. apply IHphi2. tauto.
  - intro Hctr. destruct H as [k [ilek [forphi2 allj]]].
    specialize (Hctr k ilek forphi2).
    destruct Hctr as [j [Hj forphi1]].
    contradict forphi1. apply IHphi1.
    apply allj. assumption.
  - intro Hctr. destruct Hctr as [k [ilek [forphi2 allj]]].
    specialize (H k ilek forphi2). destruct H as [j [Hj fornegphi1]].
    specialize (allj j Hj). contradict allj.
    apply IHphi1. assumption.
  - apply IHphi. assumption.
  Qed.


  (* Requires XM *)
  Theorem force_neg_not_iff :
    forall {i phi}, force M i (neg_nnf phi) <-> ~ force M i phi.
  Proof.
  intros w phi. revert w.
  induction phi as [p|p|phi1 IHphi1 phi2 IHphi2|phi1 IHphi1 phi2 IHphi2|
  phi1 IHphi1 phi2 IHphi2|phi1 IHphi1 phi2 IHphi2|phi0 IHphi0];
  intro w; simpl; try tauto.
  - setoid_rewrite IHphi1. setoid_rewrite IHphi2. tauto.
  - setoid_rewrite IHphi1. setoid_rewrite IHphi2. tauto.
  - setoid_rewrite IHphi1. split.
    + intros H Hctr. destruct H as [k [ilek [forphi2 allj]]].
      specialize (Hctr k ilek forphi2).
      destruct Hctr as [j [Hj forphi1]].
      contradict forphi1. apply allj. assumption.
    + intro H. apply not_all_ex_not in H. destruct H as [k H].
      apply imply_to_and in H. destruct H as [ilek H].
      apply imply_to_and in H. destruct H as [forphi2 H].
      exists k. repeat (split; try assumption). intro j.
      apply not_ex_all_not with (n:=j) in H.
      apply not_and_or in H. intro H0.
      destruct H as [H|H]; try contradiction. assumption.
  - setoid_rewrite IHphi1. split.
    + intros H Hctr. destruct Hctr as [k [ilek [forphi2 allj]]].
      specialize (H k ilek forphi2). destruct H as [j [Hj fornegphi1]].
      specialize (allj j Hj). contradict allj. assumption.
    + intros H k ilek forphi2.
      apply not_ex_all_not with (n:=k) in H.
      repeat (apply not_and_or in H; destruct H; try contradiction).
      apply not_all_ex_not in H. destruct H as [j H].
      exists j. apply imply_to_and in H. split; tauto.
  - apply IHphi0.
  Qed.

  Lemma sat_subset :
    forall [i G G'], incl G' G -> sat M i G -> sat M i G'.
  Proof.
  intros i G G' H H0. intros phi Hphi. apply H0. apply H. assumption.
  Qed.

  Lemma sat_eqset :
    forall [i G G'], eqset G G' -> (sat M i G <-> sat M i G').
  Proof.
  intros i G G' H. split; apply sat_subset; apply H.
  Qed.

  Lemma odd_one_out : forall [i phi G],
    unsatable (phi :: G) -> sat M i G -> ~ force M i phi.
  Proof.
  intros i phi G H H0 H1. apply (H M i). intros psi Hpsi.
  destruct Hpsi as [Hpsi|Hpsi].
  - rewrite <- Hpsi. assumption.
  - apply H0. assumption.
  Qed.



  (* Requires XM *)
  Theorem force_alpha_iff :
    forall [i phi], nnf_isalpha phi ->
      (force M i phi <->
      force M i (nnf_alpha1 phi) /\ force M i (nnf_alpha2 phi)).
  Proof.
  intros i phi aphi. split.
  - intro H. destruct phi; try contradiction;
    simpl in H |- *; try assumption. split.
    + apply force_neg_not_iff. intro Hctr.
      destruct (H i (le_n i) Hctr) as [j [Hj Hj0]]. lia.
    + destruct (classic (force M i phi1)) as [forphi1|nforphi1];
      try (now left). right. intros k Silek forphi2.
      pose proof (H k) as [j [[ilej jltk] Hj0]]; try (lia||assumption).
      exists j. split; try assumption.
      destruct (le_lt_eq_dec _ _ ilej) as [iltj|ieqj]; try lia.
      rewrite <- ieqj in Hj0. contradiction.
  - intro H. destruct phi; try contradiction;
    simpl in H |- *; try assumption.
    + destruct H as [H H0]. intros k ilek forphi2.
      destruct (le_lt_eq_dec _ _ ilek) as [iltk|ieqk].
      * destruct H0 as [H0|H0].
      -- exists i. split; try lia. assumption.
      -- specialize (H0 k iltk forphi2).
          destruct H0 as [j [[Silej jltk] forphi1]].
          exists j. split; try lia. assumption.
      * rewrite <- ieqk in forphi2. apply force_neg_not_iff in H.
        contradiction. 
  Qed.

  (* Requires XM *)
  Lemma sat_alpha_child :
    forall [i phi s], nnf_isalpha phi ->
    In phi (s_G s) -> sat M i (s_G s) ->
      sat M i (s_G (alpha_child phi s)).
  Proof.
  intros i phi s aphi Hin Hsat. simpl.
  pose proof (Hsat _ Hin) as H.
  rewrite (force_alpha_iff aphi) in H.
  intros psi Hpsi. destruct Hpsi as [Hpsi|[Hpsi|Hpsi]].
  - rewrite <- Hpsi. tauto.
  - rewrite <- Hpsi. tauto.
  - apply Hsat. apply in_remove with nnf_eqdec phi.
    assumption.
  Qed.



  Theorem force_beta_iff :
    forall [i phi], nnf_isbeta phi ->
      (force M i phi <->
      force M i (nnf_beta1 phi) \/ force M i (nnf_beta2 phi)).
  Proof.
  intros i phi bphi. split.
  - intro H. simpl in H. destruct phi; try contradiction.
    + simpl in H |- *. assumption.
    + simpl in H |- *. destruct H as [k [ilek [fork allj]]].
      destruct (le_lt_eq_dec _ _ ilek) as [iltk|ieqk].
      * right. split.
        -- apply allj. split; try assumption. left.
        -- exists k. split; try lia. split; try assumption.
            intros j Hj. apply allj. lia.
      * left. rewrite ieqk. assumption.
  - intro H. destruct phi; try contradiction; simpl in H |- *.
    + assumption.
    + destruct H as [H|H].
      * exists i. split; try split.
        -- left.
        -- assumption.
        -- intro j. lia.
      * destruct H as [H [k [Silek [forphi2 allj]]]].
        exists k. split; try split.
       -- lia.
       -- assumption.
       -- intros j [ilej jltk].
          destruct (le_lt_eq_dec _ _ ilej) as [iltj|ieqj].
         ++ apply allj. lia.
         ++ rewrite <- ieqj. assumption.
  Qed.

  Lemma unsat_beta1_sat_beta2 :
    forall [i phi s], nnf_isbeta phi ->
    In phi (s_G s) -> sat M i (s_G s) ->
    unsatable (s_G (beta1_child phi s)) ->
      sat M i (s_G (beta2_child phi s)).
  Proof.
  intros i phi s bphi Hin Hsat Hunsat. simpl in Hunsat.
  assert (~ force M i (nnf_beta1 phi)) as nfor1.
  { apply (odd_one_out Hunsat).
  apply sat_subset with (G := s_G s); try assumption.
  intros psi Hpsi. apply (in_remove nnf_eqdec _ _ _ Hpsi). }
  pose proof (Hsat _ Hin) as forphi.
  rewrite (force_beta_iff bphi) in forphi.
  destruct forphi as [for1|for2]; try contradiction.
  simpl. intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
  - rewrite <- Hpsi. assumption.
  - apply Hsat. apply (in_remove _ _ _ _ Hpsi).
  Qed.

  Lemma unsat_beta2_sat_beta1 :
    forall [i phi s], nnf_isbeta phi ->
    In phi (s_G s) -> sat M i (s_G s) ->
    unsatable (s_G (beta2_child phi s)) ->
      sat M i (s_G (beta1_child phi s)).
  Proof.
  intros i phi s bphi Hin Hsat Hunsat. simpl in Hunsat.
  assert (~ force M i (nnf_beta2 phi)) as nfor2.
  { apply (odd_one_out Hunsat).
  apply sat_subset with (G := s_G s); try assumption.
  intros psi Hpsi. apply (in_remove nnf_eqdec _ _ _ Hpsi). }
  pose proof (Hsat _ Hin) as forphi.
  rewrite (force_beta_iff bphi) in forphi.
  destruct forphi as [for1|for2]; try contradiction.
  simpl. intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
  - rewrite <- Hpsi. assumption.
  - apply Hsat. apply (in_remove _ _ _ _ Hpsi).
  Qed.

  Lemma unsat_beta1_not_force_psi :
    forall [i phi psi s], sat M i (s_G s) ->
    unsatable (s_G (beta1_child (unt phi psi) s)) ->
      ~ force M i psi.
  Proof.
  intros i phi psi s H H0. apply (odd_one_out H0).
  apply sat_subset with (G := (s_G s)); try assumption.
  intro xi. apply (in_remove nnf_eqdec).
  Qed.


  Lemma sat_beta_children : forall [i phi s],
    nnf_isbeta phi -> In phi (s_G s) -> sat M i (s_G s) ->
      sat M i (s_G (beta1_child phi s)) \/
      sat M i (s_G (beta2_child phi s)).
  Proof.
  intros i xi s bxi Hin H. pose proof (H _ Hin) as H0.
  rewrite (force_beta_iff bxi) in H0.
  destruct H0 as [H0|H0].
  - left. simpl. intros psi Hpsi.
    destruct Hpsi as [Hpsi|Hpsi].
    + rewrite <- Hpsi. assumption.
    + apply (H psi). apply (in_remove _ _ _ _ Hpsi).
  - right. simpl. intros psi Hpsi.
    destruct Hpsi as [Hpsi|Hpsi].
    + rewrite <- Hpsi. assumption.
    + apply (H psi). apply (in_remove _ _ _ _ Hpsi).
  Qed.

  Lemma sat_unnext : forall [i G], sat M i G -> sat M (S i) (unnext G).
  Proof.
  intros i G H phi Hphi. apply in_unnext_in_next in Hphi.
  apply H in Hphi. simpl in Hphi. assumption.
  Qed.

  Lemma sat_jump_child : forall [i s],
    sat M i (s_G s) -> sat M (S i) (s_G (jump_child s)).
  Proof.
  intros i s H. simpl. apply sat_unnext. assumption.
  Qed.

End SemanticsMore.

Lemma satable_subset :
forall [G G'], incl G' G -> satable G -> satable G'.
Proof.
intros G G' H [M [i Hi]]. exists M, i.
eapply sat_subset. apply H. assumption.
Qed.

(* Requires XM *)
Corollary unsat_alpha_child : forall [phi s],
  nnf_isalpha phi -> In phi (s_G s) ->
  unsatable (s_G (alpha_child phi s)) ->
    unsatable (s_G s).
Proof.
intros phi s aphi Hin Hunsat M i Hsat.
apply Hunsat with M i.
apply sat_alpha_child; assumption.
Qed.

Corollary unsat_beta_children : forall [phi s],
  nnf_isbeta phi -> In phi (s_G s) ->
  unsatable (s_G (beta1_child phi s)) ->
  unsatable (s_G (beta2_child phi s)) ->
    unsatable (s_G s).
Proof.
intros phi s bphi Hin H H0 M i H1.
pose proof (sat_beta_children bphi Hin H1) as H2.
destruct H2 as [H2|H2].
- apply (H _ _ H2).
- apply (H0 _ _ H2).
Qed.

Corollary unsat_jump_child : forall [s],
  unsatable (s_G (jump_child s)) -> unsatable (s_G s).
Proof.
intros s Hunsat M i Hsat. apply Hunsat with M (S i).
apply sat_jump_child. assumption.
Qed.

Lemma unsat_contra : forall [n s],
  In (var n) (s_G s) /\ In (neg n) (s_G s) ->
  unsatable (s_G s).
Proof.
intros n s [Hvar Hneg] M i Hsat. apply Hsat in Hvar, Hneg.
simpl in Hvar, Hneg. contradiction.
Qed.  
