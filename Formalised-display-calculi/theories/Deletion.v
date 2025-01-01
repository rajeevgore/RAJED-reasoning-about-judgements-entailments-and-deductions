Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Require Import ListSet.
Require Import Arith.
Require Import Bool.
Require Import Datatypes.

Require Import Recdef.
Require Import Lia.
Require Import Wellfounded.

Require Import Tactics.
Require Import EqDec.
Require Import ListSetNotations.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.
Require Import Cuts.
Require Import PL.
Import CPL.
Import CPLNotations.

Import ListSetNotations.

Open Scope type_scope.



Section Deletion.

  Definition sstructr := bool * structr.

  Theorem sstructr_eq_dec : eq_dec sstructr.
  Proof.
    unfold eq_dec. decide equality;
      try apply bool_dec; try apply eqdec.
  Defined.

  #[export] Instance EqDec_sstructr : EqDec (sstructr) := {| eqdec := sstructr_eq_dec |}.

  Definition remove_sstr := remove sstructr_eq_dec.

  
  Definition tog (X : structr) : structr :=
    match X with
    | ∗X0 => X0
    | X0  => ∗X0
    end.

  Fixpoint bstrComma (Z : structr) : bool :=
    match Z with
    | X,, Y => true
    | ∗X    => bstrComma X
    | _     => false
    end.

  Definition bseqComma (s : sequent) : bool :=
    match s with X ⊢ Y => orb (bstrComma X) (bstrComma Y) end.

  Definition sws (sX : sstructr) : sstructr :=
    match sX with (sgn, X) => (negb sgn, X) end.

  Definition swsc (b : bool) : sstructr -> sstructr := if b then id else sws.

  (* Checks if a structure is a substructure respecting a certain sign *)
  Fixpoint bstrSub (X : structr) (sY : sstructr) : bool :=
    match fst sY, eqdec X (snd sY) with
    | true, left _ => true
    | _, _ =>
      match X with
      | X1,, X2 => orb (bstrSub X1 sY) (bstrSub X2 sY)
      | ∗X0     => bstrSub X0 (sws sY)
      | _       => false
      end
    end.

  Lemma bstrSub_eq (X : structr) (sY : sstructr) :
    bstrSub X sY =
    match fst sY, eqdec X (snd sY) with
    | true, left _ => true
    | _, _ =>
      match X with
      | X1,, X2 => orb (bstrSub X1 sY) (bstrSub X2 sY)
      | ∗X0     => bstrSub X0 (sws sY)
      | _       => false
      end
    end.
  Proof. destruct X; reflexivity. Qed.

  (* Checks if a structure is non-isolated inside another, respecting a certain sign *)
  Fixpoint bstrNiso (X : structr) (sY : sstructr) : bool :=
    match X with
    | X1,, X2 => orb (bstrSub X1 sY) (bstrSub X2 sY)
    | ∗X0     => bstrNiso X0 (sws sY)
    | _       => false
    end.

  Definition bseqNiso (s : sequent) (sZ : sstructr) : bool :=
    match s with X ⊢ Y => orb (bstrNiso X (sws sZ)) (bstrNiso Y sZ) end.

  (* Structure deletion in a structure *)
  Fixpoint strDel (X : structr) (sY : sstructr) : structr :=
    match X with
    | X1,, X2 =>
        if bstrSub X1 sY then
          if bstrNiso X1 sY then strDel X1 sY,, X2 else X2
        else if bstrSub X2 sY then
          if bstrNiso X2 sY then X1,, strDel X2 sY else X1
        else X1,, X2
    | ∗X0 => tog (strDel X0 (sws sY))
    | X0  => X0
    end.

  (* First primitive structure of a structure *)
  Fixpoint hdPR (sgn : bool) (X : structr) : sstructr :=
    match X with
    | X1,, X2 => hdPR sgn X1
    | ∗X0     => hdPR (negb sgn) X0
    | X0      => (sgn, X0)
    end.

  Definition hdseqPR (s : sequent) : sstructr :=
    match s with X ⊢ Y => hdPR true Y end.

  Definition tostar (sX : sstructr) : structr :=
    match sX with (sgn, X) => if sgn then X else ∗X end.

  (* Structure deletion in a sequent *)
  Definition seqDel (s : sequent) (sZ : sstructr) : sequent :=
    match s with X ⊢ Y =>
      if bstrNiso X (sws sZ)
        then strDel X (sws sZ) ⊢ Y
      else if bstrNiso Y sZ
        then X ⊢ strDel Y sZ
      else X ⊢ Y
    end.

  Definition isPrim (X : structr) : Prop :=
    match X with
    | X1,, X2 => False
    | ∗X0     => False
    | _       => True
    end.

  Lemma isPrim_dec : forall X, {isPrim X} + {~ isPrim X}.
  Proof. intro X. destruct X; ((now left)||(now right)). Qed.

  Lemma isPrim_sws (sY : sstructr) : isPrim (snd sY) -> isPrim (snd (sws sY)).
  Proof. intro H. destruct sY. assumption. Qed.

  Lemma isPrim_swsc (sY : sstructr) (b : bool) : isPrim (snd sY) -> isPrim (snd (swsc b sY)).
  Proof. destruct b; try tauto. apply isPrim_sws. Qed.

  Fixpoint strPR (b : bool) (X : structr) : list sstructr :=
    match X with
    | X1,, X2 => strPR b X1 ++ strPR b X2
    | ∗X0     => strPR (negb b) X0
    | X0      => [(b, X0)]
    end.

  Definition PR (s : sequent) : list sstructr :=
    match s with X ⊢ Y => strPR false X ++ strPR true Y end.



  Definition nb_PR (s : sequent) : nat := length (PR s).
  
  Lemma nb_PR_ge1 : forall X b, length (strPR b X) >= 1.
  Proof.
    induction X; intro b; simpl; try lia.
    - apply IHX.
    - rewrite app_length. specialize (IHX1 b). specialize (IHX2 b). lia.
  Qed.

  Lemma strPR_not_nil : forall X b, strPR b X <> [].
  Proof.
    intros X b. pose proof (nb_PR_ge1 X b) as H.
    destruct (strPR b X); try discriminate. simpl in H. lia.
  Qed.

  Lemma nb_seqPR_ge2 : forall u, length (PR u) >= 2.
  Proof.
    intro u. destruct u. simpl. rewrite app_length.
    pose proof (nb_PR_ge1 X false). pose proof (nb_PR_ge1 Y true). lia.
  Qed.  

  Lemma sws_invol (sX : sstructr) : sws (sws sX) = sX.
  Proof. destruct sX. simpl. rewrite negb_involutive. reflexivity. Qed.

  Lemma swsc_invol (sX : sstructr) (b : bool) : swsc b (swsc b sX) = sX.
  Proof. destruct b; try reflexivity. apply sws_invol. Qed.

  Lemma sws_swsc : forall sX b, sws (swsc b sX) = swsc (negb b) sX.
  Proof. intros. destruct b. simpl. reflexivity. simpl. rewrite sws_invol. reflexivity. Qed.

  Lemma swsc_neg_sws : forall sX b, swsc (negb b) (sws sX) = swsc b sX.
  Proof. intros. destruct b; simpl; [now rewrite sws_invol | reflexivity]. Qed.

  Lemma snd_sws_eq : forall sX, snd (sws sX) = snd sX.
  Proof. intros [b X]. destruct b; reflexivity. Qed.
  
  Lemma snd_swsc_eq : forall sX b, snd (swsc b sX) = snd sX.
  Proof. intros sX b. destruct b; try reflexivity. now rewrite snd_sws_eq. Qed.

  Lemma isPrim_sws_iff (sY : sstructr) : isPrim (snd sY) <-> isPrim (snd (sws sY)).
  Proof. split; [idtac | rewrite <- (sws_invol sY) at 2]; apply isPrim_sws. Qed.

  Lemma isPrim_swsc_iff (sY : sstructr) (b : bool) :
    isPrim (snd sY) <-> isPrim (snd (swsc b sY)).
  Proof. split; [idtac | rewrite <- (swsc_invol sY b) at 2]; apply isPrim_swsc. Qed.

  Lemma in_PR_sw : forall {X sY b}, In sY (strPR b X) -> In (sws sY) (strPR (negb b) X).
  Proof.
    induction X; intros sY b Hin;
      try (simpl in Hin |- *; left; destruct Hin as [H|]; try contradiction;
           rewrite <- H; reflexivity).
    - simpl. apply IHX. assumption.
    - simpl. simpl in Hin. rewrite in_app_iff in Hin |- *. destruct Hin as [Hin|Hin].
      + left. apply IHX1. assumption.
      + right. apply IHX2. assumption.
  Qed.

  Lemma in_PR_sw_iff : forall X b sY, In sY (strPR b X) <-> In (sws sY) (strPR (negb b) X).
  Proof.
    intros. split; try apply in_PR_sw.
    rewrite <- (sws_invol sY) at 2. rewrite <- (negb_involutive b) at 2.
    apply in_PR_sw.
  Qed.

  Lemma PR_map_swsc : forall X b, strPR b X = map (swsc b) (strPR true X).
  Proof.
    induction X; intros b; try (destruct b; reflexivity).
    - simpl. destruct b. rewrite map_id. reflexivity.
      rewrite (IHX false). simpl. rewrite map_map.
      rewrite (map_ext _ _ sws_invol). rewrite map_id. reflexivity.
    - simpl. rewrite map_app. rewrite IHX1, IHX2. reflexivity.
  Qed.
  
  Lemma PR_eq_map_PR_negb : forall X b, strPR b X = map sws (strPR (negb b) X).
  Proof.
    intros X. induction X; intro b; simpl;
      try (rewrite negb_involutive; reflexivity).
    - apply IHX.
    - rewrite IHX1, IHX2. rewrite map_app. reflexivity.
  Qed.

  Lemma PR_PR_negb_eq_imp : forall X b l, strPR b X = l -> strPR (negb b) X = map sws l.
  Proof.
    intros X b l Heq. rewrite PR_eq_map_PR_negb.
    rewrite negb_involutive, Heq. reflexivity.
  Qed.

  Lemma PR_isPrim : forall X {sY} b, In sY (strPR b X) -> isPrim (snd sY).
  Proof.
    induction X; intros sY b Hin; simpl in Hin;
      try (destruct Hin; try contradiction; destruct sY; injection H;
      intros Heqs Heqb; rewrite <- Heqs; simpl; tauto).
    - apply (IHX _ (negb b)). assumption.
    - rewrite in_app_iff in Hin.
      destruct Hin; ((now apply (IHX1 _ b)) || (now apply (IHX2 _ b))).
  Qed.

  Lemma seqPR_isPrim : forall s {sZ}, In sZ (PR s) -> isPrim (snd sZ).
  Proof.
    intros [X Y] sZ Hin. simpl in Hin. rewrite in_app_iff in Hin.
    destruct Hin; eapply PR_isPrim; eassumption.
  Qed.

  Lemma hdPR_in_PR : forall {X b}, In (hdPR b X) (strPR b X).
  Proof.
    induction X; intro b; simpl; try now left.
    - apply IHX. 
    - rewrite in_app_iff. left. apply IHX1.
  Qed.

  Lemma hdseqPR_in_seqPR : forall s, hdseqPR s ∈ PR s.
  Proof.
    intros [X Y]. simpl.
    rewrite in_app_iff. right.
    apply hdPR_in_PR.
  Qed.

  Lemma hdPR_isPrim : forall X b, isPrim (snd (hdPR b X)).
  Proof.
    intros X b. apply (PR_isPrim X b). apply hdPR_in_PR.
  Qed.

  Lemma hdseqPR_isPrim : forall s, isPrim (snd (hdseqPR s)).
  Proof.
    intro s. apply (seqPR_isPrim s). apply hdseqPR_in_seqPR.
  Qed.
    

  Lemma in_PR_t_swsc : forall X sY b, In sY (strPR true X) <-> In (swsc b sY) (strPR b X).
  Proof.
    intros. destruct b; try tauto. simpl. apply in_PR_sw_iff.
  Qed.

  Lemma in_strPR_sub_t : forall X sY, In sY (strPR true X) -> bstrSub X sY = true.
  Proof.
    induction X; intros sY Hin; destruct sY as [sgn Y] eqn:HeqsY;
    rewrite bstrSub_eq; simpl fst; simpl snd;
     match goal with |- context[eqdec ?X' Y] =>
       destruct (eqdec X' Y) as [Heq|Hneq] end; destruct sgn; try reflexivity.
    (* Comma *)
    all: try (
    simpl in Hin; rewrite in_app_iff in Hin; destruct Hin as [Hin|Hin];
    try (rewrite IHX1; try assumption; rewrite orb_true_l; reflexivity);
    try (rewrite IHX2; try assumption; rewrite orb_true_r; reflexivity)).
    (* Star *)
    all: try (
    simpl in Hin; rewrite IHX; try reflexivity; apply (in_PR_sw Hin)).
    all: destruct Hin as [Hin|Hin]; try contradiction; injection Hin; intros;
    apply eq_sym; try tauto.
  Defined.

  Lemma in_strPR_sub : forall X sY b, In sY (strPR b X) -> bstrSub X (swsc b sY) = true.
  Proof.
    intros X sY b. destruct b.
    - apply in_strPR_sub_t.
    - change (strPR false X) with (strPR true (∗ X)).
      intro Hin. pose proof (PR_isPrim _ _ Hin) as Hpr.
      apply in_strPR_sub_t in Hin.
      rewrite bstrSub_eq in Hin.
      destruct (fst sY); destruct (eqdec (∗ X) (snd sY)) as [Heq|Hneq];
        try assumption.
      rewrite <- Heq in Hpr. contradiction.
  Qed.

  Lemma in_strPR_sub' : forall X sY b, In (swsc b sY) (strPR b X) -> bstrSub X sY = true.
  Proof.
    intros X sY b. rewrite <- (swsc_invol sY b) at 2. apply in_strPR_sub.
  Qed.

  Lemma sub_in_PR_t :
    forall {X sY}, isPrim (snd sY) -> bstrSub X sY = true -> In sY (strPR true X).
  Proof.
    induction X; intros sY HprY Hsub; rewrite bstrSub_eq in Hsub; simpl;
      match goal with _ : context[eqdec ?X' (snd sY)] |- _ =>
        destruct (eqdec X' (snd sY)) as [Heq|Hneq] end;
      try (rewrite <- Heq in HprY; contradiction);
      try (rewrite Tauto.if_same in Hsub);
      try (rewrite (surjective_pairing sY); destruct (fst sY); try (now right);
           try (rewrite Heq; now left); fail).
    - apply in_PR_sw_iff. apply IHX; try (now apply isPrim_sws). assumption.
    - rewrite in_app_iff. apply orb_prop in Hsub. destruct Hsub as [Hsub|Hsub];
        ((left; apply IHX1; assumption) || (right; apply IHX2; assumption)).
  Qed.

  Lemma sub_in_PR :
    forall {X sY b}, isPrim (snd sY) -> bstrSub X (swsc b sY) = true -> sY ∈ strPR b X.
  Proof.
    intros X sY b. destruct b.
    - apply sub_in_PR_t.
    - change (strPR false X) with (strPR true (∗ X)).
      intros Hpr Hsub. apply sub_in_PR_t; try assumption.
      rewrite bstrSub_eq.
      destruct (fst sY); destruct (eqdec (∗ X) (snd sY)) as [Heq|Hneq];
        try assumption.
      rewrite <- Heq in Hpr. contradiction.
  Qed.

  Lemma sub_in_PR' :
    forall {X sY b}, isPrim (snd sY) -> bstrSub X sY = true -> In (swsc b sY) (strPR b X).
  Proof. intros X sY b. rewrite <- in_PR_t_swsc. apply sub_in_PR_t. Qed.

  Lemma sub_in_PR_iff' :
    forall {X sY b}, isPrim (snd sY) -> bstrSub X sY = true <-> In (swsc b sY) (strPR b X).
  Proof.
    intros. split; try apply sub_in_PR'; try assumption.
    apply in_strPR_sub'.
  Qed.

  Lemma nsub_nin_PR : 
    forall {X sY b}, isPrim (snd sY) -> bstrSub X sY = false -> ~ In (swsc b sY) (strPR b X).
  Proof.
    intros X sY b HprY Hsub Hin. apply in_strPR_sub' in Hin.
    rewrite Hsub in Hin. discriminate.
  Qed.

  Lemma PR_tog : forall X b, strPR b (tog X) = strPR (negb b) X.
  Proof.
    intros X b. destruct X; try reflexivity. simpl. rewrite negb_involutive. reflexivity.
  Qed.



  Lemma primsub_niso' :
    forall {X Y b}, isPrim Y -> bstrSub X (b, Y) = true -> bstrComma X = true ->
             bstrNiso X (b, Y) = true.
  Proof.
    induction X; intros Y b HprY Hsub HC; rewrite bstrSub_eq in Hsub;
    unfold fst, snd in Hsub; destruct b.
    all: try (destruct (eqdec (X1,, X2) Y);
      destruct Y; try contradiction; try discriminate;
      apply orb_prop in Hsub; destruct Hsub as [Hsub|Hsub];
      simpl; rewrite Hsub; (now apply orb_true_l || now apply orb_true_r)).
    all: try (destruct (eqdec (∗X) Y);
      destruct Y; try contradiction; try discriminate; simpl; apply IHX; assumption).
    all: simpl in HC; try discriminate.
  Qed.

  Lemma primComma_niso :
    forall X sY, isPrim (snd sY) -> bstrSub X sY = true -> bstrComma X = true ->
             bstrNiso X sY = true.
  Proof.
    intros X sY. destruct sY. apply primsub_niso'.
  Qed.


  Lemma bstrNiso_bstrSub : forall {X sY}, bstrNiso X sY = true -> bstrSub X sY = true.
  Proof.
    induction X; intros sY Hniso; try discriminate.
    - rewrite bstrSub_eq. simpl in Hniso.
      destruct (eqdec (∗ X) (snd sY));
        [destruct (fst sY); try apply IHX; tauto | idtac].
      rewrite Tauto.if_same. apply IHX. assumption.
    - rewrite bstrSub_eq.
      destruct (eqdec (X1,, X2) (snd sY));
        [destruct (fst sY); tauto | idtac].
      rewrite Tauto.if_same. assumption.
  Qed.

  Lemma primComma_iso :
    forall X sY, isPrim (snd sY) -> bstrSub X sY = true -> bstrComma X = false ->
             bstrNiso X sY = false.
  Proof.
    induction X; intros [b Y] HprY Hsub HC; rewrite bstrSub_eq in Hsub;
      unfold fst, snd in Hsub; simpl in HprY; simpl in HC; try discriminate.
    - destruct (eqdec ($X) Y) as [HeqY|HneqY]; destruct b; try discriminate.
      rewrite <- HeqY. simpl. reflexivity.
    - destruct (eqdec (£A) Y) as [HeqY|HneqY]; destruct b; try discriminate.
      rewrite <- HeqY. simpl. reflexivity.
    - destruct (eqdec I Y) as [HeqY|HneqY]; destruct b; try discriminate.
      rewrite <- HeqY. simpl. reflexivity.
    - destruct b; simpl; destruct (eqdec (∗ X) Y) as [HeqY|HneqY];
      try (rewrite <- HeqY in HprY; contradiction);
      apply IHX; assumption.
  Qed.

  Lemma primiso_nComma :
    forall X sY, isPrim (snd sY) -> bstrSub X sY = true -> bstrNiso X sY = false ->
              bstrComma X = false.
  Proof.
    intros X sY HprY Hsub Hniso. destruct (bstrComma X) eqn:HC; try reflexivity.
    apply (primComma_niso X sY) in HC; try assumption. rewrite HC in Hniso. discriminate.
  Qed.

  Lemma primniso_Comma :
    forall {X sY}, isPrim (snd sY) -> bstrNiso X sY = true -> bstrComma X = true.
  Proof.
    induction X; intros sY HprY Hniso; try tauto.
    pose proof (bstrNiso_bstrSub Hniso) as Hsub.
    simpl. apply (IHX (sws sY)); try (now apply isPrim_sws).
    rewrite bstrSub_eq in Hsub. destruct (eqdec (∗ X) (snd sY)) as [Heq|Hneq];
      try (rewrite <- Heq in HprY; contradiction).
    rewrite Tauto.if_same in Hsub. assumption.
  Qed.

  Lemma strPR_niso_t :
    forall {X sY}, In sY (strPR true X) -> bstrComma X = true -> bstrNiso X sY = true.
  Proof.
    intros X sY Hin HC. apply primComma_niso; try assumption.
    apply (PR_isPrim _ _ Hin). apply in_strPR_sub_t. assumption.
  Qed.

  Lemma strPR_niso :
    forall {X sY} b, In (swsc b sY) (strPR b X) -> bstrComma X = true -> bstrNiso X sY = true.
  Proof.
    intros X sY b Hin HC. rewrite <- in_PR_t_swsc in Hin.
    apply strPR_niso_t; assumption.
  Qed.

  Lemma PR_iso :
    forall {X sY}, In sY (strPR true X) -> bstrComma X = false -> bstrNiso X sY = false.
  Proof.
    intros X sY Hin HC. apply primComma_iso; try assumption.
    apply (PR_isPrim _ _ Hin). apply in_strPR_sub_t. assumption.
  Qed.

  Lemma hdPR_niso : forall X, bstrComma X = true -> bstrNiso X (hdPR true X) = true.
  Proof.
    intros X HC. apply strPR_niso_t; try assumption. apply hdPR_in_PR.
  Qed.


  Open Scope nat_scope.


  Lemma seqPR_eq_PR :
    forall (X Y : structr), PR (X ⊢ Y) = strPR true (∗X,, Y).
  Proof. intros X Y. simpl. reflexivity. Qed.



  Lemma noComma_1prim : forall (X : structr) b, bstrComma X = false -> length (strPR b X) = 1.
  Proof.
    induction X; intros b HC; try discriminate; simpl; try reflexivity.
    apply IHX. assumption.
  Qed.

  Lemma noComma_1prim_inv : forall (X : structr) b, length (strPR b X) = 1 -> bstrComma X = false.
  Proof.
    induction X; intros b Hlen; simpl; try reflexivity.
    - simpl in Hlen. apply (IHX (negb b)). assumption.
    - simpl in Hlen. rewrite app_length in Hlen.
      pose proof (nb_PR_ge1 X1 b).
      pose proof (nb_PR_ge1 X2 b).
      lia.
  Qed.

  Lemma swsc_hop : forall (sX sY : sstructr) b, swsc b sX = sY -> sX = swsc b sY.
  Proof. intros sX sY b H. rewrite <- H, swsc_invol. reflexivity. Qed.

  Lemma isoprim_unique_t : forall X sY,
    isPrim (snd sY) -> bstrSub X sY = true -> bstrNiso X sY = false -> strPR true X = [sY].
  Proof.
    intros X sY HprY Hsub Hniso. pose proof (sub_in_PR_t HprY Hsub) as Hin.
    pose proof (primiso_nComma X sY HprY Hsub Hniso) as HnC.
    apply (noComma_1prim _ true) in HnC. destruct (strPR true X); try contradiction.
    destruct l; try discriminate. destruct Hin; try contradiction. rewrite H. reflexivity.
  Qed.

  Lemma isoprim_unique : forall X sY b,
    isPrim (snd sY) -> bstrSub X sY = true -> bstrNiso X sY = false -> strPR b X = [swsc b sY].
  Proof.
    intros. eapply eq_trans; try apply PR_map_swsc.
    rewrite (isoprim_unique_t X sY); try assumption. reflexivity.
  Qed.

  Lemma iso_PR_del : forall X sY b, bstrNiso X sY = false -> strPR b (strDel X sY) = strPR b X.
  Proof.
    induction X; intros sY b Hniso; try reflexivity.
    - simpl. rewrite PR_tog. rewrite IHX; tauto.
    - simpl in Hniso |- *. apply orb_false_elim in Hniso.
      destruct Hniso as [Hniso1 Hniso2].
      rewrite Hniso1, Hniso2. reflexivity.
  Qed.

  Lemma niso_PR_del :
    forall X sY b, isPrim (snd sY) -> bstrNiso X sY = true ->
              strPR b (strDel X sY) = erase (swsc b sY) (strPR b X).
  Proof.
    induction X; intros sY b HprY Hniso; try discriminate.
    - simpl. rewrite PR_tog. rewrite IHX.
      + rewrite swsc_neg_sws. reflexivity.
      + apply isPrim_sws. assumption.
      + assumption.
    - simpl.
      destruct (bstrSub X1 sY) eqn:Hsub1;
        [destruct (bstrNiso X1 sY) eqn:Hniso1 |
         destruct (bstrSub X2 sY) eqn:Hsub2;
           [destruct (bstrNiso X2 sY) eqn:Hniso2 | idtac]]; simpl.
      + rewrite IHX1; try assumption.
        rewrite erase_app_in_l; try reflexivity.
        apply sub_in_PR'; assumption.
      + rewrite (isoprim_unique _ _ _ HprY Hsub1 Hniso1).
        rewrite erase_app_in_l; try now left.
        rewrite erase_cons_eq. reflexivity.
      + rewrite IHX2; try assumption.
        rewrite erase_app_not_in_l; try reflexivity.
        apply nsub_nin_PR; assumption.
      + rewrite (isoprim_unique _ _ _ HprY Hsub2 Hniso2).
        rewrite erase_app_not_in_l.
        rewrite erase_cons_eq. rewrite app_nil_r. reflexivity.
        apply nsub_nin_PR; assumption.
      + rewrite erase_not_In; try reflexivity.
        intro Hin. rewrite in_app_iff in Hin.
        destruct Hin as [Hin|Hin]; contradict Hin;
          apply nsub_nin_PR; assumption.
  Qed.


  Lemma strDel_not_same_count : forall X sY sZ b, isPrim (snd sY) -> sY <> swsc b sZ ->
    count (strPR b X) sZ = count (strPR b (strDel X sY)) sZ.
  Proof.
    intros X sY sZ b HprY HneqsY.
    destruct (bstrNiso X sY) eqn:Hniso.
    - rewrite niso_PR_del; try assumption.
      rewrite count_erase_not_same;
        try (contradict HneqsY; now apply swsc_hop).
      reflexivity.
    - rewrite iso_PR_del; tauto.
  Qed.


  Lemma nPrim_count : forall X sY b, ~ isPrim (snd sY) -> count (strPR b X) sY = 0.
  Proof.
    intros X sY b Hnpr. rewrite <- count_not_In.
    intro Hin. apply Hnpr. apply (PR_isPrim _ _ Hin).
  Qed.


  Lemma iso_count_del : forall X sY b,
    isPrim (snd sY) -> bstrNiso X sY = false ->
      count (strPR b X) (swsc b sY) = count (strPR b (strDel X sY)) (swsc b sY).
  Proof.
    intros X sY b HprY Hniso. rewrite iso_PR_del; tauto.
  Qed.

  Lemma iso_count_del' : forall X sY b,
    isPrim (snd sY) -> bstrNiso X (swsc b sY) = false ->
      count (strPR b X) sY = count (strPR b (strDel X (swsc b sY))) sY.
  Proof.
    intros X sY b HprY Hniso. rewrite <- (swsc_invol sY b) at 1 3.
    apply (iso_count_del X (swsc b sY) b); try assumption. apply isPrim_swsc. assumption.
  Qed.


  Lemma niso_count_del : forall X sY b,
    isPrim (snd sY) -> bstrNiso X sY = true ->
      count (strPR b X) (swsc b sY) = 1 + count (strPR b (strDel X sY)) (swsc b sY).
  Proof.
    induction X; intros sY b HprY Hniso; try (simpl in Hniso; discriminate).
    - simpl in Hniso |- *. apply isPrim_sws in HprY.
      rewrite <- swsc_neg_sws. rewrite (IHX (sws sY) (negb b)); try assumption.
      rewrite PR_tog. reflexivity.
    - destruct (bstrSub X1 sY) eqn:Hsub1;
        [idtac | destruct (bstrSub X2 sY) eqn:Hsub2].
      + simpl. rewrite Hsub1. destruct (bstrNiso X1 sY) eqn:Hniso1.
        * simpl. repeat rewrite count_app.
          rewrite IHX1; try assumption. reflexivity.
        * rewrite (isoprim_unique X1 sY b); try assumption. simpl.
          destruct (sstructr_eq_dec (swsc b sY) (swsc b sY)); try contradiction. reflexivity.
      + simpl. rewrite Hsub1, Hsub2. destruct (bstrNiso X2 sY) eqn:Hniso2.
        * simpl. repeat rewrite count_app.
          rewrite IHX2; try assumption. lia.
        * rewrite (isoprim_unique X2 sY b); try assumption.
          rewrite count_app. simpl.
          destruct (sstructr_eq_dec (swsc b sY) (swsc b sY)); try contradiction. lia.
      + apply orb_prop in Hniso. destruct Hniso as [Hsub|Hsub];
          ((now rewrite Hsub in Hsub1) || (now rewrite Hsub in Hsub2)).
  Qed.

  Lemma niso_count_del' : forall X sY b,
    isPrim (snd sY) -> bstrNiso X (swsc b sY) = true ->
      count (strPR b X) sY = 1 + count (strPR b (strDel X (swsc b sY))) sY.
  Proof.
    intros X sY b HprY Hniso. rewrite <- (swsc_invol sY b) at 1 3.
    apply (niso_count_del X (swsc b sY) b); try assumption. apply isPrim_swsc. assumption.
  Qed.

  Lemma niso_count_del_t : forall X sY,
    isPrim (snd sY) -> bstrNiso X sY = true ->
      count (strPR true X) sY = 1 + count (strPR true (strDel X sY)) sY.
  Proof. intros X sY. apply (niso_count_del _ _ true). Qed.

  Lemma niso_count_del_f : forall X sY,
    isPrim (snd sY) -> bstrNiso X sY = true ->
      count (strPR false X) (sws sY) = 1 + count (strPR false (strDel X sY)) (sws sY).
  Proof. intros X sY. apply (niso_count_del _ _ false). Qed.

  Lemma mset_incl_strDel :
    forall {X b sY}, isPrim (snd sY) -> mset_incl (strPR b (strDel X sY)) (strPR b X).
  Proof.
    intros X b sY HprY sZ. destruct (isPrim_dec (snd sZ)) as [Hpr|Hnpr];
     try (now repeat rewrite (nPrim_count _ _ _ Hnpr)).
    destruct (sstructr_eq_dec sY (swsc b sZ)) as [Heq|Hneq].
    - rewrite Heq. destruct (bstrNiso X (swsc b sZ)) eqn:Hniso.
      + rewrite (niso_count_del' X); try assumption. apply le_S, le_n.
      + rewrite (iso_count_del' X); try assumption. apply le_n.
    - rewrite (strDel_not_same_count X sY sZ); try assumption. apply le_n.
  Qed.

  Lemma hdPR_sws :
    forall (X : structr) b, sws (hdPR b X) = hdPR (negb b) X.
  Proof.
    induction X; intro b; try reflexivity.
    - simpl. apply IHX.
    - simpl. apply IHX1.
  Qed.

  Lemma hdPR_swsc :
    forall (X : structr) b q, swsc b (hdPR q X) = hdPR (bool_eq b q) X.
  Proof. intros X b q. destruct b. reflexivity. simpl. apply hdPR_sws. Qed.

  Lemma bool_eq_same : forall b, bool_eq b b = true.
  Proof. intro b. destruct b; reflexivity. Qed.

  Lemma bool_eq_true_r : forall b, bool_eq b true = b.
  Proof. intro b. destruct b; reflexivity. Qed.

  Lemma mset_eq_PR_strDel :
    forall X sY b, isPrim (snd sY) -> bstrNiso X sY = true ->
            mset_eq (strPR b X) (swsc b sY :: strPR b (strDel X sY)).
  Proof.
    intros X sY b HprY Hniso sZ.
    destruct (sstructr_eq_dec (swsc b sY) sZ) as [Heq|Hneq].
    - rewrite count_cons_eq; try assumption. rewrite <- Heq.
      rewrite niso_count_del; try tauto.
    - rewrite count_cons_neq; try assumption.
      apply strDel_not_same_count; try assumption.
      contradict Hneq. rewrite <- (swsc_invol sZ b).
      apply f_equal. assumption.
  Qed.

  Lemma mset_eq_PR_strDel_t :
    forall X sY, isPrim (snd sY) -> bstrNiso X sY = true ->
            mset_eq (strPR true X) (sY :: strPR true (strDel X sY)).
  Proof.
    intros X sY HprY HnisoX.
    apply (mset_eq_PR_strDel _ _ true); assumption.
  Qed.

  Lemma mset_eq_PR_hdPR_t : forall X, bstrComma X = true ->
    mset_eq (strPR true X) ((hdPR true X) :: strPR true (strDel X (hdPR true X))).
  Proof.
    intros X HC sY. destruct (sstructr_eq_dec (hdPR true X) sY) as [Heq|Hneq].
    - rewrite count_cons_eq; try assumption.
      rewrite niso_count_del'; rewrite <- Heq.
      + reflexivity.
      + apply hdPR_isPrim.
      + simpl. apply hdPR_niso. assumption.
    - rewrite count_cons_neq; try assumption.
      apply strDel_not_same_count; try assumption.
      apply hdPR_isPrim.
  Qed.

  Lemma mset_eq_PR_hdPR : forall X b, bstrComma X = true ->
    mset_eq (strPR b X) ((hdPR b X) :: strPR b (strDel X (hdPR true X))).
  Proof.
    intros X b HC sY.
    destruct (sstructr_eq_dec (hdPR b X) sY) as [Heq|Hneq].
    - rewrite count_cons_eq; try assumption.
      rewrite niso_count_del'; rewrite <- Heq.
      + rewrite hdPR_swsc, bool_eq_same. reflexivity.
      + apply hdPR_isPrim.
      + rewrite hdPR_swsc, bool_eq_same. apply hdPR_niso. assumption.
    - rewrite count_cons_neq; try assumption.
      apply strDel_not_same_count. apply hdPR_isPrim.
      contradict Hneq. apply (f_equal (swsc b)) in Hneq.
      rewrite hdPR_swsc, bool_eq_true_r, swsc_invol in Hneq.
      assumption.
  Qed.

  Lemma PR_tostar_eq :
    forall (sX : sstructr) b, isPrim (snd sX) -> strPR b (tostar sX) = [swsc b sX].
  Proof.
    intros sX b Hpr. destruct sX as [sgn X].
    simpl in Hpr. destruct X; try contradiction; destruct sgn; destruct b; simpl; reflexivity.
  Qed.

  Lemma seqDel_not_same_count : forall s sZ sW, isPrim (snd sZ) -> sZ <> sW ->
    count (PR s) sW = count (PR (seqDel s sZ)) sW.
  Proof.
    intros [X Y] sZ sW HprZ HneqsZ. simpl.
    destruct (bstrNiso X (sws sZ)) eqn:HnisoX;
      [|destruct (bstrNiso Y sZ) eqn:HnisoY];
      [| |reflexivity].
    - simpl. repeat rewrite count_app.
      rewrite <- (strDel_not_same_count X (sws sZ) sW); try reflexivity.
      + apply isPrim_sws. assumption.
      + contradict HneqsZ.
        rewrite <- (sws_invol sZ). rewrite <- (sws_invol sW).
        apply f_equal. assumption.
    - simpl. rewrite ! count_app.
      rewrite <- (strDel_not_same_count Y sZ sW); try assumption.
      reflexivity.
  Qed.
  
  Lemma seqDel_not_same_In_iff : forall s sZ sW, isPrim (snd sZ) -> sZ <> sW ->
    In sW (PR s) <-> In sW (PR (seqDel s sZ)).
  Proof.
    intros s sZ sW HprZ Hneq.
    repeat rewrite count_In. rewrite (seqDel_not_same_count _ sZ); tauto.
  Qed.

  Lemma mset_incl_seqDel :
    forall {s sZ}, isPrim (snd sZ) -> mset_incl (PR (seqDel s sZ)) (PR s).
  Proof.
    intros [X Y] sZ HprZ. simpl.
    destruct (bstrNiso X (sws sZ)) eqn:HnisoX;
      [|destruct (bstrNiso Y sZ) eqn:HnisoY];
      [| |simpl; try apply mset_incl_refl].
    - apply mset_incl_app_app; try apply mset_incl_refl.
      apply mset_incl_strDel. apply isPrim_sws. assumption.
    - apply mset_incl_app_app; try apply mset_incl_refl.
      apply mset_incl_strDel. assumption.
  Qed.

  Lemma niso_strDel_length :
    forall X sY b, isPrim (snd sY) -> bstrNiso X sY = true ->
      length (strPR b X) = 1 + length (strPR b (strDel X sY)).
  Proof.
    intros X sY b HprY Hniso.
    apply eq_trans with (length ((swsc b sY) :: (strPR b (strDel X sY)))); try reflexivity.
    apply mset_eq_length.
    intro sZ. simpl. destruct (sstructr_eq_dec (swsc b sY) sZ) as [Heq|Hneq].
    - rewrite <- Heq. rewrite niso_count_del; try assumption. reflexivity.
    - rewrite (strDel_not_same_count _ sY sZ b); try assumption. reflexivity.
      intro Hctr. rewrite Hctr in Hneq. apply Hneq. apply swsc_invol.
  Qed.

  Lemma strgt1_Comma : forall (X : structr) b, length (strPR b X) > 1 -> bstrComma X = true.
  Proof.
    induction X; intros b Hlen; try (simpl in Hlen; lia).
    - simpl in Hlen |- *. apply IHX in Hlen. assumption.
    - reflexivity.
  Qed.

  Lemma seqgt2_Comma : forall (s : sequent), length (PR s) > 2 -> bseqComma s = true.
  Proof.
    intros s Hlenseq. destruct s. simpl in Hlenseq. rewrite app_length in Hlenseq.
    assert (length (strPR false X) > 1 \/ length (strPR true Y) > 1) as Hlenstr by lia.
    destruct Hlenstr as [Hlenstr|Hlenstr]; simpl; apply strgt1_Comma in Hlenstr;
      rewrite Hlenstr; (apply orb_true_l || apply orb_true_r).
  Qed.

  Lemma str_sub_and_niso_false :
    forall X sY, bstrSub X sY && bstrNiso X sY = false -> bstrNiso X sY = false.
  Proof.
    intros X sY H. destruct (andb_false_elim _ _ H) as [Hsub|Hniso]; [|assumption].
    apply not_true_is_false. intro Hniso.
    apply bstrNiso_bstrSub in Hniso. rewrite Hniso in Hsub. discriminate.
  Qed.

  Lemma mset_eq_seq_niso_PR_sdel :
    forall s sZ, isPrim (snd sZ) -> bseqNiso s sZ = true ->
            mset_eq (PR s) (sZ :: PR (seqDel s sZ)).
  Proof.
    intros [X Y] sZ HprZ Hniso. apply orb_prop in Hniso. simpl.
    destruct (bstrNiso X (sws sZ)) eqn:HnisoX;
      [|destruct (bstrNiso Y sZ) eqn:HnisoY].
    - apply isPrim_sws in HprZ. simpl. rewrite app_comm_cons.
      apply mset_eq_app_app; try apply mset_eq_refl.
      rewrite <- (sws_invol sZ) at 1. fold (swsc false).
      apply mset_eq_PR_strDel; tauto.
    - simpl. rewrite app_singl_eq_cons.
      eapply mset_eq_tran; try apply mset_eq_app_swap_app.
      apply mset_eq_app_app; try apply mset_eq_refl.
      simpl. apply (mset_eq_PR_strDel _ _ true); tauto.
    - pose proof diff_false_true. tauto.
  Qed.

  Lemma PR_incl_hdPR_del (Z : structr) :
    strPR true Z ⊆ strPR true (tostar (hdPR true Z)) ++ strPR true (strDel Z (hdPR true Z)).
  Proof.
    intros sX HsX. rewrite PR_tostar_eq; [| apply hdPR_isPrim].
    simpl. unfold id. destruct (eqdec (hdPR true Z) sX) as [Heq|Hneq].
    - left. assumption.
    - right. pose proof (hdPR_isPrim Z true) as Hpr.
      pose proof (strDel_not_same_count Z (hdPR true Z) sX true Hpr Hneq).
      apply count_In. rewrite <- H. apply count_In. assumption.
  Qed.

  Lemma str_ge2_niso : forall X sY b, count (strPR b X) (swsc b sY) >= 2 -> bstrNiso X sY = true.
  Proof.
    induction X; intros sY b Hcou;
    try (simpl strPR in Hcou;
      match type of Hcou with
        count ?l ?x >= 2 =>
          pose proof (count_bound x l) as Hlen;
          simpl length in Hlen; lia
      end).
    - simpl. apply (IHX _ (negb b)). simpl in Hcou.
      rewrite swsc_neg_sws. assumption.
    - simpl in Hcou. rewrite count_app in Hcou.
      match type of Hcou with
        count ?l1 ?x1 + count ?l2 ?x2 >= 2 => destruct (count l1 x1) eqn:Heq1
      end; simpl; apply orb_true_intro.
      + right. apply (in_strPR_sub' _ _ b). apply count_In. lia.
      + left. apply (in_strPR_sub' _ _ b). apply count_In. lia.
  Qed.

  Lemma mset_eq_seq_gt2_PR_sdel :
    forall s sZ, length (PR s) > 2 -> count (PR s) sZ >= 2 ->
            mset_eq (PR s) (sZ :: PR (seqDel s sZ)).
  Proof.
    intros s sZ Hlen Hcou.
    apply mset_eq_seq_niso_PR_sdel.
    - apply (seqPR_isPrim s). apply count_In. lia.
    - apply seqgt2_Comma in Hlen. destruct s as [X Y].
      simpl in Hcou. rewrite count_app in Hcou.
      destruct (count (strPR false X) sZ) as [|m] eqn:HcouX;
        [|destruct (count (strPR true Y) sZ) as [|n] eqn:HcouY].
      + simpl. apply orb_true_intro. right.
        apply (str_ge2_niso _ _ true). assumption.
      + simpl. apply orb_true_intro. left. rewrite <- HcouX in Hcou.
        apply (str_ge2_niso _ _ false).
        simpl. rewrite sws_invol. rewrite Nat.add_0_r in Hcou. assumption.
      + apply orb_prop in Hlen. destruct Hlen as [HCX|HCY].
        * apply orb_true_intro. left. apply (strPR_niso false);
            [|assumption]. rewrite sws_invol. apply count_In. lia.
        * apply orb_true_intro. right. apply (strPR_niso true);
            [|assumption]. simpl. unfold id. apply count_In. lia.
  Qed.

  Lemma seqgt2_same_del_count :
    forall s sZ, length (PR s) > 2 -> count (PR s) sZ >= 2 ->
         count (PR s) sZ = 1 + count (PR (seqDel s sZ)) sZ.
  Proof.
    intros s sZ Hlen HinsZ.
    pose proof (mset_eq_seq_gt2_PR_sdel s sZ Hlen HinsZ sZ) as H.
    rewrite count_cons_eq in H; try reflexivity. assumption.
  Qed.
  

  Lemma seqgt2_del_decr_len :
    forall s sZ, nb_PR s > 2 -> count (PR s) sZ >= 2 ->
      nb_PR (seqDel s sZ) < nb_PR s.
  Proof.
    intros s sZ Hlen Hin.
    unfold nb_PR.
    rewrite (mset_eq_length _ _ (mset_eq_seq_gt2_PR_sdel _ _ Hlen Hin)).
    simpl. lia.
  Qed.

End Deletion.
