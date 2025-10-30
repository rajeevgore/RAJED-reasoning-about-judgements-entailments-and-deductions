From Ksat Require Import utils.
From Ksat Require Import defs.

Require Import Arith.
Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Psatz.
Require Import String.


Fixpoint unbox (Gamma : list nnf) : list nnf :=
  match Gamma with
  | [] => []
  | ((box phi) :: l) => phi :: unbox l
  | (_ :: l) => unbox l
  end.

Theorem unbox_sublist_cons {Gamma : list nnf} {phi} :
  sublist (unbox Gamma) (unbox (phi :: Gamma)).
Proof.
destruct phi; try (simpl; apply sublist_refl).
simpl. constructor 2. apply sublist_refl.
Qed.

Theorem unbox_sublist : forall {G1 G2 : list nnf} (h : sublist G1 G2),
  sublist (unbox G1) (unbox G2).
Proof.
  induction G1 as [| phi G1'].
  - intros G2 H. simpl. apply sublist_nil_l.
  - destruct phi as [ | | | | phi'| ];
    try (intros G2 H; simpl; apply IHG1'; apply sublist_weak in H; exact H).
    simpl. induction G2 as [|psi G2'].
    + intro H. inversion H.
    + destruct psi as [ | | | |psi'| ];
      try (simpl; intro H; apply IHG2'; inversion H; assumption).
      simpl. intro H. inversion H.
      * constructor 2. apply IHG2'. assumption.
      * constructor 3. apply IHG1'. assumption.
Qed.

Theorem unbox_erase : forall {G : list nnf} {phi},
  erase_nnf phi (unbox G) = unbox (erase_nnf (box phi) G).
Proof.
induction G as [|psi].
- simpl. trivial.
- destruct psi as [?|?|?|?|psi'|psi'];
  try (simpl; assumption).
  intro phi. simpl. destruct (nnf_eqdec phi psi') eqn:Heq; simpl.
  + reflexivity.
  + rewrite IHG. reflexivity.
Qed.

Theorem unbox_erase_of_ne_box :
  forall {G : list nnf} {phi : nnf} (h : forall psi, phi <> box psi),
    unbox (erase_nnf phi G) = unbox G.
Proof.
intros G phi h. induction G as [|xi].
- simpl. reflexivity.
- unfold erase_nnf. simpl.
  destruct (nnf_eqdec phi xi) as [heq|hneq] eqn:Hdec.
  + rewrite <- heq.
    destruct phi as [ | | | | phi'|phi']; try (simpl; reflexivity).
    pose proof (h phi') as H. contradiction.
  + fold (erase nnf_eqdec) erase_nnf.
    destruct xi as [ | | | | xi'|xi']; try(simpl; exact IHG).
    simpl. rewrite IHG. reflexivity.
Qed.

Theorem unbox_diff : forall {G1 G2 : list nnf},
  diff_nnf (unbox G2) (unbox G1) = unbox (diff_nnf G2 G1).
Proof.
induction G1 as [|phi].
- intro G2. simpl. reflexivity.
- destruct phi as [ | | | | phi'|phi'] eqn:Hphieq;
  try (intro G2; simpl; destruct G2 as [|psi];
  (  (repeat (rewrite (diff_nil_l nnf_eqdec)); simpl; reflexivity)
  || (fold erase_nnf; rewrite <- Hphieq; rewrite <- (IHG1 (erase_nnf phi (psi :: G2)));
      cut (unbox (erase_nnf phi (psi :: G2)) = unbox (psi :: G2));
      (  (intro H; rewrite H; reflexivity)
      || (apply unbox_erase_of_ne_box; intro xi; rewrite Hphieq; discriminate))))).
  intro G2. destruct G2 as [|psi G2'] eqn:HG2eq.
  repeat (rewrite (diff_nil_l nnf_eqdec)). simpl. reflexivity.
  assert (diff_nnf (psi :: G2') (box phi' :: G1)
          = diff_nnf (erase_nnf (box phi') (psi :: G2')) G1) as H.
  + reflexivity.
  + rewrite H. rewrite <- (IHG1 (erase_nnf (box phi') (psi :: G2'))).
    rewrite <- (@unbox_erase (psi :: G2') phi'). simpl unbox at 2.
    destruct (unbox (psi :: G2')).
    * simpl. rewrite (diff_nil_l nnf_eqdec). reflexivity.
    * reflexivity.
Qed.

Theorem unbox_iff : forall {G phi}, In (box phi) G <-> In phi (unbox G).
Proof.
induction G as [|psi G'].
- simpl. tauto.
- intro phi. elim (IHG' phi). intros IHG'l IHG'r. split.
  * intro H. simpl in H. elim H.
    + intro H0. rewrite H0. simpl. left. reflexivity.
    + intro H0. apply IHG'l in H0. destruct psi as [ | | | |psi'|psi'];
      try (simpl; assumption).
      simpl. right. assumption.
  * destruct psi as [ | | | |psi'|psi'];
    try (simpl; intro H; right; apply IHG'r; assumption).
    simpl. intro H. elim H.
      + intro Hl. left. rewrite Hl. reflexivity.
      + intro Hr. right. apply IHG'r. assumption.
Qed.



Fixpoint rebox (G : list nnf) : list nnf :=
  match G with
  | []       => []
  | (hd::tl) => box hd :: rebox tl
  end.

Theorem rebox_unbox_of_mem : forall {G}, incl (rebox (unbox G)) G.
Proof.
induction G as [|phi G'].
- simpl. unfold incl. tauto.
- destruct phi as [ | | | |phi'|phi'];
  try (simpl; unfold incl; intros psi H; simpl; right; apply (IHG' psi H)).
  simpl. unfold incl. intros psi H. simpl in H. elim H.
  * intro Hl. simpl. left. assumption.
  * intro Hr. simpl. right. apply (IHG' psi Hr).
Qed.

Theorem unbox_rebox : forall {G}, unbox (rebox G) = G.
Proof.
induction G as [|phi G'].
- reflexivity.
- simpl. rewrite IHG'. reflexivity.
Qed.

Theorem box_only_rebox : forall {G}, box_only (rebox G).
Proof.
induction G as [|phi].
- simpl. apply box_only_nil.
- simpl. apply cons_box_only. assumption.
Qed.

Theorem rebox_iff : forall {phi G}, In (box phi) (rebox G) <-> In phi G.
Proof.
intro phi. induction G as [|psi G'].
- simpl. tauto.
- split.
  * intro H. simpl in H. elim H.
    + intro Hl. simpl. left. injection Hl. tauto.
    + intro Hr. simpl. right. apply IHG'. assumption.
  * intro H. simpl in H. elim H.
    + intro Hl. rewrite Hl. simpl. left. reflexivity.
    + intro Hr. simpl. right. apply IHG'. assumption.
Qed.



Fixpoint undia (Gamma : list nnf) : list nnf :=
  match Gamma with
  | [] => []
  | ((dia phi) :: l) => phi :: undia l
  | (_ :: l) => undia l
  end.

Theorem undia_iff : forall {G phi}, In (dia phi) G <-> In phi (undia G).
Proof.
induction G as [|psi G'].
- simpl. tauto.
- split.
  * intro H. simpl in H. elim H.
    + intro Hl. rewrite Hl. simpl. left. reflexivity.
    + intro Hr. destruct psi as [ | | | |psi'|psi'];
      try (simpl; apply IHG'; assumption).
      simpl. right. apply IHG'. assumption.
  * destruct psi as [ | | | |psi'|psi'];
    try (simpl; intro H; right; apply IHG'; assumption).
    intro H. simpl in H. elim H.
      + intro Hl. rewrite Hl. simpl. left. reflexivity.
      + intro Hr. simpl. right. apply IHG'. assumption.
Qed.



Fixpoint get_modal (G : list nnf) : list nnf :=
  match G with
  | [] => []
  | (dia psi) :: l => (dia psi) :: get_modal l
  | (box psi) :: l => (box psi) :: get_modal l
  | (_ :: l) => get_modal l
  end.

Theorem get_modal_iff_dia : forall {G} {phi : nnf},
  In (dia phi) (get_modal G) <-> In (dia phi) G.
Proof.
induction G as [|psi G'].
- simpl. tauto.
- split.
  * intro H. destruct psi as [ | | | |psi'|psi'];
    try (simpl; right; simpl in H; apply IHG'; assumption).
    + simpl. right. simpl in H. elim H.
     -- discriminate.
     -- intro Hr. apply IHG'. assumption.
    + simpl in H. elim H.
     -- intro Hl. injection Hl. intro H0. rewrite H0. simpl. left. reflexivity.
     -- intro Hr. simpl. right. apply IHG'. assumption.
  * intro H. destruct psi as [ | | | |psi'|psi'];
    try (simpl in H; elim H;
          (discriminate || (intro Hr; simpl; apply IHG'; assumption))).
    + simpl in H. elim H.
     -- discriminate.
     -- intro Hr. simpl. right. apply IHG'. exact Hr.
    + simpl in H. elim H.
     -- intro Hl. injection Hl. intro H0. rewrite H0. simpl. left. reflexivity.
     -- intro Hr. simpl. right. apply IHG'. exact Hr.
Qed.

Theorem get_modal_iff_box : forall {G} {phi : nnf},
  In (box phi) (get_modal G) <-> In (box phi) G.
Proof.
induction G as [|psi G'].
- simpl. tauto.
- split.
  * intro H. destruct psi as [ | | | |psi'|psi'];
    try (simpl; right; simpl in H; apply IHG'; assumption).
    + simpl in H. elim H.
     -- intro Hl. injection Hl. intro H0. rewrite H0. simpl. left. reflexivity.
     -- intro Hr. simpl. right. apply IHG'. assumption.
    + simpl. right. simpl in H. elim H.
     -- discriminate.
     -- intro Hr. apply IHG'. assumption.
  * intro H. destruct psi as [ | | | |psi'|psi'];
    try (simpl in H; elim H;
          (discriminate || (intro Hr; simpl; apply IHG'; assumption))).
    + simpl in H. elim H.
     -- intro Hl. injection Hl. intro H0. rewrite H0. simpl. left. reflexivity.
     -- intro Hr. simpl. right. apply IHG'. exact Hr.
    + simpl in H. elim H.
     -- discriminate.
     -- intro Hr. simpl. right. apply IHG'. exact Hr.
Qed.



Definition get_contra : forall G : list nnf,
                 {p : string | In (var p) G /\ In (neg p) G}
               + {forall p, In (var p) G -> ~ In (neg p) G}.
Proof.
induction G as [|phi G'].
- right. simpl. tauto.
- elim IHG'.
  * intro IHG'l. left. elim IHG'l. intros n H. elim H. intros Hl Hr.
    exists n. split; simpl; right; assumption.
  * intro IHG'r. destruct phi as [m|m| | |phi'|phi'];
    try (right; simpl; intros n H; elim H;
           (discriminate || (intros H0 H1; elim H1;
              (discriminate || (apply IHG'r; assumption))))).
    + destruct (in_dec nnf_eqdec (neg m) G') as [hin|hnin].
     -- left. exists m. split.
       ** simpl. left. reflexivity.
       ** simpl. right. exact hin.
     -- right. intros n H. simpl in H. elim H.
       ** intro Hl. injection Hl. intro H0. rewrite <- H0. simpl.
         intro H1. elim H1.
         ++ discriminate.
         ++ exact hnin.
       ** intro Hr. simpl. intro H0. elim H0.
         ++ discriminate.
         ++ apply IHG'r. exact Hr.
    + destruct (in_dec nnf_eqdec (var m) G') as [hin|hnin].
     -- left. exists m. split.
       ** simpl. right. exact hin.
       ** simpl. left. reflexivity.
     -- right. intros n H. simpl in H. elim H.
       ** discriminate.
       ** destruct (string_dec n m) as [heq|hneq].
         ++ rewrite heq. contradiction.
         ++ intro H0. simpl. intro H1. elim H1.
          --- intro H2. injection H2. intro H3. apply eq_sym in H3. contradiction.
          --- apply IHG'r. assumption.
Defined.

Definition get_and : forall G : list nnf,
              {p : nnf*nnf | In (and (fst p) (snd p)) G}
            + {forall phi psi, ~In (and phi psi) G}.
Proof.
induction G as [|xi G'].
- right. simpl. tauto.
- elim IHG'.
  * intro IHG'l. left. elim IHG'l. intros p' H. exists p'. simpl. right. exact H.
  * intro IHG'r. destruct xi;
    try (right; simpl; intros phi psi H; elim H; (discriminate || (apply IHG'r))).
    + left. exists (pair xi1 xi2). simpl. left. reflexivity.
Defined.

Definition get_or : forall G : list nnf,
              {p : nnf*nnf | In (or (fst p) (snd p)) G}
            + {forall phi psi, ~In (or phi psi) G}.
Proof.
induction G as [|xi G'].
- right. simpl. tauto.
- elim IHG'.
  * intro IHG'l. left. elim IHG'l. intros p' H. exists p'. simpl. right. exact H.
  * intro IHG'r. destruct xi;
    try (right; simpl; intros phi psi H; elim H; (discriminate || (apply IHG'r))).
    + left. exists (pair xi1 xi2). simpl. left. reflexivity.
Defined.

Definition get_box : forall G : list nnf,
              {p : nnf | In (box p) G}
            + {forall phi, ~In (box phi) G}.
Proof.
induction G as [|xi G'].
- right. simpl. tauto.
- elim IHG'.
  * intro IHG'l. left. elim IHG'l. intros p' H. exists p'. simpl. right. exact H.
  * intro IHG'r. destruct xi;
    try (right; simpl; intros phi H; elim H; (discriminate || (apply IHG'r))).
    + left. exists xi. simpl. left. reflexivity.
Defined.

Definition get_dia : forall G : list nnf,
              {p : nnf | In (dia p) G}
            + {forall phi, ~In (dia phi) G}.
Proof.
induction G as [|xi G'].
- right. simpl. tauto.
- elim IHG'.
  * intro IHG'l. left. elim IHG'l. intros p' H. exists p'. simpl. right. exact H.
  * intro IHG'r. destruct xi;
    try (right; simpl; intros phi H; elim H; (discriminate || (apply IHG'r))).
    + left. exists xi. simpl. left. reflexivity.
Defined.

Fixpoint get_var (G : list nnf) : list string :=
  match G with
  | [] => []
  | (var n) :: l => n :: get_var l
  | _ :: l => get_var l
  end.

Theorem get_var_iff : forall {G n}, In (var n) G <-> In n (get_var G).
Proof.
induction G as [|phi G'].
- simpl. tauto.
- destruct phi as [m|m| | | | ];
  try (intro n; split;
         (intro H; simpl in H; elim H;
           (discriminate || (intro Hr; simpl; apply IHG'; exact Hr)))
      || (intro H; simpl in H; simpl; right; apply IHG'; exact H)).
  * intro n. destruct (string_dec m n) as [heq|hneq].
    + rewrite heq. simpl. tauto.
    + split.
     -- intro H. simpl in H. elim H.
       ** intro Hl. injection Hl. contradiction.
       ** intro Hr. simpl. right. apply IHG'. exact Hr.
     -- intro H. simpl in H. elim H.
       ** contradiction.
       ** intro Hr. simpl. right. apply IHG'. exact Hr.
Qed.