Require Import utils.
Require Import nnf.
Require Import closure.
Require Import semantics.
Require Import seqt.

Require Import Bool.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Lia.

Set Implicit Arguments.


(* ptree stands for "pruned tree" *)
Inductive ptree :=
  | talpha : ptree -> full_seqt -> nnf -> ptree
  | tbeta1 : ptree -> full_seqt -> nnf -> ptree
  | tbeta2 : ptree -> full_seqt -> nnf -> ptree
  | talt   : ptree -> ptree -> full_seqt -> nnf -> ptree
  | tjump  : ptree -> full_seqt -> ptree
  | tloop  : full_seqt -> ptree.

Definition df_t : ptree := tloop df_fseqt.

Definition t_fseqt (x : ptree) : full_seqt :=
  match x with
  | talpha _ fs _ => fs
  | tbeta1 _ fs _ => fs
  | tbeta2 _ fs _ => fs
  | talt _ _ fs _ => fs
  | tjump _ fs    => fs
  | tloop fs      => fs
  end.

Definition t_dose (t : ptree) := fst (t_fseqt t).
Definition t_upse (t : ptree) := snd (t_fseqt t).

Definition t_G (t : ptree) := s_G (t_dose t).
Definition t_H (t : ptree) := s_H (t_dose t).
Definition t_d (t : ptree) := s_d (t_dose t).
Definition t_c (t : ptree) := s_c (t_dose t).
Definition t_R (t : ptree) := s_R (t_dose t).

Definition t_uev (t : ptree) := s_uev (t_upse t).
Definition t_lp  (t : ptree) := s_lp (t_upse t).

Definition t_isstate (t : ptree) : Prop :=
  match t with
  | tjump _ _ => True
  | tloop _   => True
  | _         => False
  end.

Definition t_isalpha (t : ptree) :=
  match t with
  | talpha _ _ _ => True
  | _            => False
  end.

Definition t_isbeta (t : ptree) : Prop :=
  match t with
  | tbeta1 _ _ _ => True
  | tbeta2 _ _ _ => True
  | talt _ _ _ _ => True
  | _            => False
  end.

Definition t_isbeta1 (t : ptree) : Prop :=
  match t with
  | tbeta1 _ _ _ => True
  | _            => False
  end.

Definition t_isbeta2 (t : ptree) : Prop :=
  match t with
  | tbeta2 _ _ _ => True
  | _            => False
  end.

Definition t_isalt (t : ptree) : Prop :=
  match t with
  | talt _ _ _ _ => True
  | _            => False
  end.

Definition t_isjump (t : ptree) : Prop :=
  match t with
  | tjump _ _ => True
  | _         => False
  end.

Definition t_isloop (t : ptree) : Prop :=
  match t with
  | tloop _ => True
  | _       => False
  end.

Definition t_prinform (t : ptree) : option nnf :=
  match t with
  | talpha _ _ phi => Some phi
  | tbeta1 _ _ phi => Some phi
  | tbeta2 _ _ phi => Some phi
  | talt _ _ _ phi => Some phi
  | tjump _ _      => None
  | tloop _        => None
  end.

Definition ptree_eqdec (x y : ptree) : {x = y} + {x <> y}.
Proof.
decide equality; (apply nnf_eqdec || apply full_seqt_eqdec).
Defined.

Definition t_isalpha_dec (x : ptree) :
  {t_isalpha x} + {~ t_isalpha x}.
Proof. destruct x; ((now left) || (now right)). Defined.

Definition t_isbeta_dec (x : ptree) :
  {t_isbeta x} + {~ t_isbeta x}.
Proof. destruct x; ((now left) || (now right)). Defined.

Definition t_isloop_dec (x : ptree) :
  {t_isloop x} + {~ t_isloop x}.
Proof. destruct x; ((now left) || (now right)). Defined.

Definition t_isstate_dec (x : ptree) :
  {t_isstate x} + {~ t_isstate x}.
Proof. destruct x; ((now left) || (now right)). Defined.

Definition option_eqdec [A : Type]
  (A_eqdec : forall (x y : A), {x = y} + {x <> y}) :
  forall (x y : option A), {x = y} + {x <> y}.
Proof. decide equality. Defined.


(* Descendent Relation *)

Definition is_child (x y : ptree) : Prop :=
  match y with
  | talpha c _ _   => x = c
  | tbeta1 c _ _   => x = c
  | tbeta2 c _ _   => x = c
  | talt c1 c2 _ _ => x = c1 \/ x = c2
  | tjump c _      => x = c
  | tloop _        => False
  end.

Definition desc := clos_trans _ is_child.
Definition desceq (x y : ptree) := desc x y \/ x = y.


Reserved Notation "x <=/ y" (at level 70, no associativity).
Reserved Notation "x </ y" (at level 70, no associativity).

Reserved Notation "x <=/ y <=/ z" (at level 70, y at next level).
Reserved Notation "x <=/ y </ z" (at level 70, y at next level).
Reserved Notation "x </ y </ z" (at level 70, y at next level).
Reserved Notation "x </ y <=/ z" (at level 70, y at next level).

Infix "</"  := desc.
Infix "<=/" := desceq.

Notation "x <=/ y <=/ z" := (x <=/ y /\ y <=/ z).
Notation "x <=/ y </ z" := (x <=/ y /\ y </ z).
Notation "x </ y </ z" := (x </ y /\ y </ z).
Notation "x </ y <=/ z" := (x </ y /\ y <=/ z).

Theorem desceq_refl : forall {x}, x <=/ x.
Proof. intro x. right. reflexivity. Qed.

Lemma desceq_desc_desc [x y z] : x <=/ y -> y </ z -> x </ z.
Proof.
intros H H0. destruct H as [H|H].
- right with y; assumption.
- rewrite H. assumption.
Qed.

Lemma desc_desceq_desc [x y z] : x </ y -> y <=/ z -> x </ z.
Proof.
intros H H0. destruct H0 as [H0|H0].
- right with y; assumption.
- rewrite <- H0. assumption.
Qed.

Lemma child_desceq : forall x y z,
  is_child x y -> y <=/ z -> x <=/ z.
Proof.
intros x y z Hch ylez. left.
apply desc_desceq_desc with y; try assumption.
left. assumption.
Qed.

Lemma desceq_trans : forall x y z, x <=/ y -> y <=/ z -> x <=/ z.
Proof.
intros x y z xley ylez. destruct ylez as [yltz|yeqz].
- left. apply desceq_desc_desc with y; assumption.
- rewrite <- yeqz. assumption.
Qed.

Fixpoint tree_size (t : ptree) : nat :=
  match t with
  | talpha c _ _   => S (tree_size c)
  | tbeta1 c _ _   => S (tree_size c)
  | tbeta2 c _ _   => S (tree_size c)
  | talt c1 c2 _ _ => S (tree_size c1 + tree_size c2)
  | tjump c _      => S (tree_size c)
  | tloop _        => 1
  end.

Lemma child_lt_tree_size [x y] : is_child y x -> tree_size y < tree_size x.
Proof.
intro H. destruct x; try ((simpl in H; rewrite H; simpl; lia)||contradiction).
simpl in H. destruct H; simpl in H; rewrite H; simpl; lia.
Qed.

Theorem desc_lt_tree_size [x y] : y </ x -> tree_size y < tree_size x.
Proof.
intro yltx. apply clos_trans_tn1 in yltx. induction yltx.
- apply (child_lt_tree_size H).
- apply child_lt_tree_size in H. lia.
Qed.

Theorem desc_not_eq [x y] : y </ x -> x <> y.
Proof.
intros H H0. apply desc_lt_tree_size in H. rewrite H0 in H. lia.
Qed.

Lemma not_desc_child_desc [x z] : z </ x ->
  (forall y, is_child y x -> ~ z </ y) -> is_child z x.
Proof.
intros zltx ally. apply clos_trans_tn1 in zltx.
inversion zltx; try assumption. apply clos_tn1_trans in H0.
contradict H0. apply ally. assumption.
Qed.

Definition desc_dec : forall z x, {z </ x} + {~ z </ x}.
Proof.
intros z x. revert z. induction x as [c IHc fs phi|c IHc fs phi|
c IHc fs phi|c1 IHc1 c2 IHc2 fs phi|c IHc fs|fs];
try (
intro z; destruct (IHc z) as [zltc|nzltc];
  [left; right with c; try assumption; left; simpl; reflexivity|
  destruct (ptree_eqdec z c) as [Heq|Hneq];
    [left; rewrite Heq; left; simpl; reflexivity|
    right; intro Hctr; apply clos_trans_tn1 in Hctr; inversion Hctr;
      [simpl in H; contradiction|
      simpl in H; rewrite H in H0;
        apply clos_tn1_trans in H0; contradiction]]]).
- intro z. destruct (IHc1 z) as [zltc1|nzltc1].
  + left. right with c1; try assumption. left. simpl. now left.
  + destruct (ptree_eqdec z c1) as [Heq1|Hneq1].
    { left. rewrite Heq1. left. simpl. now left. }
    destruct (IHc2 z) as [zltc2|nzltc2].
    * left. right with c2; try assumption. left. simpl. now right.
    * destruct (ptree_eqdec z c2) as [Heq2|Hneq2].
     -- left. rewrite Heq2. left. simpl. now right.
     -- right. intro Hctr. apply clos_trans_tn1 in Hctr. inversion Hctr.
       ++ simpl in H. destruct H; contradiction.
       ++ simpl in H. destruct H.
         ** rewrite H in H0. apply clos_tn1_trans in H0. contradiction.
         ** rewrite H in H0. apply clos_tn1_trans in H0. contradiction.
- right. intro Hctr. apply clos_trans_tn1 in Hctr.
  inversion Hctr; contradiction.
Defined.

Theorem desc_child_or_child_dec [x z] : z </ x ->
  {y | is_child y x /\ z </ y} + {is_child z x}.
Proof.
intro zltx. induction x as [c IHc fs phi|c IHc fs phi|
c IHc fs phi|c1 IHc1 c2 IHc2 fs phi|c IHc fs|fs]; try (
destruct (desc_dec z c) as [zltc1|nzltc1];
  [left; exists c; simpl; split; tauto|
  right; apply not_desc_child_desc; try assumption;
    intros y Hy; simpl in Hy; rewrite Hy; assumption]).
- destruct (desc_dec z c1) as [zltc1|nzltc1].
  + left. exists c1. simpl. split; tauto.
  + destruct (desc_dec z c2) as [zltc2|nzltc2].
    * left. exists c2. simpl. split; tauto.
    * right. apply not_desc_child_desc; try assumption.
      intros y Hy. simpl in Hy. destruct Hy as [Hy|Hy];
      (rewrite Hy; assumption).
- apply False_rec. apply clos_trans_tn1 in zltx.
  inversion zltx; contradiction.
Defined.

Lemma desc_desceq_child [x z] : z </ x -> exists y, is_child y x /\ z <=/ y.
Proof.
intro zltx. apply clos_trans_tn1 in zltx. inversion zltx.
- exists z. split; [assumption | now right].
- apply clos_tn1_trans in H0. exists y. split; [assumption | now left].
Qed.

Lemma tloop_no_desc : forall x, t_isloop x -> forall z, ~ z </ x.
Proof.
intros x lpx z zltx. destruct x as [| | | | |fs]; try contradiction.
apply clos_trans_tn1 in zltx. inversion zltx; contradiction.
Qed.

Theorem desc_ptree_induction [P : ptree -> Prop] :
  (forall x, forall (IH : (forall y, y </ x -> P y)), P x) -> forall x, P x.
Proof.
intros IS. cut (forall x y, y <=/ x -> P y).
- intros H x. apply (H x). now right.
- induction x as [c IHc fs phi|c IHc fs phi|
  c IHc fs phi|c1 IHc1 c2 IHc2 fs phi|c IHc fs|fs]; try (
  intros y ylex; destruct ylex as [yltx|yeqx];
    [apply IHc; destruct (desc_desceq_child yltx) as [c' [chc' ylec']];
    rewrite chc' in ylec'; assumption|
    rewrite yeqx; apply IS;
    intros z Hz; destruct (desc_desceq_child Hz) as [c' [chc' zlec']];
    rewrite chc' in zlec'; apply (IHc z zlec')]).
  + intros y ylex. destruct ylex as [yltx|yeqx].
    * apply desc_desceq_child in yltx.
      destruct yltx as [c' [Heqc' ylec]].
      destruct Heqc' as [Heqc'|Heqc'].
     -- rewrite Heqc' in ylec. apply IHc1. assumption.
     -- rewrite Heqc' in ylec. apply IHc2. assumption.
    * rewrite yeqx. apply IS. intros z zltx.
      apply desc_desceq_child in zltx.
      destruct zltx as [c' [Heqc' zlec]].
      destruct Heqc' as [Heqc'|Heqc'].
     -- rewrite Heqc' in zlec. apply IHc1. assumption.
     -- rewrite Heqc' in zlec. apply IHc2. assumption.
  + intros y ylex. destruct ylex as [yltx|yeqx].
    * contradict yltx. apply tloop_no_desc. exact I.
    * rewrite yeqx. apply IS. intros z Hz.
      contradict Hz. apply tloop_no_desc. exact I.
Qed.
  

Fixpoint all_nodes (x : ptree) : list (ptree) :=
  x ::
  match x with
  | talpha c _ _   => all_nodes c
  | tbeta1 c _ _   => all_nodes c
  | tbeta2 c _ _   => all_nodes c
  | talt c1 c2 _ _ => all_nodes c1 ++ all_nodes c2
  | tjump c _      => all_nodes c
  | tloop _        => []
  end.

Lemma all_nodes_self_in : forall x, In x (all_nodes x).
Proof.
intro x. destruct x; now left.
Qed.

Theorem desceq_in_all_nodes (y : ptree) :
  forall x, x <=/ y -> In x (all_nodes y).
Proof.
intros x xley. destruct xley as [xlty|xeqy].
- apply clos_trans_tn1 in xlty. induction xlty.
  + destruct y; try ((simpl in H |- *; rewrite H;
    right; apply all_nodes_self_in) || contradiction).
    destruct H as [H|H]; simpl in H |- *; rewrite H;
    right; apply in_app_iff; [left|right];
    apply all_nodes_self_in.
  + destruct z;
    try ((right; rewrite <- H; assumption) || contradiction).
    destruct H as [H|H]; right; apply in_app_iff; [left|right];
    rewrite <- H; assumption.
- rewrite xeqy. apply all_nodes_self_in.
Qed.



(* Path Relation *)

Inductive path : list ptree -> ptree -> ptree -> Prop :=
  | path_nil  : forall x, path [] x x
  | path_cons : forall p x y z, is_child y x ->
      path p y z -> path (x :: p) x z.

Lemma path_end_desceq_start : forall x y p, path p x y -> y <=/ x.
Proof.
intros x y p piep. induction piep.
- now right.
- destruct IHpiep as [Hdesc|Heq].
  + left. right with y; [assumption | now left].
  + rewrite Heq. left. left. assumption.
Qed.

Lemma in_path_desceq : forall x y z p, path p x z ->
  In y p -> y <=/ x.
Proof.
intros x y z p piep. induction piep.
- simpl. tauto.
- intros Hy. destruct Hy as [Hy|Hy].
  + now right.
  + apply IHpiep in Hy. destruct Hy as [Hy|Hy].
    * left. right with y0; [assumption | now left].
    * left. left. rewrite Hy. assumption.
Qed.

Lemma cut_path [p x z] : path p x z -> forall y, In y p ->
  exists q, path q y z /\ incl q p.
Proof.
intros H y Hy. induction H; try contradiction.
destruct Hy as [Hy|Hy].
- exists (x :: p). rewrite Hy in H |- *. split; try (apply incl_refl).
  right with y0; try assumption.
- destruct (IHpath Hy) as [q [Hq1 Hq2]].
  exists q. split; try assumption. apply incl_tl. assumption.
Qed.

Inductive path_alt : list ptree -> ptree -> ptree -> Prop :=
  | path_alt_nil  : forall x, path_alt [] x x
  | path_alt_cons : forall p x z, p <> [] -> hd df_t p = x ->
      (forall n, S n < length p -> is_child (nth (S n) p df_t) (nth n p df_t)) ->
      is_child z (last p df_t) -> path_alt p x z.

Lemma path_l_alt [p x z] : path p x z -> path_alt p x z.
Proof.
intro H. induction H; try left.
inversion IHpath.
- simpl. right.
  + discriminate.
  + simpl. reflexivity.
  + simpl. lia.
  + simpl. rewrite <- H3. assumption.
- right.
  + discriminate.
  + simpl. reflexivity.
  + intros n Hn. destruct p; try (simpl in Hn; lia).
    destruct n.
    * simpl. simpl in H2. rewrite H2. assumption.
    * specialize (H3 n). simpl. simpl in H3. apply H3.
      simpl in Hn. lia.
  + destruct p; try contradiction. rewrite last_cons_cons_eq.
    assumption.
Qed.

Lemma path_alt_l [p x z] : path_alt p x z -> path p x z.
Proof.
revert x z. induction p.
- intros x z H. inversion H; [left|contradiction].
- intros x z H. inversion H. simpl in H1. rewrite H1.
  destruct p.
  + simpl in H3. rewrite H1 in H3. right with z; [assumption|left].
  + right with p.
    * specialize (H2 O). simpl in H2. rewrite H1 in H2. apply H2. lia.
    * apply IHp. right.
     -- discriminate.
     -- simpl. reflexivity.
     -- intros n Hn. specialize (H2 (S n)). simpl in H2. simpl. apply H2.
        simpl in Hn. lia.
     -- rewrite last_cons_cons_eq in H3. assumption.
Qed.

Lemma path_l_alt_iff {p x z} : path p x z <-> path_alt p x z.
Proof.
split; [apply path_l_alt|apply path_alt_l].
Qed.
