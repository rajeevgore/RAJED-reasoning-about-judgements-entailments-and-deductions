Require Import Arith.
Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Permutation.



Theorem impl_contrapositive {P Q : Prop} : (P -> Q) -> (~Q -> ~P).
Proof.
intros Himp notq. intro p. apply Himp in p. contradiction.
Qed.

Set Implicit Arguments.

Section ListDefinitions.

  Variables A B C : Type.
  Variable A_eqdec : forall x y:A, {x = y} + {x <> y}.

  Definition ne_empty_head (l : list A) : l <> [] -> A :=
  match l with
  | []       => fun h => False_rect A (h (refl_equal []))
  | hd :: tl => fun h => hd
  end.

  Inductive sublist : list A -> list A -> Prop :=
  | slnil   : sublist [] []
  | slcons  : forall (l1 l2 : list A) (a:A),
                sublist l1 l2 -> sublist l1 (a::l2)
  | slcons2 : forall (l1 l2 : list A) (a:A),
                sublist l1 l2 -> sublist (a::l1) (a::l2).

  Definition subperm (l1 l2 : list A) : Prop :=
    exists l, Permutation l l1 /\ sublist l l2.

End ListDefinitions.


Infix "~" := Permutation (at level 70, right associativity).
Infix "<+" := sublist (at level 70, right associativity).
Infix "<+~" := subperm (at level 70, right associativity).



Section ListUtilities.

  Variables A B C : Type.
  Variable A_eqdec : forall x y:A, {x = y} + {x <> y}.

  (* General facts on lists *)

  Lemma eq_of_mem_singleton : forall (x y : A), In x [y] -> x = y.
  Proof.
  intros x y H. unfold In in H. elim H.
  exact (eq_sym (x:=y) (y:=x)). exact (False_ind (x=y)).
  Qed.

  Theorem cons_subset_cons (a:A) (l1 l2 : list A) :
    incl l1 l2 -> incl (a :: l1) (a :: l2).
  Proof.
  intros H x Hin. simpl in Hin. destruct Hin.
  - simpl. now left.
  - simpl. right. now (apply H).
  Qed.

  Lemma not_nil_ex : forall l : list A, l <> [] -> exists x, In x l.
  Proof.
  intros l H. destruct l as [|a l]; try contradiction.
  exists a. now left.
  Qed.

  (* Facts about map *)

  Theorem mapp {p : B -> Prop} (f : A -> B) (l : list A) :
    (forall x, In x l -> p (f x)) -> forall y, In y (map f l) -> p y.
  Proof.
  induction l as [|hd tl].
  - simpl. tauto.
  - simpl. intros H y H0. elim H0.
    + intro H1. rewrite <- H1. exact (H hd (or_introl (refl_equal hd))).
    + apply IHtl. intros x H1. apply H. right. assumption.
  Qed.

  Theorem mappeq {p : B -> Prop} (f : A -> B) (l : list A) :
    forall y, (forall x, y = f x -> In x l -> p y) -> In y (map f l) -> p y.
  Proof.
  induction l.
  - simpl. tauto.
  - intros y H H0. simpl in H0. destruct H0.
    + apply (H a).
      * apply eq_sym. assumption.
      * simpl. left. reflexivity.
    + apply IHl.
      * intros x H1 H2. apply (H x).
       -- assumption.
       -- simpl. right. assumption.
      * assumption.
  Qed.

  Theorem in_map_alt {f : A -> B} {l : list A} (fl : list B) :
    fl = map f l -> forall (x : A), In x l -> In (f x) (fl).
  Proof. intro H. rewrite H. apply in_map. Qed.


  (* Facts about sublist *)

  Theorem sublist_refl : forall l : list A, l <+ l.
  Proof.
  induction l.
  - constructor 1.
  - constructor 3. assumption.
  Qed.

  Theorem sublist_nil_l : forall l : list A, sublist [] l.
  Proof.
  induction l.
  - constructor 1.
  - constructor 2. assumption.
  Qed.

  Theorem sublist_weak : forall (a:A) (l1 l2 : list A),
    sublist (a::l1) l2 -> sublist l1 l2.
  Proof.
  intros a l1 l2 H.
  remember (a::l1) as al1 in H.
  induction H as [|l1' l2' b|l1' l2' b].
  - discriminate Heqal1.
  - apply slcons. apply (IHsublist Heqal1).
  - injection Heqal1. intros Heql Heqa. apply slcons.
    rewrite <- Heql. exact H.
  Qed.

  Theorem sublist_trans : forall (l1 l2: list A),
    sublist l1 l2 -> forall l3 : list A, sublist l2 l3 -> sublist l1 l3.
  Proof.
  intros l1 l2 H. induction H.
  - tauto.
  - intros l3 H0. apply sublist_weak in H0. apply IHsublist. assumption.
  - induction l3.
    + intro H0. inversion H0.
    + intro H0. inversion H0.
      * constructor 2. apply IHl3. assumption.
      * constructor 3. apply IHsublist. assumption.
  Qed.

  Theorem sublist_incl : forall (l1 l2 : list A), sublist l1 l2 -> incl l1 l2.
  Proof.
  intros l1 l2 H. induction H.
  - unfold incl. tauto.
  - intros x Hx. simpl. right. apply IHsublist. assumption.
  - intros x Hx. simpl in Hx. elim Hx.
    + intro Hxl. simpl. left. assumption.
    + intro Hxr. simpl. right. apply IHsublist. assumption.
  Qed.

  Theorem remove_sublist (a : A) (l : list A) :
    sublist (remove A_eqdec a l) l.
  Proof.
  induction l.
  - simpl. constructor 1.
  - simpl. destruct (A_eqdec a a0).
    + constructor 2. assumption.
    + constructor 3. assumption.
  Qed.

  Theorem singleton_sublist (a : A) (l : list A) : [a] <+ l <-> In a l.
  Proof.
  split.
  - intro H. inversion H.
    + right. apply sublist_incl in H0. apply (H0 a). left. reflexivity.
    + left. reflexivity.
  - induction l.
    + simpl. tauto.
    + intro H. destruct H as [Heq|Hin].
      * rewrite Heq. constructor 3. apply sublist_nil_l.
      * constructor 2. apply IHl. assumption.
  Qed.

  Theorem sublist_of_notin_sublist_cons (a : A) (l1 l2 : list A) :
  ~ In a l1 -> l1 <+ a :: l2 -> l1 <+ l2.
  Proof.
  intros Hnin Hsub. inversion Hsub.
  - assumption.
  - contradict Hnin. rewrite <- H0. rewrite H. now left.
  Qed.


  (* Facts about subperm *)

  Theorem subperm_nil_l (l : list A) : [] <+~ l.
  Proof.
  exists []. split.
  - constructor.
  - apply sublist_nil_l.
  Qed.

  Theorem subperm_of_notin_subperm_cons (a : A) (l1 l2 : list A) :
  ~ In a l1 -> l1 <+~ a :: l2 -> l1 <+~ l2.
  Proof.
  intros H H0. destruct H0 as [l [Hlp Hls]].
  apply (impl_contrapositive (Permutation_in a Hlp)) in H.
  exists l. split; try assumption.
  apply (@sublist_of_notin_sublist_cons a); assumption.
  Qed.

  Theorem subperm_cons_of_subperm (a : A) (l1 l2 : list A) :
  l1 <+~ l2 -> l1 <+~ a :: l2.
  Proof.
  intro H. destruct H as [l [Hlperm Hlsub]].
  exists l. split; try assumption. constructor 2. assumption.
  Qed.

  Theorem cons_subperm_of_mem (a : A) (l1 l2 : list A) :
  ~ In a l1 -> In a l2 -> l1 <+~ l2 -> a :: l1 <+~ l2.
  Proof.
  rename l1 into l0. generalize l0 as l1. clear l0.
  induction l2.
  - contradiction.
  - intros l1 Hnin Hin Hsp. destruct Hin as [Heq|Hin].
    + rewrite Heq in Hsp |- *. destruct Hsp as [l [Hlperm Hlsub]].
      pose proof (Permutation_in a Hlperm) as H.
      pose proof (impl_contrapositive H) as H0.
      apply H0 in Hnin.
      pose proof (sublist_of_notin_sublist_cons Hnin Hlsub) as H1.
      exists (a :: l). split.
      * constructor. assumption.
      * constructor 3. assumption.
    + destruct Hsp as [l [Hlperm Hlsub]]. inversion Hlsub.
      * apply subperm_cons_of_subperm.
        apply IHl2; try assumption.
        exists l. tauto.
      * assert (a :: l0 <+~ l2) as Hl0.
       -- apply IHl2; try assumption.
         ++ intro Hcont. contradict Hnin. apply (Permutation_in _ Hlperm).
            rewrite <- H0. now right.
         ++ exists l0. split; [apply Permutation_refl | assumption].
       -- destruct Hl0 as [l0' [Hpl0' Hsl0']].
          exists (a1 :: l0'). split.
         ++ apply (@Permutation_trans _ _ (a :: l)).
           ** apply (@Permutation_trans _ _ (a1 :: a :: l0)).
            --- apply Permutation_cons; [reflexivity | assumption].
            --- rewrite <- H0. constructor.
           ** apply Permutation_cons; [reflexivity | assumption].
         ++ rewrite H. constructor 3. assumption.
  Qed.

  Theorem subperm_incl (l1 l2 : list A) : l1 <+~ l2 -> incl l1 l2.
  Proof.
  intro H. unfold subperm in H.
  destruct H as [l [Hperm Hsub]].
  intros a Ha.
  apply Permutation_sym in Hperm.
  apply (sublist_incl Hsub).
  apply (Permutation_in a Hperm Ha).
  Qed.



  

  (* Facts about erase *)

  Fixpoint erase (l : list A) (a:A) : list A :=
  match l with
  | []       => []
  | hd :: tl => if (A_eqdec hd a)
                then tl else hd :: erase tl a
  end.

  Theorem erase_cons (a:A) (l : list A) : l = set_remove A_eqdec a (a :: l).
  Proof.
  simpl. destruct (A_eqdec a a); try contradiction. reflexivity.
  Qed.

  (* Theorem erase_cons (a:A) (l : list A) : l = erase (a :: l) a.
  Proof.
  simpl. destruct (A_eqdec a a); try contradiction. reflexivity.
  Qed. *)

  Theorem mem_of_mem_erase (a b : A) (l : list A) :
    In a (erase l b) -> In a l.
  Proof.
  induction l as [|x tl].
  - simpl. tauto.
  - simpl. destruct (A_eqdec x b) as [heq|hneq].
    + tauto.
    + intro H. simpl in H. elim H; tauto.
  Qed.

  Theorem mem_erase_of_ne (a b : A) (l : list A) :
    a <> b -> (In a (erase l b) <-> In a l).
  Proof.
  induction l as [|x tl].
  - simpl. tauto.
  - intro H. simpl. destruct (A_eqdec x b) as [heq|hneq].
    + split.
      * intro H0. right. assumption.
      * intro H0. elim H0.
       -- intro H1. contradict H1. rewrite heq. auto.
       -- tauto.
    + split.
      * intro H0. simpl in H0. elim H0.
       -- intro H1. left. exact H1.
       -- intro H1. right. apply (IHtl H). assumption.
      * intro H0. simpl. elim H0.
       -- intro H1. left. assumption.
       -- intro H1. right. apply (IHtl H). assumption.
  Qed.

  Theorem erase_of_not_mem (a:A) (l : list A) :
    ~ In a l -> set_remove A_eqdec a l = l.
  Proof.
  induction l.
  - simpl. tauto.
  - intro H. simpl. destruct (A_eqdec a a0) as [Heq|Hneq].
    + simpl in H. apply eq_sym in Heq. tauto.
    + rewrite IHl. reflexivity. simpl in H. tauto.
  Qed.

  (* Theorem erase_of_not_mem (a:A) (l : list A) : ~ In a l -> erase l a = l.
  Proof.
  induction l.
  - simpl. tauto.
  - intro H. simpl. destruct (A_eqdec a0 a).
    + simpl in H. tauto.
    + rewrite IHl. reflexivity. simpl in H. tauto.
  Qed. *)

  Theorem erase_comm (a b : A) (l : list A) :
    erase (erase l a) b = erase (erase l b) a.
  Proof.
  induction l as [|c].
  - simpl. reflexivity.
  - simpl. destruct (A_eqdec c a) as [hca|hnca] eqn:Dca.
    + destruct (A_eqdec c b) as [hcb|hncb] eqn:Dcb.
      * rewrite <- hca. rewrite <- hcb. reflexivity.
      * simpl. rewrite Dca. reflexivity.
    + destruct (A_eqdec c b) as [hcb|hncb] eqn:Dcb.
      * simpl. rewrite Dcb. reflexivity.
      * simpl. rewrite Dcb. rewrite Dca. rewrite IHl. reflexivity.
  Qed.

  Theorem erase_sublist (a:A) (l : list A) :
    sublist (set_remove A_eqdec a l) l.
  Proof.
  induction l.
  - simpl. constructor.
  - simpl. destruct (A_eqdec a a0).
    + constructor. apply sublist_refl.
    + constructor 3. apply IHl.
  Qed.

  (* Theorem erase_sublist (a:A) (l : list A) : sublist (erase l a) l.
  Proof.
  induction l.
  - simpl. constructor.
  - simpl. destruct (A_eqdec a0 a).
    + constructor. apply sublist_refl.
    + constructor 3. apply IHl.
  Qed. *)

  Theorem erase_subset (a:A) (l : list A) : incl (set_remove A_eqdec a l) l.
  Proof. apply sublist_incl. apply erase_sublist. Qed.

  Theorem remove_subset (a:A) (l : list A) : incl (remove A_eqdec a l) l.
  Proof. apply sublist_incl. apply remove_sublist. Qed.

  (* Theorem erase_subset (a:A) (l : list A) : incl (erase l a) l.
  Proof. apply sublist_incl. apply erase_sublist. Qed. *)

  Theorem sublist_erase (a:A) (l1 l2 : list A) :
    sublist l1 l2 ->
    sublist (set_remove A_eqdec a l1) (set_remove A_eqdec a l2).
  Proof.
  intro H. induction H.
  - simpl. constructor.
  - simpl. destruct (A_eqdec a a0).
    + eapply sublist_trans.
      * apply erase_sublist.
      * assumption.
    + eapply sublist_trans.
      * apply IHsublist.
      * constructor. apply sublist_refl.
  - simpl. destruct (A_eqdec a a0).
    + assumption.
    + constructor 3. assumption.
  Qed.

  Theorem sublist_remove (a:A) (l1 l2 : list A) :
    sublist l1 l2 ->
    sublist (remove A_eqdec a l1) (remove A_eqdec a l2).
  Proof.
  intro H. induction H.
  - simpl. constructor.
  - simpl. destruct (A_eqdec a a0).
    + assumption.
    + eapply sublist_trans.
      * apply IHsublist.
      * constructor. apply sublist_refl.
  - simpl. destruct (A_eqdec a a0).
    + assumption.
    + constructor 3. assumption.
  Qed.

  (* Theorem sublist_erase (a:A) (l1 l2 : list A) :
    sublist l1 l2 -> sublist (erase l1 a) (erase l2 a).
  Proof.
  intro H. induction H.
  - simpl. constructor.
  - simpl. destruct (A_eqdec a0 a).
    + eapply sublist_trans.
      * apply erase_sublist.
      * assumption.
    + eapply sublist_trans.
      * apply IHsublist.
      * constructor. apply sublist_refl.
  - simpl. destruct (A_eqdec a0 a).
    + assumption.
    + constructor 3. assumption.
  Qed. *)

  Theorem subset_cons_erase (a:A) (l : list A) :
    incl l (a :: set_remove A_eqdec a l).
  Proof.
  induction l.
  - unfold incl. simpl. tauto.
  - simpl. destruct (A_eqdec a a0) as [heq|hneq].
    + rewrite heq. apply incl_refl.
    + intros x Hin. simpl in Hin. destruct Hin.
      * simpl. tauto.
      * pose proof (IHl x H) as H0. simpl in H0. simpl. tauto.
  Qed.

  (* Theorem subset_cons_erase (a:A) (l : list A) : incl l (a :: erase l a).
  Proof.
  induction l.
  - unfold incl. simpl. tauto.
  - simpl. destruct (A_eqdec a0 a) as [heq|hneq].
    + rewrite heq. apply incl_refl.
    + intros x Hin. simpl in Hin. destruct Hin.
      * simpl. tauto.
      * pose proof (IHl x H) as H0. simpl in H0. simpl. tauto.
  Qed. *)

  Theorem erase_append_left (a:A) (l1 l2 : list A) :
    In a l1 -> erase (l1 ++ l2) a = erase l1 a ++ l2.
  Proof.
  induction l1 as [|b].
  - simpl. tauto.
  - intro H. simpl. destruct (A_eqdec b a) as [Heq|Hneq].
    + reflexivity.
    + destruct H as [Hl|Hr]; try contradiction. rewrite (IHl1 Hr).
      rewrite app_comm_cons. reflexivity.
  Qed.


  (* Facts about set_remove *)

  Lemma set_remove_comm (a b : A) (l : list A) :
    set_remove A_eqdec b (set_remove A_eqdec a l) =
    set_remove A_eqdec a (set_remove A_eqdec b l).
  Proof.
  induction l as [|c].
  - simpl. reflexivity.
  - simpl. destruct (A_eqdec a c) as [hac|hnac] eqn:Dac.
    + destruct (A_eqdec b c) as [hbc|hnbc] eqn:Dbc.
      * rewrite hac, hbc. reflexivity.
      * simpl. rewrite Dac. reflexivity.
    + destruct (A_eqdec b c) as [hbc|hnbc] eqn:Dbc.
      * simpl. rewrite Dbc. reflexivity.
      * simpl. rewrite Dbc. rewrite Dac. rewrite IHl. reflexivity.
  Qed.


  (* Facts about diff *)

  Fixpoint diff (l1 l2 : list A) :=
  match l2 with
  | []       => l1
  | a :: l2' => diff (set_remove A_eqdec a l1) l2'
  end.

  Lemma diff_nil_l : forall l : list A, diff [] l = [].
  Proof.
  simpl. induction l.
  - simpl. reflexivity.
  - simpl. exact IHl.
  Qed.

  Theorem cons_diff_of_not_mem (a:A) (l1 l2 : list A) :
    ~In a l2 -> diff (a :: l1) l2 = a :: diff l1 l2.
  Proof.
  rename l1 into l0. generalize l0 as l1. clear l0.
  induction l2 as [|b].
  - destruct l1; simpl; tauto.
  - intros l1 H. simpl. destruct (A_eqdec b a) as [heq|hneq].
    + contradict H. rewrite heq. simpl. tauto.
    + apply IHl2. intro H0. apply H. simpl. right. assumption.
  Qed.

  Theorem mem_diff_of_mem (a:A) (l1 l2 : list A) :
    In a l1 -> ~ In a l2 -> In a (diff l1 l2).
  Proof.
  rename l1 into l0. generalize l0 as l1. clear l0.
  induction l2 as [|b].
  - simpl. tauto.
  - intros l1 H H0. simpl. simpl in H0. apply IHl2.
    + assert (a <> b). auto. apply set_remove_3; assumption.
    + intro Hneg. apply H0. right. assumption.
  Qed.

  Theorem in_diff_erase_l (a b : A) (l1 l2 : list A) :
    a <> b -> In a (diff l1 l2) -> In a (diff l1 (b::l2)).
  Proof.
  rename l1 into l0. generalize l0 as l1. clear l0.
  induction l2 as [|c].
  - simpl. intros l1 H H0. apply set_remove_3; assumption.
  - intros l1 H H0. simpl. rewrite set_remove_comm.
    apply IHl2; assumption.
  Qed.

  Theorem in_diff_remove_r (a b : A) (l1 l2 : list A) :
    In a (diff l1 (remove A_eqdec b l2)) -> a = b \/ In a (diff l1 l2).
  Proof.
  rename l1 into l0. generalize l0 as l1. clear l0. induction l2 as [|c].
  - simpl. tauto.
  - destruct (A_eqdec a b) as [hab|hnab].
    + intros l1 H. left. assumption.
    + simpl. destruct (A_eqdec b c) as [hbc|hnbc].
      * intros l1 H. right. apply in_diff_erase_l.
       -- rewrite <- hbc. assumption.
       -- pose proof (IHl2 l1 H) as H0. elim H0; tauto.
      * intro l1. apply IHl2.
  Qed.

  Theorem subset_diff_erase (a:A) (l1 l2 : list A) :
    incl (diff l1 l2) (diff (a :: (set_remove A_eqdec a l1)) l2).
  Proof.
  rename l1 into l0. generalize l0 as l1. clear l0.
  induction l2.
  - simpl. apply (subset_cons_erase). 
  - intro l1. simpl. destruct (A_eqdec a0 a) as [heq|hneq].
    + rewrite <- heq. apply incl_refl.
    + rewrite set_remove_comm. apply IHl2.
  Qed.

  Theorem sublist_diff (l1 l2 l3 : list A) :
    sublist l1 l2 -> sublist (diff l1 l3) (diff l2 l3).
  Proof.
  rename l1 into l1'. rename l2 into l2'. generalize l2' as l2. generalize l1' as l1.
  clear l1' l2'. induction l3.
  - simpl. tauto.
  - intros l1 l2 H. simpl. apply IHl3. apply sublist_erase. assumption.
  Qed.

  Theorem sublist_diff_erase_of_diff (a:A) (l1 l2 : list A) :
    sublist (diff (set_remove A_eqdec a l1) l2) (diff l1 l2).
  Proof.
  apply sublist_diff. apply erase_sublist.
  Qed.

  Theorem sublist_diff_remove_of_diff (a:A) (l1 l2 : list A) :
    sublist (diff (remove A_eqdec a l1) l2) (diff l1 l2).
  Proof.
  apply sublist_diff. apply remove_sublist.
  Qed.

  Theorem subset_cons_diff (a:A) (l1 l2 : list A) :
    incl (diff (a :: l1) l2) (a :: (diff l1 l2)).
  Proof.
  rename l1 into l0. generalize l0 as l1. clear l0.
  induction l2.
  - simpl. unfold incl. tauto.
  - intro l1. simpl. destruct (A_eqdec a0 a) as [heq|hneq].
    + eapply incl_tran. 2:{ apply IHl2. }
      rewrite heq. apply subset_diff_erase.
    + apply IHl2.
  Qed.

  Theorem erase_diff_erase_sublist_of_sublist (a:A) (l1 l2 : list A) :
    sublist l1 l2 ->
    sublist (diff (set_remove A_eqdec a l2)
    (set_remove A_eqdec a l1)) (diff l2 l1).
  Proof. 
  rename l2 into l2'. generalize l2' as l2. clear l2'.
  induction l1.
  - simpl. intros l2 H. apply erase_sublist.
  - intros l2 H. simpl. destruct (A_eqdec a a0) as [heq|hneq].
    + rewrite heq. apply sublist_refl.
    + simpl. rewrite set_remove_comm.
      apply IHl1. rewrite (erase_cons a0 l1).
      apply sublist_erase. assumption.
  Qed.

  (* Theorem diff_erase_l_equal : forall a l1 l2,
    diff (set_remove A_eqdec a l1) l2 = set_remove A_eqdec a (diff l1 l2).
  Proof.
  intros a l1 l2. revert a l1. induction l2.
  - simpl. reflexivity.
  - simpl. intros a' l1. repeat rewrite IHl2. apply set_remove_comm.
  Qed.

  Theorem remove_erase_eq_remove : forall a l,
    remove A_eqdec a (set_remove A_eqdec a l) = remove A_eqdec a l.
  Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. destruct (A_eqdec a a0).
    + reflexivity.
    + simpl. destruct (A_eqdec a a0); try contradiction.
      rewrite IHl. reflexivity.
  Qed.

  Theorem erase_remove_comm : forall a1 a2 l,
    set_remove A_eqdec a1 (remove A_eqdec a2 l) =
    remove A_eqdec a2 (set_remove A_eqdec a1 l).
  Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. destruct (A_eqdec a2 a) as [Heq2|Hneq2];
    destruct (A_eqdec a1 a) as [Heq1|Hneq1].
    + rewrite IHl. rewrite Heq1, Heq2.
      rewrite remove_erase_eq_remove. reflexivity.
    + rewrite IHl. rewrite Heq2. simpl.
      destruct (A_eqdec a a); try contradiction. reflexivity.
    + rewrite Heq1. simpl.
      destruct (A_eqdec a a); try contradiction. reflexivity.
    + simpl. destruct (A_eqdec a1 a); try contradiction.
      destruct (A_eqdec a2 a); try contradiction.
      rewrite IHl. reflexivity.
  Qed.

  Theorem diff_remove_l_equal : forall a l1 l2,
    diff (remove A_eqdec a l1) l2 = remove A_eqdec a (diff l1 l2).
  Proof.
  induction l2.
  - simpl. reflexivity.
  - simpl. repeat rewrite diff_erase_l_equal.
    rewrite IHl2. apply erase_remove_comm.
  Qed. *)

  Theorem notin_diff_remove_r_eq : forall a l1 l2,
    ~ In a l1 -> diff l1 (remove A_eqdec a l2) = diff l1 l2.
  Proof.
  intros a l1 l2. revert l1. induction l2.
  - simpl. reflexivity.
  - intros l1 H. simpl. destruct (A_eqdec a a0) as [Heq|Hneq].
    + rewrite IHl2; try assumption. rewrite <- Heq.
      rewrite erase_of_not_mem; try assumption. reflexivity.
    + simpl. rewrite IHl2; try reflexivity.
      intro Hctr. contradict H. apply (set_remove_1 _ _ _ _ Hctr).
  Qed.

  Theorem remove_diff_remove_sublist_of_sublist (a:A) (l1 l2 : list A) :
    sublist l1 l2 ->
    sublist (diff (remove A_eqdec a l2)
    (remove A_eqdec a l1)) (diff l2 l1).
  Proof.
  intro H. rewrite notin_diff_remove_r_eq; try apply remove_In.
  apply sublist_diff_remove_of_diff.
  Qed.


  (* Facts about inter *)

  Fixpoint inter (l1 l2 : list A) : list A :=
  match l1 with
  | []     => []
  | a :: l => if in_dec A_eqdec a l2 then a :: inter l l2
              else inter l l2
  end.

  Theorem in_both_inter (a:A) (l1 l2 : list A) :
    In a l1 -> In a l2 -> In a (inter l1 l2).
  Proof.
  rename l2 into l0. generalize l0 as l2. clear l0.
  induction l1 as [|b l].
  - simpl. tauto.
  - intros l2 H H0. simpl in H. destruct H.
    * rewrite H. simpl. destruct (in_dec A_eqdec a l2).
      + simpl. left. reflexivity.
      + contradiction.
    * simpl. pose proof (IHl l2 H H0) as H1. destruct (in_dec A_eqdec b l2).
      + simpl. right. assumption.
      + assumption.
  Qed.

  Theorem mem_tail_of_ne_head {def : A} {a : A} : forall {l : list A},
    In a l -> a <> hd def l -> In a (tl l).
  Proof.
  intros l H H0. destruct l as [|b].
  - contradict H.
  - simpl in H, H0. apply not_eq_sym in H0. simpl. tauto.
  Qed.

End ListUtilities.

Unset Implicit Arguments.

