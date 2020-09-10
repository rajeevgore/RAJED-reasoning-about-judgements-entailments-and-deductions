Require Import PeanoNat Lt.
Require Import Lia.

Theorem strong_induction_Prop:
forall P : nat -> Prop,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
  intros P Hind.
  assert ((forall n k, k <= n -> P k) -> forall n, P n) as Hass.
    intros HH n. eapply HH. eapply le_n.
  eapply Hass. clear Hass.
    induction n; intros k Hk. eapply PeanoNat.Nat.le_0_r in Hk.
    subst. eapply Hind. intros k Hk. inversion Hk.

    eapply Lt.le_lt_or_eq in Hk. destruct Hk.
    eapply IHn. inversion H. apply le_n. subst. 
    apply Le.le_Sn_le in H1.
    assumption.
    subst. apply Hind. firstorder.
Qed.

Theorem strong_induction:
forall P : nat -> Type,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
  intros P Hind.
  assert ((forall n k, k <= n -> P k) -> forall n, P n) as Hass.
    intros HH n. eapply HH. eapply le_n.
  eapply Hass. clear Hass.
  induction n; intros k Hk.
    eapply PeanoNat.Nat.le_0_r in Hk.
    subst. eapply Hind.
    intros k Hk.
    apply PeanoNat.Nat.nlt_0_r in Hk.
    contradiction.
    eapply Compare_dec.le_lt_eq_dec in Hk. 
    destruct Hk.
    eapply IHn. inversion l. apply le_n. subst. 
    apply Le.le_Sn_le in H0.
    assumption.
    subst. apply Hind. firstorder.
Qed.

Locate well_founded.
Print well_founded.

Require Import Lia.

SearchAbout le S lt.

Require Import Wf.
Require Import Relation_Operators.
Require Import Lexicographic_Product.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import Wf_nat.


Definition dep2 := sigT (A:=nat) (fun a => nat).

Definition mk2 : nat*nat -> dep2.
intros (p,q).
exists p.
exact q.
Defined.

Definition lt_pq :dep2->dep2->Prop :=
(lexprod nat (fun a => nat) Peano.lt (fun a:nat =>Peano.lt)).

Definition le_pq (a b : dep2) : Prop :=
  lt_pq a b \/ a = b.

Lemma wf_lexprod : well_founded lt_pq.
unfold lt_pq;apply wf_lexprod.
apply lt_wf.
intro n.
apply lt_wf.
Qed.

Definition lt_mine : (nat*nat) -> (nat*nat) -> Prop :=
  fun a b => lt_pq (mk2 a) (mk2 b).

Definition le_mine : (nat*nat) -> (nat*nat) -> Prop :=
  fun a b => le_pq (mk2 a) (mk2 b).


Require Import Inverse_Image.

Lemma wf_lt_mine : well_founded lt_mine.
Proof.
  unfold lt_mine.
  eapply wf_inverse_image.
  apply wf_lexprod.
Qed.

SearchAbout "induction" well_founded.

Definition induction_lt_mine := (well_founded_induction wf_lt_mine).

(* Not good, because the last "P x" occurrence should be P (S x) for some kind of successor thing in this context - but which thing? Not appropriate for this context.
Definition induction_le_mine :=
  forall P : nat * nat -> Set,
       (P (0,0)) -> 
       (forall x : nat * nat, (forall y : nat * nat, le_mine y x -> P y) -> P x) ->
       forall a : nat * nat, P a.
*)

Parameter P : (nat*nat) -> Set.

SearchAbout "induction" nat.

(*
Lemma test2 : forall (n : nat), n = S n.
Proof.
  intros n.
  induction (lt_wf n).

  Print lt_wf.
  Print 

 *)

Definition odd (n : nat) := exists k, n = 2*k + 1.
Definition even (n : nat) := exists k, n = 2*k.

Lemma test3 : forall (a : nat), odd a \/ even a.
Proof.
  intros a.
  induction (lt_wf a) as [n _ IH].
Admitted.


Lemma test2 : forall (a : nat * nat), odd (fst a) \/ even (fst a).
Proof.
  induction a using induction_lt_mine.
  destruct a as [n m]. simpl fst.
  destruct n. right. unfold even. exists 0. auto.
  destruct (H (n,m)). econstructor. firstorder.
  simpl in H0. right. unfold odd in H0. unfold even.
  destruct H0. exists (x+1). firstorder.
  left.
Admitted.

Lemma test1 : forall a, P a -> (P a -> true = true).
Proof.
  intros a.
  induction a using induction_lt_mine.
Admitted.


  


(* Left it here 31/01/20.

Use induction_lt_mine as induction principle.
Write a test cases to make sure it'll work properly. 
Start with something based off nats then something based of derivations.


https://coq-club.inria.narkive.com/VWS50VZQ/adding-strong-induction-to-the-standard-library
https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.induction-using
https://coq.github.io/doc/master/stdlib/Coq.Structures.OrdersEx.html#PairOrderedType
https://coq-club.inria.narkive.com/7Mts7wuN/how-to-show-lexicographic-product-of-three-well-founded-sets-is-well-founded
https://coq.inria.fr/library/Coq.Arith.Wf_nat.html
https://coq.github.io/doc/master/stdlib/Coq.Wellfounded.Lexicographic_Product.html
https://coq.inria.fr/distrib/current/stdlib/Coq.Relations.Relation_Operators.html#lexprod
https://stackoverflow.com/questions/42520130/lexicographical-comparison-of-tuples-of-nats
https://coq.inria.fr/library/Coq.Init.Wf.html
http://color.inria.fr/doc/CoLoR.Util.Pair.LexOrder.html
https://coq.github.io/doc/master/stdlib/Coq.Arith.Compare.html
https://coq.inria.fr/library/Coq.Structures.OrderedType.html
https://coq.github.io/doc/master/stdlib/Coq.Structures.OrderedTypeEx.html
https://coq.github.io/doc/master/stdlib/Coq.Structures.OrderedType.html

*)
  



  unfold well_founded.
  intros [n m].
  simpl.



Lemma lem : forall n m,
    n < (S m) -> (n = m \/ n < m).
Proof.
  intros. lia.
Qed.

Theorem thm : well_founded lt.
Proof.
  unfold well_founded.
  induction a. constructor.
  intros y Hy. inversion Hy.
  constructor. intros y Hy.
  apply lem in Hy. destruct Hy.
  subst. assumption.
  eapply Acc_inv. apply IHa. assumption.
Qed.

Inductive mlex : (nat * nat) -> (nat * nat) -> Prop :=
| mlexc1 a b n m : a < n -> mlex (a,b) (n,m)
| mlexc2 a b n m : a = n -> b < m -> mlex (a,b) (n,m).
Print Acc.

Theorem thm2 : well_founded mlex.
Proof.
  unfold well_founded.
  intros a. destruct a as [a b].
  revert b.
  induction a; intros b.
  + induction b. constructor. intros [n m] H.
    inversion H. subst. inversion H1. subst. inversion H5.
    constructor. intros [n m] H. inversion H. subst.
    inversion H1. subst.

    inversion H5. subst. apply IHb.
    subst. eapply Acc_inv. apply IHb.
    constructor 2. auto. apply H1.

  + induction b. econstructor.
    intros [n m] H. inversion H. subst.
    inversion H1. subst. eapply IHa.
    subst. eapply Acc_inv. apply IHa.
    constructor 1. apply H2.
    subst. inversion H5.

    inversion IHb as [H].
    constructor. intros [n m] H2.
    inversion H2. subst. inversion H1.
    subst.  eapply IHa.
    subst. specialize (IHa m).
    eapply Acc_inv. apply IHa. constructor. apply H3.
    subst. inversion H6. subst. apply IHb.
    subst. eapply Acc_inv. apply IHb.
    constructor 2. auto. apply H1.
    Unshelve. auto.
Qed.
Print Assumptions thm2.

Print well_founded_induction.
Check (well_founded_induction thm2).

Lemma attempt_to_use_ind : forall (P : (nat * nat) -> Set), forall n,
      P n.
Proof.
  intros P n.
  induction n using (well_founded_induction thm2).
Abort.

Check mlex_ind.

Lemma mlex_induction_pre : forall (P : (nat * nat) -> Set),
   forall a' b', P (0,0) ->
    (forall a b, ( (forall n m, mlex (n,m) (a,b) -> P (n,m)) -> P (a,b))) ->
    P (a',b').
Proof.
  intros P a b H1 H2.
  remember (a,b) as c.
  revert Heqc. revert b. revert a.
  induction c using (well_founded_induction thm2).
  intros a b Heqc.
  subst. apply H2.
  intros n m Hnm.
  eapply H. 2 : reflexivity.
  apply Hnm.
Qed.

Lemma mlex_induction_pre' : forall (P : (nat * nat) -> Set),
   forall a' b', 
    (forall a b, ( (forall n m, mlex (n,m) (a,b) -> P (n,m)) -> P (a,b))) ->
    P (a',b').
Proof.
  intros P a b H2.
  remember (a,b) as c.
  revert Heqc. revert b. revert a.
  induction c using (well_founded_induction thm2).
  intros a b Heqc.
  subst. apply H2.
  intros n m Hnm.
  eapply H. 2 : reflexivity.
  apply Hnm.
Qed.

Lemma mlex_induction' : forall (P : (nat * nat) -> Set),
    (forall a b, ( (forall n m, mlex (n,m) (a,b) -> P (n,m)) -> P (a,b))) ->
   forall a b, P (a,b).
Proof.  
  intros. apply mlex_induction_pre'. auto. 
Qed.

Lemma lem1 : forall P,
    (forall b, ( (forall a, a < b -> P a ) -> P b)) ->
    P 0.
Proof.
  intros P H.
  apply H.
  intros a H2. unfold lt in H2.
  Print le. Search le -max -min.
  apply Le.le_n_0_eq in H2. discriminate.
Qed.

Lemma lem2 : forall P,
    (forall b, ( (forall a, a <= b -> P a ) -> P b)) ->
    P 0.
Proof.
  intros P H.
  apply H.
  intros a H2.
  apply Le.le_n_0_eq in H2. subst.
Abort.

Print well_founded_induction.


Lemma testing : forall (P : (nat * nat) -> Prop),
     (forall a b, ( (forall n m, mlex (n,m) (a,b) -> P (n,m)) -> P (a,b))) ->
    P (0,0).
Proof.
  intros .
  apply H. intros.
  inversion H0.
  subst. inversion H2.
  subst. inversion H6.
Qed.

Lemma nat_induction' : forall (P : nat -> Prop),
    (forall m, (forall n, n < m -> P n) -> P m) ->
   forall a, P a.
Proof.  
  intros. apply H.
  intros n H2.
  apply H. intros m Hm.
  induction a. inversion H2.
  inversion H2. subst. 
Abort.
     (*
  induction  n; intros H2.
  
  apply mlex_induction_pre'. auto. 
Qed.
      *)
     
Print well_founded.

Print lt.
Locate lt.
Search (?a <= ?a).

Lemma mlex_induction : forall (P : (nat * nat) -> Set),
   P (0,0) ->
    (forall a b, ( (forall n m, mlex (n,m) (a,b) -> P (n,m)) -> P (a,b))) ->
   forall a b, P (a,b).
Proof.  
  intros. apply mlex_induction_pre. auto. auto.
Qed.


Require Import Coq.Structures.OrdersEx.

Module test_module2 := PairOrderedType Nat_as_DT Nat_as_DT.
Module test_module := PairOrderedType Nat_as_OT Nat_as_OT.

Print test_module.
Print test_module2.

(*
Module
test_module
 : Sig
     Definition t : Type.
     Definition eq : Relation_Definitions.relation (nat * nat).
     Definition eq_equiv : RelationClasses.Equivalence eq.
     Definition eq_dec : forall x y : nat * nat, {eq x y} + {~ eq x y}.
     Definition lt : Relation_Definitions.relation (nat * nat).
     Parameter lt_strorder : RelationClasses.StrictOrder lt.
     Parameter lt_compat :
       Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) lt.
     Definition compare : nat * nat -> nat * nat -> comparison.
     Parameter compare_spec : forall x y : nat * nat, CompSpec eq lt x y (compare x y).
   End
:= (PairOrderedType Nat_as_OT Nat_as_OT)

Module
test_module2
 : Sig
     Definition t : Type.
     Definition eq : Relation_Definitions.relation (nat * nat).
     Definition eq_equiv : RelationClasses.Equivalence eq.
     Definition eq_dec : forall x y : nat * nat, {eq x y} + {~ eq x y}.
     Definition lt : Relation_Definitions.relation (nat * nat).
     Parameter lt_strorder : RelationClasses.StrictOrder lt.
     Parameter lt_compat :
       Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) lt.
     Definition compare : nat * nat -> nat * nat -> comparison.
     Parameter compare_spec : forall x y : nat * nat, CompSpec eq lt x y (compare x y).
   End
:= (PairOrderedType Nat_as_DT Nat_as_DT)
 *)
Print lexprod.

Import test_module.

Print test_module.
Locate lt.

Infix "=" := eq (at level 70, no associativity) : test_module_scope.
Infix "<" := lt (at level 70, no associativity) : test_module_scope.

Open Scope test_module_scope.
Locate "=".
Print lt.
SearchAbout well_founded.
Print symprod.

(*
Lemma Acc_fst_0 : forall b, Acc lt (0,b).
  induction b. econstructor.
  intros y Hy.
  inversion y as [a b].
  inversion Hy. inversion H. inversion H.
  inversion H1.
  econstructor. intros [n m] H.
  inversion H.
  inversion H0.
  inversion H0.
  inversion H1. simpl in *.
  subst. inverison H0.
  inversion H0.  
  
 *)
Definition lt_nat := Coq.Arith.PeanoNat.Nat.lt.
Definition lt_nat2 := PeanoNat.Nat.compare.

Lemma lt_fst_0 : forall a b m,
    (a,b) < (0,m) -> a = 0.
Proof.
  intros a b m H.
  inversion H as [H1 | H1].
  inversion H1. inversion H1 as [H2 H3].
  inversion H2. auto.
Qed.

Locate compare.
Print lt_nat2.
Print  PeanoNat.Nat.compare.




Lemma lt_inv : forall a b n m,
    (a,b) < (n,m) ->  ((a=n) /\ (b < m)%nat ) \/ (lt_nat a n).
Proof.
  firstorder.
Qed.

(*
Lemma lt_inv : forall a b n m,
    (a,b) < (n,m) ->  ((a=n) * ((lt_nat2 b m) = Lt)) + {lt_nat2 a n = Lt}.
Proof.
  intros a b n m H.
  Print lt.
  Print Relation_Definitions.relation.
  inversion H.
  case_eq (compare (a,b) (n,m)); intros H2.
  *)


Lemma not_lt_0 : forall a b, ~ (a,b) < (0,0).
Proof.
  intros a b H.
  inversion H as [H1 | H1].
  inversion H1. inversion H1 as [H2 H3].
  inversion H3.
Qed.

Lemma lt_snd : forall a m n,
    (m < n)%nat -> (a,m) < (a,n).
Admitted.

Lemma Acc_fst_0 : forall b, Acc lt (0,b).
Proof.
  induction b.
  econstructor. intros [a b] H.
  apply not_lt_0 in H. contradiction.

  econstructor. intros [n m] H.
  inversion IHb as [IH].
  inversion H as [H1 | H1].
  inversion H1. inversion H1 as [H2 H3].
  inversion H2 as [H4]. simpl in H4. subst.
  inversion H3 as [|H4 H5 H6]. subst.  assumption.
  simpl in *. subst.
  eapply IH.
  apply lt_snd.
  apply Lt.lt_S_n.
  apply Lt.le_lt_n_Sm. assumption.
Qed.

(*
Lemma lt_snd_0 : forall n, Acc lt (n,0).
Proof.
  induction n using (well_founded_induction _).
  econstructor. intros [a b] H2.
  apply lt_inv in H2. destruct H2 as [[H3 H4] | H3].
  inversion H4.
  
  econstructor. intros [c d] Hc.
  inversion 
  apply not_lt_0 in H2. contradiction.
  econstructor. intros [a b] H.
  apply lt_inv in H. destruct H as [[H1 H2] | H1].
  inversion H2.
  


  induction n using PeanoNat.Nat.lt_wf.  induction n.
  econstructor. intros [a b] H.
  apply not_lt_0 in H. contradiction.
  econstructor. intros [a b] H.
  apply lt_inv in H. destruct H as [[H1 H2] | H1].
  inversion H2.
  *)

Lemma well_founded_lt : well_founded lt.
Proof.
  Search well_founded.
  SearchAbout well_founded.
  SearchAbout sum.
SearchAbout relation_disjunction.
  unfold lt.


  unfold well_founded.
  intros [n m].
  revert m.
  induction n using (well_founded_induction _); intros m.
  econstructor. intros [a b] H2.
  apply lt_inv in H2. destruct H2 as [[H3 H4] | H3].
  subst.
  assert ( (b < m)%nat -> Acc lt (x,m)   -> Acc lt (x,b)) as Hass.
  admit. apply Hass. assumption.
  apply H. 
  apply le_n.

  apply H.
  admit.
  Unshelve. 
  apply H3.
  Unshelve. unfold lt_nat.
  firstorder.
Qed.

  SearchAbout well_founded PeanoNat.Nat.lt.
  apply H. apply H2.
  
  induction n; econstructor.
  + intros [a b] H.
    apply lt_fst_0 in H.
    subst. apply Acc_fst_0.
  + intros [a b] H.
    eapply lt_inv in H.
    destruct H as [[H1 H2] | H1].
    subst. econstructor.
    intros [c d] H.
    eapply lt_inv in H.
    destruct H as [[H4 H5] | H4].
    subst.
    
    inversion H as [H3| H3].
    
    inversion H as [[H11 H22] | H11].


    

Module test_module := PairOrderedType Nat_as_OT Nat_as_OT.

Print test_module.

Import test_module.

Print test_module.

Infix "=" := eq (at level 70, no associativity) : test_module_scope.
Infix "<" := lt (at level 70, no associativity) : test_module_scope.

Open Scope test_module_scope.
Locate "=".
Print lt.

(*
Lemma Acc_fst_0 : forall b, Acc lt (0,b).
  induction b. econstructor.
  intros y Hy.
  inversion y as [a b].
  inversion Hy. inversion H. inversion H.
  inversion H1.
  econstructor. intros [n m] H.
  inversion H.
  inversion H0.
  inversion H0.
  inversion H1. simpl in *.
  subst. inverison H0.
  inversion H0.  
  
 *)
Definition lt_nat := Coq.Arith.PeanoNat.Nat.lt.

Lemma lt_fst_0 : forall a b m,
    (a,b) < (0,m) -> a = 0.
Proof.
  intros a b m H.
  inversion H as [H1 | H1].
  inversion H1. inversion H1 as [H2 H3].
  inversion H2. auto.
Qed.

Lemma Acc_fst_0 : forall b, Acc lt (0,b).
Proof.
  induction b.
  econstructor. intros [a b] H.
Locate lt.
  Lemma lt_inv : forall a b n m,
    (a,b) < (n,m) -> {lt_nat a n} + {a=n * lt_nat b m}.
  
Admitted.
  
Lemma well_founded_le : well_founded lt.
Proof.
  unfold well_founded.
  intros [n m].
  induction n; econstructor.
  + intros [a b] H.
    apply lt_fst_0 in H.
    subst. apply Acc_fst_0.
    


    
    inversion H as [H1 | H2].
    inversion H1.
    inversion H2 as [H3 H4].
    inversion H3. simpl in *.
    subst. 
    Print RelationPairs.RelProd.
  induction a.


Definition my_le := compare.

Lemma test : forall (a : nat * nat), True.
Import (PairOrderedType Nat_as_OT Nat_as_OT).

Print Nat_as_OT.



apply H. apply Hnm. 
  induction n using (well_founded_induction thm2).

  pose proof (well_founded_induction thm2 P) as H2. intros x IHx.
  
  pose proof (well_founded_induction thm2 P) as H2.
  induction n using (well_founded_induction thm2).

  destruct H1.


  constructor. intros [n m] H.
  inversion H; subst.
  + inversion H1. subst. apply IHa.
    subst. eapply Acc_inv. eapply IHa.
    constructor. apply H2.
  + eapply Acc_inv. eapply IHa. constructor 2. intros [c d] Hd.
    
    destruct H1.
    ++ 
  constructor. intros. inversion H.
  + induction b. constructor.
    intros [a b] H.
    inversion H. subst. inversion H1.
    subst. inversion H5.
    constructor. intros [n m] H.
    inversion H; subst.
    inversion H1.
    inversion H5. subst.  exact IHb.
    subst. eapply Acc_inv.
    exact IHb.
    constructor 2. auto.
    apply H1.
  + induction b. constructor.
    intros [n m] H. inversion H.
    subst. inversion H1.
    subst. eapply IHa.
    subst.
    eapply Acc_inv. eapply (IHa 0).
    constructor. eapply H2.
    subst. inversion H5.
    

    destruct H2.
    destruct H1.
    eapply Acc_inv. eapply IHa.
    inversion H. subst.

    
    eapply Acc_inv. exact IHb.
    
    eapply (@Acc_inv _ mlex) in IHb.
    exact IHb.
    
    constructor. intros 
    eapply Acc_inv in IHb.
    eexact IHb.

    constructor. intros [n m] H.
    inversion H. subst.
    inversion H1. subst. 
    inversion H5. subst.
    constructor. intros [a b] Hb.
    inversion Hb. subst. inversion H1. subst.
  
