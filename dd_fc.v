
(* derivation trees without the conclusion as part of the type,
  so more like Isabelle trees *)

Require Export List.
Set Implicit Arguments.
Export ListNotations.

Require Import Coq.Program.Equality. (* for dependent induction/destruction *)

Require Import genT gen ddT.
Require Import PeanoNat.

Inductive derrec_fc X rules (prems : X -> Type) : Type := 
  | fcI : forall concl, derrec rules prems concl -> derrec_fc rules prems.

Inductive dersrec_fcs X rules (prems : X -> Type) : Type := 
  | fcsI : forall concls, dersrec rules prems concls -> dersrec_fcs rules prems.

Inductive in_nextup_fc X (rules : rlsT X) prems :
    relationT (derrec_fc rules prems) :=
  | in_nextup_fcI : forall concln concl 
    (dn : derrec rules prems concln) (d : derrec rules prems concl),
    in_nextup dn d -> in_nextup_fc (fcI dn) (fcI d)
  .

Lemma AccT_in_nextup_fc X rules prems dt: AccT (@in_nextup_fc X rules prems) dt.
Proof. destruct dt. revert d. revert concl.
eapply derrec_rect_mut_all.
- intros. apply AccT_intro. intros y iny.
dependent destruction iny. inversion i.  inversion X0.
- intros * apd. apply AccT_intro.  intros y iny.
dependent destruction iny. inversion i. dependent destruction X0.
exact (allP_all_in_d apd X1). Qed.

Fixpoint dersrec_trees X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => []
    | dlCons d ds => fcI d :: dersrec_trees ds
  end.

Definition nextup W rules prems (dt : @derrec_fc W rules prems) :=
  match dt with 
    | fcI (dpI _ _ _ _) => []
    | fcI (derI _ _ ds) => dersrec_trees ds
  end.

Fixpoint derrec_fc_concl X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => derrec_concl d
  end.

Fixpoint dersrec_fc_concls X rules prems 
  (ders : @dersrec_fcs X rules prems) :=
  match ders with 
    | fcsI ds => dersrec_concls ds
  end.

(* note, this includes case where the tree is simply a premise *)
Inductive botRule_fc X rules prems (der : @derrec_fc X rules prems) : rlsT X :=
  | botRule_fcI : botRule_fc der 
    (map (@derrec_fc_concl _ _ _) (nextup der)) (derrec_fc_concl der).

(* this fails, d has type "derrec rules prems x", but x not in scope
Fixpoint derrec_of_fc X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => d
  end.
  *)

(* while we can't get something of type derrec rules prems _
  from something of type derrec_fc ..., we can get it and then
  apply any function to it whose result type doesn't involve the conclusion *)
Fixpoint derrec_fc_size X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => derrec_size d
  end.

Fixpoint dersrec_fc_size X rules prems 
  (ders : @dersrec_fcs X rules prems) :=
  match ders with 
    | fcsI ds => dersrec_size ds
  end.

Fixpoint derrec_fc_height X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => derrec_height d
  end.

Fixpoint dersrec_fc_height X rules prems 
  (ders : @dersrec_fcs X rules prems) :=
  match ders with 
    | fcsI ds => dersrec_height ds
  end.

Lemma der_fc_concl_eq: forall X (rules : rlsT X) prems concl 
  (d : derrec rules prems concl), derrec_fc_concl (fcI d) = concl.
Proof. simpl. apply der_concl_eq. Qed.

Lemma dersrec_trees_concls_eq X rules prems ps (ds : dersrec rules prems ps) :
  map (@derrec_fc_concl X rules prems) (dersrec_trees ds) = ps.
Proof. induction ds.  simpl. reflexivity.
simpl. rewrite (der_concl_eq d). rewrite IHds. reflexivity. Qed.

Lemma der_der_fc X rules prems (der : @derrec_fc X rules prems) :
  derrec rules prems (derrec_fc_concl der).
Proof. destruct der. simpl. rewrite der_concl_eq. exact d. Qed. 

Lemma ders_ders_fcs X rules prems (ders : @dersrec_fcs X rules prems) :
  dersrec rules prems (dersrec_fc_concls ders).
Proof. destruct ders. simpl. rewrite ders_concls_eq. exact d. Qed. 

Lemma in_drs_trees: forall X rules prems cs ds c (d : derrec rules prems c),
  in_dersrec d ds -> InT (fcI d) (@dersrec_trees X rules prems cs ds).
Proof. intros. induction X0 ; simpl. 
apply InT_eq.  apply InT_cons. assumption. Qed. 

Lemma in_trees_drs: forall X rules prems cs ds c (d : derrec rules prems c),
  InT (fcI d) (@dersrec_trees X rules prems cs ds) -> in_dersrec d ds.
Proof. induction cs ; intro ; dependent inversion ds ; simpl ; intros.
inversion X0.
(* inversion X0. injection H2. gives existT equality *)
subst.  dependent destruction X0. apply in_dersrec_hd.
apply in_dersrec_tl. apply IHcs. assumption. Qed.

Lemma der_botRule W rules (dt : derrec_fc rules emptyT) :
  {ps : list W & {c : W & rules ps c & botRule_fc dt ps c}}.
Proof. destruct dt. destruct d. destruct e.
exists ps. exists concl. exact r.
pose botRule_fcI.
specialize (b W rules emptyT (fcI (derI concl r d))).
simpl in b. rewrite dersrec_trees_concls_eq in b. exact b. Qed.

Lemma botRule_fc_concl W rules prems ps (c : W) (dt : derrec_fc rules prems) :
  botRule_fc dt ps c -> derrec_fc_concl dt = c.
Proof. intro br. destruct br. reflexivity. Qed.

Lemma botRule_fc_rules W rules ps (c : W) (dt : derrec_fc rules emptyT) :
  botRule_fc dt ps c -> rules ps c.
Proof. intro br. destruct br. destruct dt.
rewrite (der_fc_concl_eq d).
destruct d. destruct e. simpl.
rewrite (dersrec_trees_concls_eq d). exact r.  Qed.

Lemma botRule_fc_drs W rules prems ps (c : W) (dt : derrec_fc rules prems) :
  botRule_fc dt ps c -> dersrec rules prems ps.
Proof. intro br. destruct br. destruct dt.
destruct d.  simpl. apply dlNil.
simpl.  rewrite (dersrec_trees_concls_eq d). exact d.  Qed.

Lemma botRule_fc_ps W rules prems ps (c : W) (dt : derrec_fc rules prems) :
  botRule_fc dt ps c -> map (@derrec_fc_concl W rules prems) (nextup dt) = ps.
Proof. intro br. destruct br. destruct dt. reflexivity. Qed.

Lemma in_nextup_eqv W rules prems (concln concl : W) 
  (dtn : derrec rules prems concln) (dt : derrec rules prems concl) :
  iffT (in_nextup dtn dt) (InT (fcI dtn) (nextup (fcI dt))).
Proof. apply pair ; intros.
- destruct X. destruct i. simpl. exact (in_drs_trees i0).
- simpl in X. destruct dt. inversion X. 
  apply in_trees_drs in X.
  eapply in_nextupI. apply is_nextupI. exact X. Qed.

Definition in_nextup_nu W rules prems concln concl dtn dt :=
  iffT_D1 (@in_nextup_eqv W rules prems concln concl dtn dt).
Definition nextup_in_nu W rules prems concln concl dtn dt :=
  iffT_D2 (@in_nextup_eqv W rules prems concln concl dtn dt).

Lemma in_nextup_fc_eqv W rules prems (dtn dt : @derrec_fc W rules prems) :
  iffT (in_nextup_fc dtn dt) (InT dtn (nextup dt)).
Proof. apply pair ; intros.
- destruct X. exact (in_nextup_nu i).
- destruct dtn. destruct dt. apply in_nextup_fcI. exact (nextup_in_nu _ X).
Qed.

Definition in_nextup_fc_nu W rules prems dtn dt :=
  iffT_D1 (@in_nextup_fc_eqv W rules prems dtn dt).
Definition nextup_in_nu_fc W rules prems dtn dt :=
  iffT_D2 (@in_nextup_fc_eqv W rules prems dtn dt).

(* converse to this requires is_nextup (dlNil rules prems) (dpI _ _ _ _) *)
Lemma is_nextup_ndt W rules prems concls (concl : W) 
  (dts : dersrec rules prems concls) 
  (dt : derrec rules prems concl) :
  is_nextup dts dt -> nextup (fcI dt) = dersrec_trees dts.
Proof. unfold nextup. intros.  destruct X. reflexivity. Qed.

Lemma fcI_inj: forall X rules prems concl (d1 : @derrec X rules prems concl) d2,
  fcI d1 = fcI d2 -> d1 = d2.
Proof. intros.  (* injection H gives existT equality *)
  dependent destruction H. reflexivity. Qed.

(* this doesn't work - type of Q 
Goal forall X rules prems Q cs (ds : @dersrec X rules prems cs),
  allPder Q ds -> Forall2T Q cs (dersrec_trees ds).
*)

