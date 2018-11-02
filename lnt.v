
Require Export List.
Set Implicit Arguments.
Export ListNotations.

Parameter PropVars : Set.

Lemma rappl: forall (A B : Prop), A -> (A -> B) -> B.
Proof.  tauto.  Qed.

Lemma appl: forall (A B : Prop), (A -> B) -> A -> B.
Proof.  tauto.  Qed.

(* definition of Propositional Formulas, parameterised over prim prop set *)
Inductive PropF (V : Set): Set :=
 | Var : V -> PropF V
 | Not : PropF V -> PropF V
 | Imp : PropF V -> PropF V -> PropF V
 | And : PropF V -> PropF V -> PropF V
 | Or : PropF V -> PropF V -> PropF V
 | WBox : PropF V -> PropF V
 | WDia : PropF V -> PropF V
 | BBox : PropF V -> PropF V
 | BDia : PropF V -> PropF V
.

Inductive Seq (X : Set) : Set :=
  | mkseq : X -> X -> Seq X.

Check Seq_rect.
Check Seq_ind.
Check Seq_rec.

Print Seq_rect.
Print Seq_ind.
Print Seq_rec.

(* fails Error: Large non-propositional inductive types must be in Type
Inductive S3eq (X : Type) : Set :=
  | mks3eq : list X -> list X -> S3eq X.
*)

Check (Seq (list (PropF PropVars))).

Inductive seqrule (V : Set) : 
  list (Seq (list (PropF V))) -> Seq (list (PropF V)) -> Prop :=
  | Id : forall A Gamma Delta,
    In A Gamma -> In A Delta -> seqrule [] (mkseq Gamma Delta)
  | AndR : forall A B Gamma Delta,
    seqrule [mkseq Gamma (A :: Delta); mkseq Gamma (B :: Delta)]
      (mkseq Gamma ((And A B) :: Delta))
  | OrL : forall A B Gamma Delta,
    seqrule [mkseq (A :: Gamma) Delta; mkseq (B :: Gamma) Delta]
      (mkseq ((Or A B) :: Gamma) Delta)
  | AndL : forall A B Gamma Delta,
    seqrule [mkseq (A :: B :: Gamma) Delta] (mkseq ((And A B) :: Gamma) Delta)
  | OrR : forall A B Gamma Delta,
    seqrule [mkseq Gamma (A :: B :: Delta)] (mkseq Gamma ((Or A B) :: Delta))
  | ExchR : forall A B Gamma Delta1 Delta2,
    seqrule [mkseq Gamma (Delta1 ++ A :: B :: Delta2)]
     (mkseq Gamma (Delta1 ++ B :: A :: Delta2))
  | ExchL : forall A B Gamma1 Gamma2 Delta,
    seqrule [mkseq (Gamma1 ++ A :: B :: Gamma2) Delta]
     (mkseq (Gamma1 ++ B :: A :: Gamma2) Delta)
.

(* note, this doesn't work Type replaced by Prop,
  although the actual version used allows prems : X -> Prop 
Reset derrec.

Inductive derrec (X : Set) (rules : list X -> X -> Prop) :
  (X -> Type) -> X -> Prop := 
  | dpI : forall prems concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps prems concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec (X : Set) (rules : list X -> X -> Prop) :
  (X -> Type) -> list X -> Prop :=
  | dlNil : forall prems, dersrec rules prems []
  | dlCons : forall prems seq seqs, 
    derrec rules prems seq -> dersrec rules prems seqs ->
    dersrec rules prems (seq :: seqs)
    .
    *)

Inductive derrec (X : Set) (rules : list X -> X -> Prop) (prems : X -> Prop) :
  X -> Prop := 
  | dpI : forall concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec (X : Set) (rules : list X -> X -> Prop) (prems : X -> Prop) :
  list X -> Prop :=
  | dlNil : dersrec rules prems []
  | dlCons : forall seq seqs, 
    derrec rules prems seq -> dersrec rules prems seqs ->
    dersrec rules prems (seq :: seqs)
    .

Scheme derrec_ind_mut := Induction for derrec Sort Prop
with dersrec_ind_mut := Induction for dersrec Sort Prop.

Check derrec_ind_mut.
Check dersrec_ind_mut.

Inductive derl (X : Set) (rules : list X -> X -> Prop) :
  list X -> X -> Prop := 
  | asmI : forall p, derl rules [p] p
  | dtderI : forall pss ps concl, rules ps concl ->
    dersl rules pss ps -> derl rules pss concl
with dersl (X : Set) (rules : list X -> X -> Prop) :
  list X -> list X -> Prop := 
  | dtNil : dersl rules [] []
  | dtCons : forall ps c pss cs,
    derl rules ps c -> dersl rules pss cs -> dersl rules (ps ++ pss) (c :: cs)
  . 

Scheme derl_ind_mut := Induction for derl Sort Prop
with dersl_ind_mut := Induction for dersl Sort Prop.

Check derl_ind_mut.
Check dersl_ind_mut.

Inductive dercl (X : Set) (rules : list X -> X -> Prop) :
  list X -> X -> Prop := 
  | casmI : forall p, dercl rules [p] p
  | dtcderI : forall pss ps concl, rules ps concl ->
    dercsl rules pss ps -> dercl rules (concat pss) concl
with dercsl (X : Set) (rules : list X -> X -> Prop) :
  list (list X) -> list X -> Prop := 
  | dtcNil : dercsl rules [] []
  | dtcCons : forall ps c pss cs, dercl rules ps c ->
      dercsl rules pss cs -> dercsl rules (ps :: pss) (c :: cs)
  . 

Scheme dercl_ind_mut := Induction for dercl Sort Prop
with dercsl_ind_mut := Induction for dercsl Sort Prop.

Check dercl_ind_mut.
Check dercsl_ind_mut.

Reset derrec_derrec.

Theorem derrec_derrec: forall (X : Set) rules prems (concl : X),
  derrec rules (derrec rules prems) concl -> derrec rules prems concl.

Proof.
Restart. 
intros.

Check (derrec rules (derrec rules prems) concl).
Check (derrec (derl rules) prems concl).
Check (@derrec_ind_mut X rules (derrec rules prems)).
Check (derrec_ind_mut (rules := rules) (prems := derrec rules prems)).
Check (derrec_ind_mut (rules := derl rules)).

Check (derl rules).
Check (derl (derl rules)).
Check (@derl_ind_mut X (derl rules)).
Check (derl_ind_mut (rules := derl rules)).

apply (derrec_ind_mut (rules := rules) (prems := derrec rules prems)
  (fun x : X => fun _ => derrec rules prems x)
  (fun xs : list X => fun _ => dersrec rules prems xs)).

tauto.
intros.
eapply derI. eassumption.  assumption.
apply dlNil.
intros.
apply dlCons. assumption.  assumption.
assumption.
Qed.

Reset derrec_derl.

Theorem derrec_derl: forall (X : Set) rules prems (concl : X),
  derrec (derl rules) prems concl -> derrec rules prems concl.

Proof.
Restart. 
intros.

apply (derrec_ind_mut (rules := derl rules) (prems := prems)
  (fun x : X => fun _ => derrec rules prems x)
  (fun xs : list X => fun _ => dersrec rules prems xs)).

apply dpI.
intros.
eapply derI.
(* doesn't work, requires rules ?ps concl *)
Abort.

Theorem dersl_derl: forall (X : Set) rules prems (concls : list X),
  dersl (derl rules) prems concls -> dersl rules prems concls.

intros.

apply (dersl_ind_mut (rules := derl rules) 
  (fun ps : list X => fun c => fun _ => derl rules ps c)
  (fun ps cs : list X => fun _ => dersl rules ps cs)).
apply asmI.
intros. 
eapply dtderI.
(* doesn't work, requires rules ?ps concl *)
Abort.

(* need transitivity ones first *)
Theorem derl_dersl: forall (X : Set) rules pss prems (concl : X),
  derl rules prems concl -> dersl rules pss prems -> derl rules pss concl.
intros.

eapply (derl_ind_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    forall pss, dersl rules pss ps -> derl rules pss c)
  (fun ps cs : list X => fun _ => 
    forall pss, dersl rules pss ps -> dersl rules pss cs)).

intros. (* make a lemma of this one *)
inversion H1. (* destruct H1. doesn't work *)
inversion H6. (* destruct H6 produces some weird goal *)
rewrite app_nil_r. assumption.
intros. eapply dtderI. eassumption. apply (H1 pss1 H2).
tauto.
intros.
(* need lemma here for dersl rules pss1 (ps ++ pss0)
  is dercl dercsl easier ? *)

Abort.

(* no convenient way of expressing the corresponding result
  for dercsl except using sth like allrel
Theorem dercl_dercsl: forall (X : Set) rules pss prems (concl : X),
  dercl rules prems concl -> dercsl rules pss prems -> 
    dercl rules (concat pss) concl.
intros.

eapply (dercl_ind_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    forall pss, dercsl rules pss ps -> dercl rules pss c)
  (fun pss : list (list X) => fun cs : list X => fun _ => ???? types
    forall qss, dercsl rules qss pss -> dercsl rules pss cs)).
*)

Lemma dersrec_all: forall (X : Set) rules prems (cs : list X),
  dersrec rules prems cs <-> Forall (derrec rules prems) cs.
intros. 
induction cs ; unfold iff ; apply conj ; intro.
apply Forall_nil. apply dlNil.
inversion H. apply Forall_cons. assumption. tauto.
inversion H. apply dlCons.  assumption. tauto.
Qed.

Lemma eq_TrueI: forall (P : Prop), (P -> (P <-> True)).
intros. unfold iff. apply conj ; intro.  apply I. assumption.
Qed.

Lemma Forall_cons_inv: forall (A : Set) (P : A -> Prop) (x : A) (l : list A),
  Forall P (x :: l) -> P x /\ Forall P l.
Proof. intros. inversion H. tauto. Qed.

Lemma Forall_cons_iff: forall (A : Set) (P : A -> Prop) (x : A) (l : list A),
  Forall P (x :: l) <-> P x /\ Forall P l.
Proof.  intros. unfold iff. apply conj ; intro. 
apply Forall_cons_inv. assumption.
inversion H.  apply Forall_cons ; assumption.
Qed.

Lemma Forall_append: forall (X : Set) P (xs ys: list X),
  Forall P (xs ++ ys) <-> Forall P xs /\ Forall P ys.
Proof.
intros.  induction xs.  easy.
simpl.  rewrite !Forall_cons_iff.  rewrite IHxs.  tauto.
Qed.

Theorem derl_derrec_trans: forall (X : Set) rules prems rps (concl : X),
  derl rules rps concl -> dersrec rules prems rps -> derrec rules prems concl.
Proof. 
intros.

eapply (derl_ind_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    dersrec rules prems ps -> derrec rules prems c)
  (fun ps cs : list X => fun _ => 
    dersrec rules prems ps -> dersrec rules prems cs)).

intros.  inversion H1. assumption.
intros. eapply derI. eassumption. tauto.
tauto.
intros. rewrite dersrec_all in H3.
rewrite Forall_append in H3.
rewrite <- !dersrec_all in H3.
inversion H3.  eapply dlCons ; tauto.
eassumption.  assumption.
Qed.

Check derrec_derrec.
Check derl_derrec_trans.
