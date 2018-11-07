
(* derrec, derl, etc *)

Require Export List.
Set Implicit Arguments.
Export ListNotations.

Lemma rappl: forall (A B : Prop), A -> (A -> B) -> B.
Proof.  tauto.  Qed.

Lemma appl: forall (A B : Prop), (A -> B) -> A -> B.
Proof.  tauto.  Qed.

Ltac cE :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => inversion_clear H
    | [ H : ex _ |- _ ] => inversion_clear H
    end.

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
intros. eapply derl_derrec_trans in r. eassumption.  assumption.
apply dlNil.
intros. apply dlCons ; assumption.
assumption.
Qed.

Lemma dersl_cons: forall (X : Set) rules qs p (ps : list X), 
  dersl rules qs (p :: ps) -> exists qsa qsb, qs = qsa ++ qsb /\
    derl rules qsa p /\ dersl rules qsb ps.
Proof.
intros.
inversion H.
eapply ex_intro.  eapply ex_intro.  apply conj.  reflexivity.
tauto.
Qed.

Reset dersl_append.

Lemma dersl_append: forall (X : Set) rules (psa psb : list X) qs, 
  dersl rules qs (psa ++ psb) -> exists qsa qsb, qs = qsa ++ qsb /\
    dersl rules qsa psa /\ dersl rules qsb psb.
Proof.
intro.  intro.  intro.  intro.
induction psa.
intros. 
apply ex_intro with [].
apply ex_intro with qs.
apply conj. trivial.
simpl in H. apply conj. apply dtNil. assumption.

simpl. intros. apply dersl_cons in H.
cE.  pose (IHpsa x0 H2).  cE.
eapply ex_intro.  eapply ex_intro. 
rewrite H1 in H0.  rewrite app_assoc in H0.
 apply conj.  apply H0.  apply conj.
apply dtCons. assumption.  assumption.  assumption.
Qed.

(* old version
inversion_clear H.  inversion_clear H0. 
inversion_clear H.  inversion_clear H1.
pose (IHpsa x0 H2).
inversion_clear e.  inversion_clear H1.
inversion_clear H3.  inversion_clear H4.
eapply ex_intro.  eapply ex_intro. 
rewrite H1 in H0.  rewrite app_assoc in H0.
 apply conj.  apply H0.  apply conj.
apply dtCons. assumption.  assumption.  assumption.

Qed.
*)

(* or at this point 
generalize H. (* or revert H. *)
apply ex_ind. intro. apply ex_ind. intro.
apply and_ind.   intro.  apply and_ind.   intro. intro.
pose (IHpsa x0 H2).
generalize e.
apply ex_ind. intro. apply ex_ind. intro.
apply and_ind.   intro.  apply and_ind.   intro. intro.
eapply ex_intro.  eapply ex_intro.
rewrite H3 in H0.  rewrite app_assoc in H0.
 apply conj.  apply H0.  apply conj.
apply dtCons. assumption.  assumption.  assumption.
Qed.
*)

Lemma derl_dersl: forall (X : Set) (rules : list X -> X -> Prop) 
          (pss : list X) (rps : list X) (concl : X),
    derl rules rps concl -> dersl rules pss rps -> derl rules pss concl.
Proof.
intros.

eapply (derl_ind_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    forall pss, dersl rules pss ps -> derl rules pss c)
  (fun ps cs : list X => fun _ => 
    forall pss, dersl rules pss ps -> dersl rules pss cs)).

intros. inversion_clear H1. inversion_clear H3.
rewrite app_nil_r.  assumption.
intros. apply H1 in H2.
eapply dtderI. eassumption. assumption.
intros. assumption.
intros.  apply dersl_append in H3. cE. rewrite H4. apply dtCons.
apply H1. assumption. apply H2. assumption.
eassumption. assumption. 
Qed.

Lemma dersl_dersl: forall (X : Set) (rules : list X -> X -> Prop)
          (pss : list X) (rps : list X) (cs : list X),
    dersl rules rps cs -> dersl rules pss rps -> dersl rules pss cs.
Proof.
intros.

(* can use same proof as for derl_dersl *)
eapply (dersl_ind_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    forall pss, dersl rules pss ps -> derl rules pss c)
  (fun ps cs : list X => fun _ => 
    forall pss, dersl rules pss ps -> dersl rules pss cs)).

intros. inversion_clear H1. inversion_clear H3.
rewrite app_nil_r.  assumption.
intros. apply H1 in H2.
eapply dtderI. eassumption. assumption.
intros. assumption.
intros.  apply dersl_append in H3. cE. rewrite H4. apply dtCons.
apply H1. assumption. apply H2. assumption.
eassumption. assumption. 
Qed.

(* alternatively, just induction on the list of conclusions *)
Lemma dersl_dersl_alt: forall (X : Set) (rules : list X -> X -> Prop)
           (cs rps : list X), dersl rules rps cs ->
	 forall (pss : list X), dersl rules pss rps -> dersl rules pss cs.
Proof.
intro.  intro.  intro.  

induction cs.
intros. inversion H. subst. assumption.
intros.  apply dersl_cons in H. cE. subst.
apply dersl_append in H0. cE. subst.
apply dtCons. eapply derl_dersl. eassumption. assumption.
firstorder.
Qed.

Theorem derl_derl: forall (X : Set) rules prems (concl : X),
  derl (derl rules) prems concl -> derl rules prems concl.
intros.

apply (derl_ind_mut (rules := derl rules) 
  (fun ps : list X => fun c : X => fun _ => derl rules ps c)
  (fun ps cs : list X => fun _ => dersl rules ps cs)).

intro. apply asmI.
intros. eapply derl_dersl. eassumption.  assumption.
apply dtNil.
intros.  apply dtCons.  assumption.  assumption.
assumption.  
Qed.

Check derrec_derrec.
Check derl_derrec_trans.
Check derrec_derl.
Check dersl_append.
Check derl_dersl.
Check dersl_dersl.
Check derl_derl.

