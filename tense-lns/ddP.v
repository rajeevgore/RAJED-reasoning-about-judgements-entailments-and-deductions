Add LoadPath "../general".

(* derrec, derl, etc, other useful stuff *)

Require Export List.
Set Implicit Arguments.
Export ListNotations.

Require Import gen.

(* note, this doesn't work Type replaced by Prop,
  although the actual version used allows prems : X -> Prop 
Reset derrec.

Inductive derrec X (rules : list X -> X -> Prop) :
  (X -> Type) -> X -> Prop := 
  | dpI : forall prems concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps prems concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec X (rules : list X -> X -> Prop) :
  (X -> Type) -> list X -> Prop :=
  | dlNil : forall prems, dersrec rules prems []
  | dlCons : forall prems seq seqs, 
    derrec rules prems seq -> dersrec rules prems seqs ->
    dersrec rules prems (seq :: seqs)
    .
    *)

(* definition using Forall, seems equivalent *)
Inductive aderrec X (rules : list X -> X -> Prop) 
  (prems : X -> Prop) : X -> Prop := 
  | adpI : forall concl,
    prems concl -> aderrec rules prems concl
  | aderI : forall ps concl, rules ps concl ->
    Forall (aderrec rules prems) ps -> aderrec rules prems concl.

Inductive derrec X (rules : list X -> X -> Prop) (prems : X -> Prop) :
  X -> Prop := 
  | dpI : forall concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec X (rules : list X -> X -> Prop) (prems : X -> Prop) :
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

(* this should be a more useful induction principle for derrec *)
Definition dim_all X rules prems Q := 
  @derrec_ind_mut X rules prems (fun y => fun _ => Q y) 
  (fun ys => fun _ => Forall Q ys).

(* this doesn't work
Check (dim_all _ _ (Forall_nil X Q)).
*)
(* here is how to get the tautologies out of dim_all *)
Definition dim_all3 X rules prems Q h1 h2 := 
  @dim_all X rules prems Q h1 h2 (Forall_nil Q).

Definition fce3 X Q D Ds seq seqs (d : D seq) qs (ds : Ds seqs) qss :=
  @Forall_cons X Q seq seqs qs qss.

Definition dim_all4 X rules prems Q h1 h2 := 
  @dim_all3 X rules prems Q h1 h2 
  (@fce3 X Q (derrec rules prems) (dersrec rules prems)).

Definition dim_all8 X rules prems Q h1 h2 := 
  @dim_all3 X rules prems Q h1 h2 
  (fun seq seqs _ qs _ qss => @Forall_cons X Q seq seqs qs qss).
    
(* so dim_all4, or dim_all8 better, is the same as derrec_all_ind below *)

Lemma derrec_all_ind:
  forall X (rules : list X -> X -> Prop) (prems Q : X -> Prop),
     (forall concl : X, prems concl -> Q concl) ->
     (forall (ps : list X) (concl : X),
      rules ps concl -> dersrec rules prems ps -> Forall Q ps -> Q concl) ->
     forall y : X, derrec rules prems y -> Q y.
Proof.
intros.
eapply dim_all. exact H. exact H0.
apply Forall_nil.
intros.
apply Forall_cons. assumption.  assumption.
assumption.
Qed.

Inductive derl X (rules : list X -> X -> Prop) :
  list X -> X -> Prop := 
  | asmI : forall p, derl rules [p] p
  | dtderI : forall pss ps concl, rules ps concl ->
    dersl rules pss ps -> derl rules pss concl
with dersl X (rules : list X -> X -> Prop) :
  list X -> list X -> Prop := 
  | dtNil : dersl rules [] []
  | dtCons : forall ps c pss cs,
    derl rules ps c -> dersl rules pss cs -> dersl rules (ps ++ pss) (c :: cs)
  . 

Scheme derl_ind_mut := Induction for derl Sort Prop
with dersl_ind_mut := Induction for dersl Sort Prop.

Check derl_ind_mut.
Check dersl_ind_mut.

Inductive dercl X (rules : list X -> X -> Prop) :
  list X -> X -> Prop := 
  | casmI : forall p, dercl rules [p] p
  | dtcderI : forall pss ps concl, rules ps concl ->
    dercsl rules pss ps -> dercl rules (concat pss) concl
with dercsl X (rules : list X -> X -> Prop) :
  list (list X) -> list X -> Prop := 
  | dtcNil : dercsl rules [] []
  | dtcCons : forall ps c pss cs, dercl rules ps c ->
      dercsl rules pss cs -> dercsl rules (ps :: pss) (c :: cs)
  . 

Scheme dercl_ind_mut := Induction for dercl Sort Prop
with dercsl_ind_mut := Induction for dercsl Sort Prop.

Check dercl_ind_mut.
Check dercsl_ind_mut.

Theorem derrec_trans_imp: forall X rules prems (concl : X),
  derrec rules (derrec rules prems) concl -> derrec rules prems concl.

Proof.
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

(*
Theorem dersl_derl: forall X rules prems (concls : list X),
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
*)

(* need transitivity ones first *)
(*
Theorem derl_trans: forall X rules pss prems (concl : X),
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
*)

(* no convenient way of expressing the corresponding result
  for dercsl except using sth like allrel
Theorem dercl_dercsl: forall X rules pss prems (concl : X),
  dercl rules prems concl -> dercsl rules pss prems -> 
    dercl rules (concat pss) concl.
intros.

eapply (dercl_ind_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    forall pss, dercsl rules pss ps -> dercl rules pss c)
  (fun pss : list (list X) => fun cs : list X => fun _ => ???? types
    forall qss, dercsl rules qss pss -> dercsl rules pss cs)).
*)

Lemma derrec_same: forall X rules prems (c c' : X),
  derrec rules prems c -> c = c' -> derrec rules prems c'.
Proof. intros. subst. assumption. Qed.

(* further detailed versions of derrec_same *)
Lemma derrec_same_nsL: forall Y X D rules prems G H Δ d (Γ Γ' : X),
  derrec rules prems (G ++ (Γ : X, Δ : Y, d : D) :: H) ->
    Γ = Γ' -> derrec rules prems (G ++ (Γ', Δ, d) :: H).
Proof. intros. subst. assumption. Qed.

Lemma derrec_same_nsR: forall Y X D rules prems G H Γ d (Δ Δ' : X),
  derrec rules prems (G ++ (Γ : Y, Δ : X, d : D) :: H) ->
    Δ = Δ' -> derrec rules prems (G ++ (Γ, Δ', d) :: H).
Proof. intros. subst. assumption. Qed.

Lemma dersrec_all: forall X rules prems (cs : list X),
  dersrec rules prems cs <-> Forall (derrec rules prems) cs.
Proof.
intros. 
induction cs ; unfold iff ; apply conj ; intro.
apply Forall_nil. apply dlNil.
inversion H. apply Forall_cons. assumption. tauto.
inversion H. apply dlCons.  assumption. tauto.
Qed.

Lemma dersrec_forall: forall X rules prems (cs : list X),
  dersrec rules prems cs <-> forall c, In c cs -> derrec rules prems c.
Proof. intros. rewrite dersrec_all. rewrite Forall_forall. reflexivity. Qed.

Lemma dersrec_nil: forall X rules prems,
  dersrec rules prems ([] : list X).
Proof.  intros.  rewrite dersrec_all ; apply Forall_nil. Qed.

Lemma dersrec_single: forall X rules prems c,
  dersrec rules prems [c] <-> derrec rules prems (c : X).
Proof.  intros.  rewrite dersrec_all. rewrite Forall_single. tauto. Qed.

Lemma dersrec_map_single: forall X Y (f : X -> Y) rules prems c,
  dersrec rules prems (map f [c]) <-> derrec rules prems (f c).
Proof.  intros.  simpl. rewrite dersrec_single. tauto. Qed.

Lemma dersrec_map_2: forall X Y (f : X -> Y) rules prems c d,
  dersrec rules prems (map f [c ; d]) <->
    derrec rules prems (f c) /\ derrec rules prems (f d).
Proof.  intros. rewrite dersrec_all. rewrite Forall_map_2. reflexivity. Qed.

(* try using the induction principle derrec_all_ind *)
Lemma derrec_rmono: forall W (rulesa rulesb : rls W) prems concl,
  rsub rulesa rulesb -> 
  derrec rulesa prems concl ->
  derrec rulesb prems concl.
Proof.  intros.  revert H.  eapply derrec_all_ind.
intros. apply dpI. assumption.
intros. eapply derI. unfold rsub in X. apply X. eassumption.
rewrite dersrec_forall. rewrite -> Forall_forall in H1. assumption.
Qed.

Theorem derrec_trans_imp_alt: forall X rules prems (concl : X),
  derrec rules (derrec rules prems) concl -> derrec rules prems concl.
Proof.  intros.  revert H.  eapply derrec_all_ind. tauto.
intros. eapply derI. eassumption.
rewrite dersrec_all.  assumption.
Qed.

Theorem derl_derrec_trans: forall X rules prems rps (concl : X),
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

Theorem derrec_derl_deriv: forall X rules prems (concl : X),
  derrec (derl rules) prems concl -> derrec rules prems concl.

Proof.
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

Lemma dersl_cons: forall X rules qs p (ps : list X), 
  dersl rules qs (p :: ps) -> exists qsa qsb, qs = qsa ++ qsb /\
    derl rules qsa p /\ dersl rules qsb ps.
Proof.
intros.
inversion H.
eapply ex_intro.  eapply ex_intro.  apply conj.  reflexivity.
tauto.
Qed.

Lemma dersl_app_eq: forall X rules (psa psb : list X) qs, 
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

Lemma derl_trans: forall X (rules : list X -> X -> Prop) 
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
intros.  apply dersl_app_eq in H3. cE. rewrite H4. apply dtCons.
apply H1. assumption. apply H2. assumption.
eassumption. assumption. 
Qed.

Lemma dersl_trans: forall X (rules : list X -> X -> Prop)
          (pss : list X) (rps : list X) (cs : list X),
    dersl rules rps cs -> dersl rules pss rps -> dersl rules pss cs.
Proof.
intros.

(* can use same proof as for derl_trans *)
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
intros.  apply dersl_app_eq in H3. cE. rewrite H4. apply dtCons.
apply H1. assumption. apply H2. assumption.
eassumption. assumption. 
Qed.

(* alternatively, just induction on the list of conclusions *)
Lemma dersl_trans_alt: forall X (rules : list X -> X -> Prop)
           (cs rps : list X), dersl rules rps cs ->
	 forall (pss : list X), dersl rules pss rps -> dersl rules pss cs.
Proof.
intro.  intro.  intro.  

induction cs.
intros. inversion H. subst. assumption.
intros.  apply dersl_cons in H. cE. subst.
apply dersl_app_eq in H0. cE. subst.
apply dtCons. eapply derl_trans. eassumption. assumption.
firstorder.
Qed.

Theorem derl_deriv: forall X rules prems (concl : X),
  derl (derl rules) prems concl -> derl rules prems concl.
intros.

apply (derl_ind_mut (rules := derl rules) 
  (fun ps : list X => fun c : X => fun _ => derl rules ps c)
  (fun ps cs : list X => fun _ => dersl rules ps cs)).

intro. apply asmI.
intros. eapply derl_trans. eassumption.  assumption.
apply dtNil.
intros.  apply dtCons.  assumption.  assumption.
assumption.  
Qed.

Definition derI_rules_mono X rules rulesb prems ps concl rs fuv :=
  @derI X rulesb prems ps concl (@rsub_imp _ _ rules rulesb rs ps concl fuv).

Check derrec_trans_imp.
Check derl_derrec_trans.
Check derrec_derl_deriv.
Check dersl_app_eq.
Check derl_trans.
Check dersl_trans.
Check derl_deriv.

(* this doesn't work, fixed by changing derrec to return Type,
  see file ddT.v 
Fixpoint derrec_height X rules prems concl 
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ _ _ => 0
    | derI _ _ ds => S (dersrec_height ds)
  end
with dersrec_height X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => 0
    | dlCons d ds => max (derrec_height d) (dersrec_height ds)
  end.
 *)

(* Caitlin:
Yes, Fixpoint definitions won't work. 
But Inductive definitions should, e.g. the following:

Inductive derrec_height (X : Type) (rules : list X -> X -> Prop) (prems : X -> Prop)
          : forall (concl : X) (der : @derrec X rules prems concl), nat -> Prop :=
| dpI_ht concl d H :
    d = (dpI rules prems concl H) ->  derrec_height d 1
| derI_ht concl seqs d ds n H :
    d = derI concl H ds ->
    @dersrec_height X rules prems seqs ds n -> derrec_height d (S n)
with dersrec_height (X : Type) (rules : list X -> X -> Prop) (prems : X -> Prop)
          : forall (seqs : list X) (ds : @dersrec X rules prems seqs), nat -> Prop :=
| dlNil_ht ds : ds = dlNil rules prems -> dersrec_height ds 0
| dlCons_ht concl seqs d ds ds2 n m nm :
    ds2 = dlCons d ds ->
    @derrec_height X rules prems concl d n ->
    @dersrec_height X rules prems seqs ds m ->
    nm = max n m ->
    dersrec_height ds2 nm.
*)                                                         