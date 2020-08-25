
(* sample proof of soundness of some rules using a definition of tau
  which works from the RH end of a LNS *)

Require Export List.
Set Implicit Arguments.
Export ListNotations.
Require Import genT gen.
Require Import ddT.
Require Import List_lemmasT.
Require Import lntT lntkt_exchT.
(* why doesn't this work?
Require Import existsT.
*)
Require Import Coq.Program.Basics.

(* I think we need these, rather than just using type bool,
  to get eg not_all_not_ex, for dealing with correspondence between
  diamonds and boxes *)
Require Import Classical.
Require Import Coq.Logic.Classical_Pred_Type.

(* forcing of a formula at a world *)
Fixpoint wforces V W R val (w : W) (fml : PropF V) : Prop :=
  match fml with
  | Var p => val w p
  | Bot _ => False
  (*
  | Con A B => (wforces R val w A) /\ (wforces R val w B)
  | Dis A B => (wforces R val w A) \/ (wforces R val w B)
  *)
  | WBox A => forall v: W, R w v -> wforces R val v A
  | BBox A => forall v: W, R v w -> wforces R val v A
  | Imp A B => wforces R val w A -> wforces R val w B
  end.

(* a model forcing a formula *)
Definition mforces V W R val (fml : PropF V) : Prop := 
  forall w : W, wforces R val w fml.

Print wforces.  Print mforces.

(* generalised validity *)
Definition gvalid_rule U valf (rls : rlsT U) :=
  forall ps c, rls ps c -> ForallT valf ps -> valf c.

Definition valid_fml {V : Set} fml :=
  forall W R (val : W -> V -> Prop), mforces R val fml.

Print LNSKt_rules.
Locate LNSKt_rules. (* in lntkt_exchT.v *)

(* Defined connectives *)
Definition Not V A := Imp A (Bot V).
Definition Top V := Not (Bot V).
Definition And V A B := Not (Imp A (@Not V B)).
Definition Or V A B := Imp (@Not V A) B.

Fixpoint disjall V fs :=
  match fs with
    | f :: fs' => Or f (@disjall V fs')
    | [] => Bot V
  end.

Fixpoint conjall V fs :=
  match fs with
    | f :: fs' => And f (@conjall V fs')
    | [] => Top V
  end.

(* formula translation of single sequent without direction *)
Definition tau_seq V seq := @Imp V (conjall (fst seq)) (disjall (snd seq)).

Fixpoint tau_ns V ns :=
  match ns with
    | (seq, fwd) :: ss => Or (tau_seq seq) (BBox (@tau_ns V ss))
    | (seq, bac) :: ss => Or (tau_seq seq) (WBox (@tau_ns V ss))
    | [] => Bot V
  end.

Definition valid_ns {V : Set} ns :=
  forall W R (val : W -> V -> Prop), mforces R val (tau_ns (rev ns)).
Definition valid_nsP {V : Set} ns := forall W (R : W -> W -> Prop)
  (val : W -> V -> Prop), mforces R val (tau_ns (rev ns)).

Print lntbRT.b1rrules.
Print lntbRT.b2rrules.
Print lntb1LT.b1lrules.
Print lntb2LT.b2lrules.

Axiom wf_conj_app_consI : forall V W R val w A H2l H2r,
  @wforces V W R val w A -> wforces R val w (conjall (H2l ++ H2r)) -> 
  wforces R val w (conjall (H2l ++ A :: H2r)).

Axiom wf_conj_app_consD1 : forall V W R val w A H2l H2r,
  wforces R val w (conjall (H2l ++ A :: H2r)) -> @wforces V W R val w A.

Axiom wf_disj_app_consI1 : forall V W R val w A H2l H2r,
  @wforces V W R val w A ->
  wforces R val w (disjall (H2l ++ A :: H2r)).

(* validity preserved by rules, also
  wvalid : a rule preserves forcing at a given world, or
  mvalid : a rule preserves forcing by a particular model *)

Lemma wvalid_mvalid V W R val rules : (forall w,
    gvalid_rule (fun ns => @wforces V W R val w (tau_ns (rev ns))) rules) ->
  gvalid_rule (fun ns => @mforces V W R val (tau_ns (rev ns))) rules.
Proof. repeat intro.  unfold gvalid_rule in X.
eapply X.  exact X0. clear X X0. unfold mforces in H.
apply ForallTI_forall. intros.
eapply ForallTD_forall in H.
apply H.  exact H0. Qed.

Lemma mvalid_validP V rules : (forall W (R : W -> W -> Prop) val,
    gvalid_rule (fun ns => @mforces V W R val (tau_ns (rev ns))) rules) ->
  gvalid_rule (fun ns => @valid_nsP V ns) rules.
Proof. intros g ps c X H W R val.
unfold gvalid_rule in g.
eapply g.  exact X. clear g.  unfold valid_nsP in H.
apply ForallTI_forall. intros.
eapply ForallTD_forall in H.
apply H.  exact H0. Qed.

Lemma mvalid_valid V rules : (forall W R val,
    gvalid_rule (fun ns => @mforces V W R val (tau_ns (rev ns))) rules) ->
  gvalid_rule (fun ns => @valid_ns V ns) rules.
Proof. intros g ps c X H W R val.
unfold gvalid_rule in g.
eapply g.  exact X. clear g.  unfold valid_ns in H.
apply ForallTI_forall. intros.
eapply ForallTD_forall in H.
apply H.  exact H0. Qed.

Lemma matchdeqv U V d (f : U -> V) g h :
  (match d with | fwd => f g | bac => f h end) = 
  f (match d with | fwd => g | bac => h end).
Proof. destruct d ; simpl ; reflexivity. Qed.

Lemma wvalid_b1l V W R val w :
  gvalid_rule (fun ns => @wforces V W R val w (tau_ns (rev ns)))
    (nslclrule (@lntb1LT.b1lrules V)).
Proof. repeat intro.  destruct X. 
destruct b ; simpl in H ;  unfold nslclext ;  unfold nslclext in H ;
inversion H ; subst ; clear H H3 ;
rewrite rev_app_distr in H2 ;  rewrite rev_app_distr ;  simpl ; simpl in H2 ;
pose (classic (wforces R val w A)) ;  destruct o.

+ intro. apply H2. intro wfia. apply H0. clear H2.
intro wfc. apply wfia. apply wf_conj_app_consI.
exact H. exact wfc.
+ intros x v rvw. clear x H2.  rewrite matchdeqv.
simpl. intros wwc. apply not_imply_elim in wwc.
apply wf_conj_app_consD1 in wwc. simpl in wwc. destruct (H (wwc _ rvw)).

(* following is identical to above *)
+ intro. apply H2. intro wfia. apply H0. clear H2.
intro wfc. apply wfia. apply wf_conj_app_consI.
exact H. exact wfc.
+ intros x v rvw. clear x H2.  rewrite matchdeqv.
simpl. intros wwc. apply not_imply_elim in wwc.
apply wf_conj_app_consD1 in wwc. simpl in wwc. destruct (H (wwc _ rvw)).

Qed.

Lemma mvalid_b1l V W R val :
  gvalid_rule (fun ns => @mforces V W R val (tau_ns (rev ns)))
    (nslclrule (@lntb1LT.b1lrules V)).
Proof. apply wvalid_mvalid. apply wvalid_b1l.  Qed.

Lemma valid_b1l V :
  gvalid_rule (fun ns => @valid_ns V ns) (nslclrule (@lntb1LT.b1lrules V)).
Proof. apply mvalid_valid. apply mvalid_b1l.  Qed.

Lemma mvalid_b2l V W R val :
  gvalid_rule (fun ns => @mforces V W R val (tau_ns (rev ns)))
    (nslclrule (@lntb2LT.b2lrules V)).
Proof. repeat intro.  destruct X. 
destruct b ; simpl in H ;  unfold nslclext ;  unfold nslclext in H ;
inversion H ; subst ; clear H H3 ;
rewrite rev_app_distr in H2 ;  rewrite rev_app_distr ;
simpl ; simpl in H2 ; unfold mforces in H2 ;
intro wfw ; apply not_imply_elim in wfw ;
apply wf_conj_app_consD1 in wfw ; simpl in wfw ;
intros v rwv ; specialize (wfw v rwv) ; specialize (H2 v) ;
rewrite matchdeqv ; simpl ; rewrite matchdeqv in H2 ; simpl in H2 ;
intro wwf ; apply H2 ; clear H2 ; intro wfaw ; apply wwf ;
intro wfc ; apply wfaw ; clear wwf wfaw ;
apply wf_conj_app_consI ; assumption.
Qed.

Lemma valid_b2l V :
  gvalid_rule (fun ns => @valid_ns V ns) (nslclrule (@lntb2LT.b2lrules V)).
Proof. apply mvalid_valid. apply mvalid_b2l.  Qed.

(* this requires (R : W -> W -> Prop) for the use of not_imply_elim below *)
Lemma mvalid_b2r V W (R : W -> W -> Prop) val :
  gvalid_rule (fun ns => @mforces V W R val (tau_ns (rev ns)))
    (nslclrule (@lntbRT.b2rrules V)).
Proof. repeat intro.  destruct X. 
destruct b ; simpl in H ;  unfold nslclext ;  unfold nslclext in H ;
inversion H ; subst ; clear H H4 ;
rewrite rev_app_distr in H3 ;  rewrite rev_app_distr ;
simpl ; simpl in H3 ; unfold mforces in H3 ; simpl in H3.

- pose (classic (wforces R val w (WBox A))).  destruct o.
+ intro wwff.  apply False_rect. apply wwff.  intro.
apply wf_disj_app_consI1. exact H.
+ simpl in H.  apply not_all_ex_not in H. cD.
pose H0.  apply not_imply_elim in n.
apply not_imply_elim2 in H0.
eapply H3. 2: exact n. clear H3. tauto.

(* similar to above *)
- pose (classic (wforces R val w (BBox A))).  destruct o.
+ intro wwff.  apply False_rect. apply wwff.  intro.
apply wf_disj_app_consI1. exact H.
+ simpl in H.  apply not_all_ex_not in H. cD.
pose H0.  apply not_imply_elim in n.
apply not_imply_elim2 in H0.
eapply H3. 2: exact n. clear H3. tauto.
Qed.

(* fails for @valid_ns because wants (R : W -> W -> Type) *)
Lemma valid_b2r V :
  gvalid_rule (fun ns => @valid_nsP V ns) (nslclrule (@lntbRT.b2rrules V)).
Proof. apply mvalid_validP. apply mvalid_b2r.  Qed.

Check valid_b1l.  Check valid_b2r.  Check valid_b2l.



