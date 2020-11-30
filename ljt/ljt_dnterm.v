
(* LJ logic, using lists of formulae, termination of LJT *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.
Require Import PeanoNat.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT dd_fc gen_seq swappedT rtcT.
Require Import ljt.
Require Import Coq.Program.Basics.

(* multiset ordering, but on lists - allowing swap (hopefully 1 swap not rtc *) 
Inductive ms_ord {U} R : relationT (list U) :=
    ms_ordI : forall G1 G2 ps c, (forall p : U, InT p ps -> R p c) ->
    ms_ord R (G1 ++ ps ++ G2) (G1 ++ c :: G2).

Lemma ms_ordI_eqc {U} R G1 G2 ps c G1c2 :
  (forall p : U, InT p ps -> R p c) -> 
    G1c2 = (G1 ++ c :: G2) -> ms_ord R (G1 ++ ps ++ G2) G1c2.
Proof. intros. subst. eapply ms_ordI ; eassumption. Qed.

Lemma ms_ordI_eq {U} R G1 G2 ps c Gsw G1c2 :
  (forall p : U, InT p ps -> R p c) -> Gsw = G1 ++ ps ++ G2 ->
    G1c2 = (G1 ++ c :: G2) -> ms_ord R Gsw G1c2.
Proof. intros. subst. eapply ms_ordI ; eassumption. Qed.

(* multiset ordering, transitive (if R is) *)
(*
WRONG - allowed to have some elements the same
Definition ms_ord_tc {U} (R : relationT U) G H :=
  forall p : U, InT p G -> sigT2 (fun c => R p c) (fun c => InT c H).
*)

Axiom wfT_ms_ord : forall U R, @well_foundedT U R -> well_foundedT (ms_ord R).
(*
Axiom wfT_ms_ord_tc :
  forall U R, @well_foundedT U R -> well_foundedT (ms_ord_tc R).
*)

Definition dnlw {V} fmls := fold_right Nat.add 0 (map (@dnfw V) fmls).

Definition dnsw {V} seq :=
  match seq with
    | (X, A) => fold_right Nat.add (@dnfw V A) (map (@dnfw V) X)
  end.

Lemma dnlw_app {V} xs ys : @dnlw V (xs ++ ys) = (dnlw xs + dnlw ys)%nat.
Proof. unfold dnlw.
induction xs ; simpl.  reflexivity.
rewrite IHxs. apply Nat.add_assoc. Qed.

Lemma dnsw_alt {V} xs A : @dnsw V (xs, A) = (dnlw xs + dnfw A)%nat.
Proof. unfold dnsw.  unfold dnlw.
induction xs ; simpl.  reflexivity.
rewrite IHxs. apply Nat.add_assoc. Qed.

(* this ordering won't do for ImpL, need lemmas for individual rules *)
Lemma ail_prems_dn V G ps cl cr pl pr :
  rlsmap (flip pair G) (@LJAilrules V) ps (cl, cr) ->
  InT (pl, pr) ps -> ms_ord dnsubfml (pr :: pl) (cr :: cl).
Proof. intros ljpc inp.
inversion ljpc ; subst ; clear ljpc.
destruct H1 ; destruct i ; inversion inp ; subst ; clear inp ;
unfold flip in H0 ; inversion H0 ; clear H0 ; subst.
+ eapply (@ms_ordI _ _ [pr] [] [_]).
intros p inp. inversion inp. subst. apply dnsub_Imp_AndL.
inversion H0. 
+ eapply (@ms_ordI _ _ [pr] [] [_; _]).
intros p inp. inversion inp ; subst ; clear inp. apply dnsub_Imp_OrL1.
inversion H0 ; clear H0 ; subst. apply dnsub_Imp_OrL2.
inversion H1.  Qed.

Lemma lrls_prems_dn V G ps cl cr pl pr :
  rlsmap (flip pair G) (@LJslrules V) ps (cl, cr) ->
  InT (pl, pr) ps -> ms_ord dnsubfml (pr :: pl) (cr :: cl).
Proof. intros ljpc inp.
inversion ljpc ; subst ; clear ljpc.
destruct X.
- destruct a ; inversion inp ; subst ; clear inp ;
unfold flip in H0 ; inversion H0 ; clear H0 ; subst.
eapply (@ms_ordI _ _ [pr] [] [_; _]).
intros p inp. inversion inp. subst. clear inp. apply dnsub_AndL.
inversion H0 ; clear H0 ; subst. apply dnsub_AndR.
inversion H3. 
- destruct o ; inversion inp ; subst ; clear inp ;
unfold flip in H0 ; inversion H0 ; clear H0 ; subst.
eapply (@ms_ordI _ _ [pr] [] [_]).
intros p inp. inversion inp. subst. apply dnsub_OrL.
inversion H0. 
inversion H1. clear H1. subst.
eapply (@ms_ordI _ _ [pr] [] [_]).
intros p inp. inversion inp. subst. apply dnsub_OrR.
inversion H0. 
inversion H1.
- destruct b. inversion inp. Qed.

Lemma prem_dn_lem U R (x y : U) : R x y -> ms_ord R [x] [y].
Proof. intro rxy.  eapply (@ms_ordI _ _ [] [] [_]).
intros p inp. inversion inp. subst. apply rxy.
inversion X. Qed.

Lemma rrls_prems_dn V ps cl cr pl pr :
  rlsmap (pair []) (@LJsrrules V) ps (cl, cr) ->
  InT (pl, pr) ps -> ms_ord dnsubfml (pr :: pl) (cr :: cl).
Proof. intros ljpc inp.
inversion ljpc ; subst ; clear ljpc.
destruct H1.
- destruct a ; inversion inp ; subst ; clear inp.
{ inversion H0 ; subst ; clear H0.
apply prem_dn_lem. apply dnsub_AndL. }
inversion H0 ; subst ; clear H0.
{ inversion H1 ; subst ; clear H1.
apply prem_dn_lem. apply dnsub_AndR. }
inversion H1.
- destruct o ; inversion inp ; subst ; clear inp.
{ inversion H0 ; subst ; clear H0.
apply prem_dn_lem. apply dnsub_OrL. }
inversion H0.
- destruct o ; inversion inp ; subst ; clear inp.
{ inversion H0 ; subst ; clear H0.
apply prem_dn_lem. apply dnsub_OrR. }
inversion H0. Qed.

Lemma Id_prems_dn V ps A p c any pas cas: 
  (@Idrule V A) ps c -> InT p ps -> @ms_ord (PropF V) any pas cas.
Proof. intros ljpc inp.
inversion ljpc ; subst ; clear ljpc. inversion inp. Qed.

Lemma ImpR_prems_dn V ps cl cr pl pr : @ImpRrule V ps (cl, cr) ->
  InT (pl, pr) ps -> ms_ord dnsubfml (pr :: pl) (cr :: cl).
Proof. intros ljpc inp.
inversion ljpc ; subst ; clear ljpc.
inversion inp ; subst ; clear inp.
inversion H0 ; subst ; clear H0.
eapply (@ms_ordI _ _ [] [] [_; _]).
intros p inp. inversion inp. subst. clear inp. apply dnsub_ImpR.
inversion H0 ; subst ; clear H0. apply dnsub_ImpL.
inversion H3. 
inversion H0. Qed.

Lemma Imp_prems_dn V ps cl cr pl pr : 
  @ImpL_Imp_rule V ps (cl, cr) -> InT (pl, pr) ps ->
  clos_transT (ms_ord (clos_transT dnsubfml)) (pr :: pl) (cr :: cl).
Proof. intros ljpc inp.
inversion ljpc ; subst ; clear ljpc.
inversion inp ; subst ; clear inp.
- inversion H0 ; subst ; clear H0.
apply (@tT_trans _ _ _ [Imp (Imp C pr) B]) ; apply tT_step.
+ eapply (ms_ordI_eq _ [] []). 3: reflexivity.
2: rewrite app_nil_r. 2: reflexivity.
intros p inp.  inversion inp ; subst ; clear inp.
eapply tT_trans ; apply tT_step.  apply dnsub_ImpR.  apply dnsub_ImpL.
inversion H0 ; subst ; clear H0.
apply tT_step. apply dnsub_Imp_ImpL.
inversion H1 ; subst ; clear H1.
eapply tT_trans ; apply tT_step.  apply dnsub_ImpL.  apply dnsub_ImpL.
inversion H0.
+ eapply (ms_ordI_eq _ [] [_]).
intros p inp. apply (InT_nilE _ inp).   reflexivity. reflexivity.

- inversion H0 ; subst ; clear H0.
inversion H1 ; subst ; clear H1.
apply tT_step. eapply (ms_ordI_eq _ [_] []).
3: reflexivity.  2: rewrite app_nil_r. 2: reflexivity.
intros p inp.  inversion inp ; subst ; clear inp.
apply tT_step.  apply dnsub_ImpR.
inversion H0.  inversion H1.  Qed.

(* right premise for ImpLrule_p rule *)
Lemma Imp_p_rprem_dn V lp cl cr pl pr : 
  @ImpLrule_p V [lp ; (pl, pr)] (cl, cr) -> 
  ms_ord dnsubfml (pr :: pl) (cr :: cl).
Proof. intro r. inversion r. subst. clear r.
eapply (@ms_ordI _ _ [cr] [] [B]). 
intros * inp.  inversion inp ; subst ; clear inp. apply dnsub_ImpR.
inversion H0. Qed.

(* this depends on dnfw being changed from Dyckhoff by 
  dnfw (Bot) = 1, dnfw (Var _) = 0 *)
Lemma Imp_p_lprem_dn V rp cl cr pl pr : 
  @ImpLrule_p V [(pl, pr) ; rp] (cl, cr) -> 
  (map dnfw (pr :: pl) = map dnfw (cr :: cl)) + 
  ms_ord (measure dnfw) (pr :: pl) (cr :: cl).
Proof. intro r. inversion r. subst. clear r.
destruct cr.
left. simpl. reflexivity.
all: right ; eapply (@ms_ordI _ _ [] [_] [_]) ; 
intros p0 inp ; inversion inp ; try (inversion H0) ; subst ; clear inp ;
unfold measure ; simpl ; apply Nat.lt_0_succ.
Qed.

(* theorems so far
Check Imp_prems_dn.
Check ImpR_prems_dn.
Check ail_prems_dn.
Check lrls_prems_dn.
Check rrls_prems_dn.
Check Id_prems_dn.
Print LJAncrules.
Print ImpLrule_p.
Check Imp_p_rprem_dn.
Check Imp_p_lprem_dn.
Proof from here depends on not repeated uses of ImpLrule_p up left branch 
*)

(*
need to show this holds in all cases except left premise of ImpL rule

Lemma lja_prems_dn V ps cl cr pl pr :
  @LJAncrules V ps (cl, cr) -> InT (pl, pr) ps -> 
    ms_ord (measure dnfw) (pr :: pl) (cr :: cl).
*)


