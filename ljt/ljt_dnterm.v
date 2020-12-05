
(* LJ logic, using lists of formulae, termination of LJT *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.
Require Import PeanoNat.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT dd_fc gen_seq swappedT rtcT List_lemmasT.
Require Import ljt.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.

(* multiset ordering, but on lists *) 
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

(* multiset ordering on lists - allowing swap *) 
Inductive ms_ord_sw {U} R : relationT (list U) :=
    ms_ord_swI : forall Gp Gc Gcsw Gpsw, ms_ord R Gp Gc ->
    clos_transT (@swapped _) Gp Gpsw -> clos_transT (@swapped _) Gc Gcsw ->
    ms_ord_sw R Gpsw Gcsw.

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
destruct X ; destruct i ; inversion inp ; subst ; clear inp ;
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
destruct X.
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

(* the property we need of a derivation tree -
  no repeated entries of the same "size" *)
Definition no_rpt_same U R rules prems (c0 : U) (d0 : derrec rules prems c0) :=
  forall c1 c2 (d1 : derrec rules prems c1) (d2 : derrec rules prems c2),
    in_nextup d1 d0 -> in_nextup d2 d1 -> clos_transT R c2 c0.

Definition no_rpt_same_fc U R rules prems (d0 : @derrec_fc U rules prems) :=
  forall (d1 : derrec_fc rules prems) (d2 : derrec_fc rules prems),
    in_nextup_fc d1 d0 -> in_nextup_fc d2 d1 -> 
    clos_transT R (derrec_fc_concl d2) (derrec_fc_concl d0).

(* original one, wrong, doesn't allow changing Var p for Var q 
Inductive seq_ord {V} : relationT (srseq (PropF V)) :=
  | seq_ordI : forall pl pr cl cr, 
    ms_ord (measure (@dnfw V)) (pr :: pl) (cr :: cl) ->
    seq_ord (pl, pr) (cl, cr).
*)
Inductive seq_ord {V} : relationT (srseq (PropF V)) :=
  | seq_ordI : forall pl pr cl cr, 
    ms_ord_sw lt (map dnfw (pr :: pl)) (map dnfw (cr :: cl)) ->
    seq_ord (pl, pr) (cl, cr).

Inductive seq_ord_eq {V} : relationT (srseq (PropF V)) :=
  | seq_ord_eqI : forall pl pr cl cr, 
    map dnfw (pr :: pl) = map dnfw (cr :: cl) ->
    seq_ord_eq (pl, pr) (cl, cr).

Lemma seq_ord_comp_eq {V} p q c : seq_ord_eq q p ->
  @seq_ord V p c -> seq_ord q c. 
Proof. intros se so.  inversion se.  inversion so. subst.
inversion H2. subst.
apply seq_ordI. rewrite H. exact X. Qed.

Lemma seq_ord_eq_comp {V} p q c: seq_ord q p ->
  @seq_ord_eq V p c -> seq_ord q c. 
Proof. intros se so.  inversion se.  inversion so. subst.
inversion H2. subst.
apply seq_ordI. rewrite <- H1. exact X. Qed.

Lemma rsub_ms_ord U R1 R2 : rsub R1 R2 -> rsub (ms_ord R1) (@ms_ord U R2).
Proof. intros rs12 u v ms1. destruct ms1.
apply ms_ordI. intros p inp.
exact (rs12 p c (r p inp)). Qed.

Lemma rsub_ms_ord_sw U R1 R2 : 
  rsub R1 R2 -> rsub (ms_ord_sw R1) (@ms_ord_sw U R2).
Proof. intros rs12 u v ms1. destruct ms1.
exact (ms_ord_swI (rsub_ms_ord rs12 m) c c0). Qed.

Lemma mso_meas_map U f (xs ys : list U):
  ms_ord (measure f) xs ys -> ms_ord lt (map f xs) (map f ys).
Proof. intro mm. destruct mm. rewrite !map_app. simpl.
apply ms_ordI. intros p inpm.
apply InT_mapE in inpm. cD. subst.
exact (m _ inpm1). Qed.

Lemma mso_sw_meas_map U f (xs ys : list U):
  ms_ord_sw (measure f) xs ys -> ms_ord_sw lt (map f xs) (map f ys).
Proof. intro mm. destruct mm. 
apply (ms_ord_swI (mso_meas_map m)).
clear m. induction c. apply tT_step. apply (swapped_map _ r).
exact (tT_trans IHc1 IHc2).
clear m. induction c0. apply tT_step. apply (swapped_map _ r).
exact (tT_trans IHc0_1 IHc0_2). Qed.

Lemma ms_ord_cons_fe U f (p0 c1 : U) inp c0 Γ1 Γ2:
  ms_ord f (p0 :: inp) (c1 :: c0) ->
  ms_ord_sw f (p0 :: fmlsext Γ1 Γ2 inp) (c1 :: fmlsext Γ1 Γ2 c0).
Proof. intro mso.
inversion mso.
pose (ms_ordI f (Γ1 ++ G1) (G2 ++ Γ2) c X).
assert (ms_ord f (Γ1 ++ (G1 ++ ps ++ G2) ++ Γ2) (Γ1 ++ (G1 ++ c :: G2) ++ Γ2)).
repeat (rewrite <- !app_assoc in m || rewrite <- !app_comm_cons in m).
list_assoc_r. exact m.
rewrite H0 in X0.  rewrite H in X0. clear m H0 H X.
unfold fmlsext.
apply (ms_ord_swI X0) ; apply tT_step ; swap_tac_Rc.
Qed.

(*
Lemma lja_seq_ord V concl ps (rls : @LJArules V ps concl) p :
  InT p ps -> (seq_ord p concl + seq_ord_eq p concl).
Proof. intro inp. destruct rls. inversion r. clear r.  destruct X ; subst.
- (* LJAilrules *)
left.
apply InT_mapE in inp. cD.
eapply ail_prems_dn in r. 2: apply inp1.
apply seq_ordI.
inversion inp0. subst. clear inp0.
apply mso_sw_meas_map.
apply (rsub_ms_ord_sw dnsub_fw).
apply (ms_ord_cons_fe _ _ r).

Admitted.

  



Lemma all_nrs {V} prems ps concl (ds : dersrec LJArules prems ps)
  (ljpc : LJArules ps concl) :
  ForallT (fun p => @seq_ord V p concl) ps ->  
  allPder (@no_rpt_same _ seq_ord _ _) ds ->  
  allDT (@no_rpt_same _ seq_ord _ _) (derI concl ljpc ds).
Proof. intros fp apd. simpl. split. 2: apply apd.
intros c1 * ind1 ind2.
apply in_nextup_concl_in in ind1.
apply (ForallTD_forall fp) in ind1.
destruct d1. inversion ind2. inversion X.
apply in_nextup_concl_in in ind2.
pose (lja_seq_ord l ind2). sD.
eapply tT_trans ; apply tT_step ; eassumption.
apply tT_step.  exact (seq_ord_comp_eq s ind1).
Qed.

Lemma lja_dd_ord V prems : forall concl, 
  derrec (@LJArules V) prems concl -> {d : derrec LJArules prems concl &
  allDT (@no_rpt_same _ seq_ord _ _) d}.
Proof. eapply derrec_all_rect.
- intros concl pc.
exists (dpI _ _ _ pc). simpl.
unfold no_rpt_same. 
intros * ind1 ind2.  destruct ind2.
dependent induction ind1.  inversion i.
- intros * ljpc ds fps.
assert {dsr : (dersrec LJArules prems ps) & 
  allPder (@no_rpt_same _ seq_ord LJArules prems) dsr}.
{ clear ljpc ds.
induction ps.  eexists. apply allPder_Nil.
inversion fps. subst.  apply IHps in X0. cD.
exists (dlCons X X0).  apply allPder_Cons.
exact (allDTD1 _ _  X2). exact X1. }
cD. clear ds fps.
inversion ljpc. subst. destruct X1. destruct l.
+ (* LJAilrules *)

exists (derI _ ljpc X).  destruct c.

eapply ail_prems_dn in r.
    
want the following lemma
all_nrs

*)
