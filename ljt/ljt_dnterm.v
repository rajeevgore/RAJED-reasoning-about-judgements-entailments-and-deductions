
(* LJ logic, using lists of formulae, termination of LJT *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.
Require Import PeanoNat.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT dd_fc gen_seq swappedT rtcT List_lemmasT gen_tacs.
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
    clos_transT (ms_ord_sw lt) (map dnfw (pr :: pl)) (map dnfw (cr :: cl)) ->
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

Lemma ctso_soe V c2 c1 c0 : @seq_ord V c1 c0 + seq_ord_eq c1 c0 ->  
  clos_transT seq_ord c2 c1 -> clos_transT seq_ord c2 c0.
Proof. intros c10 c21. destruct c10.
apply (tT_trans c21). apply tT_step. exact s.
induction c21. apply tT_step. eapply seq_ord_eq_comp ; eassumption.
apply (tT_trans c21_1).  exact (IHc21_2 s). Qed.

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

Lemma tc_mso_sw_meas_map U f (xs ys : list U):
  clos_transT (ms_ord_sw (measure f)) xs ys ->
  clos_transT (ms_ord_sw lt) (map f xs) (map f ys).
Proof. intro ctxy. induction ctxy. 
- apply tT_step. exact (mso_sw_meas_map r).
- eapply tT_trans ; eassumption. Qed.

Lemma ms_ord_sw_tcsw U R (Gp Gc Gcsw Gpsw : list U) : 
  ms_ord_sw R Gp Gc -> clos_transT (swapped (T:=U)) Gp Gpsw ->
  clos_transT (swapped (T:=U)) Gc Gcsw -> ms_ord_sw R Gpsw Gcsw.
Proof. intros mso ctsp ctsc. destruct mso.
exact (ms_ord_swI m (tT_trans c ctsp) (tT_trans c0 ctsc)). Qed.

Lemma ms_ord_cons_fel' U f (p0 c1 : list U) inp c0 Γ1 Γ2:
  ms_ord_sw f (p0 ++ inp) (c1 ++ c0) ->
  ms_ord_sw f (p0 ++ fmlsext Γ1 Γ2 inp) (c1 ++ fmlsext Γ1 Γ2 c0).
Proof. intro mso.  inversion mso. subst. clear mso.  destruct X. 
pose (ms_ordI f (Γ1 ++ G1) (G2 ++ Γ2) c f0).
assert (ms_ord f (Γ1 ++ (G1 ++ ps ++ G2) ++ Γ2) (Γ1 ++ (G1 ++ c :: G2) ++ Γ2)).
repeat (rewrite <- !app_assoc in m || rewrite <- !app_comm_cons in m).
list_assoc_r. exact m.
pose (ct_swL Γ1 (ct_swR Γ2 X0)).  pose (ct_swL Γ1 (ct_swR Γ2 X1)).
pose (ms_ord_swI X c2 c3).
unfold fmlsext. apply (ms_ord_sw_tcsw m0) ; apply tT_step ; swap_tac. Qed.

Lemma mso_msw_sw U f (p c : list U) : ms_ord f p c -> ms_ord_sw f p c.
Proof. intro mso. 
apply (ms_ord_swI mso) ; apply tT_step ; apply swapped_same. Qed.

Definition rsub_mso_sw U f := rsubI _ _ (@mso_msw_sw U f).

Definition ms_ord_cons_fel U f (p0 c1 inp c0 Γ1 Γ2 : list U) mso :=
  @ms_ord_cons_fel' U f p0 c1 inp c0 Γ1 Γ2 (mso_msw_sw mso).

Lemma ms_ord_cons_fe' U f (p0 c1 : U) inp c0 Γ1 Γ2:
  ms_ord_sw f (p0 :: inp) (c1 :: c0) ->
  ms_ord_sw f (p0 :: fmlsext Γ1 Γ2 inp) (c1 :: fmlsext Γ1 Γ2 c0).
Proof. intro mso.  apply (ms_ord_cons_fel' [p0] [c1]).  apply mso. Qed.

Lemma ms_ord_cons_fe U f (p0 c1 : U) inp c0 Γ1 Γ2:
  ms_ord f (p0 :: inp) (c1 :: c0) ->
  ms_ord_sw f (p0 :: fmlsext Γ1 Γ2 inp) (c1 :: fmlsext Γ1 Γ2 c0).
Proof. intro mso.  apply (ms_ord_cons_fel [p0] [c1]).  apply mso. Qed.

Lemma tc_ms_ord_cons_fel U f xs ys Γ1 Γ2:
  @clos_transT (list U) (ms_ord f) xs ys ->
  forall xs1 xs2 ys1 ys2, xs = xs1 ++ xs2 -> ys = ys1 ++ ys2 -> 
  clos_transT (ms_ord_sw f) 
    (xs1 ++ fmlsext Γ1 Γ2 xs2) (ys1 ++ fmlsext Γ1 Γ2 ys2).
Proof. intro cto. induction cto.
- intros * xe ye. subst. apply tT_step. apply ms_ord_cons_fel. exact r. 
- intros * xe ze. subst. eapply tT_trans.
+ eapply (IHcto1 _ _ [] _) ; reflexivity.
+ eapply IHcto2 ; reflexivity.
Qed.

Lemma tc_ms_ord_cons_fel' U f xs ys Γ1 Γ2:
  @clos_transT (list U) (ms_ord_sw f) xs ys ->
  forall xs1 xs2 ys1 ys2, xs = xs1 ++ xs2 -> ys = ys1 ++ ys2 -> 
  clos_transT (ms_ord_sw f) 
    (xs1 ++ fmlsext Γ1 Γ2 xs2) (ys1 ++ fmlsext Γ1 Γ2 ys2).
Proof. intro cto. induction cto.
- intros * xe ye. subst. apply tT_step. apply ms_ord_cons_fel'. exact r. 
- intros * xe ze. subst. eapply tT_trans.
+ eapply (IHcto1 _ _ [] _) ; reflexivity.
+ eapply IHcto2 ; reflexivity.
Qed.

Lemma tc_ms_ord_cons_fe U f (p0 c1 : U) inp c0 Γ1 Γ2:
  @clos_transT (list U) (ms_ord f) (p0 :: inp) (c1 :: c0) ->
  clos_transT (ms_ord_sw f) (p0 :: fmlsext Γ1 Γ2 inp) (c1 :: fmlsext Γ1 Γ2 c0).
Proof. intro cto. 
exact (tc_ms_ord_cons_fel Γ1 Γ2 cto [p0] inp [c1] c0 eq_refl eq_refl). Qed.

Lemma tc_ms_ord_cons_fe' U f (p0 c1 : U) inp c0 Γ1 Γ2:
  @clos_transT (list U) (ms_ord_sw f) (p0 :: inp) (c1 :: c0) ->
  clos_transT (ms_ord_sw f) (p0 :: fmlsext Γ1 Γ2 inp) (c1 :: fmlsext Γ1 Γ2 c0).
Proof. intro cto. 
exact (tc_ms_ord_cons_fel' Γ1 Γ2 cto [p0] inp [c1] c0 eq_refl eq_refl). Qed.

Lemma seq_ord_fe V p c Γ1 Γ2 : @seq_ord V p c ->
  @seq_ord V (apfst (fmlsext Γ1 Γ2) p) (apfst (fmlsext Γ1 Γ2) c).
Proof. intro sopc. destruct sopc.  apply seq_ordI.
simpl in c. simpl.  rewrite !map_fmlsext.
eapply tc_ms_ord_cons_fe' in c. exact c. Qed.

Lemma solem1 V p0 c1 inp c0 : ms_ord dnsubfml (p0 :: inp) (c1 :: c0) ->
  @seq_ord V (inp, p0) (c0, c1).
Proof. intro mso.  apply seq_ordI. apply tT_step.  apply mso_sw_meas_map.
apply (rsub_ms_ord_sw dnsub_fw).  apply (mso_msw_sw mso). Qed.

(* see solem', may not be required *)
Lemma solem V p0 c1 inp c0 Γ1 Γ2 : ms_ord dnsubfml (p0 :: inp) (c1 :: c0) ->
  @seq_ord V (fmlsext Γ1 Γ2 inp, p0) (apfst (fmlsext Γ1 Γ2) (c0, c1)).
Proof. intro mso.  apply seq_ordI. apply tT_step.  apply mso_sw_meas_map.
apply (rsub_ms_ord_sw dnsub_fw).  apply (ms_ord_cons_fe _ _ mso). Qed.

Definition solem' V p0 c1 inp c0 Γ1 Γ2 mso :=
  seq_ord_fe Γ1 Γ2 (@solem1 V p0 c1 inp c0 mso).

Lemma lja_so_imp V concl ps (rls : @LJAncrules V ps concl) :
  (forall p, InT p ps -> seq_ord p concl) + ImpLrule_p ps concl.
Proof. destruct rls. 
- (* LJAilrules *) left. intros p0 inp. destruct c. destruct p0.
eapply ail_prems_dn in r. 2: exact inp.  exact (solem1 r). 

- (* ImpL_Imp_rule *) left. intros p0 inp. destruct c. destruct p0.
eapply Imp_prems_dn in i. 2: apply inp.
apply seq_ordI.  apply tc_mso_sw_meas_map.
apply (clos_transT_mono (rsub_ms_ord_sw tc_dnsub_fw)).
exact (clos_transT_mono (@rsub_mso_sw _ _) i).

- (* ImpLrule_p *) right. exact i.

- (* ImpRrule *) left. intros p0 inp. destruct c. destruct p0.
eapply ImpR_prems_dn in i. 2: apply inp.  exact (solem1 i).

- (* Idrule *) left. intros p0 inp. 
inversion i. subst.  inversion inp.

- (* LJslrules *) left. intros p0 inp. destruct c. destruct p0.
eapply lrls_prems_dn in r. 2: apply inp.  apply (solem1 r).

- (* LJsrrules *) left. intros p0 inp. destruct c. destruct p0.
eapply rrls_prems_dn in r. 2: apply inp.  apply (solem1 r).

Qed.

Lemma lja_seq_ord V concl ps (rls : @LJArules V ps concl) p :
  InT p ps -> (seq_ord p concl + seq_ord_eq p concl).
Proof. intro inp. destruct rls. inversion r. clear r. subst.
apply lja_so_imp in X. destruct X.
- apply InT_mapE in inp. cD.
pose (seq_ord_fe Γ1 Γ2 (s _ inp1)).
rewrite -> inp0 in s0. left. exact s0.
- (* ImpLrule_p *) 
inversion i. subst. inversion inp ; subst ; clear inp.
+ eapply Imp_p_lprem_dn in i. destruct i.
++ right. apply seq_ord_eqI.  simpl in e. inversion e.
simpl. rewrite <- H0. reflexivity.
++ left. apply seq_ordI. apply tT_step.  apply mso_sw_meas_map.
apply (ms_ord_cons_fe _ _ m).
+ inversion H0 ; subst. clear H0.
eapply Imp_p_rprem_dn in i. left.  apply (solem _ _ i).
inversion H1. Qed.

Lemma nu_so V prems c1 c2 (d1 : derrec (@LJArules V) prems c1)
  (d2 : derrec LJArules prems c2) (inu : in_nextup d2 d1) :
  (seq_ord c2 c1) + (seq_ord_eq c2 c1).
Proof.  destruct d1.
- destruct (in_nextup_dpI inu). 
- apply in_nextup_in_drs in inu.
apply (lja_seq_ord l).  exact (in_drs_concl_in inu). Qed.

Lemma all_nrs {V} prems ps concl (ds : dersrec LJArules prems ps)
  (ljpc : LJArules ps concl) :
  ForallT (fun p => @seq_ord V p concl) ps ->  
  allPder (allDT (@no_rpt_same _ seq_ord _ _)) ds ->  
  allDT (@no_rpt_same _ seq_ord _ _) (derI concl ljpc ds).
Proof. intros fp apd. apply aderI. 2: apply apd.
intros c1 * ind1 ind2.
apply in_nextup_concl_in in ind1.
apply (ForallTD_forall fp) in ind1.
destruct d1. inversion ind2. inversion X.
apply in_nextup_concl_in in ind2.
pose (lja_seq_ord l ind2). sD.
eapply tT_trans ; apply tT_step ; eassumption.
apply tT_step.  exact (seq_ord_comp_eq s ind1).
Qed.

Lemma no_rpt_same_dpI U rules prems c R pc :
  no_rpt_same R (@dpI U rules prems c pc).
Proof. unfold no_rpt_same. intros * inn1.
inversion inn1. inversion X. Qed.
 
Lemma lja_so_tl V ph pt c (rls : @LJArules V (ph :: pt) c) p :
  InT p pt -> seq_ord p c.
Proof. intro inp. inversion rls. inversion X. clear X rls. subst.
apply lja_so_imp in X0. destruct X0.

- destruct ps0 ; inversion H2. subst. clear H2.
apply InT_mapE in inp. cD.
specialize (s _ (InT_cons _ inp1)).
rewrite - inp0.
exact (seq_ord_fe Γ1 Γ2 s).

- (* ImpLrule_p *) 
inversion i. subst. inversion H2. subst.
inversion inp ; subst ; clear inp H2.
eapply Imp_p_rprem_dn in i. apply (solem _ _ i).
inversion H0.
Qed.
 
Lemma so_ant_nil V ps cr Γ0 Γ3 (rl : @LJAncrules V ps ([], cr)) :
  forall p, InT p ps -> seq_ord (apfst (fmlsext Γ0 Γ3) p) (Γ0 ++ Γ3, cr).
Proof. inversion rl ; subst ; clear rl.
- inversion X. inversion X0 ; inversion X1.
- inversion X.  - inversion X.
- intros p inp. destruct p.
apply (ImpR_prems_dn X) in inp.
eapply solem in inp. exact inp.
- inversion X.
- inversion X. inversion X0 ; inversion X1.
- intros p inp. destruct p.
apply (rrls_prems_dn X) in inp.
eapply solem in inp. exact inp.
Qed.

(*
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
*)

Lemma nrs_ant_nil V prems ps cr Γ0 Γ3 ds d
  (l : LJArules (map (apfst (fmlsext Γ0 Γ3)) ps) (Γ0 ++ Γ3, cr))
  (rl : LJAncrules ps ([], cr))
  (deq : d = @derI _ (@LJArules V) prems _ _ l ds) :
  no_rpt_same seq_ord d.
Proof. unfold no_rpt_same. intros * inn inu.  subst.
pose (so_ant_nil Γ0 Γ3 rl). 
apply in_nextup_in_drs in inn.  apply in_drs_concl_in in inn.
apply nu_so in inu.  apply InT_mapE in inn. cD.
apply s in inn1. clear s.  rewrite inn0 in inn1.  clear ds rl l.
destruct inu.
- eapply tT_trans ; apply tT_step ; eassumption.
- apply tT_step. exact (seq_ord_comp_eq s inn1). Qed.

Lemma nrs_ant_nil' V prems ps cr Γ0 Γ3 Γ ds d
  (l : LJArules (map (apfst (fmlsext Γ0 Γ3)) ps) (Γ, cr))
  (rl : LJAncrules ps ([], cr))
  (deq : d = @derI _ (@LJArules V) prems _ _ l ds) :
  Γ0 ++ Γ3 = Γ -> no_rpt_same seq_ord d.
Proof. intro. subst Γ. eapply nrs_ant_nil ; eassumption. Qed.

Lemma lja_Imp_p V p B ps (X : LJAncrules ps ([Imp (Var p) B], Var p)) :
  @ImpLrule_p V ps ([Imp (Var p) B], Var p).
Proof. inversion X ; inversion X0.
- inversion X1 ; inversion X2.
- subst. exact X0.
- inversion X1 ; inversion X2. Qed.

Lemma nrs_Imp_rpt V prems ps Γ1 Γ2 B G p l 
  (ljpc : LJArules (map (apfst (fmlsext Γ1 Γ2)) [([Imp (Var p) B], Var p);
    ([B], G)]) (apfst (fmlsext Γ1 Γ2) ([Imp (Var p) B], G)))
  (d0 : dersrec LJArules prems [(fmlsext Γ1 Γ2 [B], G)])
  (d1 : dersrec LJArules prems (map (apfst (fmlsext Γ1 Γ2)) ps))
  (apd : allDT (no_rpt_same seq_ord (prems:=prems))
    (derI (fmlsext Γ1 Γ2 [Imp (Var p) B], Var p) l d1))
  (apd0 : allPder (allDT (no_rpt_same seq_ord (prems:=prems))) d0)
  (X0 : @LJAncrules V ps ([Imp (Var p) B], Var p)) :
  {d : derrec LJArules prems (apfst (fmlsext Γ1 Γ2) ([Imp (Var p) B], G)) &
    allDT (no_rpt_same seq_ord (prems:=prems)) d}.
Proof. apply lja_Imp_p in X0. inversion X0. subst. clear X0.
revert apd. revert l. dependent inversion d1. (* fails without revert l *)
subst. intros l apd.
exists (derI _ ljpc (dlCons d d0)). apply aderI.

- (* whole tree *)
unfold no_rpt_same. intros * inn inu.
apply in_nextup_in_drs in inn.
apply in_dersrecD in inn. sD.
++ (* left premise *) clear d0 apd0 d1.
pose (fcI_inj_concl inn).  clearbody e. subst.
apply fcI_inj in inn. subst.  
apply allDTD1 in apd.  unfold no_rpt_same in apd.  specialize (apd _ _ d d4).
require apd.  eapply in_nextupI.  apply is_nextupI.  apply in_dersrec_hd.
specialize (apd inu).
eapply lja_seq_ord in ljpc. 2: apply InT_eq.
exact (ctso_soe ljpc apd).
++ (* right premise *) clear l apd d d1 apd0.
apply nu_so in inu.
apply in_drs_concl_in in inn.  inversion inn. subst. clear inn.
eapply lja_so_tl in ljpc. 2: apply InT_eq.
destruct inu.
eapply tT_trans ; apply tT_step ; eassumption.
apply tT_step. eapply seq_ord_comp_eq ; eassumption.
inversion H0.

- (* subtrees *)
apply allPder_Cons.  apply allDTD2 in apd.  apply allPder_dlConsD in apd.
exact (fst apd). exact apd0.
Qed.

(*
now after change to allDT, have changed at lja_dd_ord 
now need to do following

NEXT TO DO 




Lemma lja_dd_ImpL_p V prems Γ1 Γ2 ps c
  (ds : dersrec LJArules prems (map (apfst (fmlsext Γ1 Γ2)) ps))
  (dsnrs : allPder (allDT (no_rpt_same seq_ord (prems:=prems))) ds)
  (ljpc : LJArules (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c))
  (i : @ImpLrule_p V ps c) :
  {d : derrec LJArules prems (apfst (fmlsext Γ1 Γ2) c) &
  allDT (no_rpt_same seq_ord (prems:=prems)) d}.
Proof. inversion i. subst.
revert dsnrs. dependent inversion ds. subst.
pose d. revert d1. dependent inversion d.
- (* left premise is dpI ... *)
subst. intros d1 dsnrs.  clear d ds.
apply allPder_dlConsD in dsnrs. cD.
epose (fextI (rmI _ _ _ _ (ImpL_anc i))).
exists (derI _ f (dlCons d1 d0)). clearbody f.  apply aderI.
+ (* whole tree *) clear dsnrs dsnrs0. unfold no_rpt_same.
intros * inn innn.
apply in_nextup_in_drs in inn. clear f.
apply in_dersrecD in inn. sD.
++ (* looking at left premise, which is dpI *)
pose (fcI_inj_concl inn).  clearbody e. subst. 
apply fcI_inj in inn. subst. subst d1.
inversion innn.  inversion X.
++ (* looking at right premise, which is itself smaller *)
clear d1 p0 f.  revert inn.
dependent inversion d0. subst.
intros inn.  apply in_dersrecD in inn. sD.
+++ pose (fcI_inj_concl inn).  clearbody e. subst.
apply fcI_inj in inn. subst.  clear d1.
apply nu_so in innn.  eapply lja_so_tl in ljpc. 2: apply InT_eq.
destruct innn.  eapply tT_trans ; apply tT_step ; eassumption.
apply tT_step. eapply seq_ord_comp_eq ; eassumption.
+++ apply in_drs_concl_in in inn. inversion inn.
+ (* subtrees *) clear f. subst d1. apply allPder_Cons ; assumption.

- (* left premise is derI ... *)
clear d ds. (* use d2, dlCons (d2 d0) instead *)
subst. intros d2 apd. apply allPder_dlConsD in apd. cD.
(* here, do we need to get that l uses the rule we find in LJAnc 
revert dependent l. intro.  dependent inversion l.  error here ??? *)
inversion l. inversion X. subst. destruct c0.
inversion H3 ; subst ; clear H3.
pose (LJAnc_seL X0). destruct s.
+ (* rule has empty antecedent, therefore not ImpLrule_p,
  therefore can use same tree *)
exists (derI _ ljpc (dlCons d2 d0)). apply aderI.
++ (* whole tree *)
unfold no_rpt_same. intros * inu inn.
apply in_nextup_in_drs in inu.
apply in_dersrecD in inu. sD.
+++ (* left premise *)
pose (fcI_inj_concl inu).  clearbody e. subst.
apply fcI_inj in inu. subst.  subst d2.
apply in_nextup_in_drs in inn.
apply in_drs_concl_in in inn.
apply InT_mapE in inn. cD. subst.
eapply (so_ant_nil Γ0 Γ3 X0) in inn1.
simpl in ljpc.  rewrite <- H0 in ljpc. simpl. rewrite <- H0.
eapply lja_seq_ord in ljpc. 2: apply InT_eq. sD.
eapply tT_trans ; apply tT_step ; eassumption.
apply tT_step. eapply seq_ord_eq_comp ; eassumption.

+++ (* right premise *) clear d2 X0 apd apd0 l H0 d1 X.
pose (lja_so_tl ljpc (InT_eq _ _)).
apply in_drs_concl_in in inu. inversion inu. subst. clear inu.
apply nu_so in inn. sD.
eapply tT_trans ; apply tT_step ; eassumption.
apply tT_step. eapply seq_ord_comp_eq ; eassumption.
inversion H0.
++ (* subtrees *) subst d2. apply allPder_Cons ; assumption.

+ unfold fmlsext in H0.  simpl in H0.
acacD'T2.
(* 4 subgoals - was 8 without simpl in H0. *)
(* note the following weird procedure, must avoid subst of Γ0 = Γ1 ++ []
because substitutes into d1 and l but won't allow rewriting in d1 and l
see emails to coq-club@inria.fr 17/12/20 *)
++ (* rule is also for [Imp (Var p) B] *)
subst H0.  rewrite app_nil_r in H1. subst.
eapply nrs_Imp_rpt ; try eassumption.

++ admit.

++ (* rule is also for [Imp (Var p) B] *)
subst H0.  rewrite app_nil_r in H1. subst.
eapply nrs_Imp_rpt ; try eassumption.

++ subst.


admit.


(* may need sth like this
inversion inn. inversion_sigma.
rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H7.
rewrite <- H6 in H8.  rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H8. 
subst. clear H H3 H2 H6 inn. inversion inn. inversion X1.

inversion_sigma.
rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H4.
rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H6.
subst. clear H2 H3 inn.
*)

Lemma lja_dd_ord V prems : forall concl, 
  derrec (@LJArules V) prems concl -> {d : derrec LJArules prems concl &
  allDT (@no_rpt_same _ seq_ord _ _) d}.
Proof. eapply derrec_all_rect.
- intros concl pc.  exists (dpI _ _ _ pc).  apply adpI.  apply no_rpt_same_dpI.
- intros * ljpc ds fps.
assert {dsr : (dersrec LJArules prems ps) & 
  allPder (allDT (@no_rpt_same _ seq_ord LJArules prems)) dsr}.
{ clear ljpc ds.
induction ps.  eexists. apply allPder_Nil.
inversion fps. subst.  apply IHps in X0. cD.
exists (dlCons X X0).  apply allPder_Cons ; assumption. }
cD. clear ds fps. 
inversion ljpc. subst. destruct X1. destruct l.
+ (* LJAilrules *)
exists (derI _ ljpc X).  destruct c.  apply all_nrs.  apply ForallTI_forall.
intros q inps.  apply InT_mapE in inps. cD. subst.
apply solem.  exact (ail_prems_dn r inps1).  exact X0.
    
+ (* ImpL_Imp_rule *)
exists (derI _ ljpc X).  destruct c.  apply all_nrs.  apply ForallTI_forall.
intros q inps.  apply InT_mapE in inps. cD. subst.
eapply Imp_prems_dn in i. 2: apply inps1.
apply seq_ordI. apply tc_mso_sw_meas_map.
apply (clos_transT_mono (rsub_ms_ord_sw tc_dnsub_fw)).
apply (tc_ms_ord_cons_fe _ _ i).  exact X0.

+ (* Imprule_p *)
admit.

+ (* ImpRrule *)
exists (derI _ ljpc X).  destruct c.  apply all_nrs.  apply ForallTI_forall.
intros q inps.  apply InT_mapE in inps. cD. subst.
apply solem.  exact (ImpR_prems_dn i inps1).  exact X0.

+ (* Idrule *)
exists (derI _ ljpc X).  destruct c.  apply all_nrs.  
inversion i. simpl. apply ForallT_nil. exact X0.

+ (* LJslrules *)
exists (derI _ ljpc X).  destruct c.  apply all_nrs.  apply ForallTI_forall.
intros q inps.  apply InT_mapE in inps. cD. subst.
apply solem.   exact (lrls_prems_dn r inps1).  exact X0.

+ (* LJsrrules *)
exists (derI _ ljpc X).  destruct c.  apply all_nrs.  apply ForallTI_forall.
intros q inps.  apply InT_mapE in inps. cD. subst.
apply solem.   exact (rrls_prems_dn r inps1).  exact X0.

Admitted.






*)
