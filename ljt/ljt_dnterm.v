
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

Lemma ms_ord_cons_fel U f (p0 c1 : list U) inp c0 Γ1 Γ2:
  ms_ord f (p0 ++ inp) (c1 ++ c0) ->
  ms_ord_sw f (p0 ++ fmlsext Γ1 Γ2 inp) (c1 ++ fmlsext Γ1 Γ2 c0).
Proof. intro mso.  inversion mso.
pose (ms_ordI f (Γ1 ++ G1) (G2 ++ Γ2) c X).
assert (ms_ord f (Γ1 ++ (G1 ++ ps ++ G2) ++ Γ2) (Γ1 ++ (G1 ++ c :: G2) ++ Γ2)).
repeat (rewrite <- !app_assoc in m || rewrite <- !app_comm_cons in m).
list_assoc_r. exact m.
rewrite H0 in X0.  rewrite H in X0. clear m H0 H X.
unfold fmlsext.
apply (ms_ord_swI X0) ; apply tT_step ; swap_tac_Rc.
Qed.

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

Lemma tc_ms_ord_cons_fe U f (p0 c1 : U) inp c0 Γ1 Γ2:
  @clos_transT (list U) (ms_ord f) (p0 :: inp) (c1 :: c0) ->
  clos_transT (ms_ord_sw f) (p0 :: fmlsext Γ1 Γ2 inp) (c1 :: fmlsext Γ1 Γ2 c0).
Proof. intro cto. 
exact (tc_ms_ord_cons_fel Γ1 Γ2 cto [p0] inp [c1] c0 eq_refl eq_refl). Qed.

Lemma solem V p0 c1 inp c0 Γ1 Γ2 : ms_ord dnsubfml (p0 :: inp) (c1 :: c0) ->
  @seq_ord V (fmlsext Γ1 Γ2 inp, p0) (apfst (fmlsext Γ1 Γ2) (c0, c1)).
Proof. intro mso.  apply seq_ordI. apply tT_step.  apply mso_sw_meas_map.
apply (rsub_ms_ord_sw dnsub_fw).  apply (ms_ord_cons_fe _ _ mso). Qed.

Lemma lja_seq_ord V concl ps (rls : @LJArules V ps concl) p :
  InT p ps -> (seq_ord p concl + seq_ord_eq p concl).
Proof. intro inp. destruct rls. inversion r. clear r. subst.
apply InT_mapE in inp. cD.
inversion inp0 ; subst ; clear inp0.
inversion X ; subst ; clear X.
- (* LJAilrules *) left.
eapply ail_prems_dn in X0. 2: apply inp1.  exact (solem _ _ X0). 

- (* ImpL_Imp_rule *) left.
eapply Imp_prems_dn in X0. 2: apply inp1.
apply seq_ordI.  apply tc_mso_sw_meas_map.
apply (clos_transT_mono (rsub_ms_ord_sw tc_dnsub_fw)).
apply (tc_ms_ord_cons_fe _ _ X0).

- (* ImpLrule_p *) 
inversion X0 ; subst.
inversion inp1 ; subst ; clear inp1.
inversion H0 ; subst ; clear H0.
+ eapply Imp_p_lprem_dn in X0. destruct X0.
++ right. apply seq_ord_eqI.  simpl in e. inversion e.
simpl. rewrite <- H0. reflexivity.
++ left. apply seq_ordI. apply tT_step.  apply mso_sw_meas_map.
apply (ms_ord_cons_fe _ _ m).
+ inversion H0 ; subst. clear H0.
inversion H1 ; subst. clear H1.
eapply Imp_p_rprem_dn in X0. left.  apply (solem _ _ X0).
inversion H1.

- (* ImpRrule *) left.
eapply ImpR_prems_dn in X0. 2: apply inp1.  exact (solem _ _ X0).

- (* Idrule *) left.
inversion X0. subst. inversion inp1.

- (* LJslrules *) left.
eapply lrls_prems_dn in X0. 2: apply inp1.  apply (solem _ _ X0).

- (* LJsrrules *) left.
eapply rrls_prems_dn in X0. 2: apply inp1.  apply (solem _ _ X0).

Qed.

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

Lemma no_rpt_same_dpI U rules prems c R pc :
  no_rpt_same R (@dpI U rules prems c pc).
Proof. unfold no_rpt_same. intros * inn1.
inversion inn1. inversion X. Qed.
 
Lemma lja_so_tl V ph pt c (rls : @LJArules V (ph :: pt) c) p :
  InT p pt -> seq_ord p c.
Proof. intro inp. inversion rls. inversion X.
destruct ps0 ; inversion H2. clear H2 rls X. subst.
apply InT_mapE in inp. cD.
inversion inp0 ; subst ; clear inp0.
inversion X0 ; subst ; clear X0.

- (* LJAilrules *) 
eapply ail_prems_dn in X. 2: apply (InT_cons _ inp1).  exact (solem _ _ X). 

- (* ImpL_Imp_rule *) 
eapply Imp_prems_dn in X. 2: apply (InT_cons _ inp1). 
apply seq_ordI.  apply tc_mso_sw_meas_map.
apply (clos_transT_mono (rsub_ms_ord_sw tc_dnsub_fw)).
apply (tc_ms_ord_cons_fe _ _ X).

- (* ImpLrule_p *) 
inversion X ; subst.
inversion inp1 ; subst ; clear inp1.
inversion H0 ; subst ; clear H0.
eapply Imp_p_rprem_dn in X. apply (solem _ _ X).
inversion H0.

- (* ImpRrule *) 
eapply ImpR_prems_dn in X. 2: apply (InT_cons _ inp1).  exact (solem _ _ X).

- (* Idrule *) inversion X.

- (* LJslrules *) 
eapply lrls_prems_dn in X. 2: apply (InT_cons _ inp1).  exact (solem _ _ X).

- (* LJsrrules *) 
eapply rrls_prems_dn in X.
2: apply (InT_cons _ inp1).  exact (solem _ _ X).
Qed.

Lemma so_ant_nil V ps cr Γ0 Γ3 
  (l : LJArules (map (apfst (fmlsext Γ0 Γ3)) ps) (Γ0 ++ Γ3, cr))
  (rl : @LJAncrules V ps ([], cr)) :
  forall p, InT p ps -> seq_ord (apfst (fmlsext Γ0 Γ3) p) (Γ0 ++ Γ3, cr).
Proof. inversion rl ; subst ; clear rl.
- inversion X. inversion X0 ; inversion X1.
- inversion X.
- inversion X.
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
pose (so_ant_nil _ _ l rl). 
apply in_nextup_in_drs in inn.  apply in_drs_concl_in in inn.
apply nu_so in inu.  apply InT_mapE in inn. cD.
apply s in inn1. clear s.  rewrite inn0 in inn1.  clear ds rl l.
destruct inu.
- eapply tT_trans ; apply tT_step ; eassumption.
- apply tT_step. exact (seq_ord_comp_eq s inn1). Qed.

(*
Lemma lja_dd_ImpL_p V prems Γ1 Γ2 ps c
  (ds : dersrec LJArules prems (map (apfst (fmlsext Γ1 Γ2)) ps))
  (dsnrs : allPder (no_rpt_same seq_ord (prems:=prems)) ds)
  (ljpc : LJArules (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c))
  (i : @ImpLrule_p V ps c) :
  {d : derrec LJArules prems (apfst (fmlsext Γ1 Γ2) c) &
  allDT (no_rpt_same seq_ord (prems:=prems)) d}.
Proof. inversion i. subst.
revert dsnrs. dependent inversion ds. subst.
pose d. revert d1. dependent inversion d.
- subst. intros d1 dsnrs.  clear d ds.
apply allPder_dlConsD in dsnrs. cD.
epose (fextI (rmI _ _ _ _ (ImpL_anc i))).
exists (derI _ f (dlCons d1 d0)).
simpl. split.
+ clearbody f. clear dsnrs dsnrs0. unfold no_rpt_same.
intros * inn innn.
apply in_nextup_in_drs in inn.
apply in_dersrecD in inn. sD.
++ pose (fcI_inj_concl inn).
clearbody e. subst. 
apply fcI_inj in inn. subst. subst d1.
inversion innn.  inversion X.
++ clear d1 p0 f.  revert inn.
dependent inversion d0. subst.
intros inn.  apply in_dersrecD in inn. sD.
+++ pose (fcI_inj_concl inn).
clearbody e. subst.
apply fcI_inj in inn. subst. 
clear d1.
(* holds because concl of d smaller than concl in goal *)
admit.
+++ revert inn. dependent inversion d1.
intro inn. inversion inn.
+ clear f. apply allPder_Cons.
++ subst d1. apply no_rpt_same_dpI.
++ exact dsnrs0.

- clear d ds. (* use d2, dlCons (d2 d0) instead *)
subst. intros d2 apd. apply allPder_dlConsD in apd. cD.
(* here, do we need to get that l uses the rule we find in LJAnc 
revert dependent l. intro.  dependent inversion l.  error here ??? *)
inversion l. inversion X. subst. destruct c0.
pose (LJAnc_seL X0). destruct s.
+ (* rule has empty antecedent, therefore not ImpLrule_p,
  therefore can use same tree *)
exists (derI _ ljpc (dlCons d2 d0)). simpl. split.
++ 


unfold no_rpt_same. intros * inu inn.

nrs_ant_nil not relevant, LJAncrules ps1 ([], p0) applies one level higher up
eapply nrs_ant_nil. exact X0. fails

eapply (nrs_ant_nil _ _ X0). fails

Check nrs_ant_nil.

all: cycle 1.
apply allPder_Cons.

+ 



simpl in H3. unfold fmlsext in H3. inversion H3. clear H3. subst. 
pose (LJAnc_seL X0). destruct s.
+ simpl in H0.
(* rule has empty antecedent, therefore not ImpLrule_p *)



eexists.


exists (dlCons d d0).




acacD'T2 ; subst.

+ 




eapply allPderD in dsnrs0. 2: apply InT_eq.
clear d1. cD.

we need the solution to be dlCons dsnrs0 dlNil
not what we are given


TBC 

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






+

*)
