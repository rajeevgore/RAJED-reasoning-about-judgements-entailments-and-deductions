
(* LJA logic, using lists of formulae - contraction (and maybe cut) *)
(* lemmas in Roy Dyckhoff and Sara Negri,
Admissibility of Structural Rules for Contraction-Free Systems of
Intuitionistic Logic, JSL 65 (2000), 1499-1518 *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT dd_fc.
Require Import List_lemmasT swappedT.
Require Import gen_tacs.
Require Import gen_seq gstep gentree rtcT.
Require Import ljt ljt_inv ljt_dn ljt_ctr.
Require Import Coq.Program.Basics.

Lemma gen_sctrL_ImpL_And V W rules (B C D : PropF V)
  (Linv : rel_adm rules (srs_ext_rel (@ImpL_And_inv V))):
  (forall G : W,
    rsub (fst_ext_rls (rlsmap (flip pair G) (@ImpL_And_rule V))) rules) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp C (Imp D B)))) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp (And C D) B))).
Proof. intros rs ctr.  apply rel_admI.
intros * sqrc. apply radmI.
intro derp. destruct sqrc. destruct s.
(* invert one instance of Imp (And C D) B *)
eapply Linv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ Φ1 (S ++ [Imp _ B] ++ Φ2)).
apply fslr_I. apply (ImpL_And_invs_I B C D).
list_assoc_r. simpl. reflexivity.  reflexivity.
(* invert 2nd instance of Imp (And C D) B *)
eapply Linv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [Imp _ _] ++ S) Φ2).
apply fslr_I. apply (ImpL_And_invs_I B C D).
list_assoc_r. simpl. reflexivity.  reflexivity.
revert derp. list_assoc_r. simpl. intro derp.
(* contract premise *)
destruct ctr. erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ Φ1 Φ2).
apply (sctr_relI _ S).  reflexivity.  reflexivity.
destruct r. revert d. list_assoc_r'. simpl.  intro d.
apply d in derp. clear d.
(* apply rule to contracted premise *)
eapply derI. apply (rsubD (rs G)).
eapply (@fextI _ _ _ Φ1 (S ++ Φ2)).
eapply rmI_eq. apply rmI. apply ImpL_And_rule_I.
reflexivity. simpl.  reflexivity.
simpl. apply dersrec_singleI. apply derp.  Qed.

Print Implicit gen_sctrL_ImpL_And.

Lemma lja_ra_ImpL_And V B C D : 
  rel_adm LJArules (srs_ext_rel (sctr_rel (Imp C (Imp D B)))) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel (@Imp V (And C D) B))).
Proof. intros. apply gen_sctrL_ImpL_And.
apply crd_ra.  apply LJA_can_rel_ImpL_And_inv.
unfold LJArules. intro. apply fer_mono.
intros ps' c' ra.  eapply il_anc.
epose (rsubD (rm_mono (rsubI _ _ And_ail))).  exact (r _ _ ra).
exact X. Qed.

Print Implicit lja_ra_ImpL_And.

(* left contraction of Imp (Or C D) B by induction on the formula *)
Lemma gen_sctrL_ImpL_Or V W rules (B C D : PropF V)
  (Linv : rel_adm rules (srs_ext_rel (@ImpL_Or_inv V))):
  (forall G : W,
    rsub (fst_ext_rls (rlsmap (flip pair G) (@ImpL_Or_rule V))) rules) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp C B))) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp D B))) ->
  rel_adm rules (srs_ext_rel (sctr_rel (Imp (Or C D) B))).
Proof. intros rs ctra ctrb.  apply rel_admI.
intros * sqrc. apply radmI.
intro derp. destruct sqrc. destruct s.
(* invert one instance of Imp (Or C D) B *)
eapply Linv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ Φ1 (S ++ [Imp (Or C D) B] ++ Φ2)).
apply fslr_I. apply (ImpL_Or_invs_I B C D).
list_assoc_r. simpl. reflexivity.  reflexivity.
(* invert 2nd instance of Imp (Or C D) B *)
eapply Linv in derp.  all:cycle 1.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [Imp C B; Imp D B] ++ S) Φ2).
apply fslr_I. apply (ImpL_Or_invs_I B C D).
list_assoc_r. simpl. reflexivity.  reflexivity.
revert derp. list_assoc_r. simpl. intro derp.
(* contract Imp C B *)
destruct ctra. erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ Φ1 (Imp D B :: Φ2)).
apply (sctr_relI (Imp C B) (Imp D B :: S)).  reflexivity.  reflexivity.
destruct r. revert d. list_assoc_r'. simpl.  intro d.
apply d in derp. clear d.
(* contract Imp D B *)
destruct ctrb.  erequire r.  erequire r.  require r.
eapply (srs_ext_relI_eq _ _ _ (Φ1 ++ [Imp C B]) Φ2).
apply (sctr_relI (Imp D B) S).  
list_assoc_r'. simpl.  reflexivity.
list_assoc_r'. simpl.  reflexivity.
destruct r.  apply d in derp. clear d.
(* apply ImpL_Or_rule rule to contracted premises *)
eapply derI. apply (rsubD (rs G)).
eapply (@fextI _ _ _ Φ1 (S ++ Φ2)).
eapply rmI_eq. apply rmI. apply ImpL_Or_rule_I.
reflexivity. simpl.  reflexivity.
simpl. apply dersrec_singleI. apply derp.  Qed.

Print Implicit gen_sctrL_ImpL_Or.

Lemma lja_ra_ImpL_Or V B C D : 
  rel_adm LJArules (srs_ext_rel (sctr_rel (Imp C B))) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel (Imp D B))) ->
  rel_adm LJArules (srs_ext_rel (sctr_rel (@Imp V (Or C D) B))).
Proof. intros. apply gen_sctrL_ImpL_Or.
apply crd_ra.  apply LJA_can_rel_ImpL_Or_inv.
unfold LJArules. intro. apply fer_mono.
intros ps' c' ra.  eapply il_anc.
epose (rsubD (rm_mono (rsubI _ _ Or_ail))).  exact (r _ _ ra).
exact X. exact X0. Qed.

Print Implicit lja_ra_ImpL_Or.

Lemma lja_ctr_il {V} ps s (l : @LJAilrules V ps [s])
  (sub : forall A', dnsubfml A' s -> forall x, derrec LJArules emptyT x ->
    can_rel LJArules (fun fml' : PropF V => srs_ext_rel (sctr_rel fml')) A' x) :
  rel_adm LJArules (srs_ext_rel (sctr_rel s)).
Proof. inversion l ; subst ; clear l.
+ inversion H. subst. clear H.  apply lja_ra_ImpL_And.
apply crd_ra.  exact (sub _ (dnsub_Imp_AndL _ _ _)).
+ inversion H. subst. clear H.  apply lja_ra_ImpL_Or.
apply crd_ra.  exact (sub _ (dnsub_Imp_OrL1 _ _ _)).
apply crd_ra.  exact (sub _ (dnsub_Imp_OrL2 _ _ _)).
Qed.

Definition gs_lja_ilrules V A Γ1 Γ2 G ps c := @gs_ljg_glrules V
  A _ _ _ Γ1 Γ2 G ps c LJAil_single il_anc' lja_ctr_il.

(*


*)


(* 



for contraction for LJA have so far
Check lja_ra_And.
Check lja_ra_Or.
Check gs_sctr_lja_And.
Check gs_sctr_lja_Or.
Check gs_lja_rrules.
Check lja_der_Bot.
Check lja_ctr_lrls.
Check gs_lja_lrules.

proof for lj

Lemma ctr_adm_lj V (fml : PropF V) :
  forall seq, derrec LJrules emptyT seq ->
  can_rel LJrules (fun fml' => srs_ext_rel (sctr_rel fml')) fml seq.
Proof. eapply gen_step_lemT. apply AccT_isubfml.
intros * ljpc. destruct ljpc.
destruct r. destruct l.
- (* ImpLrule *)
exact (gs_lj_ImpL _ _ i).
- (* ImpRrule *)
exact (gs_lj_ImpR _ _ _ i).
- (* Idrule *)
exact (gs_sctr_Id _ _ _ i). CHANGED
- (* left rules *)
exact (gs_lj_lrules _ _ r).
- (* right rules *)
exact (gs_lj_rrules _ _ _ r).

Qed.

similar proof for lja

Lemma ctr_adm_lja V (fml : PropF V) :
  forall seq, derrec LJArules emptyT seq ->
  can_rel LJArules (fun fml' => srs_ext_rel (sctr_rel fml')) fml seq.
Proof. eapply gen_step_lemT. apply AccT_dnsubfml.
intros * ljpc. destruct ljpc.
destruct r. destruct l.
- (* LJAilrules *)
exact (gs_lja_ilrules _ _ r).
- (* ImpL_Imp_rule *)
admit.
- (* ImpLrule *)
admit.
- (* ImpRrule *)
admit.
- (* Idrule *)
eapply gs_sctr_Id. 2: exact i. apply rsubI. apply Id_anc.
- (* left rules *)
exact (gs_lja_lrules _ _ r).
- (* right rules *)
exact (gs_lja_rrules _ _ _ r).

Admitted.

*)

