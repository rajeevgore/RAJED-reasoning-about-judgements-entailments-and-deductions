
(* LJA logic, using lists of formulae *)
(* lemmas in Roy Dyckhoff and Sara Negri,
Admissibility of Structural Rules for Contraction-Free Systems of
Intuitionistic Logic, JSL 65 (2000), 1499-1518 *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.

Test Universe Polymorphism. (* NB Set this causes errors *)
Test Printing Universes.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT dd_fc.
Require Import List_lemmasT swappedT.
Require Import gen_tacs.
Require Import gen_seq gstep gentree rtcT.
Require Import ljt ljt_inv.
Require Import Coq.Program.Basics.

(* don't seem to use LJA_der_id, LJT_der_id
(* lemma for use in LJA_der_id and LJT_der_id *)
Lemma LJX_der_id_lem {V} rules A
  (IH : forall y : PropF V, dnsubfml y A ->
    forall G, derrec (fst_ext_rls rules) emptyT (y :: G, y))
  (Hv : forall y : PropF V, dnsubfml y A -> forall G v,
    derrec (fst_ext_rls rules) emptyT (Imp (Var v) y :: Var v :: G, y))
  (Id_xnc' : forall v : V, rules [] ([Var v], Var v))
  (ImpR_xnc' : forall A B, rules [([A], B)] ([], Imp A B))
  (Imp_xnc' : forall B C D G,
    rules [([Imp D B; C], D); ([B], G)] ([Imp (Imp C D) B], G))
  (il_xnc' : forall G ps c, LJAilrules ps c -> 
    rules (map (flip pair G) ps) (flip pair G c))
  (lrls_xnc' : forall G ps c, LJslrules ps c -> 
    rules (map (flip pair G) ps) (flip pair G c))
  (rrls_xnc' : forall ps c, LJsrrules ps c -> 
    rules (map (pair []) ps) ([], c))
  (exchL_ljx : forall concl, derrec (fst_ext_rls rules) emptyT concl ->
     forall concl', fst_rel (@swapped _) concl concl' ->
     derrec (fst_ext_rls rules) emptyT concl') 
  (rel_adm_ImpR : rel_adm (fst_ext_rls rules) (rr_ext_rel ImpRinv)) :
  forall G, derrec (fst_ext_rls rules) emptyT (A :: G, A).
Proof. intro.  destruct A.
- eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply Id_xnc'.
reflexivity. apply dlNil.
- eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply lrls_xnc'.  apply Bot_sl'.
reflexivity. apply dlNil.

- (* Imp *)
eapply derI. eapply (@fextI _ _ _ [_] G).
eapply rmI_eqc. apply ImpR_xnc'. reflexivity.
apply dersrec_singleI.  destruct A1.
+ (* Imp (Var v) A2 - use the special hypothesis *)
sfs. apply Hv. apply dnsub_ImpR.
+ eapply derI. eapply (@fextI _ _ _ [_] G).
eapply rmI_eqc. apply lrls_xnc'. apply Bot_sl'.  reflexivity.
apply dlNil.
+ eapply derI. eapply (@fextI _ _ _ [] (_ :: G)).
eapply rmI_eqc. apply Imp_xnc'. reflexivity.
apply dlCons.  (* now invert ImpR rule *)
pose rel_adm_ImpR.  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r). sfs.
eapply (rr_ext_relI_eqc _ _ _ [_] (_ :: G)).
apply ImpRinv_I. reflexivity.
specialize (IH _ (dnsub_ImpL _ _) (Imp A1_2 A2 :: G)). 
apply (exchL_ljx _ IH).  apply fst_relI.  apply swapped_cc.
apply dersrec_singleI.
apply (IH _ (dnsub_ImpR _ _)).

+ eapply derI. eapply (@fextI _ _ _ [_] G).
eapply rmI_eqc. apply lrls_xnc'. apply AndL_sl'.  reflexivity.
apply dersrec_singleI.
eapply derI. eapply (@fextI _ _ _ [] _).
eapply rmI_eqc. apply il_xnc'.
apply And_ail'.  reflexivity.
apply dersrec_singleI.  simpl.
(* now use invertibility of ImpR twice *)
pose rel_adm_ImpR.  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).  unfold fmlsext. simpl.
eapply (rr_ext_relI_eqc _ _ _ [_ ; _] G).
apply ImpRinv_I. reflexivity. clear r.
pose rel_adm_ImpR.  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).  
eapply (rr_ext_relI_eqc _ _ _ [_] G).
apply ImpRinv_I. reflexivity.
apply (IH _ (dnsub_Imp_AndL _ _ _)).

+ eapply derI. eapply (@fextI _ _ _ [] _).
eapply rmI_eqc. apply il_xnc'.
apply Or_ail'.  reflexivity.
apply dersrec_singleI.  simpl.
eapply derI. eapply (@fextI _ _ _ [_ ; _] _).
eapply rmI_eqc. apply lrls_xnc'. apply OrL_sl'.  reflexivity.
simpl. unfold fmlsext. simpl. apply dlCons.
(* now invert ImpR rule *)
pose rel_adm_ImpR.  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).
eapply (rr_ext_relI_eqc _ _ _ [_ ; _] G).
apply ImpRinv_I. reflexivity.
apply (IH _ (dnsub_Imp_OrL1 _ _ _)).
apply dersrec_singleI.  (* now invert ImpR rule *)
pose rel_adm_ImpR.  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r).
eapply (rr_ext_relI_eqc _ _ _ [_ ; _] G).
apply ImpRinv_I. reflexivity.
(* now need to use exchange *)
specialize (IH _ (dnsub_Imp_OrL2 _ _ _) (Imp A1_1 A2 :: G)).
apply (exchL_ljx _ IH).  apply fst_relI.  apply swapped_cc.

- eapply derI. eapply (@fextI _ _ _ [] (And A1 A2 :: G)).
eapply rmI_eqc. apply rrls_xnc'. apply AndR_sr'.
reflexivity.  apply dlCons.
-- eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply lrls_xnc'. apply AndL_sl'.
reflexivity.  apply dersrec_singleI.
apply IH. apply dnsub_AndL. 
-- apply dersrec_singleI.
eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply lrls_xnc'. apply AndL_sl'.
reflexivity.  apply dersrec_singleI.
(* need to use exchange *)
sfs.  specialize (IH _ (dnsub_AndR _ _) (A1 :: G)). 
apply (exchL_ljx _ IH). apply fst_relI. apply swapped_cc.
- eapply derI. eapply (@fextI _ _ _ [] G).
eapply rmI_eqc. eapply lrls_xnc'. apply OrL_sl'.
reflexivity.  apply dlCons.
-- eapply derI. eapply (@fextI _ _ _ [A1] G).
eapply rmI_eqc. apply rrls_xnc'. apply OrR1_sr'.
reflexivity.  apply dersrec_singleI.
apply (IH _ (dnsub_OrL _ _)).
-- apply dersrec_singleI.
eapply derI. eapply (@fextI _ _ _ [A2] G).
eapply rmI_eqc. apply rrls_xnc'. apply OrR2_sr'.
reflexivity.  apply dersrec_singleI.
apply (IH _ (dnsub_OrR _ _)).
Qed.

Print Implicit LJX_der_id_lem.

(* Lemma 3.2(1) of Dyckhoff & Negri JSL 2000 *)
Lemma LJT_der_id {V} :
  forall (A : PropF V) (a : AccT dnsubfml A), 
  forall G, derrec LJTrules emptyT (A :: G, A).
Proof. 
epose (AccT_rect (fun A _ => 
  (forall G, derrec LJTrules emptyT (A :: G, A)))).
apply d. clear d.  intros A adn IH G.  
apply LJX_der_id_lem.
- exact IH.
- intros. eapply derI. eapply (@fextI _ _ _ [] G0).
eapply rmI_eqc. apply atom_tnc'. sfs. reflexivity. 
apply dersrec_singleI. sfs.  exact (IH _ H _). 
- apply Id_tnc'.  - apply ImpR_tnc'.  - apply Imp_tnc'.
- apply il_tnc'.  - apply lrls_tnc'.  - apply rrls_tnc'.
- apply exchL_ljt.  - apply LJT_rel_adm_ImpR.
Qed.

Lemma LJA_der_id {V} :
  forall (A : PropF V) (a : AccT dnsubfml A), 
  forall G, derrec LJArules emptyT (A :: G, A).
Proof. 
epose (AccT_rect (fun A _ => 
  (forall G, derrec LJArules emptyT (A :: G, A)))).
apply d. clear d.  intros A adn IH G.  
apply LJX_der_id_lem.
- exact IH.
- (* now deal with Imp (Var v) y *)
intros.  eapply derI. eapply (@fextI _ _ _ [] (Var v :: G0)).
eapply rmI_eqc. apply ImpL_anc'. reflexivity. 
apply dlCons.
eapply derI. eapply (@fextI _ _ _ [_] G0).
eapply rmI_eqc. apply Id_anc'. reflexivity. apply dlNil.
apply dersrec_singleI.
apply (IH _ H). 

- apply Id_anc'.  - apply ImpR_anc'.  - apply Imp_anc'.
- apply il_anc'.  - apply lrls_anc'.  - apply rrls_anc'.
- apply exchL_lja.  - apply LJA_rel_adm_ImpR.
Qed.
*)

(*
don't do this - wrong, follow proof in paper, just do Lemma 3.2 (1) first
Lemma LJA_der_id_mp {V} :
  forall (A : PropF V) (a : AccT dnsubfml A), 
  (forall G, derrec LJArules emptyT (A :: G, A)) *
  (forall B H, derrec LJArules emptyT (A :: Imp A B :: H, B)).
*)

(* don't seem to use LJA_der_mp, LJT_der_mp 
(* Lemma 3.2(2) of Dyckhoff & Negri JSL 2000 *)
Lemma LJA_der_mp {V} (A B : PropF V) H :
  derrec LJArules emptyT (A :: Imp A B :: H, B).
Proof. 
pose (LJA_rel_adm_ImpR V).  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r). 
eapply (rr_ext_relI_eqc _ _ _ [] _).
apply ImpRinv_I. reflexivity. clear r.
apply LJA_der_id. apply AccT_dnsubfml. Qed.

Lemma LJT_der_mp {V} (A B : PropF V) H :
  derrec LJTrules emptyT (A :: Imp A B :: H, B).
Proof. 
pose (LJT_rel_adm_ImpR V).  destruct r.  erequire r.  erequire r.  require r.
2: eapply (radmD r). 
eapply (rr_ext_relI_eqc _ _ _ [] _).
apply ImpRinv_I. reflexivity. clear r.
apply LJT_der_id. apply AccT_dnsubfml. Qed.
*)

(* Lemma 4.1 of Dyckhoff & Negri JSL 2000 *)
(* relevant property of sequent to be proved by induction *)
Definition l41prop {V} (D : PropF V) seq := 
  forall G1 G2, seq = (G1 ++ G2, D) -> 
  forall B E, derrec LJArules emptyT (fmlsext G1 G2 [B], E) ->
  derrec LJArules emptyT (apfst (fmlsext G1 G2) ([Imp D B], E)).

Definition l41prop_t {V} (D : PropF V) seq := 
  forall G1 G2, seq = (G1 ++ G2, D) -> 
  forall B E, derrec LJTrules emptyT (fmlsext G1 G2 [B], E) ->
  derrec LJTrules emptyT (apfst (fmlsext G1 G2) ([Imp D B], E)).

(* trying this instead of l41prop and l41prop_t
  runs into trouble at the second appe in inv_gl_tac
  TODO investigate and fix in due course *)
Definition l41prop' {V} (rules : rlsT (srseq (PropF V))) D seq := 
  forall G1 G2, seq = (G1 ++ G2, D) -> 
  forall B E, derrec rules emptyT (fmlsext G1 G2 [B], E) ->
  derrec rules emptyT (apfst (fmlsext G1 G2) ([Imp D B], E)).

Lemma l41_t' {V} D seq : @l41prop_t V D seq -> @l41prop' V LJTrules D seq.
Proof. firstorder. Qed.
Lemma l41' {V} D seq : @l41prop V D seq -> @l41prop' V LJArules D seq.
Proof. firstorder. Qed.

Lemma LJX_inv_sl V LJXrules G1 G2 E ps c 
  (LJX_can_rel_AndLinv : forall seq, derrec LJXrules emptyT seq ->
       can_rel LJXrules (srs_ext_rel (Y:=PropF V)) AndLinv seq)
  (LJX_can_rel_OrLinv1 : forall seq, derrec LJXrules emptyT seq ->
       can_rel LJXrules (srs_ext_rel (Y:=PropF V)) OrLinv1 seq)
  (LJX_can_rel_OrLinv2 : forall seq, derrec LJXrules emptyT seq ->
       can_rel LJXrules (srs_ext_rel (Y:=PropF V)) OrLinv2 seq) :
  (@LJslrules V) ps c -> derrec LJXrules emptyT (G1 ++ c ++ G2, E) -> 
  dersrec LJXrules emptyT (map (apfst (fmlsext G1 G2)) (map (flip pair E) ps)).
Proof. intros ljpc dce.  destruct ljpc.
- destruct a.
apply LJX_can_rel_AndLinv in dce.
unfold can_rel in dce.
apply dersrec_singleI.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply AndLinvs_I.  reflexivity.  reflexivity.
- destruct o.
apply dlCons.
+ apply LJX_can_rel_OrLinv1 in dce.
unfold can_rel in dce.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply OrLinv1s_I.  reflexivity.  reflexivity.
+ apply dersrec_singleI.
apply LJX_can_rel_OrLinv2 in dce.
unfold can_rel in dce.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply OrLinv2s_I.  reflexivity.  reflexivity.
- (* Botrule *)
destruct b. apply dlNil. Qed.

Definition LJA_inv_sl V G1 G2 E ps c := @LJX_inv_sl V _ G1 G2 E ps c
  LJA_can_rel_AndLinv LJA_can_rel_OrLinv1 LJA_can_rel_OrLinv2.
Definition LJT_inv_sl V G1 G2 E ps c := @LJX_inv_sl V _ G1 G2 E ps c
  LJT_can_rel_AndLinv LJT_can_rel_OrLinv1 LJT_can_rel_OrLinv2.

Lemma LJX_inv_ail V (LJXrules : rlsT (srseq (PropF V))) G1 G2 E ps c 
  (LJX_can_rel_ImpL_And_inv : forall seq, derrec LJXrules emptyT seq ->
       can_rel LJXrules (@srs_ext_rel _ (PropF V)) ImpL_And_inv seq)
  (LJX_can_rel_ImpL_Or_inv : forall seq, derrec LJXrules emptyT seq ->
       can_rel LJXrules (srs_ext_rel (Y:=PropF V)) ImpL_Or_inv seq) :
  (@LJAilrules V) ps c -> derrec LJXrules emptyT (G1 ++ c ++ G2, E) -> 
  dersrec LJXrules emptyT (map (apfst (fmlsext G1 G2)) (map (flip pair E) ps)).
Proof. intros ljpc dce.  destruct ljpc ; destruct i.
- apply LJX_can_rel_ImpL_And_inv in dce.
unfold can_rel in dce.
apply dersrec_singleI.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply ImpL_And_invs_I.  reflexivity.  reflexivity.
- apply LJX_can_rel_ImpL_Or_inv in dce.
unfold can_rel in dce.
apply dersrec_singleI.
apply dce.  simpl.  unfold fmlsext.
eapply srs_ext_relI_eq.  apply fslr_I.
apply ImpL_Or_invs_I.  reflexivity.  reflexivity. Qed.

Definition LJA_inv_ail V G1 G2 E ps c := @LJX_inv_ail V _ G1 G2 E ps c
  LJA_can_rel_ImpL_And_inv LJA_can_rel_ImpL_Or_inv.
Definition LJT_inv_ail V G1 G2 E ps c := @LJX_inv_ail V _ G1 G2 E ps c
  LJT_can_rel_ImpL_And_inv LJT_can_rel_ImpL_Or_inv.

(* not sure if we need this *)
Lemma LJAil_psne V ps c : (@LJAilrules V) ps c ->
  sigT (fun p => sigT (fun pt => ps = p :: pt)).
Proof. intro ljpc. 
destruct ljpc ; destruct i ; eexists ; eexists ; reflexivity. Qed.

Lemma LJAil_sing V ps c : (@LJAilrules V) ps c -> sigT (fun c' => c = [c']).
Proof. intro ljpc.  destruct ljpc ; destruct i ; eexists ; reflexivity. Qed.

Lemma LJAil_sing_empty V ps c : (@LJAilrules V) ps c -> sing_empty c.
Proof. intro ljpc.  destruct ljpc ; destruct i ; apply se_single. Qed.

Lemma LJsl_sing V ps c : (@LJslrules V) ps c -> sigT (fun c' => c = [c']).
Proof. intro ljpc.  
destruct ljpc ; rename_last r ; destruct r ; eexists ; reflexivity. Qed.

Lemma LJsl_sing_empty V ps c : (@LJslrules V) ps c -> sing_empty c.
Proof. intro ljpc. apply LJsl_sing in ljpc. cD. subst. apply se_single.  Qed. 

Lemma pair_eqD U W a b c d : (a : U, b : W) = (c, d) -> (a = c) * (b = d).
Proof. intro H. inversion H. tauto. Qed.

Ltac appe := match goal with
    | [ H : _ = _ |- _ ] => apply pair_eqD in H ; destruct H end.

(* apply rule in desired conclusion *)

Ltac inv_gl_tac gl_anc LJA_inv_gl c0 H fp dbe cin1 := 
simpl ;  unfold fmlsext ;  assoc_mid c0 ;
eapply derI ; [ eapply fextI ;  eapply rmI_eqc ; [
eapply gl_anc ;  apply rmI ;  apply H | reflexivity ] | ] ;
apply dersrecI_forall ;  intros c cin ;
apply InT_mapE in cin ; cD ; rename_last cin1 ;
apply InT_mapE in cin1 ; cD ;
(* invert rule in dbe *)
revert dbe ; unfold fmlsext ; assoc_mid c0 ; intro dbe ;
pose (LJA_inv_gl _ _ _ _ _ _ H dbe) as d ;
eapply dersrecD_forall in d ; [ |
apply InT_map ;  apply InT_map ; eassumption ] ;
eapply ForallTD_forall in fp ; [ |
apply InT_map ;  apply InT_map ; eassumption ] ;
unfold l41prop in fp ;
unfold l41prop_t in fp ;
appe ; appe ; subst ;
unfold fmlsext ;  assoc_single_mid ;
simpl in fp ;  unfold fmlsext in fp ;
apply (snd fp) ; [ list_eq_assoc |
simpl in d ;  unfold fmlsext in d ;
apply (eq_rect _ _ d) ; list_eq_assoc ].

Lemma gs_LJA_ImpL_Ail V (D : PropF V) ps c Γ1 Γ2 G 
  (r : rlsmap (flip pair G) LJAilrules ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad.
unfold l41prop. intros * ceq * dbe.
inversion r. subst. clear r. 
rewrite ceq in dc.
simpl in ceq. unfold fmlsext in ceq.
inversion ceq. subst. clear ceq.
acacD'T2 ; subst.

- inv_gl_tac (@il_anc) LJA_inv_ail c0 X fp dbe cin1.

- pose (LJAil_sing_empty X). apply sing_empty_app in s.  sD ; subst.
+ simpl in X.  rewrite ?app_nil_r.
rewrite ?app_nil_r in dbe.  rewrite ?app_nil_r in dc.
inv_gl_tac (@il_anc) LJA_inv_ail H2 X fp dbe cin1.
+ rewrite ?app_nil_r in X.  simpl in dc.  simpl in dbe.
inv_gl_tac (@il_anc) LJA_inv_ail H0 X fp dbe cin1.

- inv_gl_tac (@il_anc) LJA_inv_ail c0 X fp dbe cin1.
Qed.

Lemma gs_LJT_ImpL_Ail V (D : PropF V) ps c Γ1 Γ2 G 
  (r : rlsmap (flip pair G) LJAilrules ps c) :
  gen_step l41prop_t D isubfml (derrec LJTrules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad.
unfold l41prop_t. intros * ceq * dbe.
inversion r. subst. clear r. 
rewrite ceq in dc.
simpl in ceq. unfold fmlsext in ceq.
inversion ceq. subst. clear ceq.
acacD'T2 ; subst.

- inv_gl_tac (@il_tnc) LJT_inv_ail c0 X fp dbe cin1.

- pose (LJAil_sing_empty X). apply sing_empty_app in s.  sD ; subst.
+ simpl in X.  rewrite ?app_nil_r.
rewrite ?app_nil_r in dbe.  rewrite ?app_nil_r in dc.
inv_gl_tac (@il_tnc) LJT_inv_ail H2 X fp dbe cin1.
+ rewrite ?app_nil_r in X.  simpl in dc.  simpl in dbe.
inv_gl_tac (@il_tnc) LJT_inv_ail H0 X fp dbe cin1.

- inv_gl_tac (@il_tnc) LJT_inv_ail c0 X fp dbe cin1.
Qed.

Check gs_LJA_ImpL_Ail.  Check gs_LJT_ImpL_Ail.

Lemma gs_LJA_ImpL_sl V (D : PropF V) ps c Γ1 Γ2 G 
  (r : rlsmap (flip pair G) LJslrules ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad.
unfold l41prop. intros * ceq * dbe.
inversion r. subst. clear r. 
rewrite ceq in dc.
simpl in ceq. unfold fmlsext in ceq.
inversion ceq. subst. clear ceq.
acacD'T2 ; subst.

- inv_gl_tac (@lrls_anc) LJA_inv_sl c0 X fp dbe cin1.

- pose (LJsl_sing_empty X). apply sing_empty_app in s.  sD ; subst.
+ simpl in X.  rewrite ?app_nil_r.
rewrite ?app_nil_r in dbe.  rewrite ?app_nil_r in dc.
inv_gl_tac (@lrls_anc) LJA_inv_sl H2 X fp dbe cin1.
+ rewrite ?app_nil_r in X.  simpl in dc.  simpl in dbe.
inv_gl_tac (@lrls_anc) LJA_inv_sl H0 X fp dbe cin1.

- inv_gl_tac (@lrls_anc) LJA_inv_sl c0 X fp dbe cin1.
Qed.

Lemma gs_LJT_ImpL_sl V (D : PropF V) ps c Γ1 Γ2 G 
  (r : rlsmap (flip pair G) LJslrules ps c) :
  gen_step l41prop_t D isubfml (derrec LJTrules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad.
unfold l41prop_t. intros * ceq * dbe.
inversion r. subst. clear r. 
rewrite ceq in dc.
simpl in ceq. unfold fmlsext in ceq.
inversion ceq. subst. clear ceq.
acacD'T2 ; subst.

- inv_gl_tac (@lrls_tnc) LJT_inv_sl c0 X fp dbe cin1.

- pose (LJsl_sing_empty X). apply sing_empty_app in s.  sD ; subst.
+ simpl in X.  rewrite ?app_nil_r.
rewrite ?app_nil_r in dbe.  rewrite ?app_nil_r in dc.
inv_gl_tac (@lrls_tnc) LJT_inv_sl H2 X fp dbe cin1.
+ rewrite ?app_nil_r in X.  simpl in dc.  simpl in dbe.
inv_gl_tac (@lrls_tnc) LJT_inv_sl H0 X fp dbe cin1.

- inv_gl_tac (@lrls_tnc) LJT_inv_sl c0 X fp dbe cin1.
Qed.

Check gs_LJA_ImpL_sl.  Check gs_LJT_ImpL_sl.

Ltac gs_Imp_p_tac V c p A B D E X X0 X1 dbe La Ra Lb Rb Lc Rc Ld Rd :=
erequire c ; require c ; [
(* inversion of ImpLrule_p (2nd premise) in dbe *)
eapply (srs_ext_relI_eqp _ [Imp (Var p) A] [A] La Ra) ; [
split ; apply ImpL_Var_inv2s_I |
unfold fmlsext ; list_eq_assoc ] | ] ; 
(* apply IH to 2nd premise of ... |- D *)
clear dbe ; unfold l41prop in X0 ; specialize (X0 Lb Rb) ;
require X0 ; [ list_eq_assoc | ] ;
specialize (X0 B E) ;
require X0 ; [ unfold fmlsext ; apply (eq_rect _ _ c) ; list_eq_assoc | ] ;
(* weaken Imp D B into X *)
clear X1 c ; simpl in X0 ; unfold fmlsext in X0 ;
pose (@insL_lja V Lc Rc [Imp D B] (Var p)) as d ;
require d ; [ apply (eq_rect _ _ X) ; list_eq_assoc | ] ;
clear X ; simpl ; unfold fmlsext ;
(* now apply ImpLrule_p *)
eapply derI ; [ eapply (@fextI _ _ _ Ld Rd) ;
eapply rmI_eqc ; [ apply ImpL_anc' |
simpl ; unfold fmlsext ; list_eq_assoc ] |
apply dlCons ; [
  simpl ; unfold fmlsext ; apply (eq_rect _ _ d) ; list_eq_assoc |
apply dersrec_singleI ;
simpl ; unfold fmlsext ; apply (eq_rect _ _ X0) ; list_eq_assoc ] ].

Lemma gs_LJA_ImpL_Imp_p V (D : PropF V) ps c Γ1 Γ2 (r : ImpLrule_p ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad dc.
unfold l41prop. intros * ceq * dbe.  destruct r as [p A D'].
inversion ceq. subst. clear ceq. 
inversion fp.  inversion X0. clear fp X0 X2. subst.

unfold fmlsext in H0.  unfold fmlsext in X.  unfold fmlsext in X1.
pose (LJA_can_rel_ImpL_Var_inv2 dbe). 
unfold can_rel in c.
acacD'T2 ; subst ; clear X2.

- gs_Imp_p_tac V c p A B D E X X0 X1 dbe
(G1 ++ [B] ++ H0) Γ2 G1 (H0 ++ [A] ++ Γ2)
 G1 (H0 ++ [Imp (Var p) A] ++ Γ2) (G1 ++ [Imp D B] ++ H0) Γ2.

- gs_Imp_p_tac V c p A B D E X X0 X1 dbe
(Γ1 ++ [B]) Γ2 Γ1 ([A] ++ Γ2) Γ1 ([Imp (Var p) A] ++ Γ2) (Γ1 ++ [Imp D B]) Γ2.

- list_eq_ncT. cD. subst.
gs_Imp_p_tac V c p A B D E X X0 X1 dbe
 Γ1 ([B] ++ Γ2) (Γ1 ++ [A]) Γ2 (Γ1 ++ [Imp (Var p) A]) Γ2 Γ1 ([Imp D B] ++ Γ2).

- gs_Imp_p_tac V c p A B D E X X0 X1 dbe
 Γ1 (H2 ++ [B] ++ G2) (Γ1 ++ [A] ++ H2) G2
 (Γ1 ++ [Imp (Var p) A] ++ H2) G2 Γ1 (H2 ++ [Imp D B] ++ G2).

Qed.

Check gs_LJA_ImpL_Imp_p.

Lemma gs_LJX_ImpL_sr V LJXncrules (D : PropF V) ps c Γ1 Γ2 
  (il_xnc' : forall G ps c, LJAilrules ps c ->
    LJXncrules (map (flip pair G) ps) (flip pair G c))
  (insL_ljx : forall cl cr mid G, 
      derrec (fst_ext_rls LJXncrules) emptyT (cl ++ cr, G) ->
      derrec (fst_ext_rls LJXncrules) emptyT (cl ++ mid ++ cr, G))
  (r : rlsmap (pair []) LJsrrules ps c) :
  gen_step (l41prop' (fst_ext_rls LJXncrules)) D isubfml 
    (derrec (fst_ext_rls LJXncrules) emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. 
unfold l41prop'. intros * ceq * dbe.
inversion r. subst. clear r. 
inversion ceq. subst. clear ceq. 
destruct X.
- destruct a.  simpl in fp.  inversion fp.
inversion X0. clear fp X0 X2. subst.
rewrite H0 in X.  rewrite H0 in X1.
pose (sad _ (isub_AndR _ _) _ (fst X1)).
specialize (l _ _ eq_refl _ _ dbe).
specialize (sad _ (isub_AndL _ _) _ (fst X)).
specialize (sad _ _ eq_refl _ _ l).
clear dc dbe H0 X X1 l.
eapply derI. eapply fextI. apply rmI.
apply il_xnc'. apply And_ail'.
exact (dersrec_singleI sad).
- destruct o.  simpl in fp.  inversion fp.  clear fp X0. subst.
rewrite H0 in X.
specialize (sad _ (isub_OrL _ _) _ (fst X)).
specialize (sad _ _ eq_refl _ _ dbe).
clear dc dbe H0 X.
eapply derI. eapply fextI. apply rmI.
apply il_xnc'. apply Or_ail'. simpl. simpl in sad.
pose (insL_ljx (G1 ++ [Imp A B]) G2 [Imp B0 B]).
rewrite <- !app_assoc in d.
apply d in sad.  unfold fmlsext.  exact (dersrec_singleI sad).
- destruct o.  simpl in fp.  inversion fp.  clear fp X0. subst.
rewrite H0 in X.
specialize (sad _ (isub_OrR _ _) _ (fst X)).
specialize (sad _ _ eq_refl _ _ dbe).
clear dc dbe H0 X.
eapply derI. eapply fextI. apply rmI.
apply il_xnc'. apply Or_ail'. simpl. simpl in sad.
pose (insL_ljx G1 (Imp B0 B :: G2) [Imp A B]).
apply d in sad.  unfold fmlsext.  exact (dersrec_singleI sad).
Qed.

Definition gs_LJT_ImpL_sr V D ps c Γ1 Γ2 :=
  @gs_LJX_ImpL_sr V _ D ps c Γ1 Γ2 il_tnc' (@insL_ljt V).
Definition gs_LJA_ImpL_sr V D ps c Γ1 Γ2 :=
  @gs_LJX_ImpL_sr V _ D ps c Γ1 Γ2 il_anc' (@insL_lja V).

(* not sure if we need this or can just use gs_LJA_ImpL_sr' 
Lemma gs_LJA_ImpL_sr V (D : PropF V) ps c Γ1 Γ2 
  (r : rlsmap (pair []) LJsrrules ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. apply gs_LJA_ImpL_sr'. exact r. Qed.
*)

Check gs_LJX_ImpL_sr.  Check gs_LJA_ImpL_sr.  Check gs_LJT_ImpL_sr.

(*

Check gen_step_lemT.
Check gen_step_c_lem.  Check gen_step_tr_lem. Check gf2_step_tr_lem.
Check height_step_tr_lem.

(* proof using gen_step_lemT, don't think we want this *)
Definition l41dtprop {V} rules prems (D : PropF V) dt := 
  l41prop D (@derrec_fc_concl _ rules prems dt).
  *)
  
Ltac gs_ImpL_tac insL_ljx Imp_xnc'
  B C D E F G H X X1 dbe La Ra Lb Rb Lc Rc Ld Rd :=
(* inversion in dbe *)
unfold can_rel in dbe ;  erequire dbe ;  require dbe ; [
eapply (srs_ext_relI_eqp _ [Imp (Imp F G) H] [H] La Ra) ; [
split ; apply ImpL_Imp_inv2s_I | unfold fmlsext ; list_eq_assoc ] | ] ;
(* apply IH *)
unfold l41prop in X1 ; unfold l41prop_t in X1 ; unfold l41prop' in X1 ; 
simpl in X1 ; unfold fmlsext in X1 ;
specialize (X1 Lb Rb) ; require X1 ; [ list_eq_assoc | ] ;
specialize (X1 B E) ;
require X1 ; [ apply (eq_rect _ _ dbe) ; list_eq_assoc | ] ; clear dbe ;
(* apply weakening to left premise of ... |- D *)
unfold fmlsext in X ;
pose (insL_ljx Lc Rc [Imp D B] G) as d ;
require d ; [ apply (eq_rect _ _ X) ; list_eq_assoc | ] ;
clear X ; simpl ; unfold fmlsext ;
(* now apply ImpL_Imp_rule *)
eapply derI ; [ eapply (@fextI _ _ _ Ld Rd) ;
apply (rmI_eqc _ _ _ _ (Imp_xnc' H F G E)) ;
simpl ; unfold fmlsext ; list_eq_assoc |
simpl ; unfold fmlsext ;
apply dlCons ; [ apply (eq_rect _ _ d) ; list_eq_assoc |
apply dersrec_singleI ; apply (eq_rect _ _ X1) ; list_eq_assoc ] ].

Lemma gs_LJX_ImpL_ImpL V LJXncrules (D : PropF V) ps c Γ1 Γ2 
  (LJX_can_rel_ImpL_Imp_inv2 : forall seq : list (PropF V) * PropF V,
       derrec (fst_ext_rls LJXncrules) emptyT seq ->
       can_rel (fst_ext_rls LJXncrules) (@srs_ext_rel _ _) ImpL_Imp_inv2 seq)
  (Imp_xnc' : forall (B C D G : PropF V),
       LJXncrules [([Imp D B; C], D); ([B], G)] ([Imp (Imp C D) B], G))
  (insL_ljx : forall cl cr mid G, 
      derrec (fst_ext_rls LJXncrules) emptyT (cl ++ cr, G) ->
      derrec (fst_ext_rls LJXncrules) emptyT (cl ++ mid ++ cr, G))
  (r : ImpL_Imp_rule ps c) :
  gen_step (l41prop' (fst_ext_rls LJXncrules)) D isubfml 
    (derrec (fst_ext_rls LJXncrules) emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. unfold gen_step. intros sad fp dc. clear sad dc.
unfold l41prop'. intros * ceq * dbe.  destruct r as [H F G D'].
inversion ceq. subst. clear ceq. 
inversion fp.  inversion X0. clear fp X0 X2. subst.
apply fst in X. (* left premise of ... |- D, will want to weaken *)
apply snd in X1. (* right premise of ... |- D, will want to use IH *)
unfold fmlsext in H1.
acacD'T2 ; subst.

- apply LJX_can_rel_ImpL_Imp_inv2 in dbe.
gs_ImpL_tac insL_ljx Imp_xnc' B C D E F G H X X1 dbe
(G1 ++ [B] ++ H1) Γ2 G1 (H1 ++ [H] ++ Γ2)
G1 (H1 ++ [Imp G H; F] ++ Γ2) (G1 ++ [Imp D B] ++ H1) Γ2.

- rewrite ?app_nil_r.  rewrite ?app_nil_r in dbe. 
apply LJX_can_rel_ImpL_Imp_inv2 in dbe.
gs_ImpL_tac insL_ljx Imp_xnc' B C D E F G H X X1 dbe
(Γ1 ++ [B]) Γ2 Γ1 ([H] ++ Γ2)
Γ1 ([Imp G H; F] ++ Γ2) (Γ1 ++ [Imp D B]) Γ2.

- list_eq_ncT. cD. subst.
apply LJX_can_rel_ImpL_Imp_inv2 in dbe.
gs_ImpL_tac insL_ljx Imp_xnc' B C D E F G H X X1 dbe
Γ1 ([B] ++ Γ2) (Γ1 ++ [H]) Γ2
(Γ1 ++ [Imp G H; F]) Γ2 Γ1 ([Imp D B] ++ Γ2).

- apply LJX_can_rel_ImpL_Imp_inv2 in dbe.
gs_ImpL_tac insL_ljx Imp_xnc' B C D E F G H X X1 dbe
Γ1 (H2 ++ [B] ++ G2) (Γ1 ++ [H] ++ H2) G2
(Γ1 ++ [Imp G H; F] ++ H2) G2 Γ1 (H2 ++ [Imp D B] ++ G2).

Qed.

Definition gs_LJA_ImpL_ImpL' V D ps c Γ1 Γ2 :=
  @gs_LJX_ImpL_ImpL V LJAncrules D ps c Γ1 Γ2 
  LJA_can_rel_ImpL_Imp_inv2 (@Imp_anc' V) (@insL_lja V).
Definition gs_LJT_ImpL_ImpL' V D ps c Γ1 Γ2 :=
  @gs_LJX_ImpL_ImpL V LJTncrules D ps c Γ1 Γ2 
  LJT_can_rel_ImpL_Imp_inv2 (@Imp_tnc' V) (@insL_ljt V).

Lemma gs_LJT_ImpL_ImpL V (D : PropF V) ps c Γ1 Γ2 (r : ImpL_Imp_rule ps c) :
  gen_step (l41prop' LJTrules) D isubfml (derrec LJTrules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. apply gs_LJT_ImpL_ImpL'. exact r. Qed. 

(* not sure if we will need this *)
Lemma gs_LJA_ImpL_ImpL V (D : PropF V) ps c Γ1 Γ2 (r : ImpL_Imp_rule ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof. apply gs_LJA_ImpL_ImpL'. exact r. Qed. 

Check gs_LJA_ImpL_ImpL.

Lemma LJT_41_atom_cases V (Γ1 Γ2 G1 G2 : list (PropF V)) p B E 
  (dbe : derrec LJTrules emptyT (fmlsext G1 G2 [B], E))
  (H : fmlsext Γ1 Γ2 [Var p] = G1 ++ G2) :
  derrec LJTrules emptyT (apfst (fmlsext G1 G2) ([Imp (Var p) B], E)).
Proof. unfold fmlsext in *. simpl in *.  
acacD'T2 ; subst.
- apply (@exchL_ljt _ (G1 ++ H ++ Imp (Var p) B :: Var p :: Γ2, E)).
eapply derI.  eapply (@fextI _ _ _ (G1 ++ H) Γ2).
eapply rmI_eqc.  eapply atom_tnc'.  sfseq.
sfs. apply dersrec_singleI.  apply (exchL_ljt dbe).
apply fst_relI. swap_tac_Rc.  apply fst_relI. swap_tac_Rc.
- eapply derI. eapply (@fextI _ _ _ (Γ1 ++ []) Γ2).
eapply rmI_eqc. eapply atom_tnc'. reflexivity.
apply dersrec_singleI. exact dbe.

- apply (@exchL_ljt _ (Γ1 ++ Imp (Var p) B :: Var p :: H1 ++ G2, E)).
eapply derI.  eapply (@fextI _ _ _ Γ1 (H1 ++ G2)).
eapply rmI_eqc.  eapply atom_tnc'.  sfseq.
sfs. apply dersrec_singleI.  apply (exchL_ljt dbe).
apply fst_relI. swap_tac_Rc.
apply (swapped_simple' (Var p :: H1) [B]).
apply fst_relI. swap_tac_Rc.
apply (swapped_simple' [_] (Var p :: H1)).
Qed.

Lemma gs_LJT_ImpL_adm V (D : PropF V) ps c Γ1 Γ2 (r : LJTncrules ps c) :
  gen_step l41prop_t D isubfml (derrec LJTrules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof.  destruct r.
- destruct l.

-- (* left compound Imp rules, invertible *)
eapply gs_LJT_ImpL_Ail. exact r.

-- (* ImpL_Imp_rule *)
eapply gs_LJT_ImpL_ImpL. exact i.

-- (* ImpRrule, IH not used *) destruct i.  unfold gen_step.
intros sub fdt dab. clear sub dab.
inversion fdt. clear X0 fdt. subst.  unfold l41prop_t.
intros * abeq * dbe. destruct X. clear l.
inversion abeq. clear abeq. subst.
(* apply ImpL_Imp_rule *)
eapply derI.  eapply fextI.  apply rmI.  apply Imp_tnc'.
unfold fmlsext in H0. simpl in H0.
eapply swap_ins in H0.
unfold fmlsext in d.  eapply exchL_ljt in d.
2: apply fst_relI. 2: exact (swapped_comm H0).
apply dlCons.  exact (insL_ljt _ _ [Imp B B0] d).
apply dersrec_singleI. exact dbe.

-- (* Idrule, so D is Var _ , IH not used *) destruct i.
unfold gen_step.  intros sub fdt dt. clear sub fdt.  unfold l41prop_t.
intros * vveq * dbe.  inversion vveq. clear vveq. subst.
exact (LJT_41_atom_cases _ _ _ _ _ _ dbe H0).

-- (* common left rules, invertible *)
eapply gs_LJT_ImpL_sl. exact r.

-- (* simple right rules *)
eapply gs_LJT_ImpL_sr. exact r.

- (* ImpL_atom_rule *)
inversion r. subst. clear r. destruct X.
unfold gen_step.  intros sub fdt dt. clear sub dt.
inversion fdt. clear X0 fdt. subst.  unfold l41prop_t.
sfs. intros * abeq * dbe. destruct X.
inversion abeq. clear abeq d. subst.
acacD'T2 ; subst.

+ eapply derI.  apply (@fextI _ _ _ (G1 ++ Imp D B0 :: H0) Γ2).
eapply rmI_eqc. apply atom_tnc'. sfseq.
apply dersrec_singleI. revert l. sfs. list_assoc_r'. intro l.
apply l. reflexivity. sfs.
apply LJT_can_rel_ImpL_Var_inv2 in dbe.  apply dbe.
list_assoc_r'. apserc. apply ImpL_Var_inv2_I.

+ eapply derI.  apply (@fextI _ _ _ (Γ1 ++ [Imp D B0]) Γ2).
eapply rmI_eqc. apply atom_tnc'. sfseq.
apply dersrec_singleI. revert l. sfs. list_assoc_r'. intro l.
apply l. reflexivity. sfs.
apply LJT_can_rel_ImpL_Var_inv2 in dbe.  apply dbe.
list_assoc_r'. apserc. apply ImpL_Var_inv2_I.

+ (* this one needs exchange because the B and Imp D B
  are between the two principal formulae of the atom rule *)
(* swap ... B0 and Imp (Var p) B *)
eapply (@exchL_ljt V (Γ1 ++ Imp D B0 :: Imp (Var p) B :: Var p :: Γ2, E)).
pose (@exchL_ljt V _ dbe 
  (Γ1 ++ B0 :: Imp (Var p) B :: Var p :: Γ2, E)).
clearbody d. clear dbe.  require d. clear d.
apply fst_relI. list_assoc_r'. simpl. swap_tac. apply swapped_cc.
all: cycle 1.
apply fst_relI. list_assoc_r'. simpl. swap_tac. apply swapped_cc.
(* now should be similar to other cases *)
eapply derI.  apply (@fextI _ _ _ (Γ1  ++ [Imp D B0]) Γ2).
eapply rmI_eqc. apply atom_tnc'. sfseq.
apply dersrec_singleI. sfs.  assoc_single_mid' (Imp D B0). simpl.
apply l. sfseq. sfs.
apply LJT_can_rel_ImpL_Var_inv2 in d.  apply d.
apserc. apply ImpL_Var_inv2_I.

+ eapply derI.  apply (@fextI _ _ _ Γ1 (H4 ++ Imp D B0 :: G2)).
eapply rmI_eqc. apply atom_tnc'. sfseq.
apply dersrec_singleI. revert l. sfs. list_assoc_l'. intro l.
apply l. reflexivity. sfs.
apply LJT_can_rel_ImpL_Var_inv2 in dbe.  apply dbe.
list_assoc_r'. apserc. apply ImpL_Var_inv2_I.

- (* exchange rule *)
inversion r. subst. clear r. destruct X.
unfold gen_step.  intros sub fdt dt. clear sub dt.
inversion fdt. clear X1 fdt. subst.  unfold l41prop_t.
sfs. intros * abeq * dbe. destruct X0. 
inversion abeq. clear abeq d. subst.
acacD'T2 ; subst.

+ eapply derI.  apply (@fextI _ _ _ (G1 ++ Imp D B :: H0) Γ2).
eapply rmI_eqc. apply exch_tnc'. sfseq.
apply dersrec_singleI. revert l. sfs. list_assoc_r'. intro l.
apply l. reflexivity. sfs.
eapply derI.  apply (@fextI _ _ _ (G1 ++ B :: H0) Γ2).
eapply rmI_eqc. apply exch_tnc'. sfseq.
apply dersrec_singleI. sfs. apply (eq_rect _ _ dbe). list_eq_assoc.

+ eapply derI.  apply (@fextI _ _ _ (Γ1 ++ [Imp D B]) Γ2).
eapply rmI_eqc. apply exch_tnc'. sfseq.
apply dersrec_singleI. revert l. sfs. list_assoc_r'. intro l.
apply l. reflexivity. sfs.
eapply derI.  apply (@fextI _ _ _ (Γ1 ++ [B]) Γ2).
eapply rmI_eqc. apply exch_tnc'. sfseq.
apply dersrec_singleI. sfs. apply (eq_rect _ _ dbe). list_eq_assoc.

+ eapply derI.  apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc. apply (exch_tnc' x y X (H2 ++ Imp D B :: H5)). sfseq.
apply dersrec_singleI. sfs. assoc_single_mid' (Imp D B).
apply l. sfseq. sfs.
eapply derI.  apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc. apply (exch_tnc' y x (H2 ++ B :: H5) X). sfseq.
apply dersrec_singleI. sfs. apply (eq_rect _ _ dbe). list_eq_assoc.

+ eapply derI.  apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc. apply (exch_tnc' (Imp D B) y (x :: X) Y). sfseq.
apply dersrec_singleI. revert l. sfs. list_assoc_r'. intro l.
apply l. reflexivity. sfs.
eapply derI.  apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc. apply (exch_tnc' y B Y (x :: X)). sfseq.
apply dersrec_singleI. sfs. apply (eq_rect _ _ dbe). list_eq_assoc.

+ eapply derI.  apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc. apply (exch_tnc' x y (H8 ++ Imp D B :: H4) Y). sfseq.
apply dersrec_singleI. sfs. assoc_single_mid' (Imp D B). 
apply l. sfseq. sfs.
eapply derI.  apply (@fextI _ _ _ Γ1 Γ2).
eapply rmI_eqc. apply (exch_tnc' y x Y (H8 ++ B :: H4)). sfseq.
apply dersrec_singleI. sfs. apply (eq_rect _ _ dbe). list_eq_assoc.

+ eapply derI.  apply (@fextI _ _ _ Γ1 (H4 ++ Imp D B :: G2)).
eapply rmI_eqc. apply exch_tnc'. sfseq.
apply dersrec_singleI. revert l. sfs. list_assoc_l'. intro l.
apply l. reflexivity. sfs.
eapply derI.  apply (@fextI _ _ _ Γ1 (H4 ++ B :: G2)).
eapply rmI_eqc. apply exch_tnc'. sfseq.
apply dersrec_singleI. sfs. apply (eq_rect _ _ dbe). list_eq_assoc.

Qed.

Check gs_LJT_ImpL_adm.

Lemma gs_LJA_ImpL_adm V (D : PropF V) ps c Γ1 Γ2 (r : LJAncrules ps c) :
  gen_step l41prop D isubfml (derrec LJArules emptyT)
    (map (apfst (fmlsext Γ1 Γ2)) ps) (apfst (fmlsext Γ1 Γ2) c).
Proof.  destruct r.
- (* left compound Imp rules, invertible *)
eapply gs_LJA_ImpL_Ail. exact r.

- (* ImpL_Imp_rule *)
eapply gs_LJA_ImpL_ImpL. exact i.

- (* ImpLrule_p *) apply gs_LJA_ImpL_Imp_p. exact i.

- (* ImpRrule, IH not used *) destruct i.  unfold gen_step.
intros sub fdt dab. clear sub dab.
inversion fdt. clear X0 fdt. subst.  unfold l41prop.
intros * abeq * dbe. destruct X. clear l.
inversion abeq. clear abeq. subst.
(* apply ImpL_Imp_rule *)
eapply derI.  eapply fextI.  apply rmI.  apply Imp_anc'.
unfold fmlsext in H0. simpl in H0.
eapply swap_ins in H0.
unfold fmlsext in d.  eapply exchL_lja in d.
2: apply fst_relI. 2: exact (swapped_comm H0).
apply dlCons.  exact (insL_lja _ _ [Imp B B0] d).
apply dersrec_singleI. exact dbe.

- (* Idrule, so D is Var _ , IH not used *) destruct i.
unfold gen_step.  intros sub fdt dt. clear sub fdt.  unfold l41prop.
intros * vveq * dbe.  inversion vveq. clear vveq.
eapply derI.  eapply fextI.  apply rmI.  apply ImpL_anc'.
simpl in dt. rewrite -> H0 in dt.
apply dlCons.  exact (insL_lja _ _ [Imp (Var A) B] dt).
apply dersrec_singleI. exact dbe.

- (* common left rules, invertible *)
eapply gs_LJA_ImpL_sl. exact r.

- (* simple right rules *)
eapply gs_LJA_ImpL_sr. exact r.

Qed.

Check gs_LJA_ImpL_adm.

(* Lemma 4.1 of Dyckhoff & Negri JSL 2000 *)
Lemma LJA_ImpL_adm V D : forall seq, derrec LJArules emptyT seq -> 
  @l41prop V D seq.
Proof.  eapply gen_step_lemT. apply AccT_isubfml.
intros * ljpc.  destruct ljpc. inversion r.
apply gs_LJA_ImpL_adm. exact X. Qed.

Lemma LJT_ImpL_adm V D : forall seq, derrec LJTrules emptyT seq -> 
  @l41prop_t V D seq.
Proof.  eapply gen_step_lemT. apply AccT_isubfml.
intros * ljpc.  destruct ljpc. inversion r.
apply gs_LJT_ImpL_adm. exact X. Qed.

Check LJA_ImpL_adm.  Check LJT_ImpL_adm.

Lemma idrule_der_ljx {V : Set} rules A 
  (Id_xnc' : forall v : V, rules [] ([Var v], Var v))
  (ImpR_xnc' : forall A B, rules [([A], B)] ([], Imp A B))
  (lrls_xnc' : forall G ps c, LJslrules ps c -> 
    rules (map (flip pair G) ps) (flip pair G c))
  (rrls_xnc' : forall ps c, LJsrrules ps c -> 
    rules (map (pair []) ps) ([], c)) 
  (LJX_ImpL_adm : forall D seq, derrec (fst_ext_rls rules) emptyT seq ->
    l41prop' (fst_ext_rls rules) D seq) :
  derrec (fst_ext_rls rules) emptyT ([A : PropF V], A).
Proof. induction A.
- eapply derI. apply rsub_fer.  eapply Id_xnc'. apply dlNil.
- eapply derI. apply rsub_fer.  eapply lrls_xnc'. apply Bot_sl'.  apply dlNil.
- (* Imp - apply ImpR rule *)
eapply derI. eapply (@fextI _ _ _ _ []).
eapply rmI_eqc.  apply ImpR_xnc'.  
sfs. rewrite !app_nil_r.  reflexivity.
apply dersrec_singleI.  sfs.
(* use Lemma 4.1 *)
specialize (LJX_ImpL_adm A1 _ IHA1 [] [A1] eq_refl A2 A2).
simpl in LJX_ImpL_adm. unfold fmlsext in LJX_ImpL_adm.
apply LJX_ImpL_adm. clear LJX_ImpL_adm.
apply (fer_der [] [A1] IHA2). 

- (* And *) eapply derI. 
+ apply rsub_fer.  eapply lrls_xnc'.  apply AndL_sl'.
+ simpl.  apply dersrec_singleI. eapply derI.
++ eapply (@fextI _ _ _ [A1 ; A2] []).  eapply rmI_eqc.
eapply rrls_xnc'.  apply AndR_sr'.  reflexivity.  
++ sfs.  apply dlCons.
+++ apply (fer_der [] [A2] IHA1).
+++ apply dersrec_singleI.
apply (fer_der [A1] []) in IHA2. exact IHA2.

- (* Or *) eapply derI. 
+ apply rsub_fer.  eapply lrls_xnc'.  apply OrL_sl'.  
+ simpl. apply dlCons.
++ eapply derI.
+++ eapply (@fextI _ _ _ [A1] []).  eapply rmI_eqc.
eapply rrls_xnc'.  apply OrR1_sr'.  sfs. reflexivity.
+++ sfs. apply dersrec_singleI. apply IHA1.
++ apply dersrec_singleI.  eapply derI.
+++ eapply (@fextI _ _ _ [A2] []).  eapply rmI_eqc.
eapply rrls_xnc'.  apply OrR2_sr'.  sfs. reflexivity.
+++ sfs. apply dersrec_singleI. apply IHA2.
Qed.

Print Implicit idrule_der_ljx.

(*
Lemma idrule_der_lja {V} A : derrec LJArules emptyT ([A : PropF V], A).
Proof. induction A.
- eapply derI. apply rsub_fer.  eapply Id_anc'. apply dlNil.
- eapply derI. apply rsub_fer.  eapply lrls_anc'. apply Bot_sl'.  apply dlNil.
- (* Imp - apply ImpR rule *)
eapply derI. eapply (@fextI _ _ _ _ []).
eapply rmI_eqc.  apply ImpR_anc'.  
sfs. rewrite !app_nil_r.  reflexivity.
apply dersrec_singleI.  sfs.
(* use Lemma 4.1 *)
pose (@LJA_ImpL_adm _ A1 _ IHA1 [] [A1] eq_refl A2 A2).
simpl in d. unfold fmlsext in d.  apply d. clear d.
apply (fer_der [] [A1] IHA2). 

- (* And *) eapply derI. 
+ apply rsub_fer.  eapply lrls_anc'.  apply AndL_sl'.
+ simpl.  apply dersrec_singleI. eapply derI.
++ eapply (@fextI _ _ _ [A1 ; A2] []).  eapply rmI_eqc.
eapply rrls_anc'.  apply AndR_sr'.  reflexivity.  
++ sfs.  apply dlCons.
+++ apply (fer_der [] [A2] IHA1).
+++ apply dersrec_singleI.
apply (fer_der [A1] []) in IHA2. exact IHA2.

- (* Or *) eapply derI. 
+ apply rsub_fer.  eapply lrls_anc'.  apply OrL_sl'.  
+ simpl. apply dlCons.
++ eapply derI.
+++ eapply (@fextI _ _ _ [A1] []).  eapply rmI_eqc.
eapply rrls_anc'.  apply OrR1_sr'.  sfs. reflexivity.
+++ sfs. apply dersrec_singleI. apply IHA1.
++ apply dersrec_singleI.  eapply derI.
+++ eapply (@fextI _ _ _ [A2] []).  eapply rmI_eqc.
eapply rrls_anc'.  apply OrR2_sr'.  sfs. reflexivity.
+++ sfs. apply dersrec_singleI. apply IHA2.
Qed.
*)

Lemma idrule_der_lja {V} A : derrec LJArules emptyT ([A : PropF V], A).
Proof. apply idrule_der_ljx.  apply Id_anc'.  apply ImpR_anc'.
apply lrls_anc'.  apply rrls_anc'.  apply LJA_ImpL_adm.  Qed.

Lemma idrule_der_ljt {V} A : derrec LJTrules emptyT ([A : PropF V], A).
Proof. apply idrule_der_ljx.  apply Id_tnc'.  apply ImpR_tnc'.
apply lrls_tnc'.  apply rrls_tnc'.  apply LJT_ImpL_adm.  Qed.

Lemma InT_der_LJA V A ant : InT A ant -> derrec (@LJArules V) emptyT (ant, A).
Proof. intro ia.  apply InT_split in ia.  cD. subst.
  exact (fer_der _ _ (idrule_der_lja A)). Qed.

Lemma InT_der_LJT V A ant : InT A ant -> derrec (@LJTrules V) emptyT (ant, A).
Proof. intro ia.  apply InT_split in ia.  cD. subst.
  exact (fer_der _ _ (idrule_der_ljt A)). Qed.

(* atom rule derivable in LJA *)
Lemma lja_der_atom V ps c G : 
  rlsmap (flip pair G) (@ImpL_atom_rule V) ps c -> derl LJArules ps c.
Proof. intro r. destruct r. destruct i. simpl.
eapply dtderI.  eapply (@fextI _ _ _ [] [_]).  eapply rmI_eqc.
eapply ImpL_anc'.  reflexivity.
simpl. unfold fmlsext. simpl.  eapply (@dtCons _ _ []).
apply derrec_nil_derl.  apply InT_der_LJA. solve_InT.
eapply (@dtCons _ _ [_]). apply asmI. apply dtNil.
Qed.
  
(* and of course the atom rule is part of LJT, see atom_tnc *)
  
(* Lemma 4.2 of Dyckhoff & Negri JSL 2000 *)
Lemma LJA_dn42_princ V ps B C D E :
  LJAncrules ps ([Imp (Imp C D) B], E) ->
  forall Γ1 Γ2 : list (PropF V),
  adm (fst_ext_rls LJAncrules) (map (apfst (fmlsext Γ1 Γ2)) ps)
    (fmlsext Γ1 Γ2 [Imp D B ; Imp D B ; C], E).
Proof. intro ljpc. inversion ljpc ; subst ; clear ljpc.
- inversion X.  inversion X0 ; inversion X1.

- (* the non-trivial case *) inversion X. subst. clear X. 
simpl. unfold fmlsext. simpl.
intros *. apply admI. intro drs.
inversion drs. subst. clear drs.
pose (@LJA_ImpL_adm V D _ X _ _ eq_refl B E).  require d.
clear X d.  inversion X0. clear X0 X1. subst.
pose (@insL_lja V (Γ1 ++ [B]) Γ2 [Imp D B ; C] E).
require d.  apply (eq_rect _ _ X). list_eq_assoc.
apply (eq_rect _ _ d). list_eq_assoc.
(* now need exchange *)
clear X X0.  simpl in d.  unfold fmlsext in d.  exact d.

- inversion X. 
- inversion X.
- inversion X.
- inversion X.  inversion X0 ; inversion X1.
- inversion X. 
Qed.

Lemma LJT_dn42_princ V ps B C D E :
  LJTncrules ps ([Imp (Imp C D) B], E) ->
  forall Γ1 Γ2 : list (PropF V),
  adm (fst_ext_rls LJTncrules) (map (apfst (fmlsext Γ1 Γ2)) ps)
    (fmlsext Γ1 Γ2 [Imp D B ; Imp D B ; C], E).
Proof. intro ljpc. inversion ljpc ; subst ; clear ljpc.
- inversion X. 
+ inversion X0 ; inversion X1 ; inversion X2.

+ (* the non-trivial case *) inversion X0. subst. clear X0 X. 
sfs.  intros *. apply admI. intro drs.
inversion drs. subst. clear drs.
pose (@LJT_ImpL_adm V D _ X _ _ eq_refl B E).  require d.
clear X d.  inversion X0. clear X0 X1. subst.
pose (@insL_ljt V (Γ1 ++ [B]) Γ2 [Imp D B ; C] E).
require d.  apply (eq_rect _ _ X). list_eq_assoc.
apply (eq_rect _ _ d). list_eq_assoc.
(* now need exchange *)
clear X X0.  simpl in d.  unfold fmlsext in d.  exact d.

+ inversion X0. 
+ inversion X0. 
+ inversion X0. subst. clear X0 X. inversion X1 ; inversion X.
+ inversion X0. 
- inversion X. inversion X0.
- inversion X. inversion X0.  list_eq_ncT. inversion H5. Qed.

Inductive dn42invs {V} : PropF V -> list (PropF V) -> Type :=
  | dn42invs_I : forall B C D, 
    dn42invs (Imp (Imp C D) B) [Imp D B ; Imp D B ; C].

Definition dn42inv {V} := fslr (@dn42invs V).

Lemma dn42inv_I {V} (B C D : PropF V) : 
  dn42inv [Imp (Imp C D) B] [Imp D B ; Imp D B ; C].
Proof. apply fslr_I. apply dn42invs_I. Qed.

(* done for LJT to here *)

Lemma can_trf_dn42inv_lja {V} ps c: @LJArules V ps c ->
  can_trf_rules_rc (srs_ext_rel dn42inv) (adm LJArules) ps c.
Proof. apply can_trf_genLinv_geng.  apply LJAnc_seL.
intros * auv.  destruct auv.
apply LJA_dn42_princ.  Qed.

Lemma can_rel_dn42inv_lja {V} seq :
derrec LJArules emptyT seq ->
  can_rel LJArules (srs_ext_rel (Y:=PropF V)) dn42inv seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_dn42inv_lja.  Qed.

(* try to adapt to ljt
Lemma can_trf_dn42inv_ljt {V} ps c: @LJTrules V ps c ->
  can_trf_rules_rc (srs_ext_rel dn42inv) (adm LJTrules) ps c.
Proof. intro ljpc. destruct ljpc. inversion r. subst. clear r. destruct X.
- (* LJTSncrules *)
eapply can_trf_genLinv_geng2.  apply LJTSnc_seL.
intros * auv ljtspc.  destruct auv.
apply LJT_dn42_princ. exact (sing_tnc ljtspc).
eapply fextI. apply rmI. exact l. apply rsubI. apply sing_tnc.
- (* ImpL_atom_rule *)
admit.
- (* exchange rule *)
admit.
Admitted.

Lemma can_rel_dn42inv_ljt {V} seq :
derrec LJTrules emptyT seq ->
  can_rel LJTrules (srs_ext_rel (Y:=PropF V)) dn42inv seq.
Proof. unfold can_rel.
apply der_trf_rc_adm.  exact can_trf_dn42inv_ljt.  Qed.
*)
