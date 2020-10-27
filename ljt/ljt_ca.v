
(* LJ logic, using lists of formulae *)
(* lots copied from ../modal/k4_ca.v, often with same names *)

Require Export List.
Export ListNotations.  
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Require Import gen genT ddT.
Require Import List_lemmasT.
Require Import gen_tacs swappedT.
Require Import gen_seq gstep rtcT.
Require Import ljt ljt_inv ljt_ctr.
Require Import Coq.Program.Basics.

(* derivability of conclusion of a cut, not conditional on premises
  being derivable *) 

(* but note we are going to need to allow A to be anywhere, not just at the
front, because rule my cause that to happen in the premises *)

(* note that a pair of end-sequents not of the form
  (_, A) (_ ++ A :: _, _) satisfies cut_adm *)
(* all possible results of cut on A derivable 
  (only an issue because lists distinguish different occurrences of A) *)
(* cut puts antecedent of left premise into antecedent of right premise
  at the location of the cut-formula *)
Inductive cedc X rules (C : X) cl cr : Type :=  
  | cedcI : (forall la ra ra' D, 
    cl = (la, C) -> cr = (ra ++ C :: ra', D : X) ->
      derrec rules emptyT (ra ++ la ++ ra', D)) ->
      @cedc X rules C cl cr.

Inductive cut_adm X rules (C : X) : Type :=  
  | cadmI : (forall cl cr la ra ra' D, 
    cl = (la, C) -> cr = (ra ++ C :: ra', D : X) ->
    derrec rules emptyT cl -> derrec rules emptyT cr ->
      derrec rules emptyT (ra ++ la ++ ra', D)) -> @cut_adm X rules C.

Definition cedcD X rules A cl cr (c : @cedc X rules A cl cr) := 
  match c with | cedcI d => d end.

Definition cadmD X rules A (c : @cut_adm X rules A) :=
  match c with | cadmI d => d end.

Ltac sfea := simpl ;  unfold fmlsext ;  list_eq_assoc.

(* left rule on left premise *)
Lemma gs2_lrlsL_gen fty (fml : fty) any rules (lrules : rlsT (list fty))
  drsa drsb (G : fty) psl psr cl cr 
  (lr_gnc' : forall G ps c,
    lrules ps c -> rules (map (flip pair G) ps) (flip pair G c)) :
  fst_ext_rls (rlsmap (flip pair G) lrules) psl cl -> 
  gen_step2 (cedc (fst_ext_rls rules)) fml any drsa drsb psl cl psr cr.
Proof. intros fmrr sub fpl fpr dl dr. apply cedcI. intros * cle cre.
clear sub fpr. destruct fmrr. destruct r. destruct r. 
simpl in cle.  unfold fmlsext in cle.  simpl in cle.
inversion cle. clear cle. subst.
eapply derI.  eapply (fextI_eqc' _ (ra ++ Γ1) (Γ2 ++ ra')).
eapply (lr_gnc' D _ _ l). sfea.
eapply usefmm. exact fpl.
intro. simpl. intro dc. destruct dc.
unfold fmlsext in c0. 
unfold fmlsext. simpl. destruct c0.
specialize (d0 _ _ _ _ eq_refl eq_refl).
apply (eq_rect _ _ d0). list_eq_assoc.  Qed.

Definition gs2_lrlsL_lj V fml any drsa drsb G psl psr cl cr := 
  @gs2_lrlsL_gen (PropF V) fml any LJncrules LJslrules
  drsa drsb G psl psr cl cr lrls_nc'.
Definition gs2_lrlsL_lja V fml any drsa drsb G psl psr cl cr := 
  @gs2_lrlsL_gen (PropF V) fml any LJAncrules LJslrules
  drsa drsb G psl psr cl cr lrls_anc'.
Definition gs2_AilL_lja V fml any drsa drsb G psl psr cl cr := 
  @gs2_lrlsL_gen (PropF V) fml any LJAncrules LJAilrules
  drsa drsb G psl psr cl cr il_anc'.

(* ImpL rule on left premise *)
Lemma gs2_ImpLL V fml any drsb psl psr cl cr :
  fst_ext_rls (@ImpLrule V) psl cl -> 
  gen_step2 (cedc LJrules) fml any (derrec LJrules emptyT) drsb psl cl psr cr.
Proof. intros fmrr sub fpl fpr dl dr. apply cedcI. intros * cle cre.
clear sub fpr. destruct fmrr. destruct r.  destruct i.
simpl in cle.  unfold fmlsext in cle.  simpl in cle.
inversion cle. clear cle. subst.
unfold LJrules.
inversion fpl. clear fpl.
inversion X0. clear X2 X0. subst.
destruct X.  clear c.  destruct X1.  clear d0.  destruct c.
specialize (d0 _ _ _ _ eq_refl eq_refl).
eapply derI. eapply (fextI_eqc' _ (ra ++ Γ1) (Γ2 ++ ra')).
apply ImpL_nc'.  sfea.
apply dlCons.  pose (fer_der ra ra' d).  apply (eq_rect _ _ d1). sfea.
apply dersrec_singleI. apply (eq_rect _ _ d0). sfea.
Qed.

(* right rule on right premise *)
Lemma gs2_rrlsR_gen fty (fml : fty) any rules rrules drsa drsb psl psr cl cr 
  (rr_gnc' : forall ps c, rrules ps c -> rules (map (pair []) ps) (pair [] c)) :
  fst_ext_rls (rlsmap (pair []) rrules) psr cr -> 
  gen_step2 (cedc (fst_ext_rls rules)) fml any drsa drsb psl cl psr cr.
Proof. intros fmrr sub fpl fpr dl dr. apply cedcI. intros * cle cre.
clear sub fpl. destruct fmrr. destruct r. destruct r. 
simpl in cre.  unfold fmlsext in cre.  simpl in cre.
inversion cre. clear cre. subst.
eapply derI.  eapply fextI_eqc'.  exact (rr_gnc' _ _ r).
simpl.  unfold fmlsext.  simpl. reflexivity.
eapply usefmm. exact fpr.
intro. simpl. intro dc. destruct dc.
unfold fmlsext in c. simpl in c. rewrite H0 in c.
unfold fmlsext. simpl. destruct c.
exact (d0 _ _ _ _ eq_refl eq_refl).  Qed.

Definition gs2_rrlsR_lj V fml any drsa drsb psl psr cl cr := 
  @gs2_rrlsR_gen (PropF V) fml any LJncrules LJsrrules
  drsa drsb psl psr cl cr rrls_nc'.
Definition gs2_rrlsR_lja V fml any drsa drsb psl psr cl cr := 
  @gs2_rrlsR_gen (PropF V) fml any LJAncrules LJsrrules
  drsa drsb psl psr cl cr rrls_anc'.

Ltac irrtac ImpR_gnc' d0 Γ1 Γ2 :=
  require d0 ; [ list_eq_assoc | ] ; eapply derI ; [
  eapply (fextI_eqc' _ Γ1 Γ2) ; [ apply ImpR_gnc' | ] ; sfea |
  apply dersrec_singleI ;  apply (eq_rect _ _ d0) ; sfea ].

(* ImpR rule on right premise *)
Lemma gs2_ImpRR_gen V rules fml any drsa drsb psl psr cl cr 
  (ImpR_gnc' : forall A B, rules [([A], B)] ([], @Imp V A B)) :
  fst_ext_rls (@ImpRrule V) psr cr -> 
  gen_step2 (cedc (fst_ext_rls rules)) fml any drsa drsb psl cl psr cr.
Proof. intros fmrr sub fpl fpr dl dr. apply cedcI. intros * cle cre.
clear sub fpl. destruct fmrr. destruct r.  destruct i.
unfold fmlsext in cre.  simpl in cre.
inversion cre. clear cre. subst.
simpl in fpr.  unfold fmlsext in fpr. 
apply ForallT_singleD in fpr.
destruct fpr. destruct c.
acacD'T2 ; subst.
- specialize (d0 la (ra ++ [A]) ra' B eq_refl).
  irrtac ImpR_gnc' d0 ra (la ++ ra').
- specialize (d0 la ra (H2 ++ [A] ++ Γ2) B eq_refl).
  irrtac ImpR_gnc' d0 (ra ++ la ++ H2) Γ2.
- specialize (d0 la (Γ1 ++ [A] ++ H0) ra' B eq_refl).
  irrtac ImpR_gnc' d0 Γ1 (H0 ++ la ++ ra').
Qed.

Definition gs2_ImpRR_lj V fml any drsa drsb psl psr cl cr :=
  @gs2_ImpRR_gen V LJncrules fml any drsa drsb psl psr cl cr (@ImpR_nc' V).
Definition gs2_ImpRR_lja V fml any drsa drsb psl psr cl cr :=
  @gs2_ImpRR_gen V LJAncrules fml any drsa drsb psl psr cl cr (@ImpR_anc' V).

(* Id rule on left premise - requires weakening and exchange *)
Lemma gs2_idL_gen V rules A fml any drsa psl psr cl cr  
  (exchL : forall concl, derrec (fst_ext_rls rules) emptyT concl ->
     forall concl', fst_rel (@swapped _) concl concl' ->
       derrec (fst_ext_rls rules) emptyT concl') :
  fst_ext_rls (@Idrule V A) psl cl ->
  gen_step2 (cedc (fst_ext_rls rules)) fml any 
    drsa (derrec (fst_ext_rls rules) emptyT) psl cl psr cr.
Proof. intros fidr sub fpl fpr dl dr. apply cedcI. intros * cle cre.
clear sub fpl fpr dl. destruct fidr. destruct r. destruct i.
simpl in cle.  inversion cle. subst. clear cle.
unfold fmlsext. 
pose (fer_der Γ1 Γ2 dr).
pose (exchL _ d).
specialize (d0 (ra ++ (Γ1  ++ fml :: ra') ++ Γ2, D)).
require d0.  apply fst_relI. swap_tac.
apply (exchL _ d0).  apply fst_relI. swap_tac. Qed.

Definition gs2_idL_lj V A fml any drsa psl psr cl cr :=
  @gs2_idL_gen V LJncrules A fml any drsa psl psr cl cr (@exchL_lj V).
Definition gs2_idL_lja V A fml any drsa psl psr cl cr :=
  @gs2_idL_gen V LJAncrules A fml any drsa psl psr cl cr (@exchL_lja V).

Lemma InT_der_gen V rules p ant : rsub (Idrule (@Var V p)) rules ->
  InT (Var p) ant -> derrec (fst_ext_rls rules) emptyT (ant, Var p).
Proof. intros rsir ia.  apply InT_split in ia.  cD. subst.
eapply derI. apply (@fextI _ _ _ ia ia0).
eapply rmI_eqc. apply rsir. apply Idrule_I. reflexivity. apply dlNil. Qed.

Lemma InT_der_LJ V A ant : InT A ant -> derrec (@LJrules V) emptyT (ant, A).
Proof. intro ia.  apply InT_split in ia.  cD. subst.
  exact (fer_der _ _ (idrule_der_lj A)). Qed.

(* Id rule on right premise - general version, for Var _ only *)
Lemma gs2_idR_gen V rules p fml any drsb psl psr cl cr : 
  rsub (Idrule (Var p)) rules -> fst_ext_rls (@Idrule V (Var p)) psr cr ->
  gen_step2 (cedc (fst_ext_rls rules)) fml any 
    (derrec (fst_ext_rls rules) emptyT) drsb psl cl psr cr.
Proof. intros rsir fidr sub fpl fpr dl dr. apply cedcI. intros * cle cre.
clear sub fpl fpr dr. destruct fidr. destruct r. destruct i.
simpl in cre. unfold fmlsext in cre. simpl in cre.
inversion cre. subst. clear cre.
acacD'T2 ; subst.
- exact (fer_der _ _ dl).
- apply (InT_der_gen rsir). solve_InT.
- exact (fer_der _ _ dl).
- apply (InT_der_gen rsir). solve_InT.
Qed.

Lemma gs2_idR_lj V A fml any drsb psl psr cl cr : 
  fst_ext_rls (@Idrule V A) psr cr ->
  gen_step2 (cedc LJrules) fml any (derrec LJrules emptyT) drsb psl cl psr cr.
Proof. intros fidr sub fpl fpr dl dr. apply cedcI. intros * cle cre.
clear sub fpl fpr dr. destruct fidr. destruct r. destruct i.
simpl in cre. unfold fmlsext in cre. simpl in cre.
inversion cre. subst. clear cre.
acacD'T2 ; subst.
- exact (fer_der _ _ dl).
- apply InT_der_LJ. solve_InT.
- exact (fer_der _ _ dl).
- apply InT_der_LJ. solve_InT.
Qed.

Ltac lctr_tac d1 lc := eapply lctr_adm_lj in d1 ;
  unfold can_rel in d1 ;  erequire d1 ;  require d1 ; [
  eapply (@asa_ser_lsctr _ _ lc) ;  solve_asa | ] ;
  simpl in d1 ;  rewrite ?app_nil_r in d1.

Lemma lj_ImpR_ImpL V fml la lc rc Γ1 Γ2 (D : PropF V) psl psr cl
  (sub : forall A' : PropF V, isubfml A' fml ->
        forall dl, derrec (fst_ext_rls LJncrules) emptyT dl ->
        forall dr, derrec (fst_ext_rls LJncrules) emptyT dr ->
        cedc (fst_ext_rls LJncrules) A' dl dr)
  (fpl : ForallT (fun pl => derrec (fst_ext_rls LJncrules) emptyT pl *
           cedc (fst_ext_rls LJncrules) fml pl (lc ++ fml :: rc, D)) 
	   (map (apfst (fmlsext Γ1 Γ2)) psl))
  (fpr : ForallT (fun pr => derrec (fst_ext_rls LJncrules) emptyT pr *
           cedc (fst_ext_rls LJncrules) fml (la, fml) pr)
          (map (apfst (fmlsext lc rc)) psr)) :
  ImpLrule psr ([fml], D) -> ImpRrule psl cl ->
  apfst (fmlsext Γ1 Γ2) cl = (la, fml) ->
  derrec (fst_ext_rls LJncrules) emptyT (lc ++ la ++ rc, D).
Proof. intros ir il cle.
inversion ir. destruct il.
simpl in cle. unfold fmlsext in cle.  simpl in cle.
inversion cle. subst. clear ir cle.
inversion H4. subst. clear H4.
(* first, use IH to cut A -> B from first premise of right premise *)
inversion fpr. subst. clear fpr.
destruct (snd X). clear X.
specialize (d _ _ _ _ eq_refl eq_refl).
(* now cut on A with premise of left premise *)
inversion fpl. subst. clear fpl X1.
pose (sub _ (isub_ImpL _ _) _ d _ (fst X)).
destruct c.
specialize (d0 _ _ _ _ eq_refl eq_refl).
(* now cut on B with second premise of right premise *)
inversion X0. clear X0 X2. subst.
specialize (sub _ (isub_ImpR _ _) _ d0 _ (fst X1)).
destruct sub.
specialize (d1 _ _ _ _ eq_refl eq_refl).
(* now lots of contraction *)
clear d X d0 X1.

lctr_tac d1 lc.  lctr_tac d1 Γ1.  lctr_tac d1 Γ2.  lctr_tac d1 rc.

apply (eq_rect _ _ d1). list_eq_assoc. Qed.

About lj_ImpR_ImpL.

Lemma lj_lrlsR_rrlsL V fml la lc rc (D : PropF V) psl psr 
  (sub : forall A' : PropF V, isubfml A' fml ->
        forall dl, derrec (fst_ext_rls LJncrules) emptyT dl ->
        forall dr, derrec (fst_ext_rls LJncrules) emptyT dr ->
        cedc (fst_ext_rls LJncrules) A' dl dr)
  (fpl : ForallT (fun pl => derrec (fst_ext_rls LJncrules) emptyT pl *
           cedc (fst_ext_rls LJncrules) fml pl (lc ++ fml :: rc, D)) 
	   (map (pair la) psl))
  (fpr : ForallT (fun pr => derrec (fst_ext_rls LJncrules) emptyT pr *
           cedc (fst_ext_rls LJncrules) fml (la, fml) pr)
          (map (fun ps => (lc ++ ps ++ rc, D)) psr)) :
  LJslrules psr [fml] -> LJsrrules psl fml ->
  derrec (fst_ext_rls LJncrules) emptyT (lc ++ la ++ rc, D).
Proof. intros ir il.
inversion ir ; clear ir ; 
((inversion X ; clear X) || (inversion H ; clear H)) ; subst ; 
inversion il ; clear il ; inversion H ; clear H ; subst.
- (* And on both sides *) simpl in fpr.  simpl in fpl.
inversion fpr. clear fpr X0. destruct X. clear c.
(* cut on A *) inversion fpl. clear fpl. subst. destruct X. clear c.
destruct (sub _ (isub_AndL _ _) _ d0 _ d).
specialize (d1 _ _ _ _ eq_refl eq_refl).
(* cut on B *) inversion X0. clear X0 X1. subst. destruct X. clear c.
destruct (sub _ (isub_AndR _ _) _ d2 _ d1).
specialize (d3 _ (lc ++ la) rc D eq_refl).
require d3. list_eq_assoc.
(* now need a contraction *)
clear sub d d0 d1 d2.  lctr_tac d3 la. exact d3.
- (* Or on both sides *) simpl in fpr.  simpl in fpl.
inversion fpr. clear fpr X0. destruct X. clear c.
inversion fpl. clear fpl X0. destruct X. clear c. subst.
destruct (sub _ (isub_OrL _ _) _ d0 _ d).
exact (d1 _ _ _ _ eq_refl eq_refl).
- (* Or on both sides *) simpl in fpr.  simpl in fpl.
inversion fpr. clear fpr X. inversion X0. clear X0 X1. destruct X. clear c.
inversion fpl. clear fpl X0. destruct X. clear c. subst.
destruct (sub _ (isub_OrR _ _) _ d0 _ d).
exact (d1 _ _ _ _ eq_refl eq_refl).
Qed.

About lj_lrlsR_rrlsL.

(* lemma for right principal cases, lc and rc are left and right context
  of the right premise of the cut and the last rule on the right *)
Lemma lj_gs2_rp V fml la lc rc (D : PropF V) psl psr 
  (ljl : fst_ext_rls LJncrules psl (la, fml))
  (ljr : LJncrules psr ([fml], D))
  (sub : forall A' : PropF V, isubfml A' fml ->
        forall dl, derrec (fst_ext_rls LJncrules) emptyT dl ->
        forall dr, derrec (fst_ext_rls LJncrules) emptyT dr ->
        cedc (fst_ext_rls LJncrules) A' dl dr)
  (fpl : ForallT (fun pl => derrec (fst_ext_rls LJncrules) emptyT pl *
           cedc (fst_ext_rls LJncrules) fml pl (lc ++ fml :: rc, D)) psl)
  (fpr : ForallT (fun pr => derrec (fst_ext_rls LJncrules) emptyT pr *
           cedc (fst_ext_rls LJncrules) fml (la, fml) pr)
          (map (apfst (fmlsext lc rc)) psr))
  (dl : derrec (fst_ext_rls LJncrules) emptyT (la, fml))
  (dr : derrec (fst_ext_rls LJncrules) emptyT (lc ++ fml :: rc, D)) :
  derrec (fst_ext_rls LJncrules) emptyT (lc ++ la ++ rc, D).
Proof. inversion ljr ; subst. 
- (* ImpL on the right *)
inversion ljl.  inversion X.  subst.  clear ljl X.
destruct X0.
+ (* ImpL on the left *)
eapply fextI' in i.  eapply gs2_ImpLL in i.  apply i in sub.
specialize (sub fpl).  rewrite !H4 in sub.
specialize (sub fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
+ (* ImpR on the left *)
eapply lj_ImpR_ImpL ; eassumption.
+ (* Id on the left *)
eapply fextI' in i.  eapply gs2_idL_lj in i.  apply i in sub.
specialize (sub fpl).  rewrite !H4 in sub.
specialize (sub fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
+ (* left rules on the left *)
eapply fextI' in r.  eapply gs2_lrlsL_lj in r.  apply r in sub.
specialize (sub fpl).  rewrite !H4 in sub.
specialize (sub fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
+ (* right rules on the left - formulae different *)
clear sub fpl fpr dl dr.
destruct r. inversion H4. subst. clear H4.
inversion H. subst. clear H ljr.
inversion l ; subst ; inversion H.
- (* ImpR on the right *)
eapply fextI' in H.  eapply gs2_ImpRR_lj in H.  apply H in sub.
specialize (sub fpl fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
- (* Id on the right *)
eapply fextI' in X.  eapply gs2_idR_lj in X.  apply X in sub.
specialize (sub fpl fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
- (* left rules on the right *)
inversion ljl.  inversion X0.  subst.  clear ljl X0.
destruct X1.
+ (* ImpL on the left *)
eapply fextI' in i.  eapply gs2_ImpLL in i.  apply i in sub.
specialize (sub fpl).  rewrite !H3 in sub.
specialize (sub fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
+ (* ImpR on the left - formulae different *)
clear sub fpl fpr dl dr.
inversion X. destruct i. simpl in H3. inversion H3. subst. clear H3.
inversion X0.  inversion H.  inversion H.  inversion X1.
+ (* Id on the left *)
eapply fextI' in i.  eapply gs2_idL_lj in i.  apply i in sub.
specialize (sub fpl).  rewrite !H3 in sub.
specialize (sub fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
+ (* left rules on the left *)
eapply fextI' in r.  eapply gs2_lrlsL_lj in r.  apply r in sub.
specialize (sub fpl).  rewrite !H3 in sub.
specialize (sub fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
+ (* right rules on the left *)
inversion X. inversion r. subst. clear X r. simpl in H3.
inversion H3. subst. clear H3.
unfold fmlsext. simpl.
assert (map (apfst (fmlsext Γ1 Γ2)) (map (pair []) ps1) =
  map (pair (Γ1 ++ Γ2)) ps1).
{ clear sub fpl fpr H0.  induction ps1. reflexivity.
simpl. rewrite IHps1. reflexivity. }
assert (map (apfst (fmlsext lc rc)) (map (flip pair D) ps0) = 
  map (fun ps : list (PropF V) => (lc ++ ps ++ rc, D)) ps0).
{ clear sub fpl fpr X0 ljr.  induction ps0. reflexivity.
simpl. rewrite IHps0. reflexivity. }
rewrite H in fpl.  rewrite H1 in fpr.
exact (lj_lrlsR_rrlsL _ _ sub fpl fpr X0 H0).
- (* right rules on the right *)
eapply fextI' in X.  eapply gs2_rrlsR_lj in X.  apply X in sub.
specialize (sub fpl fpr dl dr). destruct sub.
exact (d _ _ _ _ eq_refl eq_refl).
Qed.

About lj_gs2_rp.

Lemma sing_empty_LJncrules V ps fmls D :
  @LJncrules V ps (fmls, D) -> sing_empty fmls.
Proof. intro lj. inversion lj ; subst ; 
try (inversion H || inversion X) ;
try (apply se_empty || apply se_single).
subst. inversion X0 ; subst ;
try (inversion H || inversion X1) ;
try (apply se_empty || apply se_single).
Qed.

Lemma lj_gs2 V fml psl psr cl cr:
  @LJrules V psl cl -> @LJrules V psr cr ->
  gen_step2 (cedc LJrules) fml isubfml (derrec LJrules emptyT)
        (derrec LJrules emptyT) psl cl psr cr.
Proof. unfold LJrules. intros ljl ljr.  destruct ljl.  destruct ljr.
intros sub fpl fpr dl dr. apply cedcI. intros * cle cre.
destruct r0. destruct c0 as [cra crs].
simpl in cre. unfold fmlsext in cre. simpl in cre.
acacD'T2 ; subst.
- clear sub fpl ; 
eapply derI ; [ eapply (fextI_eqc' _ ra (la ++ ra') _ _ l) ; sfea | ] ;
apply dersrecI_forall ;  intros c incm ;
apply InT_mapE in incm ; cD ;
inversion incm0 ; clear incm0 ; subst ;
unfold fmlsext ; simpl ;
destruct (ForallTD_forall fpr (InT_map _ incm1)) ;
clear d ; destruct c ;
specialize (d _ (ra ++ incm) ra' c0 eq_refl) ;
require d ; [ sfea | apply (eq_rect _ _ d) ; list_eq_assoc ].
- pose (sing_empty_LJncrules l). inversion s. subst. simpl.
simpl in *. unfold fmlsext in fpl. unfold fmlsext in dr.
rewrite app_nil_r in fpl.  rewrite app_nil_r in fpr. rewrite app_nil_r in dr.
eapply (lj_gs2_rp _ _ (fextI r) l sub fpl fpr dl dr).
- clear sub fpl. 
eapply derI.  eapply (fextI_eqc' _ (ra ++ la ++ cre2) Γ3 _ _ l). sfea.
apply dersrecI_forall.  intros c incm.
apply InT_mapE in incm. cD.
inversion incm0. clear incm0. subst.
unfold fmlsext. simpl.
eapply ForallTD_forall in fpr.  2: apply (InT_map _ incm1).
destruct fpr. clear d. destruct c.
specialize (d _ ra (cre2 ++ incm ++ Γ3) c0 eq_refl).
require d.  sfea.
apply (eq_rect _ _ d). list_eq_assoc.
- clear sub fpl. 
eapply derI.  eapply (fextI_eqc' _ Γ0 (la ++ ra') _ _ l).  sfea.
apply dersrecI_forall.  intros c incm.
apply InT_mapE in incm. cD.
inversion incm0. clear incm0. subst.
unfold fmlsext. simpl.
eapply ForallTD_forall in fpr.  2: apply (InT_map _ incm1).
destruct fpr. clear d. destruct c.
specialize (d _ (Γ0 ++ incm) ra' c0 eq_refl).
require d.  sfea.
apply (eq_rect _ _ d). list_eq_assoc.
- pose (sing_empty_LJncrules l). inversion s. list_eq_ncT. inversion H0.
list_eq_ncT. sD ; inversion H1. subst.
simpl in *. unfold fmlsext in *.  rewrite app_nil_r.
eapply (lj_gs2_rp _ _ (fextI r) l sub fpl fpr dl dr).
- clear sub fpl. 
eapply derI.  eapply (fextI_eqc' _ Γ0 (cre2 ++ la ++ ra') _ _ l).  sfea.
apply dersrecI_forall.  intros c incm.
apply InT_mapE in incm. cD.
inversion incm0. clear incm0. subst.
unfold fmlsext. simpl.
eapply ForallTD_forall in fpr.  2: apply (InT_map _ incm1).
destruct fpr. clear d. destruct c.
specialize (d _ (Γ0 ++ incm ++ cre2) ra' c0 eq_refl).
require d.  sfea.
apply (eq_rect _ _ d). list_eq_assoc.
Qed.

Theorem lj_cut_adm V fml cl cr: derrec (@LJrules V) emptyT cl ->  
  derrec LJrules emptyT cr -> cedc LJrules fml cl cr.
Proof. intros dl dr.
eapply (@gen_step2_lemT _ _ _ (cedc (@LJrules V)) fml isubfml).
apply AccT_isubfml.
intros * ra rb.  apply (lj_gs2 ra rb).
exact dl. exact dr.
Qed.

(* started to prove it like this, but not good for where cut formula
  in the right premise is not principal, which we only want to prove once 
Lemma lj_gs2 V fml psl psr cl cr:
  @LJrules V psl cl -> @LJrules V psr cr ->
  gen_step2 (cedc LJrules) fml isubfml (derrec LJrules emptyT)
        (derrec LJrules emptyT) psl cl psr cr.
Proof. unfold LJrules. intros ljl ljr.  destruct ljl.  destruct ljr.
destruct r0.
destruct l.
- destruct r. destruct l.
+ eapply gs2_ImpLL.  apply fextI'. exact i0.
+ admit.
+ eapply gs2_idL_lj.  apply fextI'. exact i0.
+ eapply gs2_lrlsL_lj. apply fextI'. exact r.
+ admit.
- eapply gs2_ImpRR_lj.  apply fextI'. exact i.
- eapply gs2_idR_lj.  apply fextI'. exact i.  
- admit.
- apply gs2_rrlsR_lj. apply fextI'. exact r0.
*)
About lj_gs2. 
About lj_cut_adm. 

