
(* linear logic as in https://en.wikipedia.org/wiki/Linear_logic
  ie, multiplicative and additive rules (mall)
  also exponentials *)

Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../modal".
Require Import gen genT ddT.
Require Import gstep.
Require Import fmlsext.
Require Import Coq.Program.Basics.

Inductive LLfml (V : Set): Type :=
 | Var : V -> LLfml V
 | DVar : V -> LLfml V
 | Bot : LLfml V
 | Top : LLfml V
 | One : LLfml V
 | Zero : LLfml V
 | tens : LLfml V -> LLfml V -> LLfml V
 | wth : LLfml V -> LLfml V -> LLfml V
 | par : LLfml V -> LLfml V -> LLfml V
 | plus : LLfml V -> LLfml V -> LLfml V
 | Bang : LLfml V -> LLfml V
 | Query : LLfml V -> LLfml V
.

Inductive isubfml {V} : LLfml V -> LLfml V -> Type :=
  | isub_tensL : forall C D, isubfml C (tens C D)
  | isub_tensR : forall C D, isubfml D (tens C D)
  | isub_wthL : forall C D, isubfml C (wth C D)
  | isub_wthR : forall C D, isubfml D (wth C D)
  | isub_parL : forall C D, isubfml C (par C D)
  | isub_parR : forall C D, isubfml D (par C D)
  | isub_plusL : forall C D, isubfml C (plus C D)
  | isub_plusR : forall C D, isubfml D (plus C D)
  | isub_Bang : forall A, isubfml A (Bang A)
  | isub_Query : forall A, isubfml A (Query A).

Lemma AccT_isubfml {V} (A : LLfml V) : AccT isubfml A.
Proof. induction A ; apply AccT_intro ; intros A' isf ;
  inversion isf ; subst ; assumption. Qed.

Fixpoint dual {V} f := match f with
  | Var v => DVar v
  | DVar v => Var v
  | Bot _ => One V
  | One _ => Bot V
  | Top _ => Zero V
  | Zero _ => Top V
  | tens A B => par (dual A) (dual B)
  | par A B => tens (dual A) (dual B)
  | plus A B => wth (dual A) (dual B)
  | wth A B => plus (dual A) (dual B)
  | Bang f => Query (dual f)
  | Query f => Bang (dual f)
  end.

Lemma dual_dual {V} A : dual (@dual V A) = A.
Proof. induction A ; simpl ; try reflexivity ; try (rewrite IHA) ;
try (rewrite IHA1) ; try (rewrite IHA2) ; try reflexivity. Qed.

Lemma dual_sub {V} A B : isubfml A B -> isubfml (@dual V A) (dual B).
Proof. intro isab. destruct isab ; simpl ; 
try (apply isub_tensL || apply isub_tensR || apply isub_wthL ||
  apply isub_wthR || apply isub_parL || apply isub_parR || apply isub_plusL ||
  apply isub_plusR || apply isub_Bang || apply isub_Query). Qed.

Lemma dual_sub' {V} A B : isubfml (@dual V A) (dual B) -> isubfml A B.
Proof. intro idd. pose (dual_sub idd). rewrite -> !dual_dual in i. exact i. Qed.

(* specifying formula, so we can limit it to propositions *)
Inductive Idrule {V} A : rlsT (list (LLfml V)) :=
  | Idrule_I : Idrule A [] [A ; dual A].

Inductive Onerule {V} : rlsT (list (LLfml V)) :=
  | Onerule_I : Onerule [] [One V].

Inductive Toprule {V} : rlsT (list (LLfml V)) :=
  | Toprule_I : Toprule [] [Top V].

Inductive Botrule {V} : rlsT (list (LLfml V)) :=
  | Botrule_I : Botrule [[]] [Bot V].

Inductive PlusRrule {V} : rlsT (list (LLfml V)) :=
  | PlusRrule_I : forall A B, PlusRrule [[B]] [plus A B].

Inductive PlusLrule {V} : rlsT (list (LLfml V)) :=
  | PlusLrule_I : forall A B, PlusLrule [[A]] [plus A B].

Inductive Wthrule {V} : rlsT (list (LLfml V)) :=
  | Wthrule_I : forall A B, Wthrule [[A] ; [B]] [wth A B].

Inductive Parrule {V} : rlsT (list (LLfml V)) :=
  | Parrule_I : forall A B, Parrule [[A ; B]] [par A B].

Inductive Queryrule {V} : rlsT (list (LLfml V)) :=
  | Queryrule_I : forall A, Queryrule [[A]] [Query A].

Inductive Bangrule {V} : rlsT (list (LLfml V)) :=
  | Bangrule_I : forall A, Bangrule [[A]] [Bang A].

(* rules which have simple context added *)
Inductive llprinc {V} : rlsT (list (LLfml V)) :=
  | Par_p : forall ps c, Parrule ps c -> llprinc ps c
  | Wth_p : forall ps c, Wthrule ps c -> llprinc ps c
  | PlusL_p : forall ps c, PlusLrule ps c -> llprinc ps c
  | PlusR_p : forall ps c, PlusRrule ps c -> llprinc ps c
  | Top_p : forall ps c, Toprule ps c -> llprinc ps c
  | Bot_p : forall ps c, Botrule ps c -> llprinc ps c
  .

Lemma llprinc_sing {V} : rsub (@llprinc V) (fun _ => sing).
Proof. apply rsubI. intros * llp. 
  destruct llp ; rename_last l ; destruct l ; apply singI. Qed.

Inductive Tensrule {V} : rlsT (list (LLfml V)) :=
  | Tensrule_I : forall A B, Tensrule [ [A] ; [B] ] [tens A B].
  
Lemma tens_sing {V} : rsub (@Tensrule V) (fun _ => sing).
Proof. apply rsubI. intros * tr.  destruct tr. apply singI. Qed.

Inductive wkrule {W} A : rlsT (list W) :=
  | wkrule_I : wkrule A [[]] [A].
  
Inductive ctrrule {W} A : rlsT (list W) :=
  | ctrrule_I : ctrrule A [[A ; A]] [A].
  
Inductive wkrules {W} : rlsT (list W) :=
  | wkrules_I : forall A ps c, wkrule A ps c -> wkrules ps c.
  
Inductive ctrrules {W} : rlsT (list W) :=
  | ctrrules_I : forall A ps c, ctrrule A ps c -> ctrrules ps c.
  
Inductive wkqrules {V} : rlsT (list (LLfml V)) :=
  | wkqrules_I : forall A ps c, wkrule (@Query V A) ps c -> wkqrules ps c.
  
Inductive ctrqrules {V} : rlsT (list (LLfml V)) :=
  | ctrqrules_I : forall A ps c, ctrrule (@Query V A) ps c -> ctrqrules ps c.
  
(* arbitrary weakening / contraction *)
Inductive wcrule {W} A : rlsT (list W) :=
  | wcrule_I : forall n, wcrule A [repeat A n] [A].
  
Lemma wk_sing {V} A : rsub (@wkrule V A) (fun _ => sing).
Proof. apply rsubI. intros * wr.  destruct wr. apply singI. Qed.

Lemma ctr_sing {V} A : rsub (@ctrrule V A) (fun _ => sing).
Proof. apply rsubI. intros * cr.  destruct cr. apply singI. Qed.

Lemma query_sing {V} : rsub (@Queryrule V) (fun _ => sing).
Proof. apply rsubI. intros * qr.  destruct qr. apply singI. Qed.

Lemma bang_sing {V} : rsub (@Bangrule V) (fun _ => sing).
Proof. apply rsubI. intros * br.  destruct br. apply singI. Qed.

(* for rule with 2 prems and merge contexts *)
Inductive merge_ctxt W cl cr prs : rlsT (list W) :=
  merge_ctxtI : forall al bl ar br pl pr c, 
    prs [pl ; pr] c -> merge al bl cl -> merge ar br cr -> 
    merge_ctxt cl cr prs [ al ++ pl ++ ar ; bl ++ pr ++ br] (cl ++ c ++ cr).

Inductive merge_ctxtg W prs : rlsT (list W) :=
  merge_ctxtgI : forall cl cr ps c, 
    merge_ctxt cl cr prs ps c -> merge_ctxtg prs ps c.

(* cut-admissibility, concatenating contexts *)
Inductive ossca X dual rules (A : X) cl cr : Type :=
    osscaI : (forall ls rs : list X, cl = A :: ls -> cr = dual A :: rs ->
             derrec rules emptyT (ls ++ rs)) -> ossca dual rules A cl cr.

(* cut-admissibility, merging contexts *)
Inductive osscam X dual rules (A : X) cl cr : Type :=
    osscamI : (forall ls rs ms : list X, cl = A :: ls -> cr = dual A :: rs ->
       merge ls rs ms -> derrec rules emptyT ms) -> osscam dual rules A cl cr.

Inductive osscan {W} dual rules n (A : W) cl cr : Type :=
    osscanI : (forall ls rs ms,
	cl = repeat A n ++ ls -> cr = dual A :: rs ->
	merge ls rs ms -> derrec rules emptyT ms) -> 
      osscan dual rules n A cl cr.

Inductive osscann {W} dual rules nl nr (A : W) cl cr : Type :=
    osscannI : (forall ls rs ms,
	cl = repeat A nl ++ ls -> cr = repeat (dual A) nr ++ rs ->
	merge ls rs ms -> derrec rules emptyT ms) -> 
      osscann dual rules nl nr A cl cr.

Lemma osscan_eq {W} dual rules n (A : W):
  req (osscan dual rules n A) (osscann dual rules n 1 A).
Proof. repeat split ; intros ; subst ; simpl in X ;
  destruct X ; firstorder. Qed.
  
Inductive osscang {W} dual rules A cl cr : Type :=
    osscangI : (forall n, @osscan W dual rules n A cl cr) ->
      osscang dual rules A cl cr.

Inductive osscangl {W} dual rules n A cl cr : Type :=
    osscanglI : (forall m, leT m n -> @osscan W dual rules m A cl cr) ->
      osscangl dual rules n A cl cr.

Inductive osscanq {V} dual rules n qA cl cr : Type :=
    osscanqI : (forall A, qA = @Query V A -> forall ls rs ms,
	cl = repeat qA n ++ ls -> cr = Bang (dual A) :: rs ->
	merge ls rs ms -> derrec rules emptyT ms) -> 
      osscanq dual rules n qA cl cr.

Inductive osscaq {V} dual rules qA cl cr : Type :=
    osscaqI : (forall n, @osscanq V dual rules n qA cl cr) ->
      osscaq dual rules qA cl cr.

(* temporarily, try alternative, using Q *)
Inductive osscaQ {V} dual rules qA cl cr : Type :=
    osscaQI : (forall A, qA = @Query V A -> @osscang _ dual rules qA cl cr) ->
      osscaQ dual rules qA cl cr.

Definition osscaQ' {V} dual rules A cl cr := 
  @osscaQ V dual rules (dual A) cr cl.

Definition osscaq' {V} dual rules A cl cr := 
  @osscaq V dual rules (dual A) cr cl.

Definition osscan' {W} dual rules n A cl cr := 
  @osscan W dual rules n (dual A) cr cl.

Lemma osscan'_eq {V} rules n (A : LLfml V):
  req (osscan' dual rules n A) (osscann dual rules 1 n A).
Proof. repeat split ; intros ; subst ; simpl in X ; destruct X ;
  rewrite -> dual_dual in d ; apply merge_sym in H1 ; firstorder. Qed.

Check osscan_eq.  Check osscan'_eq.

Lemma osscam_n_eq {W} rules dual (A : W) :
  req (osscam dual rules A) (osscan dual rules 1 A).
Proof. repeat split ; intros * ue ve mrg.
- destruct X. simpl in ue.  exact (d _ _ _ ue ve mrg).
- inversion X. simpl in X0.  exact (X0 _ _ _ ue ve mrg). Qed.

Definition osscam_nn_eq {V} dual rules (A : LLfml V) :=
  req_trans (@osscam_n_eq _ rules dual A) (@osscan_eq _ dual rules 1 A).

Definition osscam_n'_eq {V} rules (A : LLfml V) :=
  req_trans (@osscam_nn_eq _ dual rules A) (req_sym (@osscan'_eq V _ 1 A)).

Definition osscamQ {V} dual rules A cl cr : Type :=
  prod (osscam dual rules A cl cr) 
    (prod (@osscaQ V dual rules A cl cr) (osscaQ' dual rules A cl cr)).

Definition osscamq {V} dual rules A cl cr : Type :=
  prod (osscam dual rules A cl cr) 
    (prod (@osscaq V dual rules A cl cr) (osscaq' dual rules A cl cr)).

Lemma osscaQ_eq V dual rules A : 
  req (osscaQ dual rules (@Query V A)) (osscang dual rules (@Query V A)).
Proof. split ; intros u v oq.
destruct oq. exact (o A eq_refl).
split. intros. exact oq. Qed.

Lemma osscaQ_m {V} dual rules (A : LLfml V) cl cr :
  osscaQ dual rules (Query A) cl cr -> osscam dual rules (Query A) cl cr.
Proof. intro oq. apply osscamI. intros * cle cre mrg.
destruct oq. specialize (o A eq_refl).
destruct o.  specialize (o 1).
inversion o. simpl in X. exact (X ls rs ms cle cre mrg). Qed.

Lemma osscaQ'_m {V} rules (A : LLfml V) cl cr :
  osscaQ' dual rules (Bang (dual A)) cr cl -> osscam dual rules (Query A) cl cr.
Proof. intro oq. apply osscamI. intros * cle cre mrg.
destruct oq. simpl in o. specialize (o _ eq_refl).
destruct o.  specialize (o 1).
inversion o. simpl in X. simpl in cre.
rewrite -> !dual_dual in X.
exact (X ls rs ms cle cre mrg). Qed.

Inductive mall_rules {V} : rlsT (list (LLfml V)) :=
  | princ_mallI : forall ps c, fmlsruleg llprinc ps c -> mall_rules ps c
  | tens_mallI : forall ps c, merge_ctxtg Tensrule ps c -> mall_rules ps c
  | one_mallI : forall ps c, Onerule ps c -> mall_rules ps c
  | id_mallI : forall v ps c, Idrule (Var v) ps c -> mall_rules ps c
  | idd_mallI : forall v ps c, Idrule (DVar v) ps c -> mall_rules ps c.

Inductive maell_rules {V} : rlsT (list (LLfml V)) :=
  | mall_maellI : forall ps c, mall_rules ps c -> maell_rules ps c
  | wk_maellI : forall A ps c, 
    fmlsruleg (wkrule (Query A)) ps c -> maell_rules ps c
  | ctr_maellI : forall A ps c,
    fmlsruleg (ctrrule (Query A)) ps c -> maell_rules ps c
  | query_maellI : forall ps c, fmlsruleg Queryrule ps c -> maell_rules ps c
  | bang_maellI : forall ps c, 
    fmlsrulegq (@Query _) Bangrule ps c -> maell_rules ps c.
  (*
  | bang_maellI : forall xs ys ps c, fmlsrule (map (@Query _) xs)
    (map (@Query _) ys) Bangrule ps c -> maell_rules ps c.
    *)

Definition id_maellI {V} v ps c r := mall_maellI (@id_mallI V v ps c r).
Definition idd_maellI {V} v ps c r := mall_maellI (@idd_mallI V v ps c r).
Definition princ_maellI {V} ps c r := mall_maellI (@princ_mallI V ps c r).
Definition tens_maellI {V} ps c r := mall_maellI (@tens_mallI V ps c r).
Definition one_maellI {V} ps c r := mall_maellI (@one_mallI V ps c r).

Lemma ctrq_maell {V} : rsub (fmlsruleg ctrqrules) (@maell_rules V).
Proof. intros ps c cqr. destruct cqr. destruct c0.
eapply ctr_maellI.  apply OSgctxt. apply c0. Qed.

Lemma wkq_maell {V} : rsub (fmlsruleg wkqrules) (@maell_rules V).
Proof. intros ps c cqr. destruct cqr. destruct w.
eapply wk_maellI.  apply OSgctxt. apply w. Qed.

Theorem maell_id {V} (A : LLfml V) : derrec maell_rules emptyT [ A ; dual A ].
Proof. induction A ; eapply derI.
- eapply id_maellI. apply Idrule_I. - apply dlNil.
- eapply idd_maellI. apply Idrule_I. - apply dlNil.
- eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []). apply Bot_p.
  eapply Botrule_I. reflexivity. reflexivity.
- unfold fmlsext. simpl. apply dersrec_singleI.
  eapply derI. apply one_maellI. apply Onerule_I. apply dlNil.
- eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []). apply Top_p.
  eapply Toprule_I. reflexivity. reflexivity.
- simpl. apply dlNil.
- eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [One V] []). apply Bot_p.
  eapply Botrule_I. reflexivity. reflexivity.
- unfold fmlsext. simpl. apply dersrec_singleI.
  eapply derI. apply one_maellI. apply Onerule_I. apply dlNil.
- eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [Zero V] []). apply Top_p.
  eapply Toprule_I. reflexivity. reflexivity.
- simpl. apply dlNil.
- simpl.  eapply princ_maellI. 
  eapply (OSgctxt_eq _ _ _ [tens A1 A2] []). apply Par_p.
  eapply Parrule_I. reflexivity. reflexivity.
- apply dersrec_singleI. unfold fmlsext. simpl.
  eapply derI. apply tens_maellI.
  eapply merge_ctxtgI. eapply eq_rect.
  eapply (@merge_ctxtI _ _ _ _ [] [] [dual A1] [dual A2]).
  apply Tensrule_I.
  apply merge_nil. 
  apply (mergeLI _ (mergeRI _ merge_nil)).
  reflexivity. simpl.
  apply (dlCons IHA1 (dlCons IHA2 (dlNil _ _))).
- eapply princ_maellI. eapply (OSgctxt_eq _ _ _ []). apply Wth_p.
  eapply Wthrule_I. reflexivity. reflexivity.
- simpl. unfold fmlsext. simpl.  apply dlCons. eapply derI.
  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [A1]). apply PlusL_p.
  apply PlusLrule_I. reflexivity. reflexivity.
  simpl. apply dersrec_singleI. unfold fmlsext. simpl. apply IHA1.
  apply dersrec_singleI. eapply derI.
  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [A2]). apply PlusR_p.
  apply PlusRrule_I. reflexivity. reflexivity.
  simpl. apply dersrec_singleI. unfold fmlsext. simpl. apply IHA2.
- simpl.  eapply princ_maellI. 
  eapply (OSgctxt_eq _ _ _ [] [tens _ _]). apply Par_p.
  eapply Parrule_I. reflexivity. reflexivity.
- apply dersrec_singleI. unfold fmlsext. simpl.
  eapply derI. apply tens_maellI.
  eapply merge_ctxtgI. eapply eq_rect.
  eapply (@merge_ctxtI _ _ _ _ [A1] [A2] [] []).
  apply Tensrule_I.
  apply (mergeLI _ (mergeRI _ merge_nil)).
  apply merge_nil. 
  reflexivity. simpl.
  apply (dlCons IHA1 (dlCons IHA2 (dlNil _ _))).
- simpl. eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [_] []). apply Wth_p.
  eapply Wthrule_I. reflexivity. reflexivity.
- simpl. unfold fmlsext. simpl.  apply dlCons. eapply derI.
  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [] [_]). apply PlusL_p.
  apply PlusLrule_I. reflexivity. reflexivity.
  simpl. apply dersrec_singleI. unfold fmlsext. simpl. apply IHA1.
  apply dersrec_singleI. eapply derI.
  eapply princ_maellI. eapply (OSgctxt_eq _ _ _ [] [_]). apply PlusR_p.
  apply PlusRrule_I. reflexivity. reflexivity.
  simpl. apply dersrec_singleI. unfold fmlsext. simpl. apply IHA2.
- apply bang_maellI. simpl.
  eapply (fmlsrulegq_I _ _ [] [_]) ; split. (*( why does this work? *)
- simpl. apply dersrec_singleI. unfold fmlsext. simpl.
  eapply derI.  apply query_maellI. 
  eapply (OSgctxt_eq _ _ _ [A] []). apply Queryrule_I.
  reflexivity. reflexivity. 
  simpl. apply dersrec_singleI. unfold fmlsext. simpl. exact IHA.
- simpl.  apply bang_maellI. 
  eapply (fmlsrulegq_I _ _ [_] []) ; split. (*( why does this work? *)
- simpl. apply dersrec_singleI. unfold fmlsext. simpl.
  eapply derI.  apply query_maellI. 
  eapply (OSgctxt_eq _ _ _ [] [dual A]). apply Queryrule_I.
  reflexivity. reflexivity. 
  simpl. apply dersrec_singleI. unfold fmlsext. simpl. exact IHA.
Qed.

Check maell_id.

(* arbitrary weakening/contraction is derivable *)
Lemma gen_wk_ctr W (A : W) rules :
  rsub (fmlsruleg (wkrule A)) rules ->
  rsub (fmlsruleg (ctrrule A)) rules ->
  rsub (fmlsruleg (wcrule A)) (derl rules).
Proof. intros rsw rsc ps c fw. destruct fw. destruct w.
revert Φ1 Φ2.
induction n ; simpl ; intros.
- apply (rsubD (rsub_derl rules)).  apply (rsubD rsw).
eapply OSgctxt_eq ; split.
- (* if n is 0 then nothing to prove, else use induction *)
destruct n ; simpl.
+ apply asmI.
+ simpl in IHn. 
eapply dtderI. apply (rsubD rsc). apply OSgctxt. apply ctrrule_I.
pose (dtCons (IHn (Φ1 ++ [A]) Φ2) (dtNil rules)).
unfold fmlsext.  unfold fmlsext in d.  simpl.
rewrite -> app_nil_r in d.  rewrite <- !app_assoc in d.
simpl in d.  exact d. Qed.

Definition maell_gen_wk_ctr V A :=
  gen_wk_ctr (rsubI _ _ (@wk_maellI V A)) (rsubI _ _ (@ctr_maellI V A)).

Lemma osscan_gl_lem {W} rules dual n (A : W) dl dr:
  osscangl dual rules n A dl dr -> osscan dual rules n A dl dr.
Proof. intro. destruct X. exact (o n (leT_n n)). Qed.

Lemma osscang_l_lem {W} rules dual n (A : W) dl dr:
  osscang dual rules A dl dr -> osscangl dual rules n A dl dr.
Proof. intro. destruct X. apply osscanglI. intros. exact (o m). Qed.

Lemma osscangl_le {W} rules dual n m (A : W) dl dr:
  leT m n -> osscangl dual rules n A dl dr -> osscangl dual rules m A dl dr.
Proof. intros. apply osscanglI. intros. destruct X.
  exact (o _ (leT_trans H0 H)). Qed.
  
Lemma osscaQ_mQ V A rules cl cr:
  osscaQ dual rules (@Query V A) cl cr -> osscamQ dual rules (Query A) cl cr.
Proof. intro oq. split.
- destruct oq. 
  specialize (o A eq_refl). destruct o. specialize (o 1). 
  destruct o.  simpl in d. split. simpl. exact d.
- split. exact oq. simpl. split. intros a0 bq. inversion bq. Qed.
  
Lemma osscang_mQ V A rules cl cr:
  osscang dual rules (@Query V A) cl cr -> osscamQ dual rules (Query A) cl cr.
Proof. intro ong. destruct ong. repeat split ; intros * cxe cye mrg.
- specialize (o 1). destruct o. simpl in d. exact (d _ _ _ cxe cye mrg).
- specialize (o n). destruct o. exact (d _ _ _ cxe cye mrg).
- inversion H. Qed.

Lemma osscamQ_ng V A rules cl cr:
  osscamQ dual rules (@Query V A) cl cr -> osscang dual rules (Query A) cl cr.
Proof. intro omq. destruct omq. cD. destruct p.  exact (o0 _ eq_refl). Qed.

