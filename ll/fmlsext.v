
Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Add LoadPath "../general".
Add LoadPath "../tense-lns".
Require Import gen.
Require Import genT.
Require Import ddT.
Require Import List_lemmasT gen_tacs.

Definition fmlsext (W : Type) Γ1 Γ2 (fmls : (list W)) := (Γ1 ++ fmls ++ Γ2).

Lemma fmlsext_fmlsext: forall V (Γ1 Γ2 Φ1 Φ2 : list V) seq,
  fmlsext Γ1 Γ2 (fmlsext Φ1 Φ2 seq) = fmlsext (Γ1 ++ Φ1) (Φ2 ++ Γ2) seq.
Proof. intros. unfold fmlsext.  rewrite !app_assoc. reflexivity. Qed.  

Lemma map_fmlsext_fmlsext: forall V (Γ1 Γ2 Φ1 Φ2 : list V) seqs,
  map (fmlsext Γ1 Γ2) (map (fmlsext Φ1 Φ2) seqs) =
  map (fmlsext (Γ1 ++ Φ1) (Φ2 ++ Γ2)) seqs.
Proof. induction seqs. tauto. 
simpl. rewrite IHseqs. rewrite fmlsext_fmlsext. reflexivity. Qed.  

Lemma fmlsext_def : forall (W : Type) Φ1 Φ2 U,
      @fmlsext W Φ1 Φ2 U = (Φ1 ++ U ++ Φ2).
Proof. reflexivity. Qed.

Inductive fmlsrule (W : Type) Φ1 Φ2 (pr : rlsT (list W)) : rlsT (list W) := 
  | OSctxt : forall ps c, pr ps c -> 
    fmlsrule Φ1 Φ2 pr (map (fmlsext Φ1 Φ2) ps) (fmlsext Φ1 Φ2 c).

Lemma OSctxt_e: forall (W : Type) (pr : rlsT (list W)) ps U Φ1 Φ2,
  pr ps U -> fmlsrule Φ1 Φ2 pr (map (fmlsext Φ1 Φ2) ps) (Φ1 ++ U ++ Φ2).
Proof.
  intros *. intros H. rewrite <- fmlsext_def.
  apply OSctxt. exact H.
Qed.

Lemma OSctxt_eq: forall (W : Type) pr ps mps (ca U Φ1 Φ2 : list W),
  pr ps U -> ca = Φ1 ++ U ++ Φ2 -> 
  mps = map (fmlsext Φ1 Φ2) ps -> fmlsrule Φ1 Φ2 pr mps ca.
Proof. intros.  subst. apply OSctxt_e. exact X. Qed.  

Lemma fmlsrule_id (W : Type) (pr : rlsT (list W)) :
  forall ps c, pr ps c -> fmlsrule [] [] pr ps c.
Proof. intros.
apply (OSctxt_eq pr ps c [] []). assumption.
simpl. rewrite app_nil_r.  reflexivity.
clear X. induction ps.  simpl.  reflexivity.
simpl. rewrite <- IHps.
unfold fmlsext. simpl.  rewrite !app_nil_r.
reflexivity. Qed.

Lemma fmlsrule_fmlsrule (W : Type) Γ1 Γ2 Φ1 Φ2 (pr : rlsT (list W)) :
  rsub (fmlsrule Γ1 Γ2 (fmlsrule Φ1 Φ2 pr)) (fmlsrule (Γ1 ++ Φ1) (Φ2 ++ Γ2) pr).
Proof. unfold rsub. intros. inversion X. subst. clear X. 
inversion X0.  subst. clear X0.
rewrite fmlsext_fmlsext.
eapply OSctxt_eq. exact X. 
reflexivity.
clear X. induction ps0.  simpl.  reflexivity.
simpl. rewrite IHps0.  rewrite fmlsext_fmlsext. reflexivity. Qed.

Definition fmlsrule_fmlsrule' (W : Type) Γ1 Γ2 Φ1 Φ2 pr :=
  rsubD (@fmlsrule_fmlsrule W Γ1 Γ2 Φ1 Φ2 pr).
 
Lemma derl_fmlsrule'' (W : Type) Φ1 Φ2 (rules : rlsT (list W)) :
  (forall ps c, derl rules ps c -> 
   derl (fmlsrule Φ1 Φ2 rules) (map (fmlsext Φ1 Φ2) ps) (fmlsext Φ1 Φ2 c)) * 
  (forall ps cs, dersl rules ps cs -> 
    dersl (fmlsrule Φ1 Φ2 rules) (map (fmlsext Φ1 Φ2) ps) 
    (map (fmlsext Φ1 Φ2) cs)).
Proof.  eapply (derl_dersl_rect_mut (rules := rules)
  (fun ps c => fun _ => derl (fmlsrule Φ1 Φ2 rules)
    (map (fmlsext Φ1 Φ2) ps) (fmlsext Φ1 Φ2 c))
  (fun ps cs : list _ => fun _ => dersl (fmlsrule Φ1 Φ2 rules)
    (map (fmlsext Φ1 Φ2) ps) (map (fmlsext Φ1 Φ2) cs))).
- simpl. intros. apply asmI.
- intros. eapply dtderI.  apply OSctxt. eassumption.  assumption. 
- simpl. apply dtNil.
- intros. rewrite map_app. simpl. apply dtCons ; assumption. Qed.
 
Definition derl_fmlsrule' W Φ1 Φ2 rules := 
  fst (@derl_fmlsrule'' W Φ1 Φ2 rules).
Definition dersl_fmlsrule' W Φ1 Φ2 rules := 
  snd (@derl_fmlsrule'' W Φ1 Φ2 rules).
 
Lemma derl_fmlsrule (W : Type) Φ1 Φ2 (rules : rlsT (list W)) :
  rsub (fmlsrule Φ1 Φ2 (derl rules)) (derl (fmlsrule Φ1 Φ2 rules)).
Proof.  unfold rsub.  intros.  destruct X.  
apply derl_fmlsrule'. assumption. Qed.

(* need to use general version, fmlsruleg, for this 
Lemma fmlsrule_derl_fmlsrule (W : Type) Φ1 Φ2 (rules : rlsT (list W)) :
  rsub (fmlsrule Φ1 Φ2 (derl (fmlsrule Φ1 Φ2 rules))) 
    (derl (fmlsrule Φ1 Φ2 rules)).
Proof.  eapply rsub_trans. apply derl_fmlsrule.
 unfold rsub.  intros.  eapply derl_mono. 2: eassumption.
 apply fmlsrule_fmlsrule. Qed.

Definition fmlsrule_derl_fmlsrule' W rules :=
  rsubD (@fmlsrule_derl_fmlsrule W rules).
 *)

Lemma OSctxt_e': forall (W : Type) (pr : rlsT (list W)) ps U Φ1 Φ2,
  pr ps U -> fmlsrule Φ1 Φ2 pr (map (fmlsext Φ1 Φ2) ps) ((Φ1 ++ U) ++ Φ2).
Proof.
  intros *. intros H.
  rewrite <- app_assoc. apply OSctxt_e. exact H.
Qed.  

Lemma fmlsext_defp : forall (W : Type) Φ1 Φ2 U,
      @fmlsext W Φ1 Φ2 U = (Φ1 ++ U ++ Φ2).
Proof. reflexivity. Qed.

Lemma fmlsrule_same: forall (W : Type) Φ1 Φ2 pr ps (c c' : (list W)),
  fmlsrule Φ1 Φ2 pr ps c -> c = c' -> fmlsrule Φ1 Φ2 pr ps c'.
Proof. intros. subst. assumption. Qed.  

Lemma fmlsrule_mono X (rulesa rulesb : rlsT (list X)) Φ1 Φ2 :
  rsub rulesa rulesb -> rsub (fmlsrule Φ1 Φ2 rulesa) (fmlsrule Φ1 Φ2 rulesb).
Proof. unfold rsub. intros. destruct X1. apply OSctxt. firstorder. Qed.

Definition fmlsrule_mono' X Φ1 Φ2 rulesa rulesb rs :=
  rsubD (@fmlsrule_mono X Φ1 Φ2 rulesa rulesb rs).

Lemma OSctxt_nil: forall (W : Type) pr c Γ1 Γ2, (pr [] c : Type) ->
  @fmlsrule W Γ1 Γ2 pr [] (fmlsext Γ1 Γ2 c).
Proof.
  intros *.  intros H. eapply OSctxt in H.
  simpl in H. exact H.
Qed.

(** general version of fmlsrule, not specifying contexts **)

Inductive fmlsruleg (W : Type) (pr : rlsT ((list W))) : rlsT ((list W)) := 
  | OSgctxt : forall ps c Φ1 Φ2, pr ps c -> 
    fmlsruleg pr (map (fmlsext Φ1 Φ2) ps) (fmlsext Φ1 Φ2 c).

Lemma fmlsrule_g (W : Type) Φ1 Φ2 (pr : rlsT ((list W))) :
  rsub (fmlsrule Φ1 Φ2 pr) (fmlsruleg pr).
Proof. unfold rsub. intros. destruct X. apply OSgctxt. exact p. Qed.

Lemma fmlsrule_g_ex (W : Type) (pr : rlsT ((list W))) ps c :
  fmlsruleg pr ps c -> { xs : list W & { ys : list W & fmlsrule xs ys pr ps c}}.
Proof. intro f. destruct f. eexists. eexists. apply OSctxt. apply p. Qed.

Lemma OSgctxt_e: forall (W : Type) (pr : rlsT ((list W))) ps U Φ1 Φ2,
  pr ps U -> fmlsruleg pr (map (fmlsext Φ1 Φ2) ps) (Φ1 ++ U ++ Φ2).
Proof.
  intros *. intros H. rewrite <- fmlsext_def.
  apply OSgctxt. exact H.
Qed.

Lemma OSgctxt_eq: forall (W : Type) pr ps mps (ca U Φ1 Φ2 : list W),
  pr ps U -> ca = Φ1 ++ U ++ Φ2 -> 
  mps = map (fmlsext Φ1 Φ2) ps -> fmlsruleg pr mps ca.
Proof. intros.  subst. apply OSgctxt_e. exact X. Qed.  

Lemma fmlsruleg_id (W : Type) (pr : rlsT ((list W))) :
  forall ps c, pr ps c -> fmlsruleg pr ps c.
Proof. intros.
apply (OSgctxt_eq pr ps c [] []). assumption.
simpl. rewrite app_nil_r.  reflexivity.
clear X. induction ps.  simpl.  reflexivity.
simpl. rewrite <- IHps.
unfold fmlsext. simpl.  rewrite !app_nil_r.
reflexivity. Qed.

Lemma fmlsruleg_fmlsruleg (W : Type) (pr : rlsT ((list W))) :
  rsub (fmlsruleg (fmlsruleg pr)) (fmlsruleg pr).
Proof. unfold rsub. intros. inversion X. subst. clear X. 
inversion X0.  subst. clear X0.
rewrite fmlsext_fmlsext.
eapply OSgctxt_eq. exact X. 
reflexivity.
clear X. induction ps0.  simpl.  reflexivity.
simpl. rewrite IHps0.  rewrite fmlsext_fmlsext. reflexivity. Qed.

Definition fmlsruleg_fmlsruleg' (W : Type) pr :=
  rsubD (@fmlsruleg_fmlsruleg W pr).
 
Lemma derl_fmlsruleg'' (W : Type) (rules : rlsT ((list W))) :
  forall Φ1 Φ2, (forall ps c, derl rules ps c -> 
   derl (fmlsruleg rules) (map (fmlsext Φ1 Φ2) ps) (fmlsext Φ1 Φ2 c)) * 
  (forall ps cs, dersl rules ps cs -> 
    dersl (fmlsruleg rules) (map (fmlsext Φ1 Φ2) ps) 
    (map (fmlsext Φ1 Φ2) cs)).
Proof. intros Φ1 Φ2.
eapply (derl_dersl_rect_mut (rules := rules)
  (fun ps c => fun _ => derl (fmlsruleg rules)
    (map (fmlsext Φ1 Φ2) ps) (fmlsext Φ1 Φ2 c))
  (fun ps cs : list _ => fun _ => dersl (fmlsruleg rules)
    (map (fmlsext Φ1 Φ2) ps) (map (fmlsext Φ1 Φ2) cs))).
- simpl. intros. apply asmI.
- intros. eapply dtderI.  apply OSgctxt. eassumption.  assumption. 
- simpl. apply dtNil.
- intros. rewrite map_app. simpl. apply dtCons ; assumption. Qed.
 
Definition derl_fmlsruleg' W rules Φ1 Φ2 := 
  fst (@derl_fmlsruleg'' W rules Φ1 Φ2).
Definition dersl_fmlsruleg' W rules Φ1 Φ2 := 
  snd (@derl_fmlsruleg'' W rules Φ1 Φ2).
 
Lemma derl_fmlsruleg (W : Type) (rules : rlsT ((list W))) :
  rsub (fmlsruleg (derl rules)) (derl (fmlsruleg rules)).
Proof.  unfold rsub.  intros.  destruct X.  
apply derl_fmlsruleg'. assumption. Qed.

Lemma fmlsruleg_derl_fmlsruleg (W : Type) (rules : rlsT ((list W))) :
  rsub (fmlsruleg (derl (fmlsruleg rules))) (derl (fmlsruleg rules)).
Proof.  eapply rsub_trans. apply derl_fmlsruleg.
 unfold rsub.  intros.  eapply derl_mono. 2: eassumption.
 apply fmlsruleg_fmlsruleg. Qed.

Definition fmlsruleg_derl_fmlsruleg' W rules :=
  rsubD (@fmlsruleg_derl_fmlsruleg W rules).

Lemma OSgctxt_e': forall (W : Type) (pr : rlsT ((list W))) ps U Φ1 Φ2,
  pr ps U -> fmlsruleg pr (map (fmlsext Φ1 Φ2) ps) ((Φ1 ++ U) ++ Φ2).
Proof.
  intros *. intros H.
  rewrite <- app_assoc. apply OSgctxt_e. exact H.
Qed.  

Lemma fmlsruleg_same: forall (W : Type) pr ps (c c' : (list W)),
  fmlsruleg pr ps c -> c = c' -> fmlsruleg pr ps c'.
Proof. intros. subst. assumption. Qed.  

Lemma fmlsruleg_mono X (rulesa rulesb : rlsT ((list X))) :
  rsub rulesa rulesb -> rsub (fmlsruleg rulesa) (fmlsruleg rulesb).
Proof. unfold rsub. intros. destruct X1. apply OSgctxt. firstorder. Qed.

Definition fmlsruleg_mono' X rulesa rulesb rs :=
  rsubD (@fmlsruleg_mono X rulesa rulesb rs).

Lemma OSgctxt_nil: forall (W : Type) pr c Γ1 Γ2, (pr [] c : Type) ->
  @fmlsruleg W pr [] (fmlsext Γ1 Γ2 c).
Proof.
  intros *.  intros H. eapply OSgctxt in H.
  simpl in H. exact H.
Qed.

(* specialized version for fmlsextg for Bang rule *)
Inductive fmlsrulegq W U (f : U -> W) pr : rlsT (list W) :=
  | fmlsrulegq_I : forall (cl cr : list U) (mcl mcr mc : list W) mps ps c,
    pr ps c -> mcl = map f cl -> mcr = map f cr -> 
    mps = map (fmlsext mcl mcr) ps -> mc = fmlsext mcl mcr c ->
    @fmlsrulegq _ _ f pr mps mc.

(* order-preserving merge *)
Inductive merge {W : Type} : list W -> list W -> list W -> Type :=
  | mergeLI : forall xs ys zs x, merge xs ys zs -> merge (x :: xs) ys (x :: zs)
  | mergeRI : forall xs ys zs y, merge xs ys zs -> merge xs (y :: ys) (y :: zs)
  | merge_nil : merge [] [] [].

Lemma merge_sym {W} xs ys zs : @merge W xs ys zs -> merge ys xs zs.
Proof. intro. induction X. apply mergeRI. exact IHX.
  apply mergeLI. exact IHX. apply merge_nil. Qed.

Lemma merge_Lnil {W} xs : @merge W [] xs xs.
Proof. induction xs. apply merge_nil. exact (mergeRI _ IHxs). Qed.

Definition merge_Rnil {W} xs := merge_sym (@merge_Lnil W xs).

Lemma merge_LnilE' {W} xs ys ms : @merge W xs ys ms -> xs = [] -> ys = ms.
Proof. intro. induction X.
- intro. discriminate H.
- firstorder.  subst. reflexivity.
- tauto. Qed.

Definition merge_LnilE {W} ys ms mrg := @merge_LnilE' W [] ys ms mrg eq_refl.
Definition merge_RnilE {W} xs ms mrg := @merge_LnilE W xs ms (merge_sym mrg).

Lemma merge_app {W} (x1 y1 z1 x2 y2 z2 : list W) :
  merge x1 y1 z1 -> merge x2 y2 z2 -> merge (x1 ++ x2) (y1 ++ y2) (z1 ++ z2).
Proof. intros * m. induction m.
- intros m2. simpl. apply mergeLI. apply IHm. apply m2.
- intros m2. simpl. apply mergeRI. apply IHm. apply m2.
- simpl. tauto. Qed.

Lemma merge_simple_app W xs ys : @merge W xs ys (xs ++ ys).
Proof. induction xs ; simpl. apply merge_Lnil.
exact (mergeLI _ IHxs). Qed.

Inductive sing {X} : list X -> Type :=
  | singI : forall a, sing [a].

Lemma merge_splitM' {W} (xs ys ms : list W) :
  merge xs ys ms -> forall ms1 ms2, ms = ms1 ++ ms2 -> 
    sigT (fun xs1 => sigT (fun xs2 =>  
      sigT (fun ys1 => sigT (fun ys2 => 
    prod (prod (merge xs1 ys1 ms1) (merge xs2 ys2 ms2)) 
      (prod (xs = xs1 ++ xs2) (ys = ys1 ++ ys2)))))).
Proof. intro. induction X ; cD.
- intros. destruct ms1.
+ simpl in H. subst.
repeat eexists. apply merge_nil.
apply (mergeLI x X). reflexivity. reflexivity.
+ simpl in H. injection H as . subst.
specialize (IHX _ _ eq_refl). cD. subst.
repeat eexists. apply (mergeLI w IHX3). exact IHX6. reflexivity.
- intros. destruct ms1.
+ simpl in H. subst.
repeat eexists. apply merge_nil.
apply (mergeRI y X). reflexivity.  reflexivity.
+ simpl in H. injection H as . subst.
specialize (IHX _ _ eq_refl). cD. subst.
repeat eexists. apply (mergeRI w IHX3). exact IHX6. reflexivity.
- intros. apply nil_eq_appT in H. cD. subst.
repeat eexists.  apply merge_nil.  apply merge_nil.
reflexivity.  reflexivity. Qed.

Definition merge_splitM {W} (xs ys ms1 ms2 : list W) m :=
  @merge_splitM' W xs ys _ m ms1 ms2 eq_refl.

Lemma merge_splitL' {W} (xs ys ms : list W) :
  merge xs ys ms -> forall xs1 xs2, xs = xs1 ++ xs2 -> 
    sigT (fun ys1 => sigT (fun ys2 => sigT (fun ms1 => sigT (fun ms2 => 
    prod (prod (merge xs1 ys1 ms1) (merge xs2 ys2 ms2)) 
      (prod (ys = ys1 ++ ys2) (ms = ms1 ++ ms2)))))).
Proof. intro. induction X ; cD.
- intros. destruct xs1.
+ simpl in H. subst.
repeat eexists. apply merge_nil.  apply (mergeLI x X). 
reflexivity.  reflexivity.
+ simpl in H. injection H as . subst.
specialize (IHX _ _ eq_refl). cD. subst.
repeat eexists. apply (mergeLI w IHX3). exact IHX6. reflexivity.
- intros. subst.
specialize (IHX _ _ eq_refl).  cD. subst.
repeat eexists. apply (mergeRI y IHX3).  apply IHX6.
reflexivity.  reflexivity.
- intros. apply nil_eq_appT in H. cD. subst.
repeat eexists.  apply merge_nil.  apply merge_nil.
reflexivity.  reflexivity. Qed.

Definition merge_splitL {W} (xs1 xs2 ys ms : list W) m :=
  @merge_splitL' W _ ys ms m xs1 xs2 eq_refl.

Lemma merge_splitR {W} (xs ys1 ys2 ms : list W) :
  merge xs (ys1 ++ ys2) ms -> 
    sigT (fun xs1 => sigT (fun xs2 => sigT (fun ms1 => sigT (fun ms2 => 
    prod (prod (merge xs1 ys1 ms1) (merge xs2 ys2 ms2)) 
      (prod (xs = xs1 ++ xs2) (ms = ms1 ++ ms2)))))).
Proof. intros m. 
pose (merge_splitL _ _ (merge_sym m)). cD.  subst.
repeat eexists. exact (merge_sym s3).  exact (merge_sym s6). Qed.

(* need better than merge_splitL !!
for   m : merge (xs ++ [a] ++ ys) rs ms
want to split ms at a
*)
Lemma merge_singleL' {W} x (xs ys ms : list W) :
  merge xs ys ms -> xs = [x] -> sigT (fun ys1 => sigT (fun ys2 => 
    prod (ys = ys1 ++ ys2) (ms = ys1 ++ [x] ++ ys2))).
Proof. intro. induction X ; cD.
- intro. injection H as . subst.
exists []. exists zs.
apply merge_LnilE in X. subst. split ; reflexivity.
- intro. specialize (IHX H). cD.
exists (y :: IHX).  exists IHX0. subst. simpl. split ; reflexivity.
- intro. discriminate H. Qed.

Definition merge_singleL {W} x ys ms mrg :=
  @merge_singleL' W x [x] ys ms mrg eq_refl.

Definition merge_singleR {W} y xs ms mrg :=
  @merge_singleL W y xs ms (merge_sym mrg).

Lemma merge_ctns_singleL {W} x (xs1 xs2 ys ms : list W) :
  merge (xs1 ++ [x] ++ xs2) ys ms -> 
    sigT (fun ys1 => sigT (fun ys2 => sigT (fun ms1 => sigT (fun ms2 => 
    prod (prod (merge xs1 ys1 ms1) (merge xs2 ys2 ms2)) 
      (prod (ys = ys1 ++ ys2) (ms = ms1 ++ [x] ++ ms2)))))).
Proof. intro. apply merge_splitL in X.  cD.
apply merge_splitL in X6.  cD.
apply merge_singleL in X10. cD. subst.
exists (X ++ X10).  exists (X14 ++ X7).
exists (X1 ++ X10).  exists (X14 ++ X9).
replace xs1 with (xs1 ++ []).
replace xs2 with ([] ++ xs2) by reflexivity.
repeat split.
exact (merge_app X3 (merge_Lnil X10)).
exact (merge_app (merge_Lnil X14) X13).
rewrite - !app_assoc. reflexivity.
rewrite - !app_assoc. reflexivity.
apply app_nil_r. Qed.

Lemma merge_consL W x (xs ys ms : list W) :
  merge (x :: xs) ys ms -> 
    sigT (fun ys1 => sigT (fun ys2 => sigT (fun ms2 => 
    prod (merge xs ys2 ms2) 
      (prod (ys = ys1 ++ ys2) (ms = ys1 ++ [x] ++ ms2))))).
Proof. intro m. pose (merge_ctns_singleL x [] xs m). cD.
apply merge_LnilE in s3. subst.
repeat eexists. exact s6. Qed.

(* could fix by using merge_sym twice *)
Definition merge_ctns_singleR' W y xs ys1 ys2 ms mrg :=
  @merge_ctns_singleL W y ys1 ys2 xs ms (merge_sym mrg).

Definition merge_consR' W y xs ys ms mrg :=
  @merge_consL W y ys xs ms (merge_sym mrg).

Lemma merge_assoc W (xs ys ms : list W) :
  merge xs ys ms -> forall us vs, merge us vs xs -> 
    sigT2 (fun ws => merge us ws ms) (merge vs ys).
Proof. intro.  induction X ; intros us vs mrg.
- inversion mrg ; subst ; clear mrg.
+ apply IHX in X0. cD. eexists. exact (mergeLI x X1). exact X2.
+ apply IHX in X0. cD. eexists. exact (mergeRI x X1). exact (mergeLI x X2).
- apply IHX in mrg. cD. exists (y :: mrg). 
  exact (mergeRI y mrg0).  exact (mergeRI y mrg1).
- inversion mrg. exists [] ; exact merge_nil. Qed.

Lemma merge_repeat' W xs ys zs (A : W):
  merge xs ys zs -> forall n, (zs = repeat A n) ->
  {k : nat & (xs = repeat A k) & {m : nat & (Nat.add k m = n) & 
    (ys = repeat A m)}}.
Proof. intro mrg. induction mrg ; intros ; destruct n ; subst.
- inversion H.
- inversion H.
specialize (IHmrg _ H2). cD. subst.
exists (S IHmrg). reflexivity.  exists IHmrg1 ; reflexivity.
- inversion H.
- inversion H. subst.
  specialize (IHmrg _ eq_refl). cD. subst.
  eexists. reflexivity.
  exists (S IHmrg1). apply PeanoNat.Nat.add_succ_r. reflexivity.
- exists 0. reflexivity.  exists 0 ; reflexivity.
- inversion H.
Qed.

Definition merge_repeat {W} xs ys (A : W) n mrg :=
  @merge_repeat' W xs ys _ (A : W) mrg n eq_refl.

Fixpoint doubles W (xs : list W) :=
  match xs with | y :: ys => y :: y :: doubles ys | [] => [] end.

Lemma merge_doubles W (xs : list W) : merge xs xs (doubles xs).
Proof. induction xs ; simpl. apply merge_nil.
apply (mergeLI a (mergeRI a IHxs)).  Qed.

(* note this lemma doesn't do what we want because it doesn't show
  that duplicated formulae are adjacent in mqs (so can be contracted),
  see ll_lems.merge_doubles_via_der instead *)
Lemma merge_doubles_via W (xs qs ms : list W) (mrg : merge xs qs ms) :
  { mqs : list W & merge xs (doubles qs) mqs & merge ms qs mqs }.
Proof. induction mrg ; cD.
exists (x :: IHmrg) ; apply mergeLI ; assumption.
exists (y :: y :: IHmrg) ; repeat (apply mergeRI || apply mergeLI) ;
  assumption.
exists [] ; apply merge_nil. Qed.

Lemma get_prefix W n : forall (zs : list W), leT n (length zs) ->
  { xs : list W & length xs = n & { ys : list W & zs = xs ++ ys}}.
Proof. induction n ; intros.
- exists []. simpl. reflexivity.  exists zs. reflexivity.
- destruct zs ; simpl in H.
+ inversion H.
+ apply leT_S_n in H.  specialize (IHn zs H). cD.
subst. exists (w :: IHn). reflexivity.
eexists. reflexivity. Qed.

Lemma strip_prefixes W : forall (xs ys us vs : list W),
  xs ++ us = ys ++ vs -> length xs = length ys -> (xs = ys) * (us = vs).
Proof. induction xs.
- intros. simpl in H0.  destruct ys.
+ simpl in H. subst. tauto.
+ simpl in H0. inversion H0.
- simpl. intros * leq lneq. destruct ys ; simpl in lneq ; inversion lneq.
simpl in leq. inversion leq.
specialize (IHxs _ _ _ H2 H0). cD. subst. tauto. Qed.

Lemma repeat_eq_app W (A : W) n : forall xs ys, repeat A n = xs ++ ys ->
  { k : nat & xs = repeat A k & { m : nat & ys = repeat A m}}.
Proof. induction n ; intros ; simpl in H.
- list_eq_ncT. cD. subst. exists 0. reflexivity. exists 0. reflexivity.
- destruct xs ; simpl in H.
+ exists 0. reflexivity. exists (S n). subst. reflexivity.
+ inversion H. subst.  specialize (IHn _ _ H2). cD. subst.
exists (S IHn). reflexivity.  eexists. reflexivity. Qed.

Lemma repeat_add W (A : W) m n : repeat A (m + n) = repeat A m ++ repeat A n.
Proof. induction m ; subst ; simpl.
reflexivity.  rewrite IHm. reflexivity. Qed.






