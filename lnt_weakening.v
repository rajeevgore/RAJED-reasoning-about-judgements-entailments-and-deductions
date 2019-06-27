Require Import ssreflect.

Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt lntacs lntls lntbR lntmtacs.
Require Import lntb1L lntb2L.
Require Import lntkt_exch.


Inductive weakened {T} : list T -> list T -> Prop :=
  | weakened_I : forall (X Y A B C : list T), X = (A ++ C) -> 
    Y = (A ++ B ++ C) -> weakened X Y.

Lemma weakened_I': forall T (A B C D : list T),
   weakened (A ++ C) (A ++ B ++ C).
Proof.  intros.  eapply weakened_I ; reflexivity. Qed.

(* -------------------------- *)
(* LEFT WEAKENING DEFINITIONS *)
(* -------------------------- *)

Definition can_gen_weakL {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 Δ,
  ns = G ++ (seq, d) :: K -> seq = pair (Γ1 ++ Γ3) Δ ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ Γ2 ++ Γ3) Δ, d) :: K).

Definition gen_weakL_step {V : Set}
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  Forall (can_gen_weakL rules) ps -> rsub last_rule rules -> 
  can_gen_weakL rules concl.

Lemma can_gen_weakL_def': forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_weakL rules ns <-> forall G K seq Γ Δ Γ' (d : dir), 
  weakened Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros.  unfold iff.  split ; intros. 
  destruct H0. subst. unfold can_gen_weakL in H.
  eapply H. reflexivity.  reflexivity.
  unfold can_gen_weakL. intros. eapply H.
  2: exact H0.  2: exact H1. apply weakened_I'. auto. Qed.

(* --------------------------- *)
(* RIGHT WEAKENING DEFINITIONS *)
(* --------------------------- *)

Definition can_gen_weakR {V : Set}
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 Δ3,
    ns = G ++ (seq, d) :: K -> seq = pair Γ (Δ1 ++ Δ3)->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ Δ2 ++ Δ3), d) :: K).

Definition gen_weakR_step {V : Set}
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  Forall (can_gen_weakR rules) ps -> rsub last_rule rules -> 
  can_gen_weakR rules concl.

Lemma can_gen_weakR_def': forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_weakR rules ns <-> forall G K seq Γ Δ Δ' (d : dir), 
  weakened Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K).
Proof.  intros.  unfold iff.  split ; intros. 
  destruct H0. subst. unfold can_gen_weakR in H.
  eapply H. reflexivity.  reflexivity.
  unfold can_gen_weakR. intros. eapply H.
  2: exact H0.  2: exact H1. apply weakened_I'. auto. Qed.

(* ----------------- *)
(* WEAKENING TACTICS *)
(* ----------------- *)

Ltac nsgen_sw_weak rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; subst q ;
rewrite -> Forall_forall in acm ;
rename_last inps0 ;  eapply in_map in inps0 ;
eapply acm in inps0 ;
rewrite -> ?can_gen_weakL_def' in inps0 ;
rewrite -> ?can_gen_weakR_def' in inps0 ; 
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply inps0 ; [> exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | reflexivity ]].
   
Lemma weak_same: forall T X, weakened X (X : list T).
Proof.
  intros. apply (weakened_I _ _ [] [] X); reflexivity.
Qed.

Lemma weak_L: forall T X Y Z,
  weakened X (Y : list T) -> weakened (Z ++ X) (Z ++ Y).
Proof.  intros. destruct H. subst. 
  rewrite !(app_assoc Z). apply weakened_I'. auto. Qed.

Lemma weak_R: forall T X Y Z,
  weakened X (Y : list T) -> weakened (X ++ Z) (Y ++ Z).
Proof.
  intros. destruct H. subst. rewrite <- !app_assoc.
  apply weakened_I'. auto.
Qed.

Lemma weak_cons: forall T (x : T) Y Z,
  weakened Y Z -> weakened (x :: Y) (x :: Z).
Proof.  intros. destruct H. subst. list_assoc_l. rewrite <- !app_assoc.
  apply weakened_I'. auto. Qed.

Lemma weak_simpleRX : forall T (A B : list T),
    weakened A (A ++ B).
Proof.
  intros. apply (weakened_I _ _ A B []);
            list_app_nil; reflexivity.
Qed.

Lemma weak_simpleLX : forall T (A B : list T),
    weakened A (B ++ A).
Proof.
  intros. apply (weakened_I _ _ [] B A);
            list_app_nil; reflexivity.
Qed.

Ltac weak_tacX :=
 list_assoc_r ; try (apply weak_same) ; 
    repeat (apply weak_L || apply weak_cons) ;  
    list_assoc_l ; repeat (apply weak_R); try apply weak_simpleRX;
    try apply weak_simpleLX.

Ltac nsprsame_weak rs pr q qin inmps acm inps0 x0 := 
derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
  apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ; 
rewrite -> Forall_forall in acm ;
rename_last inps0 ;  eapply in_map in inps0 ;
eapply in_map in inps0 ;
eapply acm in inps0 ;
clear acm ;
rewrite -> ?can_gen_weakL_def' in inps0 ;
rewrite -> ?can_gen_weakR_def' in inps0 ;
subst ;
destruct x0 ;
unfold seqext ;
unfold nsext ; unfold nslcext ;
eapply inps0 ;
  [> | unfold nsext ; unfold nslcext ; reflexivity |
    unfold seqext ; reflexivity ] ;
  weak_tacX.


Ltac nsprsameL_weak princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end ;
nsprsame_weak rs pr q qin inmps acm inps0 x0.

Ltac nsprsameR_weak princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end ;
nsprsame_weak rs pr q qin inmps acm inps0 x0.

(* ----------------------------- *)
(* LEFT WEAKENING FOR PRINCRULES *)
(* ----------------------------- *)

Lemma gen_weakL_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_L_oe princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
rewrite can_gen_weakL_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw_weak rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection H0 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oe in loe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameL_weak princrules rs pr q qin inmps acm inps0 x0.
}

{ list_eq_nc. contradiction. }

Qed.

Lemma gen_weakL_step_pr_lc: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule V)) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros. eapply gen_weakL_step_loe_lc.
  apply princrule_L_oe'. exact H. Qed.

Lemma gen_weakL_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_weakL (nslcrule (seqrule (@princrule V))) ns.

Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_weakL_step_pr_lc.
unfold gen_weakL_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

(* ------------------------------ *)
(* RIGHT WEAKENING FOR PRINCRULES *)
(* ------------------------------ *)

Lemma gen_weakR_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  rules_R_oe princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2 in pp.

destruct c.
sE ; subst.

{ nsgen_sw_weak rs sppc (l, l0, d) (Γ, Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection H0 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oe in loe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD' ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameR_weak princrules rs pr q qin inmps acm inps0 x0.
}

{ list_eq_nc. contradiction. }

Qed.

Lemma gen_weakR_step_pr_lc: forall V ps concl 
  (last_rule rules : rls (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule V)) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros. eapply gen_weakR_step_loe_lc.
        apply princrule_R_oe'. exact H. Qed.

Lemma gen_weakR_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_weakR (nslcrule (seqrule (@princrule V))) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H. 
subst.
pose gen_weakR_step_pr_lc.
unfold gen_weakR_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

(* ---------------------- *)
(* WEAKENING FOR B2RRULES *)
(* ---------------------- *)

Ltac ms_cgs_weak acm := 
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_weakL_def' in acm ;
rewrite -> ?can_gen_weakR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac use_acm1_weak acm rs ith :=
derIrs rs; [> 
apply NSlctxt2 || apply NSlclctxt' ;
assoc_single_mid ;
apply ith | 
ms_cgs acm ;
  list_assoc_r' ; simpl];
(* unfold can_gen_weakR in acm. *)
   (*   assoc_mid B; *)

   first [eapply acm | list_assoc_l'; rewrite <- app_assoc; eapply acm];
   unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl; reflexivity.


Ltac use_acm_os_weak acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith |
ms_cgs_weak acm ;
eapply acm in swap ] ;
[> eapply swap |
  unfold nslext ; unfold nslclext ; reflexivity |
  reflexivity ].

Lemma gen_weakL_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
   + use_acm_os_weak acm rs weak WBox2Rs.
   + use_acm_os_weak acm rs weak BBox2Rs. }
(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_weak rs sppc c (Γ', Δ, d) acm inps0 weak. }
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
    * use_acm_os_weak acm rs weak WBox2Rs.
    }
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
    * use_acm_os_weak acm rs weak BBox2Rs.
    }
  }
Qed.

Lemma gen_weakR_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak; subst;
   acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)

   use_acm1_weak acm rs WBox2Rs. }
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs BBox2Rs. }
  }
-{ nsgen_sw_weak rs sppc c (Γ, Δ', d) acm inps0 weak. }
-{ inversion sppc ; subst ; clear sppc.  (* 2 subgoals *)
(* WBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1_weak acm rs WBox2Rs. }
}
(* BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1_weak acm rs BBox2Rs. }
} }
Qed.

(* ---------------------- *)
(* WEAKENING FOR B1LRULES *)
(* ---------------------- *)

Ltac use_acm2s_weak acm rs ith rw:=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
apply ith |
ms_cgs_weak acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22 ; eapply acm ] ; [> | 
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; weak_tacX.

Ltac use_acm_sw_sep_weak acm rs weak ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs_weak acm ;
eapply acm in weak ] ;
[> (rewrite - list_rearr21 ; eapply weak) || 
  (list_assoc_r' ; simpl ; eapply weak) |
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ].

Lemma gen_weakL_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* swap in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs WBox1Ls. }
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs BBox1Ls. }
  }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_weak rs sppc c (Γ', Δ, d) acm inps0 weak. }

(* here, weak in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs WBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s_weak acm rs WBox1Ls ltac: (do 2 rewrite app_assoc). }

  use_acm2s_weak acm rs WBox1Ls ltac: (assoc_mid H). }
(* { use_acm2s_weak acm rs WBox1Ls ltac: (assoc_mid H). } } *)
}

(* BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weak acm rs BBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst.
acacD' ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s_weak acm rs BBox1Ls ltac: (do 2 rewrite app_assoc). }
{ use_acm2s_weak acm rs BBox1Ls ltac: (assoc_mid H). } }
}
}
Qed.

Lemma gen_weakR_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; [> 
  use_acm_sw_sep_weak acm rs weak WBox1Ls |
  use_acm_sw_sep_weak acm rs weak BBox1Ls ]. }
-{ nsgen_sw_weak rs sppc c (Γ, Δ', d) acm inps0 weak. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_weak acm rs weak WBox1Ls. }
*{ use_acm_sw_sep_weak acm rs weak WBox1Ls. }
}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_weak acm rs weak BBox1Ls. }
*{ use_acm_sw_sep_weak acm rs weak BBox1Ls. }
}
}  

Qed.

(* ---------------------- *)
(* WEAKENING FOR B2LRULES *)
(* ---------------------- *)

Lemma gen_weakL_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. (* no clear drs. *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* weak in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2s_weak acm rs WBox2Ls ltac: (do 2 rewrite app_assoc). 
  * use_acm2s_weak acm rs WBox2Ls ltac: (assoc_mid H). 
  }
+{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2s_weak acm rs BBox2Ls ltac: (do 2 rewrite app_assoc). 
  * use_acm2s_weak acm rs BBox2Ls ltac: (assoc_mid H).
  } }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_weak rs sppc c (Γ', Δ, d) acm inps0 weak. }

(* here, swap in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2s_weak acm rs WBox2Ls ltac: (do 2 rewrite app_assoc). 
  ** use_acm2s_weak acm rs WBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst. 
acacD' ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs WBox2Ls. }
}

(* BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2s_weak acm rs BBox2Ls ltac: (do 2 rewrite app_assoc). 
  ** use_acm2s_weak acm rs BBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst. 
acacD' ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs BBox2Ls. }
}
}
Qed.

Lemma gen_weakR_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros lreq nsr drs acm rs. (* no clear drs! *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; 
  [> use_acm_sw_sep_weak acm rs weak WBox2Ls |
     use_acm_sw_sep_weak acm rs weak BBox2Ls ]. }
-{ nsgen_sw_weak rs sppc c (Γ, Δ', d) acm inps0 weak. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_weak acm rs weak WBox2Ls. }
*{ use_drs rs drs WBox2Ls. }
}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_weak acm rs weak BBox2Ls. }
*{ use_drs rs drs BBox2Ls. }
}
}  
Qed.


(* ---------------------- *)
(* WEAKENING FOR B1RRULES *)
(* ---------------------- *)

Lemma cons_singleton : forall {A : Type} (l : list A) a,
    a :: l = [a] ++ l.
Proof. induction l; intros b; firstorder. Qed.

Ltac list_cons_singleton a := repeat rewrite (cons_singleton _ a).
Ltac tac_cons_singleton_arg a l :=
    match l with
    | nil => idtac
    | _ => rewrite (cons_singleton l a)
    end.

Ltac tac_cons_singleton :=
  repeat
  match goal with
   | [ |- context [?a :: ?l]] => progress (tac_cons_singleton_arg a l)
  end.

Ltac acmi_snr_sw_weak acmi := eapply acmi ;
  [>  apply nslclext_def|] ;  [>swap_tac; reflexivity].

Ltac use_acm_2_sw_weak_exch acm rs swap rw ith Hexch A B :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split; [>
        try tac_cons_singleton; eapply Hexch; auto | ];
     assoc_mid B; [>  acmi_snr_sw_weak acm1 | acmi_snr_sw_weak acm2]].

Ltac use_acm_2_sw_weak acm rs swap rw ith B :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split; assoc_mid B; [>  acmi_snr_sw_weak acm1 | acmi_snr_sw_weak acm2]].

Lemma can_gen_weakL_imp: forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_weakL rules ns -> forall G K seq Γ Δ Γ' (d : dir), 
  weakened Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros until 0. intro.
  rewrite -> can_gen_weakL_def' in H. exact H. Qed.

Lemma can_gen_weakR_imp: forall {V : Set} 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns,
  can_gen_weakR rules ns -> forall G K seq Γ Δ Δ' (d : dir), 
  weakened Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K).
Proof.  intros until 0. intro.
  rewrite -> can_gen_weakR_def' in H. exact H. Qed.

Ltac weakL2 rs sppc acm swap :=
derIrs rs ; [> list_assoc_l' ;
    apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
rewrite dersrec_forall ; intros L H ;
rewrite -> in_map_iff in H ; destruct H ; destruct H as [H1 H2] ; subst ;
rewrite -> Forall_forall in acm ; eapply in_map in H2 ; eapply acm in H2 ;
eapply can_gen_weakL_imp in H2 || eapply can_gen_weakR_imp in H2 ;
  [> | exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact H2
    | unfold nslclext ; list_assoc_r' ; reflexivity].

Ltac acmi_snr_sw''_weak acmi swap rw3 rw4 := rw3 ; eapply acmi ;
  [> rw4 ;  apply nslclext_def | swap_tac; reflexivity ].

Ltac use_acm_2_sw''_weak acm rs swap rw1 rw2 rw3 rw4 ith :=
derIrs rs ; [> rw1 ;
apply NSlclctxt' || apply NSlctxt2 ;
rw2 ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_sw''_weak acm1 swap rw3 rw4 | 
        acmi_snr_sw''_weak acm2 swap rw3 rw4 ]
            ].

Ltac acmi_snr_weak acmi swap := 
  eapply acmi ; [> apply nslclext_def | reflexivity ].

Ltac use_acm_2_weak acm rs swap ith :=
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; inversion swap; subst;
[> acmi_snr_weak acm1 swap | acmi_snr_weak acm2 swap ]
].     

Ltac acmi_snr_snd_weak acmi swap := rewrite list_rearr16' ; eapply acmi ;
  [>  list_assoc_r' ; simpl ; apply nslclext_def |
    reflexivity ].

Ltac use_acm_2_snd_weak acm rs swap ith :=
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; inversion swap; subst;
[> acmi_snr_snd_weak acm1 swap | acmi_snr_snd_weak acm2 swap ]
            ].

Lemma gen_weakL_step_b1R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1rrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
   + use_acm_2_weak acm rs swap WBox1Rs.

+ use_acm_2_weak acm rs swap BBox1Rs. }

(* case of exchange in sequent to the left of where rule applied,
  no need to expand sppc *) 
- weakL2 rs sppc acm swap.

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
* use_acm_2_weak acm rs swap WBox1Rs.
(* swapping in antecedent of second sequent in rule skeleton *)
* use_acm_2_snd_weak acm rs swap WBox1Rs.

}
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
* use_acm_2_weak acm rs swap BBox1Rs.
(* swapping in antecedent of second sequent in rule skeleton *)
* use_acm_2_snd_weak acm rs swap BBox1Rs.
} }
  
Qed.

Lemma gen_weakR_step_b1R_lc: forall V ps concl last_rule rules,
(forall (V : Set) ns
  (D : derrec rules (fun _ => False) ns),
      can_gen_swapR rules ns) ->
  last_rule = nslclrule (@b1rrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0. intros Hexch. unfold gen_weakR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
rewrite can_gen_weakR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD' ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals, WBox and BBox *)
+{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
   * use_acm_2_sw_weak_exch acm rs swap ltac : (assoc_mid H) WBox1Rs Hexch A B.
   * use_acm_2_sw_weak acm rs swap ltac : (assoc_mid H) WBox1Rs B.
}
+{ inversion_clear swap. subst.
   acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
   * use_acm_2_sw_weak_exch acm rs swap ltac : (assoc_mid H) BBox1Rs Hexch A B.
   * use_acm_2_sw_weak acm rs swap ltac : (assoc_mid H) BBox1Rs B.
} 
}
(* case of exchange in sequent to the left of where rule applied,
  no need to expand sppc *) 
- weakL2 rs sppc acm swap. 

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals, WBox and BBox *)
+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swap in first sequent in rule skeleton *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
** use_acm_2_sw_weak_exch acm rs swap ltac: (assoc_mid H) WBox1Rs Hexch A B.
** use_acm_2_sw_weak acm rs swap ltac: (assoc_mid H) WBox1Rs B.
}
(* swap in second sequent in rule skeleton *)
*{ inversion_clear swap. subst.
   acacD' ; subst ; simpl ; rewrite ?app_nil_r . (* 10 subgoals *)
  use_acm_2_sw''_weak acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
    ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs. 
  use_acm_2_sw''_weak acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
    ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs. 
  use_acm_2_sw''_weak acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
                                                                ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs.
}
 }

+{ acacDe ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swap in first sequent in rule skeleton *)
*{ inversion_clear swap. subst.
   acacD' ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
** use_acm_2_sw_weak_exch acm rs swap ltac: (assoc_mid H) BBox1Rs Hexch A B.
** use_acm_2_sw_weak acm rs swap ltac: (assoc_mid H) BBox1Rs B.
}
(* swap in second sequent in rule skeleton *)
*{ inversion_clear swap. subst.
  acacD' ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm_2_sw''_weak acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
    ltac: (rewrite list_rearr16'; assoc_mid B) ltac: (rewrite - list_rearr16') BBox1Rs. }
}
}
Qed.



(*
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply WBox1Rs |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split; inversion swap; subst];
[> eapply acm1; [> apply nslclext_def | reflexivity] |
eapply acm2; [> apply nslclext_def | reflexivity]].
acmi_snr acm1 swap.
[> acmi_snr acm1 swap | acmi_snr acm2 swap ]
].     


  
acmi_snr_weak acm1 swap.
acmi_snr_weak acm2 swap.
eapply acm1.
apply nslclext_def.
acmi_snr acm1 swap.

unfold can_gen_weakL in acm1.

  eapply acm1. ; [> exact swap | apply nslclext_def | reflexivity ].


acmi_snr acm1 swap.

; [> acmi_snr acm1 swap | acmi_snr acm2 swap ]
].

Ltac acmi_snr acmi swap := 
  eapply acmi ; [> exact swap | apply nslclext_def | reflexivity ].

 
Ltac use_acm_2 acm rs swap ith :=
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr acm1 swap | acmi_snr acm2 swap ]
].     

(*     eapply Forall_forall in acm. 
     eapply can_gen_weakL_imp.
     2:exact swap.
     2-3: reflexivity.
     unfold can_gen_weakL.
     intros G K seq d0 Γ1 Γ2 Γ3 Δ HH1 HH2.
     subst.
     exact acm. exact swap.
     apply nslclext_def. 

     eapply can_gen_weakL_imp.
     eapply Forall_forall in acm.
     exact acm.
     2 : exact swap.
     2-3 : reflexivity.
     simpl. right.
     SearchAbout Forall.
SearchAbout  can_gen_swapL swapped. *)
     use_acm_2 acm rs swap WBox1Rs. *)

(*
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply WBox1Rs |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split].
inversion swap; subst.

rewrite list_rearr16'; eapply acm1.

acmi_snr_snd acm1 swap.
rewrite list_rearr16'.
unfold can_gen_weakL in acm1.

; eapply acm1 ;
  [> exact swap | 
    list_assoc_r' ; simpl ; apply nslclext_def |
    reflexivity ].
acmi_snr_snd acm1 swap.
; [> acmi_snr_snd acm1 swap | acmi_snr_snd acm2 swap ]
].




  use_acm_2_snd acm rs swap WBox1Rs.
*)