Require Import ssreflect.

Require Import genT gen.
Require Import ddT.
Require Import List_lemmasT.
Require Import lntT lntacsT lntlsT lntbRT lntmtacsT.
Require Import lntb1LT lntb2LT.
Require Import lntkt_exchT.


Inductive weakened {T} : list T -> list T -> Type :=
  | weakened_I : forall (X Y A B C : list T), X = (A ++ C) -> 
    Y = (A ++ B ++ C) -> weakened X Y.

Lemma weakened_I': forall T (A B C D : list T),
   weakened (A ++ C) (A ++ B ++ C).
Proof.  intros.  eapply weakened_I ; reflexivity. Qed.

(* -------------------------- *)
(* LEFT WEAKENING DEFINITIONS *)
(* -------------------------- *)

Definition can_gen_weakL {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 Δ,
  ns = G ++ (seq, d) :: K -> seq = pair (Γ1 ++ Γ3) Δ ->
  derrec rules (fun _ => False) 
         (G ++ (pair (Γ1 ++ Γ2 ++ Γ3) Δ, d) :: K).

Definition gen_weakL_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_weakL rules) ps -> rsub last_rule rules -> 
  can_gen_weakL rules concl.

Lemma can_gen_weakL_def': forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  iffT (can_gen_weakL rules ns) (forall G K seq Γ Δ Γ' (d : dir), 
  weakened Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K)).
Proof.  intros.  unfold iffT.  split ; intros. 
  destruct H. subst. unfold can_gen_weakL in X.
  eapply X. reflexivity.  reflexivity.
  unfold can_gen_weakL. intros. eapply X.
  2: exact H.  2: exact H0. apply weakened_I'. auto. Qed.

(* --------------------------- *)
(* RIGHT WEAKENING DEFINITIONS *)
(* --------------------------- *)

Definition can_gen_weakR {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ Δ1 Δ2 Δ3,
    ns = G ++ (seq, d) :: K -> seq = pair Γ (Δ1 ++ Δ3)->
  derrec rules (fun _ => False) 
         (G ++ (pair Γ (Δ1 ++ Δ2 ++ Δ3), d) :: K).

Definition gen_weakR_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_weakR rules) ps -> rsub last_rule rules -> 
  can_gen_weakR rules concl.

Lemma can_gen_weakR_def': forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
    iffT (can_gen_weakR rules ns)
         (forall G K seq Γ Δ Δ' (d : dir), 
  weakened Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K)).
Proof.  intros.  unfold iffT.  split ; intros. 
  destruct H. subst. unfold can_gen_weakR in X.
  eapply X. reflexivity.  reflexivity.
  unfold can_gen_weakR. intros. eapply X.
  2: exact H.  2: exact H0. apply weakened_I'. auto. Qed.

(* -------------------------- *)
(* WEAKENING LEMMAS & TACTICS *)
(* -------------------------- *)

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
Proof.  intros. destruct X0. subst. 
  rewrite !(app_assoc Z). apply weakened_I'. auto. Qed.

Lemma weak_R: forall T X Y Z,
  weakened X (Y : list T) -> weakened (X ++ Z) (Y ++ Z).
Proof.
  intros. destruct X0. subst. rewrite <- !app_assoc.
  apply weakened_I'. auto.
Qed.

Lemma weak_cons: forall T (x : T) Y Z,
  weakened Y Z -> weakened (x :: Y) (x :: Z).
Proof.  intros. destruct X. subst. list_assoc_l. rewrite <- !app_assoc.
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

Ltac ms_cgs_weak acm := 
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_weakL_def' in acm ;
rewrite -> ?can_gen_weakR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac ms_cgs_weakT acm := 
eapply dersrec_map_single ;
eapply ForallT_map in acm ;
try eapply can_gen_weakL_def' in acm ;
try eapply can_gen_weakR_def' in acm ;
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
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  can_gen_weakL rules ns -> forall G K seq Γ Δ Γ' (d : dir), 
  weakened Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros until 0. intro.
  eapply can_gen_weakL_def'. exact X. Qed.

Lemma can_gen_weakR_imp: forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  can_gen_weakR rules ns -> forall G K seq Γ Δ Δ' (d : dir), 
  weakened Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K).
Proof.  intros until 0. intro.
  apply can_gen_weakR_def'. exact X. Qed.

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

Ltac egx_app g exch := eapply g; [> intros; apply exch; assumption |
                                  reflexivity | eassumption | assumption | assumption | ].


(* ----------------------------- *)
(* LEFT WEAKENING FOR PRINCRULES *)
(* ----------------------------- *)

Ltac nsgen_sw_weakT rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ; subst q ;
rename_last inps0 ; 
eapply ForallT_forall in acm ;
eapply InT_map in inps0 ;
[ | eapply inps0];
try eapply can_gen_weakL_def' in acm ;
  try eapply can_gen_weakR_def' in acm ;
[>unfold nslclext; unfold nslcext; assoc_single_mid' c'; eapply acm |
 exact swap | unfold nslcext; list_eq_assoc | (assumption || reflexivity) ]].

Ltac nsprsame_weakT rs pr q qin inmps acm inps0 x0 := 
derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
  apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ;
rename_last inmps ;
eapply InT_map_iffT in inmps ; cD ;
rename_last inps0 ; destruct inmps ; subst ;
  eapply ForallT_forall in acm ;
[ | eapply InT_map; eapply InT_map; eapply inps0];
try eapply can_gen_weakL_def' in acm ;
try eapply can_gen_weakR_def' in acm ;
[> eapply  acm | |
 unfold nsext ; unfold nslcext ; reflexivity |
    unfold seqext ; reflexivity ] ;
  weak_tacX.

Ltac nsprsameL_weakT princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end ;
nsprsame_weakT rs pr q qin inmps acm inps0 x0.

Ltac nsprsameR_weakT princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end ;
nsprsame_weakT rs pr q qin inmps acm inps0 x0.

Lemma gen_weakL_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  rules_L_oeT princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
apply can_gen_weakL_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2T in pp.

destruct c.
sD ; subst.

{  nsgen_sw_weakT rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection pp1 as. inversion ss. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oeT in loe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD'T2 ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameL_weakT princrules rs pr q qin inmps acm inps0 x0.
}

{ list_eq_nc. contradiction. }
Unshelve. all : solve_unshelved.
Qed.

(* Old pr rules. *)
Lemma gen_weakL_step_pr_lc_old: forall V ps concl 
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule V)) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros. eapply gen_weakL_step_loe_lc.
  apply princrule_L_oe'T. exact H. Qed.

Lemma gen_weakL_lc_old: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_weakL (nslcrule (seqrule (@princrule V))) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros. inversion X. 
subst.
pose gen_weakL_step_pr_lc_old.
unfold gen_weakL_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

(* New pr rules. *)
Lemma gen_weakL_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros. eapply gen_weakL_step_loe_lc.
  apply princrule_pfc_L_oe'T. exact H. Qed.

Lemma gen_weakL_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule_pfc V))) (fun _ => False) ns),
  can_gen_weakL (nslcrule (seqrule (@princrule_pfc V))) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros. inversion X. 
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
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  rules_R_oeT princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros loe lreq nsr drs acm rs. subst. clear drs.

inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
unfold nslcext in nsc.
eapply can_gen_weakR_def'.  intros until 0. intros swap pp ss.
unfold nslcext in pp.

apply partition_2_2T in pp.

destruct c.
sD ; subst.

{ nsgen_sw_weakT rs sppc (l, l0, d) (Γ, Δ, d0) acm inps0 swap. }

(* now case where move and rule application occur in the same sequent *)
{
injection pp1 as. subst.
inversion sppc as [? ? ? ? ? ? pr mse se].
destruct c.
unfold seqext in se.
subst.  clear sppc.
injection se as sel ser.
subst.

unfold rules_L_oeT in loe.
inversion_clear swap ; subst.

(* do as much as possible for all rules at once *)
acacD'T2 ; (* gives 10 subgoals *)
subst ;
repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
  sD ; subst ; simpl ; simpl in pr ;
  try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
(* above produces 20 subgoals, following solves all of them!! *)
nsprsameR_weakT princrules rs pr q qin inmps acm inps0 x0.
}

{ list_eq_nc. contradiction. }
Unshelve. all : solve_unshelved.
Qed.

(* Old pr rules. *)
Lemma gen_weakR_step_pr_lc_old: forall V ps concl 
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule V)) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros. eapply gen_weakR_step_loe_lc.
        apply princrule_R_oe'T. exact H. Qed.

Lemma gen_weakR_lc_old: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_gen_weakR (nslcrule (seqrule (@princrule V))) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros. inversion X. 
subst.
pose gen_weakR_step_pr_lc_old.
unfold gen_weakR_step in g.
eapply g. reflexivity. eassumption. assumption. assumption.
unfold rsub. clear g. 
intros.  assumption.
Qed.

(* New pr rules. *)
Lemma gen_weakR_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))),
  last_rule = nslcrule (seqrule (@princrule_pfc V)) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros. eapply gen_weakR_step_loe_lc.
        apply princrule_pfc_R_oe'T. exact H. Qed.

Lemma gen_weakR_lc: forall {V : Set} ns
  (D : derrec (nslcrule (seqrule (@princrule_pfc V))) (fun _ => False) ns),
  can_gen_weakR (nslcrule (seqrule (@princrule_pfc V))) ns.
Proof. 
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros. inversion X. 
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

Ltac use_acm_os_weakT acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith |
             ms_cgsTT1 acm ];
try eapply can_gen_weakL_def' in acm;
try eapply can_gen_weakR_def' in acm;
[exact acm | exact swap | reflexivity | reflexivity].

Lemma gen_weakL_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
eapply can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
   +     use_acm_os_weakT acm rs weak WBox2Rs.
   +     use_acm_os_weakT acm rs weak BBox2Rs. }
   
(* case of exchange in sequent to the left of where rule applied *)
-{  nsgen_sw_weakT rs sppc c (Γ', Δ, d) acm inps0 weak. }
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
     *  use_acm_os_weakT acm rs weak WBox2Rs.
    }
  +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
    * use_acm_os_weakT acm rs weak BBox2Rs.
    }
  }
Unshelve. all : solve_unshelved.
Qed.

Ltac use_acm1_weakT acm rs ith :=
derIrs rs; [> 
apply NSlctxt2 || apply NSlclctxt' ;
assoc_single_mid ;
apply ith | 
ms_cgsTT1 acm ;
  list_assoc_r' ; simpl];
(* unfold can_gen_weakR in acm. *)
   (*   assoc_mid B; *)

   first [eapply acm | list_assoc_l'; rewrite <- app_assoc; eapply acm];
   unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl; reflexivity.


Lemma gen_weakR_step_b2R_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2rrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
eapply can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak; subst;
   acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)

   use_acm1_weakT acm rs WBox2Rs. }
+{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weakT acm rs BBox2Rs. }
  }
-{ nsgen_sw_weakT rs sppc c (Γ, Δ', d) acm inps0 weak. }
-{ inversion sppc ; subst ; clear sppc.  (* 2 subgoals *)
(* WBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
*{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1_weakT acm rs WBox2Rs. }
}
(* BBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 1 subgoals *)
*{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
    use_acm1_weakT acm rs BBox2Rs. }
} }
Unshelve. all : solve_unshelved.
Qed.


(* ---------------------- *)
(* WEAKENING FOR B1LRULES *)
(* ---------------------- *)

(*
Ltac use_acm2s_weakT acm rs ith rw:=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
apply ith |
ms_cgsTT1 acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22 ; eapply acm ] ; [> 
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; weak_tacX.
*)

Ltac use_acm2s_weakT2 acm rs ith rw:=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
apply ith |
ms_cgsTT1 acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22 ;
try eapply can_gen_weakL_def' in acm;
try eapply can_gen_weakR_def' in acm ] ; [> eapply acm | |
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; weak_tacX.

Lemma gen_weakL_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
eapply  can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* swap in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weakT acm rs WBox1Ls. }
+{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weakT acm rs BBox1Ls. }
  }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_weakT rs sppc c (Γ', Δ, d) acm inps0 weak. }

(* here, weak in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weakT acm rs WBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst.
acacD'T2 ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)



{ use_acm2s_weakT2 acm rs WBox1Ls ltac: (do 2 rewrite app_assoc). }
{ use_acm2s_weakT2 acm rs WBox1Ls ltac: (assoc_mid H). }
(* { use_acm2s_weak acm rs WBox1Ls ltac: (assoc_mid H). } } *)
  }
  }

(* BBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm1_weakT acm rs BBox1Ls. }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst.
acacD'T2 ; subst.
(* 4 subgoals, cases of where swapping occurs in the two parts
  of context in conclusion (where no principal formula) *)
{ use_acm2s_weakT2 acm rs BBox1Ls ltac: (do 2 rewrite app_assoc). }
{ use_acm2s_weakT2 acm rs BBox1Ls ltac: (assoc_mid H). } }
}
}
Unshelve. all : solve_unshelved.
Qed.

Ltac use_acm_sw_sep_weakT acm rs weak ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
             apply ith |
             ms_cgsTT1 acm ;
try eapply can_gen_weakR_def' in acm;
try eapply can_gen_weakL_def' in acm ];
[eapply acm | exact weak | reflexivity | reflexivity].

Lemma gen_weakR_step_b1L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b1lrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros lreq nsr drs acm rs. clear drs. subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
eapply can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)
        -{ inversion sppc ; subst ;
           [> 
  use_acm_sw_sep_weakT acm rs weak WBox1Ls |
  use_acm_sw_sep_weakT acm rs weak BBox1Ls ]. }
-{ nsgen_sw_weakT rs sppc c (Γ, Δ', d) acm inps0 weak. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_weakT acm rs weak WBox1Ls. }
*{ use_acm2s_weakT2 acm rs WBox1Ls idtac; assumption. }
}
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_weakT acm rs weak BBox1Ls. }
*{ use_acm2s_weakT2 acm rs BBox1Ls idtac; assumption. }
}
}  
Unshelve. all : solve_unshelved.
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
eapply can_gen_weakL_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

(* weak in the first of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2s_weakT2 acm rs WBox2Ls ltac: (do 2 rewrite app_assoc). 
  * use_acm2s_weakT2 acm rs WBox2Ls ltac: (assoc_mid H). 
  }
+{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  * use_acm2s_weakT2 acm rs BBox2Ls ltac: (do 2 rewrite app_assoc). 
  * use_acm2s_weakT2 acm rs BBox2Ls ltac: (assoc_mid H).
  } }

(* case of exchange in sequent to the left of where rule applied *)
-{ nsgen_sw_weakT rs sppc c (Γ', Δ, d) acm inps0 weak. }

(* here, swap in either of the two sequents affected by the rule *)
-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)

(* WBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2s_weakT2 acm rs WBox2Ls ltac: (do 2 rewrite app_assoc). 
  ** use_acm2s_weakT2 acm rs WBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst. 
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs WBox2Ls. }
}

(* BBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ inversion_clear weak. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
  ** use_acm2s_weakT2 acm rs BBox2Ls ltac: (do 2 rewrite app_assoc). 
  ** use_acm2s_weakT2 acm rs BBox2Ls ltac: (assoc_mid H). 
  }
(* swapping in second sequent of principal rule *) 
*{
inversion_clear weak. subst. 
acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
(* 10 subgoals, cases of where swapping occurs in conclusion,
 but swap does not appear in premises *)
use_drs_mid rs drs BBox2Ls. }
}
}
 Unshelve. all : solve_unshelved.
Qed.

Lemma gen_weakR_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros lreq nsr drs acm rs. (* no clear drs! *) subst.

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
eapply can_gen_weakR_def'.  intros until 0. intros weak pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; 
  [> use_acm_sw_sep_weakT acm rs weak WBox2Ls |
     use_acm_sw_sep_weakT acm rs weak BBox2Ls ]. }
-{ nsgen_sw_weakT rs sppc c (Γ, Δ', d) acm inps0 weak. }

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_weakT acm rs weak WBox2Ls. }
*{ use_drs rs drs WBox2Ls. }
}
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
*{ use_acm_sw_sep_weakT acm rs weak BBox2Ls. }
*{ use_drs rs drs BBox2Ls. }
}
 }
 Unshelve. all : solve_unshelved.
Qed.


(* ---------------------- *)
(* WEAKENING FOR B1RRULES *)
(* ---------------------- *)

Ltac use_acm_2_weakT acm rs swap ith :=
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split ; inversion swap; subst;
[> acmi_snr_weak acm1 swap | acmi_snr_weak acm2 swap ]
].     

Ltac weakL2T rs sppc acm swap :=
derIrs rs ; [> list_assoc_l' ;
    apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
eapply dersrec_forall ; intros L H ;
eapply InT_map_iffT in H ;
destruct H as [H3 H]; destruct H as [H1 H2] ; subst ;
  eapply ForallT_forall in acm  ; [ | eapply InT_map in H2 ; eapply H2] ;
(eapply can_gen_weakL_imp in acm || eapply can_gen_weakR_imp in acm ) ;
 [> |  exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact acm
  | unfold nslclext ; list_assoc_r' ; reflexivity].

Ltac use_acm_2_snd_weakT acm rs swap ith :=
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
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
eapply can_gen_weakL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
   + use_acm_2_weakT acm rs swap WBox1Rs.
   + use_acm_2_weakT acm rs swap BBox1Rs. }

(* case of exchange in sequent to the left of where rule applied,
  no need to expand sppc *) 
- weakL2T rs sppc acm swap.

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals *)
  +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
* use_acm_2_weakT acm rs swap WBox1Rs.
(* swapping in antecedent of second sequent in rule skeleton *)
*  use_acm_2_snd_weakT acm rs swap WBox1Rs.

}
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swapping in antecedent of first sequent in rule skeleton *)
* use_acm_2_weakT acm rs swap BBox1Rs.
(* swapping in antecedent of second sequent in rule skeleton *)
* use_acm_2_snd_weakT acm rs swap BBox1Rs.
} }
  
Qed.

Ltac use_acm_2_sw_weak_exchT acm rs swap rw ith Hexch A B :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split; [>
        try tac_cons_singleton; eapply Hexch; auto | ];
     assoc_mid B; [>  acmi_snr_sw_weak acm1 | acmi_snr_sw_weak acm2]].

Ltac use_acm_2_sw_weakT acm rs swap rw ith B :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split; assoc_mid B; [>  acmi_snr_sw_weak acm1 | acmi_snr_sw_weak acm2]].

Ltac use_acm_2_sw''_weakT acm rs swap rw1 rw2 rw3 rw4 ith :=
derIrs rs ; [> rw1 ;
apply NSlclctxt' || apply NSlctxt2 ;
rw2 ; apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_sw''_weak acm1 swap rw3 rw4 | 
        acmi_snr_sw''_weak acm2 swap rw3 rw4 ]
            ].


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
eapply can_gen_weakR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. (* 3 subgoals, the various locs
  where the exchange might be relative to where the rule is active *)

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals, WBox and BBox *)
+{ inversion_clear swap. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
   * use_acm_2_sw_weak_exchT acm rs swap ltac : (assoc_mid H) WBox1Rs Hexch A B.
   * use_acm_2_sw_weakT acm rs swap ltac : (assoc_mid H) WBox1Rs B.
}
+{ inversion_clear swap. subst.
   acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
   * use_acm_2_sw_weak_exchT acm rs swap ltac : (assoc_mid H) BBox1Rs Hexch A B.
   * use_acm_2_sw_weakT acm rs swap ltac : (assoc_mid H) BBox1Rs B.
} 
}
(* case of exchange in sequent to the left of where rule applied,
  no need to expand sppc *) 
- weakL2T rs sppc acm swap. 

-{ inversion sppc ; subst ; clear sppc. (* 2 subgoals, WBox and BBox *)
+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swap in first sequent in rule skeleton *)
*{ inversion_clear swap. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
** use_acm_2_sw_weak_exchT acm rs swap ltac: (assoc_mid H) WBox1Rs Hexch A B.
** use_acm_2_sw_weakT acm rs swap ltac: (assoc_mid H) WBox1Rs B.
}
(* swap in second sequent in rule skeleton *)
*{ inversion_clear swap. subst.
   acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r . (* 10 subgoals *)
  use_acm_2_sw''_weakT acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
    ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs. 
  use_acm_2_sw''_weakT acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
    ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs. 
  use_acm_2_sw''_weakT acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
                                                                ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs.
}
 }

+{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. (* 2 subgoals *)
(* swap in first sequent in rule skeleton *)
*{ inversion_clear swap. subst.
   acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. (* 4 subgoals *)
** use_acm_2_sw_weak_exchT acm rs swap ltac: (assoc_mid H) BBox1Rs Hexch A B.
** use_acm_2_sw_weakT acm rs swap ltac: (assoc_mid H) BBox1Rs B.
}
(* swap in second sequent in rule skeleton *)
*{ inversion_clear swap. subst.
  acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; (* 10 subgoals *)
  use_acm_2_sw''_weakT acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
    ltac: (rewrite list_rearr16'; assoc_mid B) ltac: (rewrite - list_rearr16') BBox1Rs. }
}
}
Qed.


(* ---------------- *)
(* WEAKENING FOR EW *)
(* ---------------- *)

Lemma gen_weakR_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakR_step.
intros lreq nsr drs acm rs. subst. (* keep drs in this case *)

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
eapply can_gen_weakR_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 

- inversion sppc ; subst ; clear sppc.

+ derIrs rs.
* apply NSlclctxt.  apply EW.
* apply drs.

- weakL2T rs sppc acm swap.

- inversion sppc ; subst ; clear sppc.
acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
derIrs rs.
+ apply NSlclctxt.  apply EW.
+ apply drs.
Qed.

Lemma gen_weakL_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
intros lreq nsr drs acm rs. subst. (* keep drs in this case *)

inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
unfold nslclext in nsc.
eapply can_gen_weakL_def'.  intros until 0. intros swap pp ss.
unfold nslclext in pp. subst.

acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 

- inversion sppc ; subst ; clear sppc.

+ derIrs rs.
* apply NSlclctxt.  apply EW.
* apply drs.

- weakL2T rs sppc acm swap.

- inversion sppc ; subst ; clear sppc.
acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
derIrs rs.
+ apply NSlclctxt.  apply EW.
+ apply drs.
Qed.


(* --------------------------------------- *)
(* FULL LEFT AND RIGHT WEAKENING FOR LNSKT *)
(* --------------------------------------- *)

Lemma LNSKt_weakR: forall (V : Set) ns
  (D : derrec (@LNSKt_rules V) (fun _ => False) ns),
      can_gen_weakR (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros. inversion X ; subst ; [> pose gen_weakR_step_b2R_lc 
  | pose gen_weakR_step_b1R_lc; egx_app g LNSKt_exchR
  | pose gen_weakR_step_b2L_lc
  | pose gen_weakR_step_b1L_lc
  | pose gen_weakR_step_EW_lc
  | pose gen_weakR_step_pr_lc ] ; 
        unfold gen_weakR_step in g; try egx g;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.

Lemma LNSKt_weakL: forall (V : Set) ns
  (D : derrec (@LNSKt_rules V) (fun _ => False) ns),
      can_gen_weakL (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros. inversion X ; subst ; [> pose gen_weakL_step_b2R_lc 
  | pose gen_weakL_step_b1R_lc
  | pose gen_weakL_step_b2L_lc
  | pose gen_weakL_step_b1L_lc
  | pose gen_weakL_step_EW_lc
  | pose gen_weakL_step_pr_lc ] ; 
unfold gen_weakL_step in g ; egx g ;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.