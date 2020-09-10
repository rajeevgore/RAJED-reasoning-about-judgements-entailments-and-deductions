
(* tactics etc for lntom *)

Require Import ssreflect.

Add LoadPath "../general".

Require Import genT gen.
Require Import ddT.
Require Import List_lemmasT.
Require Import gen_seq gen_tacs lntT.
Require Import swappedT.

Ltac use_prX princrule_X pr := 
  pose pr as Qpr ;
  apply princrule_X in Qpr ;
  repeat (sD_list_eq ; subst ; simpl ; simpl in pr ;
  rewrite -> ?app_nil_r in * ; rewrite ?app_nil_r).

Ltac use_prL pr := use_prX princrule_L pr.
Ltac use_prR pr := use_prX princrule_R pr.

Ltac check_app_app :=
  match goal with
    | [ |- _ ++ _ = _ ++ _ ] => idtac
    end.

Lemma nsI: forall T (G H : list T) (x y : T),
  x = y -> G ++ x :: H = G ++ y :: H.
Proof. intros. subst. reflexivity. Qed.

Lemma all_eq_imp: forall (T : Type) (y : T) (z : T -> Prop),
(forall (x : T), y = x \/ False -> z x) <-> z y.
Proof. firstorder. subst.  assumption. Qed.

Definition can_gen_moveL {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 (Q : PropF V) Δ,
  ns = G ++ (seq, d) :: K -> seq = pair (Γ1 ++ Q :: Γ2 ++ Γ3) Δ ->
  derrec rules (fun _ => False) 
    (G ++ (pair (Γ1 ++ Γ2 ++ Q :: Γ3) Δ, d) :: K).

Definition can_gen_moveR {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Δ1 Δ2 Δ3 (Q : PropF V) Γ,
  ns = G ++ (seq, d) :: K -> seq = pair Γ (Δ1 ++ Q :: Δ2 ++ Δ3) ->
  derrec rules (fun _ => False) 
    (G ++ (pair Γ (Δ1 ++ Δ2 ++ Q :: Δ3), d) :: K).

Definition can_gen_swapL {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Γ1 Γ2 Γ3 Γ4 Δ,
  ns = G ++ (seq, d) :: K -> seq = pair (Γ1 ++ Γ2 ++ Γ3 ++ Γ4) Δ ->
  derrec rules (fun _ => False) 
    (G ++ (pair (Γ1 ++ Γ3 ++ Γ2 ++ Γ4) Δ, d) :: K).

Definition can_gen_swapR {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns :=
  forall G K seq (d : dir) Δ1 Δ2 Δ3 Δ4 Γ,
  ns = G ++ (seq, d) :: K -> seq = pair Γ (Δ1 ++ Δ2 ++ Δ3 ++ Δ4) ->
  derrec rules (fun _ => False) 
    (G ++ (pair Γ (Δ1 ++ Δ3 ++ Δ2 ++ Δ4), d) :: K).

(* alternative definition of can_gen_swapL(R) in terms of swapped *)
Lemma can_gen_swapL_def': forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
    iffT (can_gen_swapL rules ns)
         (forall G K seq Γ Δ Γ' (d : dir), 
  swapped Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K)).
Proof.  intros.  unfold iffT.  split ; intros. 
  destruct H. subst. unfold can_gen_swapL in X.
  eapply X. reflexivity.  reflexivity.
  unfold can_gen_swapL. intros. eapply X.
  2: exact H.  2: exact H0. apply swapped_I'. Qed.

Lemma can_gen_swapR_def': forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
    iffT (can_gen_swapR rules ns)
    (forall G K seq Γ Δ Δ' (d : dir), 
  swapped Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K)).
Proof.  intros.  unfold iffT.  split ; intros. 
  destruct H. subst. unfold can_gen_swapR in X.
  eapply X. reflexivity.  reflexivity.
  unfold can_gen_swapR. intros. eapply X.
  2: exact H.  2: exact H0. apply swapped_I'. Qed.

Lemma can_gen_swapL_imp: forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  can_gen_swapL rules ns -> forall G K seq Γ Δ Γ' (d : dir), 
  swapped Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K).
Proof.
  intros until 0. intro H; intros.
  edestruct (@can_gen_swapL_def' V) as [HH1 HH2].
  eapply HH1; eassumption.
Qed.

Lemma can_gen_swapR_imp: forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  can_gen_swapR rules ns -> forall G K seq Γ Δ Δ' (d : dir), 
  swapped Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
    derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K).
Proof.
  intros until 0. intro H; intros.
  edestruct (@can_gen_swapR_def' V) as [HH1 HH2].
  eapply HH1; eassumption.
Qed.

Lemma can_gen_swapL_imp_rev: forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  (forall G K seq Γ Δ Γ' (d : dir), 
  swapped Γ Γ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
  derrec rules (fun _ => False) (G ++ (pair Γ' Δ, d) :: K)) ->
  can_gen_swapL rules ns.
Proof.
  intros until 0. intro H; intros.
  edestruct (@can_gen_swapL_def' V) as [HH1 HH2].
  eapply HH2; eassumption.
Qed.

Lemma can_gen_swapR_imp_rev: forall {V : Set} 
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns,
  (forall G K seq Γ Δ Δ' (d : dir), 
  swapped Δ Δ' -> ns = G ++ (seq, d) :: K -> seq = pair Γ Δ ->
  derrec rules (fun _ => False) (G ++ (pair Γ Δ', d) :: K)) ->
  can_gen_swapR rules ns.
Proof.
  intros until 0. intro H; intros.
  edestruct (@can_gen_swapR_def' V) as [HH1 HH2].
  eapply HH2; eassumption.
Qed.

Lemma can_gen_moveL_mono: forall {V : Set}
  (rulesa rulesb : rlsT (list (rel (list (PropF V)) * dir))) ns,
  rsub rulesa rulesb ->
  can_gen_moveL rulesa ns -> can_gen_moveL rulesb ns.
Proof.
  intros until 0; intros Hr H.
  unfold can_gen_moveL. intros until 0; intros Hn1 Hn2.
  eapply derrec_rmono. exact Hr. eapply H; eassumption.
Qed.

Lemma can_gen_moveR_mono: forall {V : Set}
  (rulesa rulesb : rlsT (list (rel (list (PropF V)) * dir))) ns,
  rsub rulesa rulesb ->
  can_gen_moveR rulesa ns -> can_gen_moveR rulesb ns.
Proof.
  intros until 0; intros Hr H.
  unfold can_gen_moveR. intros until 0; intros Hn1 Hn2.
  eapply derrec_rmono. exact Hr. eapply H; eassumption.
Qed.

Lemma can_gen_swapL_mono: forall {V : Set}
  (rulesa rulesb : rlsT (list (rel (list (PropF V)) * dir))) ns,
  rsub rulesa rulesb ->
  can_gen_swapL rulesa ns -> can_gen_swapL rulesb ns.
Proof.
  intros until 0; intros Hr H.
  unfold can_gen_swapL. intros until 0; intros Hn1 Hn2.
  eapply derrec_rmono. exact Hr. eapply H; eassumption.
Qed.

Lemma can_gen_swapR_mono: forall {V : Set}
  (rulesa rulesb : rlsT (list (rel (list (PropF V)) * dir))) ns,
  rsub rulesa rulesb ->
  can_gen_swapR rulesa ns -> can_gen_swapR rulesb ns.
Proof.
  intros until 0; intros Hr H.
  unfold can_gen_swapR. intros until 0; intros Hn1 Hn2.
  eapply derrec_rmono. exact Hr. eapply H; eassumption.
Qed.

Definition gen_moveL_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_moveL rules) ps -> rsub last_rule rules -> 
  can_gen_moveL rules concl.

Definition gen_moveR_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_moveR rules) ps -> rsub last_rule rules -> 
  can_gen_moveR rules concl.

Definition gen_swapL_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_swapL rules) ps -> rsub last_rule rules -> 
  can_gen_swapL rules concl.

Definition gen_swapR_step {V : Set}
  (last_rule rules : rlsT (list (rel (list (PropF V)) * dir))) ps concl :=
  last_rule ps concl -> dersrec rules (fun _ => False) ps ->
  ForallT (can_gen_swapR rules) ps -> rsub last_rule rules -> 
  can_gen_swapR rules concl.

Ltac use_cgm cgmX H1 := 
  rewrite -> Forall_forall in H1 ;
  simpl in H1 ;
  specialize_full H1 ;
  [ | unfold cgmX in H1 ; unfold nsext ;
    rewrite <- app_assoc ;
    eapply H1 ; reflexivity ] ;
  unfold nsext ; tauto.

Ltac use_cgmL H1 := use_cgm can_gen_moveL H1.
Ltac use_cgmR H1 := use_cgm can_gen_moveR H1.

Ltac stage2 H1 qin1 qin3 := 
rewrite dersrec_forall ;
intros q qin ; rewrite -> in_map_iff in qin ; cD ;
rename_last qin1 ;
rewrite -> in_map_iff in qin1 ; cD ;
rename_last qin3 ;
destruct qin1 ; subst ;
rewrite -> Forall_forall in H1 ;
eapply in_map in qin3 ;
eapply in_map in qin3 ;
apply H1 in qin3 ;
unfold can_gen_moveL in qin3 ;
unfold nsext.

Ltac stage2alt H0 H1 qin1 qin3 := 
rewrite dersrec_forall ;
rewrite -> dersrec_forall in H0 ;
intros q qin ; rewrite -> in_map_iff in qin ; cD ;
rename_last qin1 ;
rewrite -> in_map_iff in qin1 ; cD ;
rename_last qin3 ;
destruct qin1 ; subst ;
rewrite -> Forall_forall in H1 ;
eapply in_map in qin3 ;
eapply in_map in qin3 ;
(* see if can solve goal without swapping premises *)
try (apply H0 in qin3 ; unfold seqext in qin3 ; exact qin3) ;
apply H1 in qin3 ;
unfold can_gen_moveL in qin3 ;
unfold nsext.

Ltac stage3 qin3 l l1 := 
eapply qin3 ; [ apply nsext_def |
rewrite seqext_def ; list_eq_assoc ].

Ltac stage2altds H0 H1 qin1 qin3 := 
  stage2alt H0 H1 qin1 qin3 ; (eapply derrec_same ; [
    eapply qin3 ; [ apply nsext_def | unfold seqext ] | ]).

Ltac stage2ds H1 qin1 qin3 := 
  stage2 H1 qin1 qin3 ; eapply derrec_same ; [
    eapply qin3 ; [ apply nsext_def | unfold seqext ] | ].

Ltac srs pr := eapply seqrule_same ; [ exact pr |
  apply pair_eqI ; try reflexivity ]. 

Ltac amt l0 := eapply eq_trans ; [> assoc_mid l0 .. ] ; [> reflexivity ..].
  
Ltac stage1 rs pr :=
subst ;
rewrite -> ?app_nil_r in * ;
eapply derI ; [
unfold rsub in rs ; apply rs ;
rewrite <- nsext_def ; apply NSctxt ;
eapply Sctxt in pr ;
unfold seqext in pr ;
simpl in pr | idtac ].

Ltac stage12altds rs H0 H1 qin1 qin3 pr l0 := 
  stage1 rs pr ; [ srs pr ; amt l0 | stage2altds H0 H1 qin1 qin3 ].

Ltac stage12ds rs H1 qin1 qin3 pr l0 := 
  stage1 rs pr ; [ srs pr ; amt l0 | stage2ds H1 qin1 qin3 ].

Ltac stage12altdsL rs H0 H1 qin1 qin3 pr := 
  match goal with
    | [ H : princrule _ (?x, _) |- _ ] =>
      stage12altds rs H0 H1 qin1 qin3 pr x end.

Ltac stage12altdsLg princrules rs H0 H1 qin1 qin3 pr := 
  match goal with
    | [ H : princrules _ (?x, _) |- _ ] =>
      stage12altds rs H0 H1 qin1 qin3 pr x end.

Ltac stage12altdsR rs H0 H1 qin1 qin3 pr := 
  match goal with
    | [ H : princrule _ (_, ?x) |- _ ] =>
      stage12altds rs H0 H1 qin1 qin3 pr x end.

Ltac stage12altdsRg princrules rs H0 H1 qin1 qin3 pr := 
  match goal with
    | [ H : princrules _ (_, ?x) |- _ ] =>
      stage12altds rs H0 H1 qin1 qin3 pr x end.

Ltac midLg princrules := 
  match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end.

Ltac midRg princrules := 
  match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end.

Ltac app_cancel := 
  (list_assoc_l' ; rewrite ?appr_cong ;
  list_assoc_r' ; rewrite ?appl_cong).

Ltac derIrs rs := eapply derI ; [> unfold rsub in rs ; apply rs ; clear rs | ].

Ltac solve_eqs := 
  prgt 33 ;
  repeat clear_one ;
  try (apply nsI) ;
  repeat (apply pair_eqI) ;
  try refl_ni ;
  assoc_single_mid ;
  try (apply midI) ;
  try (first [check_app_app | reflexivity]) ;
  repeat app_cancel ;
  try (first [check_app_app | reflexivity]) ;
  try refl_ni ;
  prgt 44.

(* tactic for when principal formula to be moved *)
Ltac mpv use_prL use_cgmL H1 H0 rs pr := 
  subst ; use_prL pr ; stage1 rs pr ; [ 
  rewrite !app_assoc ; rewrite !app_assoc in pr ; apply pr |
  destruct pr ; simpl ; repeat (apply dlNil || apply dlCons) ;
  try (use_cgmL H1) ;
  rewrite -> dersrec_forall in H0 ; apply H0 ; simpl ;
  rewrite <- app_assoc ;  tauto ].

(* tactic for admissibility proof in nested sequents,
  case where the rule is applied in a sequent to the right
  of where the move takes place *)

(* version of nsright suitable for case where 
  rs : rsub (nsrule ...) rules, and rest of goal involves rules *)
Ltac nsright pp G0 seqe d0 x Ge HeqGe K d ps ps0 inps0 pse K0 drs nsr acm
  G seq rs := 
clear drs nsr ;  clear pp ;  cE ;
(* case where the rule is applied in a sequent to the right
  of where the swap takes place *)
remember (G0 ++ (seqe, d0) :: x) as Ge ;
remember (map (nsext Ge K d) ps0) as pse ;
apply derI with pse ; [
  subst pse ; subst K0 ; rewrite list_rearr14 ;
  unfold rsub in rs ; apply rs ;
  (* it must be easier than this
    to rewrite using the inverse of the definition of nsext *)
  rewrite <- nsext_def ;  subst seqe ;  rewrite <- HeqGe ;
  apply NSctxt ; assumption |
  rewrite dersrec_forall ;
  intros q qin ;  subst pse ;  rewrite -> in_map_iff in qin ; cE ;
  subst q ;  subst ps ;
  rewrite -> Forall_forall in acm ;
  rename_last inps0 ;  eapply in_map in inps0 ; 
  apply acm in inps0 ;
  unfold can_gen_swapL in inps0 ;
  unfold nsext ; subst Ge ; subst seqe ;
  rewrite <- list_rearr14 ;
  eapply inps0 ; [> | reflexivity ] ;
  unfold nsext ; subst G ; subst seq ;
  list_eq_assoc ].

Ltac nsleft pp G0 seqe d0 x He HeqHe K d ps ps0 inps0 pse K0 drs nsr acm
  G seq rs := 
clear drs nsr ;  clear pp ;  cE ;
(* case where the rule is applied in a sequent to the left
  of where the swap takes place *)
remember (x ++ (seqe, d0) :: K0) as He ;
remember (map (nsext G He d) ps0) as pse ;
apply derI with pse ; [
  subst pse ; subst G0 ; rewrite <- list_rearr14 ;
  unfold rsub in rs ; apply rs ;
  (* it must be easier than this
    to rewrite using the inverse of the definition of nsext *)
  rewrite <- nsext_def ;  subst seqe ;  rewrite <- HeqHe ;
  apply NSctxt ; assumption |
  rewrite dersrec_forall ;
  intros q qin ;  subst pse ;  rewrite -> in_map_iff in qin ; cE ;
  subst q ;  subst ps ;
  rewrite -> Forall_forall in acm ;
  rename_last inps0 ;  eapply in_map in inps0 ; 
  apply acm in inps0 ;
  unfold can_gen_swapL in inps0 ;
  unfold nsext ; subst He ; subst seqe ;
  rewrite list_rearr14 ;
  eapply inps0 ; [> | reflexivity ] ;
  unfold nsext ; subst K ; subst seq ;
  list_eq_assoc ].

(* for using swap in the case when the rule affects a list of
  sequents or a single sequent, plus context (ie nslext or nsext), and
  the operation of the rule is distinct from the sequent where the swap is;
  note, where the context is on the left only,
  exchL2 rs sppc acm swap. generally seems to work also *)
Ltac nsgen_sw rs sppc c c' acm inps0 swap :=
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
rewrite -> ?can_gen_swapL_def' in inps0 ;
rewrite -> ?can_gen_swapR_def' in inps0 ;
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply inps0 ; [> exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | reflexivity ]].

Ltac nsgen_swT rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc | 
apply dersrec_forall ;
intros q qin ;
apply InT_map_iffT in qin ;
do 2 cET_nr ;
 subst ;
rename_last inps0 ;
eapply ForallT_forall in acm ;
eapply InT_map in inps0 ; 
[ | eexact inps0 ] ];
(eapply can_gen_swapL_def' in acm ||
eapply can_gen_swapR_def' in acm );
[unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply acm |
 exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | assumption]. 

Ltac nsgen_swTT rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
apply dersrec_forall ;
intros q qin ;
apply InT_map_iffT in qin ; cET ; subst q ;
rename_last inps0 ;
eapply ForallT_forall in acm ;
eapply InT_map in inps0 ;
[ | eexact inps0 ] ];
(eapply can_gen_swapL_def' in acm ||
eapply can_gen_swapR_def' in acm );
[unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply acm |
 exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | reflexivity ].

Ltac nsprsame rs pr q qin inmps acm inps0 x0 := 
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
rewrite -> ?can_gen_swapL_def' in inps0 ;
rewrite -> ?can_gen_swapR_def' in inps0 ;
subst ;
destruct x0 ;
unfold seqext ;
unfold nsext ; unfold nslcext ;
eapply inps0 ;
  [> | unfold nsext ; unfold nslcext ; reflexivity |
    unfold seqext ; reflexivity ] ;
  swap_tac.

Ltac nsprsameL princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end ;
nsprsame rs pr q qin inmps acm inps0 x0.

Ltac nsprsameR princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end ;
nsprsame rs pr q qin inmps acm inps0 x0.

Ltac nsprsameT rs pr q qin inmps acm inps0 x0 :=
  derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
  apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cET ;
rename_last inmps ;
eapply InT_map_iffT in inmps ; cET ; subst ;
  rename_last inps0 ;
  eapply ForallT_forall in acm ; [ | eapply InT_map; eapply InT_map; exact inps0];
    destruct x0;
try eapply can_gen_swapL_def' in acm ;
try eapply can_gen_swapR_def' in acm ;
[ eapply acm | |
unfold nsext ; unfold nslcext ; reflexivity |
 unfold seqext; reflexivity ]; swap_tac.

Ltac nsprsameLT princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end ;
nsprsameT rs pr q qin inmps acm inps0 x0.

Ltac nsprsameRT princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end ;
nsprsameT rs pr q qin inmps acm inps0 x0.

Definition can_gen_init {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns A :=
  forall G seq (d : dir) Γ1 Γ2 Δ1 Δ2,
  ns = G ++ [(seq, d)] -> seq = pair (Γ1 ++ [A] ++ Γ2) (Δ1 ++ [A] ++ Δ2) ->
  derrec rules (fun _ => False) ns.

 Ltac solve_unshelved :=
   (exact nat || (intros; exact 0)).

