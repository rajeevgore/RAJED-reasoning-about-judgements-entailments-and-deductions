Add LoadPath "../general".

Require Export List.
Set Implicit Arguments.
Export ListNotations.
Require Import gen.
Require Import dd.
Require Import List_lemmas.
Require Import lnt.

Inductive proprule (V : Set) : rls (rel (list (PropF V))) :=
  | Id : forall U Φ1 Φ2 Ψ1 Ψ2, 
    proprule [] (pair (Φ1 ++ U :: Φ2) (Ψ1 ++ U :: Ψ2))
  | ImpR : forall U W Φ Ψ1 Ψ2, 
    proprule [pair (U :: Φ) (Ψ1 ++ W :: Ψ2)] (pair Φ (Ψ1 ++ Imp U W :: Ψ2))
  | ImpL : forall U W Φ1 Φ2 Ψ, 
    proprule [pair (Φ1 ++ W :: Φ2) Ψ ; pair (Φ1 ++ Φ2) (U :: Ψ)]
      (pair (Φ1 ++ Imp U W :: Φ2) Ψ)
  | BotL : forall Φ1 Φ2 Ψ, proprule [] (pair (Φ1 ++ (Bot V) :: Φ2) Ψ)
.

Definition can_exchL (V : Set) 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ1 (A B : PropF V) Γ2 Δ, 
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ A :: B :: Γ2) Δ ->
  derrec rules (fun _ => False) (G ++ (pair (Γ1 ++ B :: A :: Γ2) Δ, d) :: H).

Lemma exchL: forall (V : Set) ns 
  (D : derrec (nsrule (@proprule V)) (fun _ => False) ns),
  can_exchL (nsrule (@proprule V)) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.  unfold nsext in H5.
unfold can_exchL.  intros. 
unfold nsext in H7.
(* cases of where the exchange occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ1 ++ B :: A :: Γ2, Δ) as seqe.

decompose [or] H7. clear H7.  cE.
(* case where the rule is applied in a sequent to the right
  of where the exchange takes place *)
remember (G0 ++ (seqe, d0) :: x) as Ge.
remember (map (nsext Ge H2 d) ps0) as pse.

apply derI with pse. subst pse. subst H6.
rewrite list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqGe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchL in c0.
unfold nsext. subst Ge. subst seqe.
rewrite <- list_rearr14.
eapply c0. 2:reflexivity.
unfold nsext. subst G. subst seq.
rewrite list_rearr14.  reflexivity.

all : revgoals. clear H7. cE.
(* now the case where the rule is applied in a sequent to the left
  of where the exchange takes place *)
remember (x ++ (seqe, d0) :: H6) as He.
remember (map (nsext G He d) ps0) as pse.

apply derI with pse. subst pse. subst G0.
rewrite <- list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqHe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchL in c0.
unfold nsext. subst He. subst seqe.
rewrite list_rearr14.

eapply c0. 2:reflexivity.
unfold nsext. subst H2. subst seq.
apply list_rearr14.

(* now case where exchange and rule application occur in the same sequent *)
cE. clear H7. injection H10 as. 
inversion H3.  subst. rename_last eqll. 
(* case of Id rule *)
injection eqll as eql eqr. subst. 
apply derI with [].  2: apply dlNil.
rewrite <- nsext_def. apply NSctxt_nil.
acacD ; subst ;
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
  repeat (apply Id || rewrite list_rearr16 || rewrite list_rearr15).

all : revgoals.
(* case of BotL rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst. 
apply derI with [].  2: apply dlNil.
rewrite <- nsext_def. apply NSctxt_nil.
acacD ; subst ;
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
  repeat (apply BotL || rewrite list_rearr16 || rewrite list_rearr15).

all : revgoals. (* ImpL and ImpR rules remain *)
(* case of ImpR rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst. 
clear H H0 H3.
eapply derI.  rewrite <- nsext_def. apply NSctxt.  apply ImpR.
rewrite dersrec_all. rewrite Forall_forall. intros.
rewrite Forall_forall in H1. simpl in H1. simpl in H. sD.
subst.  unfold can_exchL in H1. unfold nsext. rewrite app_comm_cons.
eapply H1.
left. reflexivity.
apply nsext_def. 
rewrite app_comm_cons.  reflexivity.

(* now for the ImpL rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst.
clear H H3. (* not H0 in this case as will need non-exchanged premises *)
rewrite dersrec_all in H0.  rewrite Forall_forall in *.
unfold can_exchL in H1. simpl in *.  
(* rewrite <- nsext_def in H1. fails, why? *)
rewrite <- nsext_def.
pose (H0 _ (or_intror (or_introl eq_refl))) as H0re.
(* can't apply derI right away as premises will vary *)
acacD ; subst ; eapply derI ;
  try (apply NSctxt ;
    repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
    repeat (apply ImpL || rewrite list_rearr16 || rewrite list_rearr15)) ;
  rewrite dersrec_all ; rewrite Forall_forall ; intros p inps ;
  simpl in inps ; sD ; subst ; 
  rewrite ?app_nil_r in * ; 
  rewrite ?app_nil_r ; rewrite <- ?list_rearr16'.

(*
Check (or_introl (nsext_def _ _ _ _)).
Check (H0 _ (or_introl (nsext_def _ _ _ _))).
pose (H0 _ (or_introl (nsext_def _ _ _ _))) as H0l.
Check (or_intror (or_introl (nsext_def _ _ _ _))).
pose (H0 _ (or_intror (or_introl (nsext_def _ _ _ _)))) as H0r.
pose (H1 _ (or_intror (or_introl eq_refl))) as H1re.
pose (H1 _ (or_introl eq_refl)) as H1le.
pose (H1 _ (or_introl eq_refl)) as H1le.
Check (H1re _ _ _ _ _ _ _ _ _ eq_refl).
pose (H1le G H6) as H1lee.
Check (H1le G H6 _ d0 _ _ _ _ _ (nsext_def _ _ _ _)).
pose (H1le G H6 _ d0 _ _ _ _ _ (nsext_def _ _ _ _)).
(* pose (H1re _ _ _ _ _ _ _ _ _ eq_refl) as H1ree. fails *)
(* pose (H1le _ _ _ _ _ _ _ _ _ eq_refl) as H1lee. fails *)
*)

eapply H1. left. reflexivity. apply nsext_def.  reflexivity.

exact H0re.

eapply H1. left. reflexivity. apply nsext_def.
rewrite <- list_rearr16. reflexivity.

rewrite <- !list_rearr16 in H0re. exact H0re.

list_assoc_r.  eapply H1.  left. reflexivity. apply nsext_def.  list_eq_assoc.

list_assoc_r. 
eapply H1. right. left. reflexivity. apply nsext_def.
list_eq_assoc.

eapply H1.  left. reflexivity. apply nsext_def.  reflexivity.

exact H0re.

list_assoc_l.  eapply H1. left. reflexivity. apply nsext_def.  list_eq_assoc.

list_assoc_l. eapply H1. right. left. reflexivity. apply nsext_def.
list_eq_assoc.

Qed.

Ltac nsrule_rewrites :=  (match goal with
                          | [ |- nsrule ?a ?b ?c ] => apply NSctxt;
(match goal with
| [ |- proprule ?a (?Γ, ?Δ1 ++ ?B :: Imp ?U ?W :: ?Δ2)] =>
  rewrite list_rearr16_R
| [ |- proprule ?a (?Γ, ?Δ1 ++ ?B :: ?A :: ?eqr3 ++ Imp ?U ?W :: ?Ψ2)] =>
  rewrite list_rearr17_R
| [ |- proprule ?ps (?Γ, (?Ψ1 ++ Imp ?U ?W :: ?eqr1) ++ ?B :: ?A :: ?Δ2)] =>
  rewrite <- list_rearr15_R; simpl
| _ => trivial end); apply ImpR
| _ => trivial end).


Definition can_exchR (V : Set) 
  (rules : rls (list (rel (list (PropF V)) * dir))) ns :=
  forall G H seq (d : dir) Γ Δ1 (A B : PropF V) Δ2 ,
  ns = G ++ (seq, d) :: H -> seq = pair Γ (Δ1 ++ A :: B :: Δ2) ->
  derrec rules (fun _ => False) (G ++ (pair Γ (Δ1 ++ B :: A :: Δ2), d) :: H).

Lemma exchR: forall (V : Set) ns 
  (D : derrec (nsrule (@proprule V)) (fun _ => False) ns),
  can_exchR (nsrule (@proprule V)) ns.
Proof.
intros.
eapply derrec_all_ind in D.
exact D. tauto.
intros. inversion H.  unfold nsext in H5.
unfold can_exchR.  intros. 
unfold nsext in H7.
(* cases of where the exchange occurs vs where the last rule applied *)
apply partition_2_2 in H7.
remember (Γ, Δ1 ++ B :: A :: Δ2) as seqe.

decompose [or] H7. clear H7.  cE.
(* case where the rule is applied in a sequent to the right
  of where the exchange takes place *)
remember (G0 ++ (seqe, d0) :: x) as Ge.
remember (map (nsext Ge H2 d) ps0) as pse.

apply derI with pse. subst pse. subst H6.
rewrite list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqGe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchR in c0.
unfold nsext. subst Ge. subst seqe.
rewrite <- list_rearr14.
eapply c0. 2:reflexivity.
unfold nsext. subst G. subst seq.
rewrite list_rearr14.  reflexivity.

all : revgoals. clear H7. cE.
(* now the case where the rule is applied in a sequent to the left
  of where the exchange takes place *)
remember (x ++ (seqe, d0) :: H6) as He.
remember (map (nsext G He d) ps0) as pse.

apply derI with pse. subst pse. subst G0.
rewrite <- list_rearr14.
(* it must be easier than this
  to rewrite using the inverse of the definition of nsext *)
rewrite <- nsext_def.  subst seqe.  rewrite <- HeqHe.
apply NSctxt. assumption.

rewrite dersrec_all.  rewrite Forall_forall.
intros q qin.  subst pse.  rewrite in_map_iff in qin. cE.
subst q.  clear H0 H.  subst ps.
rewrite Forall_forall in H1.
rename_last inps0.  eapply in_map in inps0. pose (H1 _ inps0).
unfold can_exchR in c0.
unfold nsext. subst He. subst seqe.
rewrite list_rearr14.

eapply c0. 2:reflexivity.
unfold nsext. subst H2. subst seq.
apply list_rearr14.

(* now case where exchange and rule application occur in the same sequent *)
cE. clear H7. injection H10 as. 
inversion H3.  subst. rename_last eqll. 
(* case of Id rule *)
injection eqll as eql eqr. subst. 
apply derI with [].  2: apply dlNil.
rewrite <- nsext_def. apply NSctxt_nil.
acacD ; subst ;
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
  repeat (apply Id || rewrite list_rearr16 || rewrite list_rearr15).

all : revgoals.
(* case of BotL rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst. 
apply derI with [].  2: apply dlNil.
rewrite <- nsext_def. apply NSctxt_nil.
acacD ; subst ;
  repeat (rewrite <- !app_assoc || rewrite <- !app_comm_cons) ;
  repeat (apply BotL || rewrite list_rearr16 || rewrite list_rearr15).

all : revgoals. (* ImpL and ImpR rules remain *)
(* case of ImpR rule *)
1-3:(rewrite <- list_rearr15; simpl;
     (rewrite list_rearr17_R || rewrite list_rearr16_R));
  constructor.

subst. rename_last eqll.  injection eqll as eql eqr. subst. 
rewrite dersrec_all in H0.  rewrite Forall_forall in *.
unfold can_exchL in H1. simpl in *.  
(* rewrite <- nsext_def in H1. fails, why? *)
rewrite <- nsext_def.
pose (H0 _ ( (or_introl eq_refl))) as H0re.
(* can't apply derI right away as premises will vary *)

acacD; subst; eapply derI; nsrule_rewrites;
  try (rewrite dersrec_all ; rewrite Forall_forall ; intros p inps ;
  simpl in inps ; sD ; subst ; 
  rewrite ?app_nil_r in * ; 
  rewrite ?app_nil_r ; rewrite <- ?list_rearr16'; unfold can_exchR in H1).

 eapply H1. left. reflexivity.
unfold nsext. reflexivity. reflexivity.

eapply H1. left. reflexivity.
unfold nsext. reflexivity.  rewrite <- app_assoc. reflexivity.

rewrite <- app_assoc. simpl.
eapply H1. left. reflexivity. reflexivity.
rewrite <- app_assoc. reflexivity.

eapply H1. left. reflexivity. reflexivity. reflexivity.

rewrite list_rearr16_R. rewrite app_assoc.
eapply H1. left. reflexivity. reflexivity. rewrite <- app_assoc.
rewrite <- list_rearr16_R. reflexivity.

(* now for the ImpL rule *)
subst. rename_last eqll.  injection eqll as eql eqr. subst. 
clear H H0 H3.
eapply derI.  rewrite <- nsext_def. apply NSctxt.  apply ImpL.
rewrite dersrec_all. rewrite Forall_forall. intros.
rewrite Forall_forall in H1. simpl in H1. simpl in H. sD.
subst.  unfold can_exchR in H1. unfold nsext. 
eapply H1.
left. reflexivity.
apply nsext_def. reflexivity.

subst.
unfold can_exchR in H1. rewrite app_comm_cons. 
eapply H1.
right. left. reflexivity. apply nsext_def. reflexivity.
Qed.

Check exchL.
Check exchR.
