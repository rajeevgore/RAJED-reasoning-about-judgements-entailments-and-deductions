
(* derrec, derl, etc, other useful stuff *)

Require Export List.
Set Implicit Arguments.
Export ListNotations.

Require Import Coq.Program.Equality. (* for dependent induction/destruction *)

Require Import genT gen.
Require Import PeanoNat.


(* note, this doesn't work Type replaced by Prop,
  although the actual version used allows prems : X -> Prop 
Reset derrec.

Inductive derrec X (rules : list X -> X -> Prop) :
  (X -> Type) -> X -> Prop := 
  | dpI : forall prems concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps prems concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec X (rules : list X -> X -> Prop) :
  (X -> Type) -> list X -> Prop :=
  | dlNil : forall prems, dersrec rules prems []
  | dlCons : forall prems seq seqs, 
    derrec rules prems seq -> dersrec rules prems seqs ->
    dersrec rules prems (seq :: seqs)
    .
    *)


(* definition using Forall, seems equivalent *)
Inductive aderrec X (rules : list X -> X -> Prop) 
  (prems : X -> Prop) : X -> Prop := 
  | adpI : forall concl,
    prems concl -> aderrec rules prems concl
  | aderI : forall ps concl, rules ps concl ->
    Forall (aderrec rules prems) ps -> aderrec rules prems concl.
(* need type version of Forall, to change this to Type *)

Inductive derrec X (rules : list X -> X -> Type) (prems : X -> Type) :
  X -> Type := 
  | dpI : forall concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec X (rules : list X -> X -> Type) (prems : X -> Type) :
  list X -> Type :=
  | dlNil : dersrec rules prems []
  | dlCons : forall seq seqs, 
    derrec rules prems seq -> dersrec rules prems seqs ->
    dersrec rules prems (seq :: seqs)
    .

Scheme derrec_rect_mut := Induction for derrec Sort Type
with dersrec_rect_mut := Induction for dersrec Sort Type.
Scheme derrec_rec_mut := Induction for derrec Sort Set
with dersrec_rec_mut := Induction for dersrec Sort Set.
Scheme derrec_ind_mut := Induction for derrec Sort Prop
with dersrec_ind_mut := Induction for dersrec Sort Prop.
(*
Check derrec_ind_mut.
Check dersrec_ind_mut.
*)
(* combine the two inductive principles *)
Definition derrec_dersrec_rect_mut X rules prems P P0 dp der dln dlc :=
  pair (@derrec_rect_mut X rules prems P P0 dp der dln dlc)
    (@dersrec_rect_mut X rules prems P P0 dp der dln dlc).

Ltac solve_dersrec := repeat (apply dlCons || apply dlNil || assumption).

(* this should be a more useful induction principle for derrec *)
Definition dim_all X rules prems Q := 
  @derrec_ind_mut X rules prems (fun y => fun _ => Q y) 
  (fun ys => fun _ => Forall Q ys).

Definition dim_allT X rules (prems Q : X -> Type) := 
  @derrec_rect_mut X rules prems (fun y => fun _ => Q y) 
  (fun ys => fun _ => ForallT Q ys).

(* this doesn't work
Check (dim_all _ _ (Forall_nil X Q)).
*)
(* here is how to get the tautologies out of dim_all *)
Definition dim_all3 X rules prems Q h1 h2 := 
  @dim_all X rules prems Q h1 h2 (Forall_nil Q).

Definition fce3 X Q D Ds seq seqs (d : D seq) qs (ds : Ds seqs) qss :=
  @Forall_cons X Q seq seqs qs qss.

Definition dim_all4 X rules prems Q h1 h2 := 
  @dim_all3 X rules prems Q h1 h2 
  (@fce3 X Q (derrec rules prems) (dersrec rules prems)).

Definition dim_all8 X rules prems Q h1 h2 := 
  @dim_all3 X rules prems Q h1 h2 
  (fun seq seqs _ qs _ qss => @Forall_cons X Q seq seqs qs qss).
    
(* so dim_all4, or dim_all8 better, is the same as derrec_all_ind below *)

Lemma derrec_all_ind:
  forall X (rules : list X -> X -> Type) (prems Q : X -> Prop),
     (forall concl : X, prems concl -> Q concl) ->
     (forall (ps : list X) (concl : X),
      rules ps concl -> dersrec rules prems ps -> Forall Q ps -> Q concl) ->
     forall y : X, derrec rules prems y -> Q y.
Proof.  intros.
eapply dim_all. exact H. exact H0.
apply Forall_nil.
intros.  apply Forall_cons. assumption.  assumption.
assumption.  Qed.

Lemma derrec_all_indT:
  forall X (rules : list X -> X -> Type) (prems Q : X -> Type),
     (forall concl : X, prems concl -> Q concl) ->
     (forall (ps : list X) (concl : X),
      rules ps concl -> dersrec rules prems ps -> ForallT Q ps -> Q concl) ->
     forall y : X, derrec rules prems y -> Q y.
Proof.  intros until 0. intros H H0.
eapply dim_allT. exact H. exact H0.
apply ForallT_nil.
intros.  apply ForallT_cons. assumption.  assumption.
Qed.

Lemma derrec_all_rect:
  forall X (rules : list X -> X -> Type) (prems Q : X -> Type),
     (forall concl : X, prems concl -> Q concl) ->
     (forall (ps : list X) (concl : X),
      rules ps concl -> dersrec rules prems ps -> ForallT Q ps -> Q concl) ->
     forall y : X, derrec rules prems y -> Q y.
Proof.  intros.
eapply dim_allT. exact X0. exact X1.
apply ForallT_nil.
intros.  apply ForallT_cons. assumption.  assumption.
assumption.  Qed.

(* tried to do a similar thing where property Q also involved the 
proof tree (as well as the endsequent): this created a problem that
the list of proof trees which are part of the dersrec object are not 
all of the same type - so one cannot go from 
ds : dersrec rules prems concls to ForallT (dersrec rules prems ??) ds'
instead need to define allPder and do the following *)

Inductive allPder X (rules : rlsT X) (prems : X -> Type) P : 
  forall concls : list X, dersrec rules prems concls -> Type :=
  | allPder_Nil : @allPder X rules prems P [] (dlNil rules prems)
  | allPder_Cons : forall seq seqs d, P seq d -> forall ds, 
    @allPder X rules prems P seqs ds -> 
    @allPder X rules prems P (seq :: seqs) (dlCons d ds)
  .

Lemma allPderD : forall X rules prems Q ps (dpss : dersrec rules prems ps) p,
  allPder Q dpss -> InT (p : X) ps -> {d : derrec rules prems p & Q p d}.
Proof. induction ps.
intros. inversion X1.
intros dpss p adp inp. inversion adp. subst. 
inversion inp ; subst.
exists d. assumption.
clear X0 inp adp. exact (IHps ds p X1 X2).  Qed.

(* destruct for allPder dlCons *)
Lemma allPder_dlConsD: forall X rules prems Q seq seqs d ds,
  @allPder X rules prems Q (seq :: seqs) (dlCons d ds) ->
    Q seq d * allPder Q ds.
Proof.
intros. (* inversion X0 produces existT equalities *)
(* induction X0 produces trivial subgoal 2, unsolvable subgoal 1 *)
(* dependent induction X0. OK, but irrelevant IHX0, trivial subgoal *)
dependent destruction X0. 
split ; assumption. Qed.

Inductive in_dersrec X (rules : rlsT X) prems concl 
  (d : derrec rules prems concl) : 
  forall concls, dersrec rules prems concls -> Type :=
  | in_dersrec_hd : forall concls ds, in_dersrec d 
    (@dlCons X rules prems concl concls d ds)
  | in_dersrec_tl : forall concl' d' concls ds, in_dersrec d ds -> 
    in_dersrec d (@dlCons X rules prems concl' concls d' ds)
  .

Lemma all_in_d_allP: forall X rules prems Q ps (dpss : dersrec rules prems ps),
  (forall (p : X) (d : derrec rules prems p), in_dersrec d dpss -> Q p d) -> 
  allPder Q dpss.
Proof.  induction dpss. intros. apply allPder_Nil.
intros.  apply allPder_Cons.  apply X0. apply in_dersrec_hd.
apply IHdpss.  intros. apply X0. apply in_dersrec_tl. assumption. Qed.
(* alternative proof, longer, shows need to use dependent inversion 
Proof. induction ps. intros. dependent inversion dpss. apply allPder_Nil.
intro. dependent inversion dpss. subst. 
intros.  apply allPder_Cons. apply X0. apply in_dersrec_hd.
apply IHps. intros. apply X0. apply in_dersrec_tl. assumption. Qed.
*)

Lemma allP_all_in_d: forall X rules prems Q ps (dpss : dersrec rules prems ps),
  allPder Q dpss -> 
  forall (p : X) (d : derrec rules prems p), in_dersrec d dpss -> Q p d.  
Proof. induction ps. intro. dependent inversion dpss.
intros. inversion X1.
intro. dependent inversion dpss. subst.
intro. (* inversion X0 gives existT equalities *)
dependent destruction X0.
intros. (* inversion X1 gives existT equalities *) 
dependent destruction X1. assumption.
eapply IHps. eassumption. assumption. Qed.

Definition derrec_rect_mut_all X (rules : rlsT X) prems Q cl1 cl2 :=
  derrec_rect_mut Q (@allPder X rules prems Q) cl1 cl2 
    (allPder_Nil Q) (@allPder_Cons X rules prems Q).
(*
Check derrec_rect_mut_all.
*)
Lemma allPderD_in :
  forall X rules prems Q ps (dpss : dersrec rules prems ps) p,
    allPder Q dpss -> InT (p : X) ps ->
      {d : derrec rules prems p & in_dersrec d dpss & Q p d}.
Proof. induction ps.
intros. inversion X1.
intros dpss p adp inp. dependent destruction adp.
inversion inp ; subst.
exists d.  apply in_dersrec_hd.  assumption.
pose (IHps ds p adp X0). destruct s. (* cD doesn't work here - why?? *)
exists x. apply in_dersrec_tl. assumption.  assumption. Qed.
(*
Check allPderD_in.
*)
Inductive derl X (rules : list X -> X -> Type) : list X -> X -> Type := 
  | asmI : forall p, derl rules [p] p
  | dtderI : forall pss ps concl, rules ps concl ->
    dersl rules pss ps -> derl rules pss concl
with dersl X (rules : list X -> X -> Type) : list X -> list X -> Type := 
  | dtNil : dersl rules [] []
  | dtCons : forall ps c pss cs,
    derl rules ps c -> dersl rules pss cs -> dersl rules (ps ++ pss) (c :: cs)
  . 

Scheme derl_ind_mut := Induction for derl Sort Prop
with dersl_ind_mut := Induction for dersl Sort Prop.
Scheme derl_rec_mut := Induction for derl Sort Set
with dersl_rec_mut := Induction for dersl Sort Set.
Scheme derl_rect_mut := Induction for derl Sort Type
with dersl_rect_mut := Induction for dersl Sort Type.
(*
Check derl_ind_mut.
Check dersl_ind_mut.
*)
Lemma dtCons_eq X rules ps c pss cs psa: derl rules ps (c : X) ->
  dersl rules pss cs -> psa = ps ++ pss -> dersl rules psa (c :: cs). 
Proof. intros. subst. apply dtCons ; assumption. Qed.

(* combine the two inductive principles *)
Definition derl_dersl_rect_mut X rules P P0 asm dtd dtn dtc :=
  pair (@derl_rect_mut X rules P P0 asm dtd dtn dtc)
    (@dersl_rect_mut X rules P P0 asm dtd dtn dtc).

Lemma asmsI X rules ps: @dersl X rules ps ps .
Proof. induction ps. apply dtNil. pose (asmI rules a).
pose (dtCons d IHps). simpl in d0. exact d0. Qed.

Lemma in_derl X rules ps c: rules ps c -> @derl X rules ps c.
Proof. intro. eapply dtderI. eassumption. apply asmsI. Qed.

Inductive dercl X (rules : list X -> X -> Type) :
  list X -> X -> Type := 
  | casmI : forall p, dercl rules [p] p
  | dtcderI : forall pss ps concl, rules ps concl ->
    dercsl rules pss ps -> dercl rules (concat pss) concl
with dercsl X (rules : list X -> X -> Type) :
  list (list X) -> list X -> Type := 
  | dtcNil : dercsl rules [] []
  | dtcCons : forall ps c pss cs, dercl rules ps c ->
      dercsl rules pss cs -> dercsl rules (ps :: pss) (c :: cs)
  . 

Scheme dercl_ind_mut := Induction for dercl Sort Prop
with dercsl_ind_mut := Induction for dercsl Sort Prop.
Scheme dercl_rec_mut := Induction for dercl Sort Set
with dercsl_rec_mut := Induction for dercsl Sort Set.
Scheme dercl_rect_mut := Induction for dercl Sort Type
with dercsl_rect_mut := Induction for dercsl Sort Type.
(*
Check dercl_ind_mut.
Check dercsl_ind_mut.
*)
(* combine the two inductive principles *)
Definition dercl_dercsl_rect_mut X rules P P0 asm dtd dtn dtc :=
  pair (@dercl_rect_mut X rules P P0 asm dtd dtn dtc)
    (@dercsl_rect_mut X rules P P0 asm dtd dtn dtc).

Inductive ccps X f (qs cs : list X) : Type :=
  | ccpsI : forall pss, f pss cs -> qs = concat pss -> ccps f qs cs.

Lemma ccpsD X f qs cs: ccps f qs cs ->
  {pss : list (list X) & qs = concat pss & f pss cs}.
Proof. intro cc. destruct cc. subst. exists pss ; tauto. Qed.

Definition drl_allT X (rules Q : list X -> X -> Type) R :=
  @derl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun pss => fun cs => fun _ => R pss cs).

Definition drsl_allT X (rules Q : list X -> X -> Type) R :=
  @dersl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun pss => fun cs => fun _ => R pss cs).

(* these may be too strong, have a condition that has to hold
  even if dersl and Forall2T Q hold for different partition of pss *)
Definition drl_allT' X (rules Q : list X -> X -> Type) :=
  @derl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun ps => fun cs => fun _ => ccps (Forall2T Q) ps cs).

Definition drsl_allT' X (rules Q : list X -> X -> Type) :=
  @dersl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun ps => fun cs => fun _ => ccps (Forall2T Q) ps cs).

Definition dcl_allT X (rules Q : list X -> X -> Type) :=
  @dercl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun pss => fun cs => fun _ => Forall2T Q pss cs).

Definition dcsl_allT X (rules Q : list X -> X -> Type) :=
  @dercsl_rect_mut X rules (fun ps => fun c => fun _ => Q ps c)
  (fun pss => fun cs => fun _ => Forall2T Q pss cs).

Lemma dercl_all_rect: forall X (rules Q : list X -> X -> Type),
  (forall p : X, Q [p] p) ->
  (forall pss qs ps concl, rules ps concl -> dercsl rules pss ps ->
    Forall2T Q pss ps -> qs = concat pss -> Q qs concl) ->
  forall ps c, dercl rules ps c -> Q ps c.
Proof.  intros. eapply dcl_allT.  exact X0.
{ intros. eapply X1.  eassumption.
  eassumption.  eassumption. reflexivity. }
apply Forall2T_nil.
intros. apply Forall2T_cons ; assumption. assumption. Qed.

Lemma derscl_all_dercl: forall X (rules : list X -> X -> Type),
  forall pss cs, dercsl rules pss cs -> Forall2T (dercl rules) pss cs.
Proof. intros X rules. apply dcsl_allT. apply casmI.
intros. eapply dtcderI ; eassumption.
apply Forall2T_nil.  intros.  apply Forall2T_cons ; assumption. Qed.

Lemma all_dercl_derscl: forall X (rules : list X -> X -> Type),
  forall pss cs, Forall2T (dercl rules) pss cs -> dercsl rules pss cs.
Proof. induction pss.
intros. inversion X0. apply dtcNil.
intros. inversion X0. subst. apply dtcCons. assumption.
apply IHpss. assumption.  Qed.

Lemma all_derl_dersl: forall X (rules : list X -> X -> Type),
  forall pss cs, Forall2T (derl rules) pss cs -> dersl rules (concat pss) cs.
Proof. induction pss.
intros. inversion X0. simpl. apply dtNil.
intros. inversion X0. subst. simpl. apply dtCons. assumption.
apply IHpss. assumption.  Qed.

Lemma all_derl_dersl': forall X (rules : list X -> X -> Type),
  forall qs cs, ccps (Forall2T (derl rules)) qs cs -> dersl rules qs cs.
Proof. intros. destruct X0. subst. apply all_derl_dersl. exact f. Qed.

Lemma dersl_all_derl: forall X (rules : list X -> X -> Type),
  forall qs cs, dersl rules qs cs ->
  {pss : list (list X) & qs = concat pss & Forall2T (derl rules) pss cs}.
Proof. intros X rules. eapply drsl_allT. apply asmI.
intros. destruct X0. subst. eapply dtderI. apply r. apply d.
exists []. simpl. reflexivity.  apply Forall2T_nil.
intros. destruct X1. subst. exists (ps :: x).  simpl. reflexivity.
apply Forall2T_cons ; assumption. Qed.

Lemma dersl_all_derl': forall X (rules : list X -> X -> Type),
  forall qs cs, dersl rules qs cs -> ccps (Forall2T (derl rules)) qs cs.
Proof. intros X rules. eapply drsl_allT'. apply asmI.
intros. destruct X0. eapply dtderI ; eassumption.
eapply ccpsI. apply Forall2T_nil.  simpl. reflexivity.
intros. destruct X1. subst. eapply ccpsI.
apply Forall2T_cons ; eassumption.  simpl. reflexivity.  Qed.

Lemma dercl_derl': forall X (rules : list X -> X -> Type),
  prod (forall ps c, dercl rules ps c -> derl rules ps c)
    (forall pss cs, dercsl rules pss cs -> dersl rules (concat pss) cs).
Proof. intros.
eapply (dercl_dercsl_rect_mut (rules := rules)
  (fun ps : list X => fun c => fun _ => derl rules ps c)
  (fun pss cs => fun _ => dersl rules (concat pss) cs)).
apply asmI.
intros. eapply dtderI. eassumption.
subst. assumption.
simpl. apply dtNil.
intros. simpl. apply dtCons ; assumption.  Qed.

Definition dercl_derl X rules := fst (@dercl_derl' X rules).
Definition dercsl_dersl X rules := snd (@dercl_derl' X rules).

Lemma derl_dercl: forall X (rules : list X -> X -> Type),
  forall ps c, derl rules ps c -> dercl rules ps c.
Proof.  intros X rules.
eapply (drl_allT (dercl rules) (ccps (dercsl rules))).
apply casmI.
{ intros. destruct X0. subst.
eapply dtcderI. eassumption.  eassumption. }
{ eapply ccpsI. apply dtcNil. simpl. reflexivity. }
{ intros. destruct X1. subst.
eapply ccpsI. eapply dtcCons ; eassumption.
simpl. reflexivity. } Qed.

Lemma derl_all_rect: forall X (rules Q : list X -> X -> Type),
  (forall p : X, Q [p] p) ->
  (forall pss qs ps concl, rules ps concl -> dersl rules qs ps ->
    Forall2T Q pss ps -> qs = concat pss -> Q qs concl) ->
  forall ps c, derl rules ps c -> Q ps c.
Proof.  intros X rules Q asm dtd.
eapply (drl_allT Q (ccps (Forall2T Q))).
exact asm.
{ intros. destruct X0. subst.
eapply dtd. eassumption. eassumption. eassumption. reflexivity. }
{ eapply ccpsI. apply Forall2T_nil. simpl. reflexivity. }
{ intros. destruct X1. subst.
eapply ccpsI. eapply Forall2T_cons ; eassumption.
simpl. reflexivity. } Qed.
(*
Check derl_all_rect.  
Check derl_dercl. 
Check dercl_derl.
*)
(* no convenient way of expressing the corresponding result
  for dercsl except using sth like allrel *)

Lemma derrec_same: forall X rules prems (c c' : X),
  derrec rules prems c -> c = c' -> derrec rules prems c'.
Proof. intros. subst. assumption. Qed.

(* further detailed versions of derrec_same *)
Lemma derrec_same_nsL: forall Y X D rules prems G H Δ d (Γ Γ' : X),
  derrec rules prems (G ++ (Γ : X, Δ : Y, d : D) :: H) ->
    Γ = Γ' -> derrec rules prems (G ++ (Γ', Δ, d) :: H).
Proof. intros. subst. assumption. Qed.

Lemma derrec_same_nsR: forall Y X D rules prems G H Γ d (Δ Δ' : X),
  derrec rules prems (G ++ (Γ : Y, Δ : X, d : D) :: H) ->
    Δ = Δ' -> derrec rules prems (G ++ (Γ, Δ', d) :: H).
Proof. intros. subst. assumption. Qed.

Lemma dersrec_all: forall X rules prems (cs : list X),
  iffT (dersrec rules prems cs) (ForallT (derrec rules prems) cs).
Proof.  intros. 
induction cs ; unfold iffT ; apply pair ; intro.
apply ForallT_nil. apply dlNil.
inversion X0. apply ForallT_cons. assumption. 
unfold iffT in IHcs. destruct IHcs. tauto.
inversion X0. subst. apply dlCons.  assumption. 
unfold iffT in IHcs. destruct IHcs. tauto.
Qed.

Definition dersrecD_all X rs ps cs := iffT_D1 (@dersrec_all X rs ps cs).
Definition dersrecI_all X rs ps cs := iffT_D2 (@dersrec_all X rs ps cs).

Lemma prems_dersrec X rules prems cs:
  ForallT prems cs -> @dersrec X rules prems cs.
Proof. induction cs ; intros. apply dlNil.
inversion X0. subst. apply dlCons. apply dpI. assumption. tauto. Qed. 

Lemma dersrec_forall: forall X rules prems (cs : list X),
  iffT (dersrec rules prems cs) (forall c, InT c cs -> derrec rules prems c).
Proof. intros. rewrite dersrec_all. rewrite ForallT_forall. reflexivity. Qed.

Definition dersrecD_forall X rs ps cs := iffT_D1 (@dersrec_forall X rs ps cs).
Definition dersrecI_forall X rs ps cs := iffT_D2 (@dersrec_forall X rs ps cs).

Lemma dersrec_nil: forall X rules prems, dersrec rules prems ([] : list X).
Proof. apply dlNil. Qed.

Lemma dersrec_single: forall X rules prems c,
  iffT (dersrec rules prems [c]) (derrec rules prems (c : X)).
Proof. intros.  rewrite dersrec_all. rewrite ForallT_single. reflexivity. Qed.

Definition dersrec_singleD X rs ps c := iffT_D1 (@dersrec_single X rs ps c).
Definition dersrec_singleI X rs ps c := iffT_D2 (@dersrec_single X rs ps c).

Lemma dersrec_map_single: forall X Y (f : X -> Y) rules prems c,
  iffT (dersrec rules prems (map f [c])) (derrec rules prems (f c)).
Proof. simpl. intros. apply dersrec_single. Qed.

Lemma dersrec_map_2: forall X Y (f : X -> Y) rules prems c d,
  iffT (dersrec rules prems (map f [c ; d]))
    (derrec rules prems (f c) * derrec rules prems (f d)).
Proof. intros. rewrite dersrec_all. rewrite ForallT_map_2. reflexivity. Qed.

(* try using the induction principle derrec_all_rect *)
Theorem derrec_trans_imp: forall X rules prems (concl : X),
  derrec rules (derrec rules prems) concl -> derrec rules prems concl.
Proof.  intros. revert X0.
eapply derrec_all_rect. tauto.
intros.  eapply derI. exact X0.
apply dersrecI_all. exact X2. Qed.

Lemma derrec_rmono: forall W (rulesa rulesb : rlsT W) prems concl,
  rsub rulesa rulesb -> 
  derrec rulesa prems concl ->
  derrec rulesb prems concl.
Proof.
  intros.  revert X0.  eapply derrec_all_rect.
  intros. apply dpI. assumption.
  intros. eapply derI. unfold rsub in X. apply X. eassumption.
  apply dersrec_forall; intros. eapply ForallT_forall in X2; eassumption.
Qed.

Theorem derl_derrec_trans: forall X rules prems rps (concl : X),
  derl rules rps concl -> dersrec rules prems rps -> derrec rules prems concl.
Proof. 
intros.

eapply (derl_rect_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    dersrec rules prems ps -> derrec rules prems c)
  (fun ps cs : list X => fun _ => 
    dersrec rules prems ps -> dersrec rules prems cs)).

intros.  inversion X2. assumption.
intros. eapply derI. eassumption. tauto.
tauto.
intros.
apply dlCons. apply X2. apply dersrecD_all in X4.
apply ForallT_appendD1 in X4.
apply dersrecI_all. exact X4.
apply X3. apply dersrecD_all in X4.
apply ForallT_appendD2 in X4.
apply dersrecI_all. exact X4.

exact X0. exact X1. Qed.

Theorem derrec_derl_deriv: forall X rules prems (concl : X),
  derrec (derl rules) prems concl -> derrec rules prems concl.

Proof.
intros.

apply (derrec_rect_mut (rules := derl rules) (prems := prems)
  (fun x : X => fun _ => derrec rules prems x)
  (fun xs : list X => fun _ => dersrec rules prems xs)).

apply dpI.
intros. eapply derl_derrec_trans in r. eassumption.  assumption.
apply dlNil.
intros. apply dlCons ; assumption.
assumption.  Qed.

Definition derl_derrec X rules prems rps (concl : X) drrc prems_cond :=
  @derl_derrec_trans X rules prems rps (concl : X) drrc 
    (@prems_dersrec X rules prems rps prems_cond).

Definition derl_derrec_nil X rules prems (concl : X) drrc :=
  @derl_derrec_trans X rules prems [] (concl : X) drrc 
    (@dlNil X rules prems).

Lemma dersl_dersrec_nil X rules prems (cs : list X):
  dersl rules [] cs -> dersrec rules prems cs.
Proof. induction cs ; intros. apply dlNil.
inversion X0. destruct ps. simpl in H0. subst. 
apply dlCons. apply derl_derrec_nil. assumption. tauto.
simpl in H0. discriminate H0.  Qed.

Lemma dersl_cons: forall X rules qs p (ps : list X), 
  dersl rules qs (p :: ps) -> sigT (fun qsa => sigT (fun qsb =>
    prod (qs = qsa ++ qsb) (prod (derl rules qsa p) (dersl rules qsb ps)))).
Proof.  intros.  inversion X0. subst.
eapply existT.  eapply existT.  apply pair.  reflexivity. tauto. Qed.

Lemma dersl_app_eq: forall X rules (psa psb : list X) qs, 
  dersl rules qs (psa ++ psb) -> sigT (fun qsa => sigT (fun qsb =>
    prod (qs = qsa ++ qsb) (prod (dersl rules qsa psa) (dersl rules qsb psb)))).
Proof.  intro.  intro.  intro.  intro.  induction psa.  intros. 
apply existT with [].  apply existT with qs. simpl. simpl in X0.
apply pair. trivial.
apply pair. apply dtNil. apply X0.

simpl. intros. apply dersl_cons in X0.
cD.  pose (IHpsa _ X4).  cD. subst.
eapply existT.  eapply existT. 
apply pair.  apply app_assoc.  apply pair.
apply dtCons. assumption.  assumption.  assumption.
Qed.

Lemma derl_trans: forall X (rules : list X -> X -> Type) 
          (pss : list X) (rps : list X) (concl : X),
    derl rules rps concl -> dersl rules pss rps -> derl rules pss concl.
Proof.  intros.

eapply (derl_rect_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    forall pss, dersl rules pss ps -> derl rules pss c)
  (fun ps cs : list X => fun _ => 
    forall pss, dersl rules pss ps -> dersl rules pss cs)).

intros. inversion_clear X2. inversion_clear X4.
rewrite app_nil_r.  assumption.
intros. apply X2 in X3.
eapply dtderI. eassumption. assumption.
intros. assumption.
intros.  apply dersl_app_eq in X4. cD. subst. apply dtCons.
apply X2. assumption. apply X3. assumption.
eassumption. assumption.  Qed.

Lemma dersl_trans: forall X (rules : list X -> X -> Type)
          (pss : list X) (rps : list X) (cs : list X),
    dersl rules rps cs -> dersl rules pss rps -> dersl rules pss cs.
Proof.  intros.

(* can use same proof as for derl_trans *)
eapply (dersl_rect_mut (rules := rules) 
  (fun ps : list X => fun c => fun _ =>
    forall pss, dersl rules pss ps -> derl rules pss c)
  (fun ps cs : list X => fun _ => 
    forall pss, dersl rules pss ps -> dersl rules pss cs)).

intros. inversion_clear X2. inversion_clear X4.
rewrite app_nil_r.  assumption.
intros. apply X2 in X3.
eapply dtderI. eassumption. assumption.
intros. assumption.
intros.  apply dersl_app_eq in X4. cD. subst. apply dtCons.
apply X2. assumption. apply X3. assumption.
eassumption. assumption.  Qed.

(* alternatively, just induction on the list of conclusions *)
Lemma dersl_trans_alt: forall X (rules : list X -> X -> Type)
           (cs rps : list X), dersl rules rps cs ->
	 forall (pss : list X), dersl rules pss rps -> dersl rules pss cs.
Proof.  intro.  intro.  intro.  

induction cs.
intros. inversion X0. subst. assumption.
intros.  apply dersl_cons in X0. cD. subst.
apply dersl_app_eq in X1. cD. subst.
apply dtCons. eapply derl_trans. eassumption. assumption.
firstorder.  Qed.

Theorem derl_deriv: forall X rules prems (concl : X),
  derl (derl rules) prems concl -> derl rules prems concl.
Proof. intros.

apply (derl_rect_mut (rules := derl rules) 
  (fun ps : list X => fun c : X => fun _ => derl rules ps c)
  (fun ps cs : list X => fun _ => dersl rules ps cs)).

intro. apply asmI.
intros. eapply derl_trans. eassumption.  assumption.
apply dtNil.
intros.  apply dtCons.  assumption.  assumption.
assumption.  Qed.

Lemma derrec_nil_derl_s X rules: (forall concl, 
  derrec rules (@emptyT X) concl -> derl rules [] concl) *
  (forall cs, dersrec rules (@emptyT X) cs -> dersl rules [] cs).
Proof. 
apply (derrec_dersrec_rect_mut (rules := rules) (prems := (@emptyT X))
  (fun x : X => fun _ => derl rules [] x)
  (fun xs : list X => fun _ => dersl rules [] xs)) ; intros.
- inversion p.
- eapply dtderI ; eassumption. 
- apply dtNil.
- eapply dtCons_eq. eassumption. eassumption. tauto. Qed.

Definition derrec_nil_derl X rules := fst (@derrec_nil_derl_s X rules).
Definition dersrec_nil_dersl X rules := snd (@derrec_nil_derl_s X rules).

Definition derI_rules_mono X rules rulesb prems ps concl rs fuv :=
  @derI X rulesb prems ps concl (@rsub_imp _ _ rules rulesb rs ps concl fuv).
(*
Check derrec_trans_imp.
Check derl_derrec_trans.
Check derrec_derl_deriv.
Check dersl_app_eq.
Check derl_trans.
Check dersl_trans.
Check derl_deriv.
*)
Fixpoint derrec_height X rules prems concl 
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ _ _ => 0
    | derI _ _ ds => S (dersrec_height ds)
  end
with dersrec_height X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => 0
    | dlCons d ds => max (derrec_height d) (dersrec_height ds)
  end.

Fixpoint derrec_size X rules prems concl 
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ _ _ => 0
    | derI _ _ ds => S (dersrec_size ds)
  end
with dersrec_size X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => 0
    | dlCons d ds => (derrec_size d) + (dersrec_size ds)
  end.

Fixpoint derrec_concl X rules prems concl 
  (der : @derrec X rules prems concl) :=
  match der with 
    | dpI _ _ c _ => c
    | derI c _ _ => c
  end.

Fixpoint dersrec_concls X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => []
    | dlCons d ds => derrec_concl d :: dersrec_concls ds
  end.

Lemma dersrec_height_le: forall X rules prems n ps 
  (ds : dersrec rules prems ps),
  (forall (p : X) (d : derrec rules prems p),
  in_dersrec d ds -> derrec_height d <= n) -> dersrec_height ds <= n.
Proof. (* induction ps. 
intros. inversion ds.  this step seems to do nothing *)
induction ds. 
intros.  simpl. apply le_0_n. 
intros.  simpl.  apply Nat.max_lub.
apply H. apply in_dersrec_hd.
apply IHds.  intros. apply H.  apply in_dersrec_tl. assumption. Qed.

Lemma le_dersrec_height: forall X rules prems n ps 
  (ds : dersrec rules prems ps),
  forall (p : X) (d : derrec rules prems p),
  in_dersrec d ds -> n <= derrec_height d -> n <= dersrec_height ds.
Proof. (* induction ps. 
intros. inversion ds.  this step seems to do nothing *)
(* this doesn't work - why ??
induction ds ; intros ; inversion X0 ; subst ; simpl ; rewrite Nat.max_le_iff.
left. assumption.
right.  eapply IHds. 2: eassumption.
WHAT NOW ???
*)
intros. induction X0 ; simpl ; rewrite Nat.max_le_iff ; tauto. Qed.

(*
Fixpoint aderrec_height X 
  (rules : list X -> X -> Prop) (prems : X -> Prop) concl 
  (der : @aderrec X rules prems concl) :=
  match der with 
    | adpI _ _ _ _ => 0
    | aderI _ _ _ => 0
  end.
  *)

Fixpoint derl_height X 
  (rules : list X -> X -> Prop) (prems : list X) (concl : X) 
  (der : @derl X rules prems concl) :=
  match der with 
    | asmI _ _ => 0
    | dtderI _ _ ds => S (dersl_height ds)
  end
with dersl_height X (rules : list X -> X -> Prop) (prems concls : list X) 
  (ders : @dersl X rules prems concls) :=
  match ders with
    | dtNil _ => 0
    | dtCons d ds => max (derl_height d) (dersl_height ds)
  end.

(* induction for two proof trees *)

Lemma derrec_all_rect2:
  forall X Y (rulesx : list X -> X -> Type) (rulesy : list Y -> Y -> Type) 
    (premsx : X -> Type) (premsy : Y -> Type) (Q : X -> Y -> Type),
    (forall px, premsx px -> forall cy, derrec rulesy premsy cy -> Q px cy) ->
    (forall py, premsy py -> forall cx, derrec rulesx premsx cx -> Q cx py) ->
    (forall psx cx psy cy, rulesx psx cx -> rulesy psy cy -> 
      dersrec rulesx premsx psx -> dersrec rulesy premsy psy -> 
      ForallT (fun px => Q px cy) psx -> ForallT (Q cx) psy -> Q cx cy) ->
    forall (conclx : X), derrec rulesx premsx conclx ->
    forall (concly : Y), derrec rulesy premsy concly ->
    Q conclx concly.
Proof.  intros until conclx. intro Dx.
eapply (derrec_all_rect (Q := fun conclx => 
  forall concly : Y, derrec rulesy premsy concly -> Q conclx concly)).
intros.  apply X0. exact X3. exact X4.
intros until concly. intro Dy.
eapply (derrec_all_rect (Q := Q concl)).
intros. apply X1. exact X6.  eapply derI ; eassumption.
intros. eapply X2. eassumption. eassumption. assumption. assumption. 
eapply ForallT_impl in X5. exact X5.
intros. simpl. apply X9. eapply derI ; eassumption.
assumption.  assumption.  assumption.  Qed.
(*
Check derrec_all_rect2.
*)
(* version with no premises *)
Definition derrec_all_rect2_nops X Y rulesx rulesy Q := 
  @derrec_all_rect2 X Y rulesx rulesy (@emptyT X) (@emptyT Y) Q
  (@emptyT_any X _) (@emptyT_any Y _).
(*
Check derrec_all_rect2_nops.
*)
(* without specifying conclusion in the type, more like Isabelle trees *)
Inductive derrec_fc X rules (prems : X -> Type) : Type := 
  | fcI : forall concl, derrec rules prems concl -> derrec_fc rules prems.

Inductive dersrec_fcs X rules (prems : X -> Type) : Type := 
  | fcsI : forall concls, dersrec rules prems concls -> dersrec_fcs rules prems.

Fixpoint dersrec_trees X rules prems concls
  (ders : @dersrec X rules prems concls) :=
  match ders with 
    | dlNil _ _ => []
    | dlCons d ds => fcI d :: dersrec_trees ds
  end.

Lemma der_concl_eq: forall X (rules : rlsT X) prems concl 
  (d : derrec rules prems concl), derrec_concl d = concl.
Proof. dependent inversion d ; simpl ; reflexivity. Qed.

Lemma ders_concls_eq: forall X (rules : rlsT X) prems concls 
  (ds : dersrec rules prems concls), dersrec_concls ds = concls.
Proof. induction ds ; simpl.  reflexivity.
rewrite -> (der_concl_eq d). rewrite IHds. reflexivity. Qed.

Fixpoint derrec_fc_concl X rules prems 
  (der : @derrec_fc X rules prems) :=
  match der with 
    | fcI d => derrec_concl d
  end.

Fixpoint dersrec_fc_concls X rules prems 
  (ders : @dersrec_fcs X rules prems) :=
  match ders with 
    | fcsI ds => dersrec_concls ds
  end.

Lemma in_drs_trees: forall X rules prems cs ds c (d : derrec rules prems c),
  in_dersrec d ds -> InT (fcI d) (@dersrec_trees X rules prems cs ds).
Proof. intros. induction X0 ; simpl. 
apply InT_eq.  apply InT_cons. assumption. Qed. 

Lemma in_trees_drs: forall X rules prems cs ds c (d : derrec rules prems c),
  InT (fcI d) (@dersrec_trees X rules prems cs ds) -> in_dersrec d ds.
Proof. induction cs ; intro ; dependent inversion ds ; simpl ; intros.
inversion X0.
(* inversion X0. injection H2. gives existT equality *)
subst.  dependent destruction X0. apply in_dersrec_hd.
apply in_dersrec_tl. apply IHcs. assumption. Qed.

(*
Goal forall X rules prems concl (d1 : @derrec X rules prems concl) d2,
  fcI d1 = fcI d2 -> d1 = d2.
Proof. intros. injection H. (* gives existT equality *)
*)

(* this doesn't work - type of Q 
Goal forall X rules prems Q cs (ds : @dersrec X rules prems cs),
  allPder Q ds -> Forall2T Q cs (dersrec_trees ds).
*)

