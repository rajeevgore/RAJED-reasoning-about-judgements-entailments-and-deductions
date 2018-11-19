
Require Export List.
Set Implicit Arguments.
Export ListNotations.
Require Import dd.
Require Import List_lemmas.

Parameter PropVars : Set.

(* Indicates the direction connecting sequents look. *)
Inductive dir : Type :=
| fwd : dir
| bac : dir.

(* definition of Propositional Formulas, parameterised over prim prop set *)
Inductive PropF (V : Set): Set :=
 | Var : V -> PropF V
 | Bot : PropF V
 | Imp : PropF V -> PropF V -> PropF V
 (*
 | Not : PropF V -> PropF V
 | And : PropF V -> PropF V -> PropF V
 | Or : PropF V -> PropF V -> PropF V
 *)
 | WBox : PropF V -> PropF V
 | WDia : PropF V -> PropF V
 | BBox : PropF V -> PropF V
 | BDia : PropF V -> PropF V
.

(* statement of exchL fails if using Type here 
Definition rel (W : Type) : Type := prod W W.
*)
Definition rel (W : Set) : Set := prod W W.
Definition rls (W : Type) : Type := list W -> W -> Prop.  
Definition trf (W : Type) : Type := W -> W.  

(*
Inductive Seq (X : Set) : Set :=
  | mkseq : X -> X -> Seq X.

Check Seq_rect.
Check Seq_ind.
Check Seq_rec.

Print Seq_rect.
Print Seq_ind.
Print Seq_rec.
*)

(* don't want this approach, try principal rule 
  (effect of rule on principal formulae, then context) 
Inductive seqrule (V : Set) : 
  list (rel (list (PropF V))) -> rel (list (PropF V)) -> Prop :=
  | Id : forall A Gamma Delta,
    In A Gamma -> In A Delta -> seqrule [] (pair Gamma Delta)
  (*
  | AndR : forall A B Gamma Delta,
    seqrule [pair Gamma (A :: Delta); pair Gamma (B :: Delta)]
      (pair Gamma ((And A B) :: Delta))
  | OrL : forall A B Gamma Delta,
    seqrule [pair (A :: Gamma) Delta; pair (B :: Gamma) Delta]
      (pair ((Or A B) :: Gamma) Delta)
  | AndL : forall A B Gamma Delta,
    seqrule [pair (A :: B :: Gamma) Delta] (pair ((And A B) :: Gamma) Delta)
  | OrR : forall A B Gamma Delta,
    seqrule [pair Gamma (A :: B :: Delta)] (pair Gamma ((Or A B) :: Delta))
  *)
  | ExchR : forall A B Gamma Delta1 Delta2,
    seqrule [pair Gamma (Delta1 ++ A :: B :: Delta2)]
     (pair Gamma (Delta1 ++ B :: A :: Delta2))
  | ExchL : forall A B Gamma1 Gamma2 Delta,
    seqrule [pair (Gamma1 ++ A :: B :: Gamma2) Delta]
     (pair (Gamma1 ++ B :: A :: Gamma2) Delta)
.
*)

Inductive princrule (V : Set) : rls (rel (list (PropF V))) :=
  | Id' : forall A, princrule [] (pair [A] [A])
  | ImpR' : forall A B, princrule [pair [A] [B]] (pair [] [Imp A B])
  | ImpL' : forall A B, princrule
    [pair [B] [] ; pair [] [A]] (pair [Imp A B] [])
  | BotL' : princrule [] (pair [Bot V] []).

Definition seqext (W : Set) Γ1 Γ2 Δ1 Δ2 (seq : rel (list W)) :=
  match seq with | pair U V => pair (Γ1 ++ U ++ Γ2) (Δ1 ++ V ++ Δ2) end.

Inductive seqrule (W : Set) (pr : rls (rel (list W))) : 
    rls (rel (list W)) := 
  | Sctxt : forall ps c Γ1 Γ2 Δ1 Δ2, pr ps c -> 
    seqrule pr (map (seqext Γ1 Γ2 Δ1 Δ2) ps) (seqext Γ1 Γ2 Δ1 Δ2 c).

Lemma seqext_def : forall (W : Set) Γ1 Γ2 Δ1 Δ2 (seq : rel (list W)) U V,
      @seqext W Γ1 Γ2 Δ1 Δ2 (U,V) =  ((Γ1 ++ U ++ Γ2),(Δ1 ++ V ++ Δ2)).
Proof. reflexivity. Qed.

(* w : Set fails *)
Definition nsext (W : Type) G H (d : dir) (seq : W) := G ++ (seq, d) :: H.
Lemma nsext_def: forall (W : Type) G H d seq, 
  @nsext W G H (d : dir) (seq : W) = G ++ (seq, d) :: H.
Proof.
unfold nsext. reflexivity.
Qed.

Inductive nsrule (W : Set) (sr : rls (rel (list W))) : 
    rls (list (rel (list W) * dir)) :=
  | NSctxt : forall ps c G H d, sr ps c -> 
    nsrule sr (map (nsext G H d) ps) (nsext G H d c).

Lemma NSctxt_nil: forall (W : Set) sr G H d c, (sr [] c : Prop) ->
  @nsrule W sr [] (nsext G H d c).
Proof.  intros.  eapply NSctxt in H0.  simpl in H0. exact H0.  Qed.

Check princrule.
Check seqext.
Check seqrule.
Check nsext.
Check nsrule.

(* problem with the seqrule/princrule approach, try this instead *)

Lemma princrule_L : forall {V : Set} ps Γ Δ,
    @princrule V ps (Γ, Δ) ->
    Γ = [] \/ exists E, Γ = [E].
Proof.
  intros V ps Γ Δ P.
  inversion P as [ A P2| P2 | A B P2 | P2];
                       try (left; reflexivity).
  right. exists A. reflexivity.
  right. exists (Imp A B). reflexivity.
  right. exists (Bot V). reflexivity.
Qed.

Lemma princrule_R : forall {V : Set} ps Γ Δ,
    @princrule V ps (Γ, Δ) ->
    Δ = [] \/ exists E, Δ = [E].
Proof.
  intros V ps Γ Δ P. inversion P as [ A P2| A B P2 | P2 | P2];
                       try (left; reflexivity).
  right. exists A. reflexivity.
  right. exists (Imp A B). reflexivity.
Qed.

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

(*
Lemma exchL: forall (V : Set) ns (D : derrec (nsrule (@proprule V)) 
  (fun _ => False) ns) G H seq d Γ1 A B Γ2 Δ, 
  ns = G ++ (seq, d) :: H -> seq = pair (Γ1 ++ A :: B :: Γ2) Δ ->
  derrec (nsrule (@proprule V)) (fun _ => False) 
    (G ++ (pair (Γ1 ++ B :: A :: Γ2) Δ, d) :: H).
intro.  intro.  intro.
Check derrec_all_ind.
eapply derrec_all_ind in D.
(* eexact D. fails - why? *)
or, which doesn't work without using can_exchL
intro.  intro.
eapply derrec_all_ind.
tauto.
*)

Ltac acacE :=
  repeat match goal with
    | [ H : _ |- _ ] => apply app_eq_app in H ; sE
    | [ H : _ |- _ ] => apply cons_eq_app in H ; sE
    | [ H : _ |- _ ] => apply app_eq_cons in H ; sE
    end.

Ltac acacD :=
  repeat match goal with
    | [ H : _ |- _ ] => apply app_eq_app in H ; sD
    | [ H : _ |- _ ] => apply cons_eq_app in H ; sD
    | [ H : _ |- _ ] => apply app_eq_cons in H ; sD
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H as ?H ?H 
    end.

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

Check exchL.

Lemma Partition_0_2 : forall {T : Type} l1 l2 l3 (A B : T),
    l1 ++ l2 = A :: B :: l3 ->
    (l1 = [] /\ l2 = A :: B :: l3) \/
    (l1 = [A] /\ l2 = B :: l3) \/
    (l1 = [A;B] /\ l2 = l3) \/
    (exists l4, l1 = [A;B]++l4 /\ l3 = l4 ++ l2).
Proof.
  intros T l1 l2 l3 A B H1.
  destruct l1. auto.
  right. simpl in H1. inversion H1 as [[H2 H3]]. 
  destruct l1. auto. 
  simpl in H1. inversion H3. subst. right.
  right. exists l1. auto.
Qed.

(* Lemma that allows us to not have to rewrite [] as (map ... []) *)
Lemma seqrule_nil : forall (W : Set) (pr : rls (rel (list W)))
                           (c : rel (list W)) (Γ1 Γ2 Δ1 Δ2 : list W),
    pr [] c ->
    seqrule pr [] (seqext Γ1 Γ2 Δ1 Δ2 c).
Proof.
  intros until 0. intros P.
  assert (seqrule pr (map (seqext Γ1 Γ2 Δ1 Δ2) []) (seqext Γ1 Γ2 Δ1 Δ2 c) =
          seqrule pr [] (seqext Γ1 Γ2 Δ1 Δ2 c)) as P2.
  reflexivity.
  rewrite <- P2. apply Sctxt. assumption.
Qed.

(* An intermediate rewrite lemma that gets around annoyances with type checker.
Will figure out a cleaner way to do this. *)
Lemma rewrite_lem : forall V Γ1 E B A Γ2 Δ3 F Δ4,
	  seqrule (princrule (V:=V)) [(Γ1 ++ E :: B :: A :: Γ2, Δ3 ++ F :: Δ4)]
                  (Γ1 ++ B :: A :: Γ2, Δ3 ++ Imp E F :: Δ4) =
  seqrule (princrule (V:=V)) (map (seqext Γ1 (B :: A :: Γ2) Δ3 Δ4) [([E], [F])])
    (seqext Γ1 (B :: A :: Γ2) Δ3 Δ4 ([], [Imp E F])).
Proof.
  auto.
Qed.

(* Not sure if I want or need this for the suggested approach.
(See long comment in proof below) 
Lemma Partition_2_1: forall {T : Type} Γ1 Γ2 Γ3 Γ4 Γ0 (A B : T),
    Γ1 ++ A :: B :: Γ2 = Γ3 ++ Γ0 ++ Γ4 ->
    (Γ3 ++ Γ0 = Γ1 ++ [A] /\ Γ4 = B :: Γ2) \/
    (Γ3 = Γ1 ++ [A] /\ Γ0 ++ Γ4 = B :: Γ2) \/
    (exists l1 l2,
        Γ0 = l1 ++ [A;B] ++ l2 /\
        Γ1 = Γ3 ++ l1 /\
        Γ2 = l2 ++ Γ4) \/
    (exists l,
        Γ1 = Γ3 ++ Γ0 ++ l /\
        Γ4 = l ++ A :: B :: Γ2) \/
    (exists l,
        Γ2 = l ++ Γ0 ++ Γ4 /\
        Γ3 = Γ1 ++ A :: B :: l).
Proof.
  intros T. induction Γ1 as [|c l1 Hl1]; intros l2 l3 l4 l5 a b P.
  simpl in *. destruct l3. destruct l5. simpl in *. subst.
  right. right. right. left. exists nil. auto.
  simpl in *. destruct l5. simpl in *. inversion P. subst.
  left. auto.
  simpl in *. inversion P. subst.
  right. right. left. exists nil. exists l5. auto.
  destruct l3. simpl in *. destruct l5. simpl in *.
  inversion P. subst. left. auto.
  inversion P. subst. right. left. auto.
  inversion P. subst. right. right. right. right. exists l3. auto.
  simpl in *. destruct l3. simpl in *. destruct l5. simpl in *.
  destruct l4. discriminate. destruct l4. destruct l1; discriminate.
  destruct l1. simpl in *. inversion P. subst.
Admitted.
*)

(* Caitlin's proof of exchL' *)
Lemma exchL': forall (V : Set) ns 
  (D : derrec (nsrule (seqrule (@princrule V))) (fun _ => False) ns),
  can_exchL (nsrule (seqrule (@princrule V))) ns.
Proof.
  intros V ns D.
  eapply derrec_all_ind in D.
  exact D. tauto.
  intros ps concl P1 P2 P3.
  inversion P1 as [ps2 c2 G2 H3 d2 P4 P5 P6].
  unfold nsext in P6. unfold can_exchL.
  intros G' H' seq d Γ1 A B Γ2 Δ P7 P8.
  unfold nsext in P7.
  apply partition_2_2 in P7.
  (* cases of where the exchange occurs vs where the last rule applied *)
  destruct P7 as [ [J' [P9 P10]] | [
                   [P9 [P10 P11]] |
                   [J' [P9 P10]] ]].
(* case where the rule is applied in a sequent to the right
  of where the exchange takes place *)
  - subst. do 2 rewrite <- nsext_def in P1.
    apply derI with
        (ps := map (nsext (G' ++ (Γ1 ++ B :: A :: Γ2, Δ, d) :: J') H3 d2) ps2).
    rewrite list_rearr14.
    apply NSctxt. assumption.
    rewrite dersrec_all. apply Forall_forall.
    intros q qin. rewrite in_map_iff in qin.
    destruct qin as [r [P5 rin]].
    rewrite <- nsext_def in P5.
    eapply in_map in rin.
    unfold can_exchL in P3.
    rewrite <- P5. unfold nsext. rewrite <- list_rearr14.
    edestruct Forall_forall as [fwd rev].
    pose proof (fwd P3) as H. clear fwd rev.
    eapply H. 3 : reflexivity. apply rin. unfold nsext.
    rewrite list_rearr14.  reflexivity.
(* case where the principal sequent is where the exchange occurs. *)
  - inversion P10 as [[P12 P13]].
    subst G2 H3 c2 d2. clear P10.
    inversion P4 as [ps3 c3 Γ3 Γ4 Δ3 Δ4 P9 P10 P11].
    rewrite P8 in P11. destruct c3 as [Γ0 Δ0].
    simpl in P11. inversion P11 as [[P12 P13]].
    subst Δ. symmetry in P12.

 (* Have to make a decision here on which order to do the following:
 1) case analysis if A, B, both or neither are in Γ0. 
   (5 cases incl two for "neither".)
   Γ1 ++ A :: B :: Γ2 = Γ3 ++ Γ0 ++ Γ4
 2) case analysis on which princrule ps3, Γ0 and Δ0 encode.
   (4 cases.)

For case analysis 1):
a) A is in Γ0 but B isn't. I.e. Γ3 ++ Γ0 = Γ1 ++ [A].
b) B is in Γ0 but A isn't. I.e. Γ3 = Γ1 ++ [A].
c) A and B are in Γ0. Contradiction since there are no rules that allow such a situation.
d) Neither A and B are in Γ0, and Γ0 lies in Γ1. Should be easy, no need to look inside Γ0.
e) Neither A and B are in Γ0, and Γ0 lies in Γ2. Should be easy, no need to look inside Γ0.

Went with 1) first, then 2) but I think there's a better way.
Tomorrow try:
 - Γ0 being empty: 1 case.
 - Γ0 having two or more elements: contradiction on princrule.
 - Γ0 having one element, C.
   - C is left of A.
   - C is A.
     - Then three cases for each rule (except ImpR, already covered.)
   - C is B.
     - Then three cases for each rule (except ImpR, already covered.)
   - C is right of A.

Total number of (significant) cases: 9.

*)    
    
    apply partition_2_3 in P12.
(* cases of where the exchange occurs within the sequent vs principal fml. *)
    destruct P12 as [ [P14 P15] | [
                        [l5 [P14 P15]] | [
                          [P14 P15] | [
                            [P14 P15] |
                            [l5 [P14 P15]]]]]].
    + subst Γ3.
(* cases of the rules *)
      inversion P9 as [ E P12 | E F P12 | E F P12 | P12].
(* Id *)       
      * subst ps3 Γ0 Δ0. simpl in *.
        inversion P15. subst Γ4 E ps2. simpl in *.
        subst ps. clear P11 P15. rewrite <- nsext_def.
        apply derI with (ps := map (nsext G' H' d) []). 
        rewrite (app_cons_single _ _ B).
        apply NSctxt.
        change ((Γ1 ++ [B]) ++ A :: Γ2, Δ3 ++ A :: Δ4) with
            (seqext (Γ1 ++ [B]) Γ2 Δ3  Δ4 ([A],[A])).
        apply seqrule_nil. assumption.
        rewrite dersrec_all. apply Forall_forall.
        contradiction.
(* ImpR *)
      * subst ps3 Γ0 Δ0. simpl in *.
        subst Γ4 ps2. simpl in *.
        subst ps. clear P11. rewrite <- nsext_def.
        apply derI with
            (ps := map (nsext G' H' d)[(Γ1 ++ E :: B :: A :: Γ2, Δ3 ++ F :: Δ4)]). 
        apply NSctxt.
        rewrite rewrite_lem. apply Sctxt.
        assumption.
        unfold can_exchL in P3. unfold nsext. 
        edestruct Forall_forall as [fwd rev].
        pose proof (fwd P3) as H. clear fwd rev. simpl.
        apply dlCons. 2 :constructor. rewrite (app_cons_single _ _ E).
        eapply H. 3 :reflexivity. simpl. left. reflexivity.
        unfold nsext. rewrite <- app_cons_single. reflexivity.
(* ImpL *)
      * subst Δ0 Γ0 ps3 ps2. simpl in *. inversion P15 as [[P16 P17]].
        subst Γ4 A. clear P15 P11.
        apply derI with
            (ps := map (nsext G' H' d)
                        [(Γ1 ++ B :: F :: Γ2, Δ3 ++ Δ4); (Γ1 ++ B :: Γ2, Δ3 ++ E :: Δ4)]).
        apply NSctxt.
        assert (  seqrule (princrule (V:=V))
    [(Γ1 ++ B :: F :: Γ2, Δ3 ++ Δ4); (Γ1 ++ B :: Γ2, Δ3 ++ E :: Δ4)]
    (Γ1 ++ B :: Imp E F :: Γ2, Δ3 ++ Δ4) =
                    seqrule (princrule (V:=V)) (map (seqext (Γ1 ++ [B]) Γ2 Δ3 Δ4)
                                                    [([F],[]); ([],[E])]) (seqext (Γ1 ++ [B]) Γ2 Δ3 Δ4 ([Imp E F],[]))) as P10.
        simpl. do 3 rewrite <- app_assoc. simpl. auto.
        rewrite P10. apply Sctxt. assumption.
        unfold can_exchL in P3. unfold nsext.
        subst ps.
        apply dlCons.
        ** edestruct Forall_forall as [fwd rev].
           pose proof (fwd P3) as H. clear fwd rev. simpl.
           eapply H. 3 :reflexivity. simpl. left. reflexivity.
           unfold nsext. reflexivity.
        ** apply dlCons.
           rewrite dersrec_all in P2. edestruct Forall_forall as [fwd rev].
           pose proof (fwd P2) as H. clear fwd rev. simpl.
           eapply H. simpl. right. left. reflexivity.
           apply dlNil.
(* Bot *)
      * subst Δ0 Γ0 ps3 ps2. simpl in *. inversion P15 as [[P16 P17]].
        subst Γ4 A ps. clear P15 P11.
        apply derI with
            (ps := map (nsext G' H' d) []).
        rewrite <- nsext_def. apply NSctxt.
        rewrite (app_cons_single _ _ B).
        change (((Γ1 ++ [B]) ++ Bot V :: Γ2)) with
            ((Γ1 ++ [B]) ++ [Bot V] ++ Γ2).
        change (Δ3 ++ Δ4) with (Δ3 ++ [] ++ Δ4).
        rewrite <- seqext_def.
        apply seqrule_nil.
        assumption. auto.
        constructor.
    + subst Γ1.   


      admit.
    + admit.
    + admit.
    + admit.

(* case where the rule is applied in a sequent to the left
  of where the exchange takes place *)

  - subst. do 2 rewrite <- nsext_def in P1.
    rewrite <- list_rearr14.
    do 2 rewrite <- nsext_def.
    apply derI with
        (ps := map (nsext G2 (nsext J' H' d (Γ1 ++ B :: A :: Γ2, Δ)) d2) ps2).
    apply NSctxt. assumption.
    rewrite dersrec_all. apply Forall_forall.
    intros q qin. rewrite in_map_iff in qin.
    destruct qin as [r [P5 rin]].
    eapply in_map in rin. unfold can_exchL in P3.
    rewrite <- P5. unfold nsext. rewrite list_rearr14.
    edestruct Forall_forall as [fwd rev].
    pose proof (fwd P3) as H; clear fwd rev.
    eapply H. 3 : reflexivity. apply rin. unfold nsext.
    rewrite list_rearr14. reflexivity.
(* Go back and solve admitted goals. 
Qed.*)
Admitted.


