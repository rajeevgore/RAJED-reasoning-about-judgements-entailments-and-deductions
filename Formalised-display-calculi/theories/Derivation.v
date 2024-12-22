Require Import Relations.
Require Import List.
Import ListNotations.
Require Import ListSetNotations.
Require Import Arith.

Require Import EqDec.
Require Import Tactics.
Require Import Utils.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.


Section Derivation.

  Context `{SL : STRLANG}.


  (* Code adjusted from https://github.com/uwplse/cheerios/blob/master/theories/Core/Tree.v *)

  (* Each node of the tree contains a list of subtrees.
   Coq does not generate a useful induction scheme for such types,
   so we just tell it not to generate anything, and we'll write our own. *)
  Local Unset Elimination Schemes.

  Inductive dertree :=
  | Unf : sequent -> dertree
  | Der : sequent -> rule -> list dertree -> dertree.

  Section dertree_rect_gen.
    Variable P : dertree -> Type.
    Variable P_list : list dertree -> Type.
    Hypothesis P_nil : P_list [].
    Hypothesis P_cons : forall t l, P t -> P_list l -> P_list (t :: l).
    Hypothesis P_Unf : forall s, P (Unf s).
    Hypothesis P_Der : forall s r l, P_list l -> P (Der s r l).

    Fixpoint dertree_rect_gen (dt : dertree) : P dt :=
      let fix go_list (l : list dertree) : P_list l :=
        match l with
        | [] => P_nil
        | t :: l => P_cons t l (dertree_rect_gen t) (go_list l)
      end
      in
      match dt with
      | Unf s => P_Unf s
      | Der s r l => P_Der s r l (go_list l)
      end.

    Fixpoint dertree_rect_gen_list (l : list dertree) : P_list l :=
      match l with
      | [] => P_nil
      | t :: l => P_cons t l (dertree_rect_gen t) (dertree_rect_gen_list l)
      end.

    Definition dertree_rect_gen_both : (forall dt, P dt) * (forall l, P_list l) :=
      pair dertree_rect_gen dertree_rect_gen_list.
  End dertree_rect_gen.

  (* Setting P_list := List.Forall P is a reasonable default. *)
  Section dertree_ind.
    Variable P : dertree -> Prop.

    Hypothesis P_Unf : forall s, P (Unf s).
    Hypothesis P_Der : forall s r l, List.Forall P l -> P (Der s r l).

    Definition dertree_ind (dt : dertree) : P dt :=
      dertree_rect_gen P (List.Forall P)
        (List.Forall_nil _)
        (fun t l Pt Pl => List.Forall_cons _ Pt Pl) P_Unf P_Der dt.
  End dertree_ind.

  Section dertree_rect.
    Variable P : dertree -> Type.

    Hypothesis P_Unf : forall s, P (Unf s).
    Hypothesis P_Der : forall s r l, ForallT P l -> P (Der s r l).

    Definition dertree_rect (dt : dertree) : P dt :=
      dertree_rect_gen P (ForallT P)
        (ForallT_nil P)
        (fun t l Pt Pl => ForallT_cons _ Pt Pl) P_Unf P_Der dt.

  End dertree_rect.

  Proposition dertree_eq_dec : forall (d1 d2 : dertree), {d1 = d2} + {d1 <> d2}.
  Proof.
    apply (dertree_rect_gen (fun d1 => forall d2, {d1 = d2} + {d1 <> d2})
             (fun l1 => forall l2, {l1 = l2} + {l1 <> l2})).
    - intro l2. destruct l2; [now left | now right].
    - intros d1 l1 Hd Hl l2. destruct l2 as [|d2]; try now right.
      destruct (Hd d2) as [Hdeq|Hdneq]; destruct (Hl l2) as [Hleq|Hlneq];
        try (right; injection; contradiction). rewrite Hdeq, Hleq. now left.
    - intros s d2. destruct d2; try now right.
      destruct (sequent_eq_dec s s0) as [Heq|Hneq];
        try (right; injection; contradiction). rewrite Heq. now left.
    - intros s1 r1 l1 IH d2. destruct d2 as [|s2 r2 l2]; try now right.
      destruct (sequent_eq_dec s1 s2) as [Hseq|Hsneq];
        destruct (rule_eq_dec  r1 r2) as [Hreq|Hrneq];
        destruct (IH l2) as [Hleq|Hlneq]; try (right; injection; contradiction).
      rewrite Hseq, Hreq, Hleq. now left.
  Defined.

  #[export] Instance EqDec_dertree : EqDec dertree := {| eqdec := dertree_eq_dec |}.

(*
  Definition dtNoV (dt : dertree) : Prop :=
    match dt with
    | Unf s     => seqNoV s
    | Der s r l => seqNoV s
    end.
*)

  Definition botRule (dt : dertree) : option rule :=
    match dt with
    | Unf _     => None
    | Der s r l => Some r
    end.

  (* Extend the property of a node to the whole tree *)
  Fixpoint allDT (P : dertree -> Prop) (dt : dertree) {struct dt} : Prop :=
    match dt with
    | Unf s     => P (Unf s)
    | Der s r l => P (Der s r l) /\ fold_right (fun dt' => and (allDT P dt')) True l
    end.

  Definition allDTs (P : dertree -> Prop) (l : list dertree) : Prop :=
    fold_right (fun dt' => and (allDT P dt')) True l.

  Definition allNextDTs (P : dertree -> Prop) (dt : dertree) : Prop :=
    match dt with
    | Unf s     => True
    | Der s r l => allDTs P l
    end.

  (* Dual of allDT: there exists a node in the tree satisfying such property *)
  Fixpoint exDT (P : dertree -> Prop) (dt : dertree) : Prop :=
    match dt with
    | Unf s     => P (Unf s)
    | Der s r l => P (Der s r l) \/ fold_right (fun dt' => or (exDT P dt')) False l
    end.

  Definition exDTs (P : dertree -> Prop) (l : list dertree) : Prop :=
    fold_right (fun dt' => or (exDT P dt')) False l.

  Lemma allDT_Next (P : dertree -> Prop) (dt : dertree) :
    allDT P dt <-> (P dt /\ allNextDTs P dt).
  Proof.
    split.
    - intro H. destruct dt. 
      + unfold allDT in H. simpl. split; auto.
      + simpl in H |- *. assumption.
    - intro H. destruct dt.
      + tauto.
      + simpl in H |- *. assumption.
  Qed.

  Lemma allDTs_Forall {P l} : allDTs P l <-> Forall (allDT P) l.
  Proof. rewrite Forall_fold_right. tauto. Qed.

  Lemma exDTs_Exists {P l} : exDTs P l <-> Exists (exDT P) l.
  Proof. rewrite Exists_fold_right. tauto. Qed.

  Definition nextUp (dt : dertree) : list dertree :=
    match dt with
    | Der s r l => l
    | Unf s     => []
    end.

  Lemma exDT_Next (P : dertree -> Prop) (dt : dertree) :
    exDT P dt <-> (P dt \/ exDTs P (nextUp dt)).
  Proof.
    split.
    - intro H. destruct dt.
      + now left.
      + destruct H as [H|H].
        * now left.
        * now right.
    - intro H. destruct dt.
      + destruct H as [H|H].
        * assumption.
        * contradiction.
      + destruct H as [H|H].
        * now left.
        * now right.
  Qed.
        
  Lemma allDT_Der (P : dertree -> Prop) {s r l} :
    allDT P (Der s r l) = (P (Der s r l) /\ allDTs P l).
  Proof. reflexivity. Qed.

  Definition conclDT (dt : dertree) : sequent :=
    match dt with
    | Unf s     => s
    | Der s _ _ => s
    end.

  Fixpoint premsDT (dt : dertree) : list sequent :=
    match dt with
    | Unf s     => [s]
    | Der _ _ l => fold_right (fun dt' => app (premsDT dt')) [] l
    end.

  Definition premsDTs (l : list dertree) : list sequent :=
    fold_right (fun dt' => app (premsDT dt')) [] l.

  Lemma premsDT_Der {s r l} :
    premsDT (Der s r l) = premsDTs l.
  Proof. reflexivity. Qed.

  Definition wfr (dt : dertree) : Prop :=
    match dt with
    | Unf _     => True
    | Der s r l => ruleInst r (map conclDT l, s)
    end.

  Definition exr (DC : DISPCALC) (dt : dertree) : Prop :=
    match dt with
    | Unf _     => True
    | Der _ r _ => r ∈ DC
    end.

  Definition dtFmls (dt : dertree) := seqFmls (conclDT dt).
  Definition dtSVs (dt : dertree) := seqSVs (conclDT dt).

  Definition proper (DC : DISPCALC) (dt : dertree) : Prop :=
    allDT (exr DC) dt /\ allDT wfr dt /\ premsDT dt = [].

  Definition semiproper (DC : DISPCALC) (dt : dertree) : Prop :=
    allDT (exr DC) dt /\ allDT wfr dt.

  Lemma not_proper_Unf {rls} : forall s, ~ proper rls (Unf s).
  Proof.
    intros s Hctr. destruct Hctr as (_ & _ & H). discriminate.
  Qed.

  Lemma exr_subset (rls rls' : list rule) :
    forall dt, incl rls rls' -> exr rls dt -> exr rls' dt.
  Proof.
    intros dt H H0. destruct dt; try auto. apply H. assumption.
  Qed.

  Lemma allDT_impl (P Q : dertree -> Prop) :
    (forall dt, P dt -> Q dt) -> forall dt, allDT P dt -> allDT Q dt.
  Proof.
    intros PimpQ dt allPdt. apply (dertree_ind (fun t => allDT P t -> allDT Q t));
      try assumption; clear dt allPdt.
    - intros s H. simpl. apply PimpQ. assumption.
    - intros s r l Hdt. simpl. intro H. destruct H as [HP H]. split; try (now apply PimpQ).
      rewrite <- Forall_fold_right in H |- *. rewrite Forall_forall in H, Hdt |- *.
      intros x Hx. apply Hdt; try assumption. apply H; assumption.
  Qed.

  Lemma allDTs_impl (P Q : dertree -> Prop) :
      (forall dt, P dt -> Q dt) -> forall dtl, allDTs P dtl -> allDTs Q dtl.
  Proof.
    intros PimpQ dtl. unfold allDTs. setoid_rewrite <- Forall_fold_right.
    setoid_rewrite Forall_forall. intro allPdtl.
    intros dt Hdt. specialize (allPdtl dt Hdt). revert allPdtl.
    apply allDT_impl. assumption.
  Qed.

  Lemma premsDTs_eq_nil_iff {l} : Forall (fun d => premsDT d = []) l <-> premsDTs l = [].
  Proof.
    induction l.
    - split; constructor.
    - simpl. setoid_rewrite app_eq_nil_iff. setoid_rewrite <- IHl. rewrite Forall_cons_iff. tauto.
  Qed.

  Lemma allDTUp {P : dertree -> Prop} {dt : dertree} :
    allDT P dt -> Forall (allDT P) (nextUp dt).
  Proof.
    intro H. apply allDT_Next in H. apply proj2 in H. apply Forall_fold_right. destruct dt; tauto.
  Qed.

  Lemma premsDTUp {dt : dertree} (ls : list sequent) :
    incl (premsDT dt) ls -> Forall (fun d => incl (premsDT d) ls) (nextUp dt).
  Proof.
    intro H. destruct dt as [|s r l]; try constructor.
    induction l; try constructor.
    - intros x Hx. apply H. apply in_app_iff. now left.
    - apply IHl. intros x Hx. apply H. apply in_app_iff. now right.
  Qed.


  Lemma Forall_incl_premsDTs :
    forall ldt (prems : list (sequent)),
      Forall (fun dt => incl (premsDT dt) prems) ldt -> incl (premsDTs ldt) prems.
  Proof.
    induction ldt as [|dt ldt].
    - intros. apply incl_nil_l.
    - simpl. intros prems Hall.
      pose proof (Forall_inv Hall) as Hdt. simpl in Hdt.
      pose proof (Forall_inv_tail Hall) as Hldt.
      apply incl_app; try assumption.
      apply IHldt. assumption.
  Qed.

  Lemma premsDTUp_nil {dt : dertree} :
    premsDT dt = [] -> Forall (fun d => premsDT d = []) (nextUp dt).
  Proof.
    intro H. rewrite <- (Forall_map premsDT (fun s => s = [])).
    apply (Forall_impl _ (@incl_l_nil sequent)).
    rewrite Forall_map. apply premsDTUp. rewrite H. apply incl_refl.
  Qed.

  Lemma premsDTs_incl {ldt : list dertree} {l : list (list sequent)} :
    Forall2 (@incl sequent) (map premsDT ldt) l ->
    incl (premsDTs ldt) (fold_right (@app sequent) [] l).
  Proof.
    intro H. remember (map premsDT ldt) as mldt. revert ldt Heqmldt. induction H.
    - intros. simpl. destruct ldt; try discriminate. apply incl_nil_l.
    - intros ldt Hldt. destruct ldt as [| hldt tldt]; try discriminate.
      simpl. injection Hldt. intros Heql Heqx. apply incl_app_app.
      + rewrite <- Heqx. assumption.
      + apply IHForall2. assumption.
  Qed.

  Lemma properUp {rls : list rule} {dt : dertree} :
    proper rls dt -> Forall (proper rls) (nextUp dt).
  Proof.
    intro H. unfold proper in H |- *. repeat (apply Forall_and; [now apply allDTUp | idtac]).
    now apply premsDTUp_nil.
  Qed.

  Lemma allDT_up_forall {P s r l} : allDT P (Der s r l) -> forall d, List.In d l -> allDT P d.
  Proof.
    intro H. rewrite allDT_Der in H. destruct H as [_ H].
    unfold allDTs in H. rewrite <- Forall_fold_right in H.
    rewrite Forall_forall in H. intros. apply H. assumption.
  Qed.

  Lemma proper_up_forall {rls s r l} : proper rls (Der s r l) -> forall d, d ∈ l -> proper rls d.
  Proof.
    intro H. apply properUp in H. rewrite Forall_forall in H. simpl in H. assumption.
  Qed.

  Lemma proper_up_Forall (DC : DISPCALC) {s r l} : proper DC (Der s r l) -> Forall (proper DC) l.
  Proof.
    intro H. apply Forall_forall. apply (proper_up_forall H).
  Qed.

  Lemma proper_Der {rls s r l} :
    ruleInst r (map conclDT l, s) -> r ∈ rls -> Forall (proper rls) l ->
      proper rls (Der s r l).
  Proof.
    intros Hrlf Hin Hall.
    unfold proper in Hall. repeat setoid_rewrite Forall_and_iff in Hall.
    split; [idtac | split]; try (simpl; rewrite <- Forall_fold_right); try tauto.
    apply premsDTs_eq_nil_iff. tauto.
  Qed.

  Lemma proper_Der_immUp {rls s r l d} : proper rls (Der s r l) -> In d l -> proper rls d.
  Proof.
    intros H Hin. apply properUp in H. rewrite Forall_forall in H.
    apply H. assumption.
  Qed.

  Lemma semiproperUp (DC : DISPCALC) :
    forall dt, semiproper DC dt -> Forall (semiproper DC) (nextUp dt).
  Proof.
    intros dt Hsp.
    unfold semiproper in Hsp |- *. repeat (apply Forall_and; [now apply allDTUp | idtac]).
    now apply allDTUp.
  Qed.

  Lemma semiproper_Der (DC : DISPCALC) :
    forall s r l, exr DC (Der s r l) -> wfr (Der s r l) -> Forall (semiproper DC) l ->
                               semiproper DC (Der s r l).
  Proof.
    intros s r l Hexr Hwfr Hl. unfold semiproper in Hl |- *.
    apply Forall_and_inv in Hl. destruct Hl.    
    repeat rewrite allDT_Der. repeat rewrite allDTs_Forall. tauto.
  Qed.
  
  Lemma wfr_switch {s r l l'} :
    wfr (Der s r l) -> allDTs wfr l' ->
    map conclDT l = map conclDT l' ->
      allDT wfr (Der s r l').
  Proof.
    intros Hwfr Hwfrl' Hconcleq. rewrite allDT_Der. split; try assumption.
    unfold wfr. rewrite <- Hconcleq. assumption.
  Qed.

  Lemma exr_switch {rls s r l l'} :
    exr rls (Der s r l) -> allDTs (exr rls) l' -> allDT (exr rls) (Der s r l').
  Proof.
    intros Hexr Hexrl'. rewrite allDT_Der. tauto.
  Qed.

  Lemma proper_switch {rls s r l l'} :
    proper rls (Der s r l) -> Forall (proper rls) l' ->
    map conclDT l = map conclDT l' ->
      proper rls (Der s r l').
  Proof.
    intros Hval Hallval Hallconcl. unfold proper.
    destruct Hval as (Hexr & Hwfr & Hprems). rewrite allDT_Der in Hwfr, Hexr.
    destruct Hwfr as [Hwfr _]. destruct Hexr as [Hexr _].
    destruct (Forall_and_inv _ _ Hallval) as [Hallwfr H].
    destruct (Forall_and_inv _ _ H) as [Hallexr Hallprems].
    clear Hallval H. split; [idtac | split].
    - apply (exr_switch Hexr). unfold allDTs. now rewrite <- Forall_fold_right.
    - apply (wfr_switch Hwfr); try assumption. unfold allDTs. now rewrite <- Forall_fold_right.
    - apply premsDTs_eq_nil_iff. assumption.
  Qed.


  Lemma allDT_mono (P Q : dertree -> Prop) :
    forall dt, allDT P dt -> (forall s, P s -> Q s) -> allDT Q dt.
  Proof.
    intros dt H H0. revert H. pattern dt. apply (dertree_rect_gen _
    (fun l => allDTs P l -> allDTs Q l)).
    - auto.
    - intros t l H H1. simpl. intro H2. split; [apply H | apply H1]; tauto.
    - simpl. intro s. apply H0.
    - intros s r l H. simpl. fold (allDTs P l) (allDTs Q l). intro H1.
      split; [apply H0 | apply H]; tauto.
  Qed.

  Lemma allDT_and_iff (P Q R : dertree -> Prop) :
    (forall dt, P dt <-> (Q dt /\ R dt)) -> forall dt, allDT P dt <-> (allDT Q dt /\ allDT R dt).
  Proof.
    intro H. intro dt. pattern dt. apply (dertree_rect_gen _
    (fun l => allDTs P l <-> (allDTs Q l /\ allDTs R l))); try assumption; clear dt.
    - tauto.
    - intros t l H0 H1. simpl. rewrite H0, H1. tauto.
    - intro s. simpl. apply H.
    - intros s r l H0. simpl. fold (allDTs P l) (allDTs Q l) (allDTs R l).
      rewrite H, H0. tauto.
  Qed.

  Lemma allDT_and {P Q : dertree -> Prop} :
    forall dt, allDT (fun d => P d /\ Q d) dt <-> allDT P dt /\ allDT Q dt.
  Proof.
    intro dt. apply allDT_and_iff. tauto.
  Qed.

  Lemma allDT_and_acc {P Q} :
    forall dt, allDT P dt -> allDT Q dt -> allDT (fun d => P d /\ Q d) dt.
  Proof. intros dt HP HQ. rewrite allDT_and. tauto. Qed.

  Lemma allDT_and_mono (P Q R : dertree -> Prop) :
    forall dt, allDT P dt -> allDT Q dt -> (forall s, P s -> Q s -> R s) -> allDT R dt.
  
  Proof.
    intros dt H H0 H1. apply allDT_mono with (fun s => P s /\ Q s).
    - rewrite (allDT_and_iff _ P Q); tauto.
    - intro s. apply and_rect. apply H1.
  Qed.

  Lemma allDT_nextUp {P dt} : allDT P dt <-> P dt /\ allDTs P (nextUp dt).
  Proof. rewrite allDT_Next. destruct dt; tauto. Qed.

  (* Expressing a "subtree" relation *)
  Definition isUp (d1 d2 : dertree) : Prop :=
    d1 ∈ nextUp d2.
  Definition in_tree : dertree -> dertree -> Prop :=
    clos_refl_trans_n1 dertree isUp.

  Lemma in_tree_Unf {d s} : in_tree d (Unf s) -> d = Unf s.
  Proof.
    intro H. inversion H; try reflexivity. contradiction.
  Qed.

  Lemma in_tree_Der {d s r l} :
    in_tree d (Der s r l) -> d = Der s r l \/ exists d', List.In d' l /\ in_tree d d'.
  Proof.
    intro H. inversion H; try now left. right. exists y. tauto.
  Qed.

  Lemma in_tree_tran {d d0 d1} : in_tree d d0 -> in_tree d0 d1 -> in_tree d d1.
  Proof.
    unfold in_tree. repeat rewrite <- clos_rt_rtn1_iff. apply rt_trans.
  Qed.

  Lemma allDT_in_tree {P dt} :
    allDT P dt <-> forall d, in_tree d dt -> P d.
  Proof.
    induction dt.
    - simpl. split.
      + intros PUnf d Hd. inversion Hd; try contradiction; try assumption.
      + intro H. apply H. now left.
    - apply Forall_and_inv in H. destruct H as [Hl Hr]. split.
      + intro PDer. destruct PDer as [PDer Pup].
        apply Forall_fold_right in Pup.
        apply (Forall_mp Pup) in Hl. rewrite Forall_forall in Hl.
        intros d Hd. apply in_tree_Der in Hd. destruct Hd as [Hd|Hd].
        * rewrite Hd. assumption.
        * destruct Hd as (d' & Hd'in & Hdd'). apply (Hl d'); assumption.
      + intro HallP. split.
        * apply HallP. constructor.
        * apply Forall_fold_right. eapply (Forall_mp _ Hr). Unshelve.
          apply Forall_forall. intros d' Hd'l d Hdd'.
          apply HallP. constructor 2 with d'; assumption.
  Qed.

  Lemma allDT_in_tree_allDT {P dt} :
    allDT P dt <-> forall d, in_tree d dt -> allDT P d.
  Proof.
    split.
    - intros H d Hd. rewrite allDT_in_tree in H. rewrite allDT_in_tree.
      intros d0 Hd0. apply H. eapply in_tree_tran; eassumption.
    - intro H. rewrite allDT_in_tree. intros d Hd.
      specialize (H d Hd). rewrite allDT_in_tree in H. apply H. constructor.
  Qed.
 
  Lemma premsDT_nil_allDT : forall dt, premsDT dt = [] -> allDT (fun d => premsDT d = []) dt.
  Proof.
    induction dt as [s|s r l IH]; try discriminate.
    intro H. apply premsDTUp_nil in H. simpl in H.
    apply (Forall_mp H) in IH. rewrite allDT_Der, premsDT_Der, <- premsDTs_eq_nil_iff.
    rewrite allDTs_Forall. tauto.
  Qed.

  Lemma proper_allDT {rls dt} : proper rls dt -> allDT (proper rls) dt.
  Proof.
    intros [Hwfr [Hexr Hprems]]. apply premsDT_nil_allDT in Hprems.
    rewrite allDT_in_tree in Hwfr. rewrite allDT_in_tree in Hexr.
    rewrite allDT_in_tree in Hprems. rewrite allDT_in_tree.
    intros d Hind. repeat split.
    - rewrite allDT_in_tree. intros d0 Hind0. apply Hwfr.
      eapply in_tree_tran; eassumption.
    - rewrite allDT_in_tree. intros d0 Hind0. apply Hexr.
      eapply in_tree_tran; eassumption.
    - apply Hprems. assumption.
  Qed.

  Lemma Exists_Forall_mp {A : Type} {P Q : A -> Prop} {l : list A} :
    Forall (fun x => P x -> Q x) l -> Exists P l -> Exists Q l.
  Proof.
    intros Hall Hex. rewrite Forall_forall in Hall. rewrite Exists_exists in Hex |- *.
    destruct Hex as [a [Hinx HPx]]. exists a. split; try assumption. apply Hall; assumption.
  Qed.

  Lemma exDT_in_tree {P dt} :
    exDT P dt <-> exists d, in_tree d dt /\ P d.
  Proof.
    induction dt.
    - simpl. split.
      + intro PUnf. exists (Unf s). split; try assumption. constructor.
      + intros [d [Hind HPd]]. apply in_tree_Unf in Hind. rewrite <- Hind. assumption.
    - apply Forall_and_inv in H. destruct H as [Hl Hr]. split.
      + intro HPDer. destruct HPDer as [HPder|HPup].
        * exists (Der s r l). split; [constructor | assumption].
        * apply Exists_fold_right in HPup. apply (Exists_Forall_mp Hl) in HPup.
          rewrite Exists_exists in HPup. destruct HPup as [dt [Hindt [d [Hind HPd]]]].
          exists d. split; try assumption. constructor 2 with dt; assumption.
      + intro HexP. simpl. destruct HexP as [d [Hind HPd]].
        inversion Hind; try (rewrite <- H; now left). rename y into dt.
        right. rewrite <- Exists_fold_right.
        apply (Exists_Forall_mp Hr). rewrite Exists_exists.
        exists dt. split; try assumption. exists d. tauto.
  Qed.

  Lemma allDT_exDT_and {P Q dt} : allDT P dt -> exDT Q dt -> exDT (fun d => P d /\ Q d) dt.
  Proof.
    intros Hall Hex. rewrite allDT_in_tree in Hall.
    rewrite exDT_in_tree in Hex. rewrite exDT_in_tree.
    destruct Hex as [d [Hin HQd]]. exists d. repeat (split; try assumption).
    apply Hall. assumption.
  Qed.

  Lemma allDTs_exDTs_and {P Q ldt} : allDTs P ldt -> exDTs Q ldt -> exDTs (fun d => P d /\ Q d) ldt.
  Proof.
    intros Hall Hex. induction ldt as [|dt ldt]; try contradiction.
    simpl in Hall, Hex. destruct Hall as [Halldt Halldts]. destruct Hex as [Hex|Hex].
    - left. apply allDT_exDT_and; assumption.
    - right. apply IHldt; assumption.
  Qed.
        

  Lemma allDT_root {P dt} : allDT P dt -> P dt.
  Proof. rewrite allDT_Next. tauto. Qed.

  Lemma allDTs_root {P l} : allDTs P l -> Forall P l.
  Proof.
    unfold allDTs. rewrite <- Forall_fold_right. intro H.
    induction H; try constructor; try apply allDT_root; try assumption.
  Qed.

  Lemma allDT_Der_immUp_root {P s r l d} : allDT P (Der s r l) -> In d l -> P d.
  Proof.
    intros Hall Hin. rewrite allDT_Der in Hall. destruct Hall as [_ Hall].
    apply allDTs_root in Hall. rewrite Forall_forall in Hall.
    apply Hall. assumption.
  Qed.

  Lemma allDT_Der_immUp {P s r l d} : allDT P (Der s r l) -> In d l -> allDT P d.
  Proof.
    intros Hall Hin. rewrite allDT_Next in Hall. destruct Hall as [_ Hall].
    simpl in Hall. unfold allDTs in Hall. rewrite <- Forall_fold_right in Hall.
    rewrite Forall_forall in Hall. apply Hall. assumption.
  Qed.

  Lemma proper_root (DC : DISPCALC) (dt : dertree) : proper DC dt -> exr DC dt /\ wfr dt.
  Proof.
    intros [Hexr [Hwfr _]]. split; apply allDT_root; assumption.
  Qed.

  Lemma semiproper_root (DC : DISPCALC) (dt : dertree) : semiproper DC dt -> exr DC dt /\ wfr dt.
  Proof.
    intros [Hexr Hwfr]. split; apply allDT_root; assumption.
  Qed.

  Lemma semiproper_Unf (DC : DISPCALC) (s : sequent) : semiproper DC (Unf s).
  Proof. split; simpl; exact Logic.I. Qed.

  Lemma premsDT_in_tree {dt} :
    premsDT dt = [] <-> forall d, in_tree d dt -> premsDT d = [].
  Proof.
    split; [idtac | intro H; apply H; left].
    intro Hprems. induction dt; try discriminate.
    intros d Hd. apply in_tree_Der in Hd. destruct Hd as [Hd|Hd].
    - rewrite Hd. assumption.
    - destruct Hd as (d' & Hd'l & Hdd').
      rewrite Forall_forall in H. apply (H d'); try assumption.
      apply premsDTUp_nil in Hprems. rewrite Forall_forall in Hprems.
      apply Hprems. assumption.
  Qed.

  Set Elimination Schemes.

  (* Expressing that a sequent occurs somewhere in a tree *)
  (* A mutually inductive definition might have been a better choice *)
  Inductive seqInDT (s : sequent) (dt : dertree) : Prop :=
    | seqInRoot   : conclDT dt = s -> seqInDT s dt
    | seqInNextUp : forall d, d ∈ nextUp dt -> seqInDT s d -> seqInDT s dt.

  Inductive seqInDTs (s : sequent) (ldt : list dertree) : Prop :=
    | seqInOneDT : forall dt, dt ∈ ldt -> seqInDT s dt -> seqInDTs s ldt.

  (* A tree is irredudant if no sequent has an ancestor with same sequent *) 
  Definition irredundant (dt : dertree) : Prop :=
    allDT (fun d => ~ seqInDTs (conclDT d) (nextUp d)) dt.


  Lemma in_tree_seqInDT : forall d dt s, in_tree d dt -> seqInDT s d -> seqInDT s dt.
  Proof.
    intros d dt s Hint Hsin. induction Hint; try assumption.
    constructor 2 with y; assumption.
  Qed.

  Lemma seqInDT_exDT : forall s dt, seqInDT s dt -> exDT (fun d => conclDT d = s) dt.
  Proof.
    intros s dt Hsin. induction Hsin.
    - apply exDT_Next. now left.
    - destruct dt; try contradiction. right.
      apply Exists_fold_right, Exists_exists. exists d. split; assumption.
  Qed.

  Lemma seqInDTs_exDTs : forall s ldt, seqInDTs s ldt -> exDTs (fun d => conclDT d = s) ldt.
  Proof.
    intros s ldt Hsin. induction ldt as [|dt ldt]; try (inversion Hsin; contradiction).
    simpl. inversion Hsin. destruct H.
    - left. rewrite <- H in H0. apply seqInDT_exDT. assumption.
    - right. apply IHldt. constructor 1 with dt0; assumption.
  Qed.

  

  Lemma seqInDT_dec : forall (dt : dertree) (s : sequent),
    {d | in_tree d dt /\ conclDT d = s} + (~ seqInDT s dt).
  Proof.
    intros dt s0. induction dt as [s|s r l IH].
    - destruct (sequent_eq_dec s s0) as [Heq|Hneq].
      + left. exists (Unf s). rewrite <- Heq. split; [constructor | reflexivity].
      + right. intro H. contradict Hneq. inversion H; try assumption. contradiction.
    - destruct (ForallT_dec_E l IH) as [Hex|Hall].
      + left. rewrite ExistsT_exists in Hex.
        destruct Hex as [dt Hindt [d [Hind Hconcd]]].
        exists d. split; try assumption. constructor 2 with dt; assumption.
      + destruct (sequent_eq_dec s s0) as [Heq|Hneq].
        * left. exists (Der s r l). split; try constructor. assumption.
        * right. intro H. inversion H; try contradiction.
          rewrite ForallT_forall in Hall.
          apply (Hall d); assumption.
  Defined.

  Lemma seqInDTs_dec : forall (ldt : list dertree) (s : sequent),
      {d & {dt | in_tree d dt /\ In dt ldt /\ conclDT d = s} } + (~ seqInDTs s ldt).
  Proof.
    induction ldt as [|dt ldt]; intro s.
    - right. intro H. inversion H. contradiction.
    - destruct (IHldt s) as [yes|no].
      + destruct yes as [d [dt' [Hind [Hindt' Hconc]]]].
        left. exists d, dt'. repeat (split; try assumption). now right.
      + destruct (seqInDT_dec dt s) as [yes0|no0].
        * left. destruct yes0 as [d [Hind Hconcd]].
          exists d, dt. repeat (split; try assumption). now left.
        * right. intro H. inversion H. destruct H0 as [H0|H0].
         -- rewrite <- H0 in H1. contradiction.
         -- contradict no. constructor 1 with dt0; assumption.
  Defined.

  Fixpoint mapDT (f : sequent -> sequent) (dt : dertree) : dertree :=
    match dt with
    | Unf s     => Unf (f s)
    | Der s r l => Der (f s) r (map (mapDT f) l)
    end.

End Derivation.

Section Deriv_Mut.

  Context `{SL : STRLANG}.
  Context (DC : DISPCALC).

  (* A bunch of mutually inductive definitions expressing derivability.
     They are more malleable than dertree in proofs *)

  Inductive deriv_seq : sequent -> Type :=
  | deriv_seq_ext : forall ps c r, r ∈ DC -> ruleInst r (ps, c) -> deriv_seqs ps
                              -> deriv_seq c
  with
    deriv_seqs : list sequent -> Type :=
  | deriv_seqs_nil  : deriv_seqs []
  | deriv_seqs_cons : forall c cs, deriv_seq c -> deriv_seqs cs
                                      -> deriv_seqs (c :: cs).

  Inductive deriv_prseq (prems : list sequent) : sequent -> Type :=
  | deriv_prseq_prem : forall c, c ∈ prems -> deriv_prseq prems c
  | deriv_prseq_ext : forall ps c r, r ∈ DC -> ruleInst r (ps, c) -> deriv_prseqs prems ps
                              -> deriv_prseq prems c
  with
    deriv_prseqs (prems : list sequent) : list sequent -> Type :=
  | deriv_prseqs_nil  : deriv_prseqs prems []
  | deriv_prseqs_cons : forall c cs, deriv_prseq prems c -> deriv_prseqs prems cs
                                      -> deriv_prseqs prems (c :: cs).

  Definition deriv_rule (r : rule) :=
    match r with (ps, c) => deriv_prseq ps c end.                                                

  Scheme deriv_seq_mut_ind := Minimality for deriv_seq Sort Prop
      with deriv_seqs_mut_ind := Minimality for deriv_seqs Sort Prop.

  Scheme deriv_seq_mut_rect := Minimality for deriv_seq Sort Type
      with deriv_seqs_mut_rect := Minimality for deriv_seqs Sort Type.

  Scheme deriv_prseq_mut_ind := Minimality for deriv_prseq Sort Prop
      with deriv_prseqs_mut_ind := Minimality for deriv_prseqs Sort Prop.

  Scheme deriv_prseq_mut_rect := Minimality for deriv_prseq Sort Type
      with deriv_prseqs_mut_rect := Minimality for deriv_prseqs Sort Type.


  Lemma ForallT_deriv_seqs : forall cs, ForallT deriv_seq cs -> deriv_seqs cs.
  Proof.
    induction cs as [|c cs]; intro Hall; try apply deriv_seqs_nil.
    apply deriv_seqs_cons.
    - apply ForallT_inv in Hall. assumption.
    - apply IHcs. apply ForallT_inv_tail in Hall. assumption.
  Defined.

  Lemma ForallT_deriv_prseqs :
    forall ps cs, ForallT (deriv_prseq ps) cs -> deriv_prseqs ps cs.
  Proof.
    induction cs as [|c cs]; intro Hall; try apply deriv_prseqs_nil.
    apply deriv_prseqs_cons.
    - apply ForallT_inv in Hall. assumption.
    - apply IHcs. apply ForallT_inv_tail in Hall. assumption.
  Defined.


  Lemma deriv_seq_prseq_nil :
    forall c, deriv_seq c <+> deriv_prseq [] c.
  Proof.
    intro c. split.
    - revert c. apply (deriv_seq_mut_rect (deriv_prseq []) (deriv_prseqs [])).
      + intros. apply (deriv_prseq_ext _ ps c r); assumption.
      + apply deriv_prseqs_nil.
      + intros. apply (deriv_prseqs_cons _ c cs); assumption.
    - revert c. apply (deriv_prseq_mut_rect _ deriv_seq deriv_seqs).
      + contradiction.
      + intros. apply (deriv_seq_ext ps c r); assumption.
      + apply deriv_seqs_nil.
      + intros. apply (deriv_seqs_cons c cs); assumption.
  Defined.


  Lemma ForallT_deriv_prseqs_iff :
    forall ps cs, ForallT (deriv_prseq ps) cs <+> deriv_prseqs ps cs.
  Proof.
    intros ps cs. split; try apply ForallT_deriv_prseqs.
    revert cs. apply (deriv_prseqs_mut_rect _ (deriv_prseq ps) (ForallT (deriv_prseq ps))).
    - apply deriv_prseq_prem.
    - intros ss c r Hexr Hwfr Hders Hallders.
      eapply deriv_prseq_ext; eassumption.
    - apply ForallT_nil.
    - intros c cs Hder _ Hders Hallders.
      apply ForallT_cons; assumption.
  Defined.


  Lemma deriv_prseq_weak (ps ps' : list sequent) (c : sequent) :
    ps ⊆ ps' -> deriv_prseq ps c -> deriv_prseq ps' c.
  Proof.
    intro Hinc. revert c.
    apply (deriv_prseq_mut_rect _ (deriv_prseq ps') (deriv_prseqs ps')).
    - intros c Hc. apply deriv_prseq_prem. apply Hinc. assumption.
    - intros cs c r Hexr Hwfr Hders Hders'.
      eapply deriv_prseq_ext; eassumption.
    - apply deriv_prseqs_nil.
    - intros c cs Hder Hder' Hders Hders'.
      eapply deriv_prseqs_cons; assumption.
  Defined.

  Lemma deriv_prseq_tran :
    forall ps ss c, deriv_prseq ss c -> deriv_prseqs ps ss -> deriv_prseq ps c.
  Proof.
    intros ps ss c Hder Hders. revert c Hder.
    apply (deriv_prseq_mut_rect _ (deriv_prseq ps) (deriv_prseqs ps)).
    - intros c Hc. apply ForallT_deriv_prseqs_iff in Hders.
      rewrite ForallT_forall in Hders.
      apply Hders. assumption.
    - intros ts c r Hexr Hwfr Hssders Hpsders.
      eapply deriv_prseq_ext; eassumption.
    - apply deriv_prseqs_nil.
    - intros c cs Hssder Hpsder Hssders Hpsders.
      apply deriv_prseqs_cons; assumption.
  Defined.

  Lemma deriv_prseq_tran_afs :
    forall ps ss c afs, deriv_prseq ss c ->
                   deriv_prseqs ps (map (seqSubst afs) ss) -> deriv_prseq ps (seqSubst afs c).
  Proof.
    intros ps ss c afs Hder Hders. revert c Hder.
    apply (deriv_prseq_mut_rect _ (comp (deriv_prseq ps) (seqSubst afs))
             (comp (deriv_prseqs ps) (map (seqSubst afs)))).
    - intros c Hc. apply ForallT_deriv_prseqs_iff in Hders.
      rewrite ForallT_forall in Hders.
      apply Hders. apply in_map. assumption.
    - intros ts c r Hexr Hwfr Hssders Hpsders.
      eapply deriv_prseq_ext; try eassumption.
      eapply ruleInst_tran; try eassumption.
      exists afs. reflexivity.
    - apply deriv_prseqs_nil.
    - intros c cs Hssder Hpsder Hssders Hpsders.
      apply deriv_prseqs_cons; assumption.
  Defined.

  Lemma deriv_rule_Inst (r r' : rule) :
    ruleInst r r' -> deriv_rule r -> deriv_rule r'.
  Proof.
    intro Hins. apply ruleInst_ruleSubst in Hins.
    destruct Hins as [afs Hafs].
    destruct r as [ps c]. destruct r' as [ps' c'].
    unfold deriv_rule. simpl. injection Hafs.
    intros Heqc' Heqps'. rewrite Heqc', Heqps'.
    clear Hafs Heqc' Heqps' c' ps'. revert c.
    apply (deriv_prseq_mut_rect _
             (fun c => deriv_prseq (map (seqSubst afs) ps) (seqSubst afs c))
             (fun lc => deriv_prseqs (map (seqSubst afs) ps) (map (seqSubst afs) lc))).
    - intros c Hc. apply deriv_prseq_prem.
      apply in_map. assumption.
    - intros ss c r Hexr Hwfr Hders Hders'.
      eapply deriv_prseq_ext; try eassumption.
      eapply ruleInst_tran; try eassumption.
      exists afs. reflexivity.
    - apply deriv_prseqs_nil.
    - intros c cs Hder Hder' Hders Hders'.
      apply deriv_prseqs_cons; assumption.
  Defined.

End Deriv_Mut.


Section Deriv_Mut_More.

  Context `{SL : STRLANG}.

  Lemma deriv_rule_replace (DC1 DC2 : DISPCALC) (r : rule) :
    ForallT (deriv_rule DC2) DC1 -> deriv_rule DC1 r -> deriv_rule DC2 r.
  Proof.
    intro HderDC. destruct r as [ps c]. revert c.
    apply (deriv_prseq_mut_rect _ _ (deriv_prseq DC2 ps) (deriv_prseqs DC2 ps)).
    - apply deriv_prseq_prem.
    - intros ss c r Hexr Hwfr Hders1 Hders2.
      eapply deriv_prseq_tran; try eassumption.
      fold (deriv_rule DC2 (ss, c)). apply (deriv_rule_Inst _ _ _ Hwfr).
      rewrite ForallT_forall in HderDC. apply HderDC.
      assumption.
    - apply deriv_prseqs_nil.
    - intros c cs Hder1 Hder2 Hders1 Hders2.
      apply deriv_prseqs_cons; assumption.
  Defined.

End Deriv_Mut_More.
    


(* Some tactics *)

Ltac destruct_proper H :=
  let Hwfb := fresh "Hwfb" in let Hfrb := fresh "Hfrb" in let Hprems := fresh "Hprems" in
  let Hwfbup := fresh "Hwfbup" in let Hfrbup := fresh "Hfrbup" in
    destruct H as (Hfrb & Hwfb & Hprems); rewrite allDT_Next in Hwfb, Hfrb;
    destruct Hwfb as [Hwfb Hwfbup]; destruct Hfrb as [Hfrb Hfrbup].


Ltac discriminate_Unf dt :=
  let s := fresh "s" in let r := fresh "r" in let l := fresh "l" in
    match goal with
    | [ Hdt : proper _ dt |- _ ] => 
        destruct dt as [|s r l]; try (apply not_proper_Unf in Hdt; tauto)
    end.

Ltac discriminate_Unf_list ld :=
  match ld with
  | ?dt :: ?ldt => discriminate_Unf dt; discriminate_Unf_list ldt
  | [] => idtac
  end.

(*
Ltac destruct_proper_dertree Hval :=
  let Hvalup := fresh "Hvalup" in
  pose proof (properUp Hval) as Hvalup; rewrite Forall_forall in Hvalup;
  let Hwfb := fresh "Hwfb" in
  let Hfrb := fresh "Hfrb" in
  let Hprems := fresh "Hprems" in
  let Hwfbup := fresh "Hwfbup" in
  let Hfrbup := fresh "Hfrbup" in
  let Hval' := fresh "Hval'" in
  pose proof Hval as Hval';
  destruct Hval' as (Hfrb, (Hwfb, Hprems)); rewrite allDT_Next in Hwfb, Hfrb;
  destruct Hwfb as [Hwfb Hwfbup]; destruct Hfrb as [Hfrb Hfrbup];
  let pfs := fresh "pfs" in
  let Hpfs := fresh "Hpfs" in
  destruct (ruleInst_ruleSubst Hwfb) as [pfs Hpfs];
  injection Hpfs; intros;
  (repeat match goal with | H : map conclDT [] = [] |- _ => clear H end);
  match goal with
  | [ _ : map conclDT ?l = [] |- _ ] => destruct l; try discriminate
  | [ H : map conclDT ?l = _ |- _] =>
      let d := fresh "d" in
      destruct_list_easy l d; injection H; intros; unfold nextUp in Hvalup; specialize_list;
      match goal with
      | [ H : map conclDT ?ld = _ |- _] => discriminate_Unf_list ld
      end
  end; repeat
         match goal with
         | [ H : conclDT _ = _ |- _ ] => simpl in H; rewrite H in Hval
         end.
*)
