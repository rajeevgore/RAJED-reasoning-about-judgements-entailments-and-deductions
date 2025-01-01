Require Import String.
Require Import Relations Datatypes.
Require Import List ListDec SetoidList Decidable.
Import ListNotations.
Require Import ListSetNotations.
Require Import Arith.

Require Import Tactics.
Require Import EqDec.
Require Import Utils.
Require Import FunAgree.
Require Import Lang.
Require Import Sequents.
Require Import Substitutions.
Require Import Derivation.

Open Scope list.



Section Cuts.

  Context `{SL : STRLANG}.

  (* The cut rule *)
  Definition CUT : rule := ([SV "X" ⊢ FS (FV "A") ; FS (FV "A") ⊢ SV "Y"],
                             SV "X" ⊢ SV "Y").

  Definition CUT_spec (A : formula) (X Y : structr) :=
    afs_spec [] [("A", A)] [("X", X); ("Y", Y)].

  Definition rootIsAntP (dt : dertree) : Prop :=
    match dt with
    | Unf s     => False
    | Der s r l => strIsFml (antec (conclRule r))
    end.

  Definition rootIsSucP (dt : dertree) : Prop :=
    match dt with
    | Unf s     => False
    | Der s r l => strIsFml (succ (conclRule r))
    end.

  Definition remove_rule := remove rule_eq_dec.

  Definition derLP (rls : list rule) (seq : sequent) :=
    exists dt, proper (remove_rule CUT rls) dt /\ conclDT dt = seq /\ rootIsSucP dt.

  Definition derRP (rls : list rule) (seq : sequent) :=
    exists dt, proper (remove_rule CUT rls) dt /\ conclDT dt = seq /\ rootIsAntP dt.

  (* Restriction of cuts to formulae satisfying a given property *)
  Definition cutOnFmls (P : formula -> Prop) (dt : dertree) : Prop :=
    match dt with
    | Unf s     => True
    | Der s r l => r <> CUT \/
        (exists pl pr Y A, P A /\ l = [pl; pr] /\ conclDT pr = FS A ⊢ Y)
    end.

  Definition nocut (dt : dertree) : Prop :=
    match dt with
    | Unf _     => True
    | Der _ r _ => r <> CUT
    end.

  (* conclusion of dt is either not obtained by cut or
     A is principal (= non-parametric in the conclusion) in the left premises *)
  Definition cutIsLP (A : formula) (dt : dertree) : Prop :=
    match dt with
    | Unf s     => True
    | Der s r l => r <> CUT \/
        (exists X r' l' pr, l = [Der (X ⊢ FS A) r' l'; pr] /\ strIsFml (succ (conclRule r')))
    end.

  (* conclusion of dt is either not obtained by cut or
     A is principal in the right premises *)
  Definition cutIsRP (A : formula) (dt : dertree) : Prop :=
    match dt with
    | Unf s     => True
    | Der s r l => r <> CUT \/
        (exists Y pl r' l', l = [pl ; Der (FS A ⊢ Y) r' l'] /\ strIsFml (antec (conclRule r')))
    end.

  Definition cutIsLRP (A : formula) (dt : dertree) : Prop :=
    cutIsLP A dt /\ cutIsRP A dt.


  Lemma LP_dec : forall (l : list dertree) (A : formula),
    {ant & {r' & {l' & {pr | l = [Der (ant ⊢ FS A) r' l'; pr] /\ strIsFml (succ (conclRule r'))} } } } +
    {forall ant r' l' pr, l <> [Der (ant ⊢ FS A) r' l'; pr] \/ ~ strIsFml (succ (conclRule r'))}.
  Proof.
    intros l A. destruct (list_2_elems_dec l) as [Hl|Hnl];
      try (right; intros; left; apply Hnl).
    destruct Hl as (pl & pr & Heql). destruct pl as [|s' r' l'];
      try (right; intros; left; intro H; rewrite H in Heql; discriminate).
    destruct s' as [X Y]. destruct (eqdec Y (FS A)) as [HeqY|HneqY];
      try (right; intros; left; intro H; contradict HneqY;
           rewrite Heql in H; injection H; tauto).
    rewrite HeqY in Heql. destruct (strIsFml_dec (succ (conclRule r'))) as [Hfml|Hnfml].
    - left. exists X, r', l', pr. tauto.
    - right. intros.
        destruct (list_eq_dec dertree_eq_dec l [Der (ant ⊢ FS A) r'0 l'0; pr0]) as [H|];
        try (now left). rewrite H in Heql. injection Heql. intros _ _ Heqr'0 _.
        rewrite Heqr'0. right. assumption.
  Qed.


  Lemma RP_dec : forall (l : list dertree) (A : formula),
    {suc & {pl & {r' & {l' | l = [pl ; Der (FS A ⊢ suc) r' l'] /\
                               strIsFml (antec (conclRule r'))}}}} +
    {forall suc pl r' l', l <> [pl ; Der (FS A ⊢ suc) r' l'] \/ ~ strIsFml (antec (conclRule r'))}.
  Proof.
    intros l A. destruct (list_2_elems_dec l) as [Hl|Hnl];
      try (right; intros; left; apply Hnl).
    destruct Hl as (pl & pr & Heql). destruct pr as [|s' r' l'];
      try (right; intros; left; intro H; rewrite H in Heql; discriminate).
    destruct s' as [X Y]. destruct (eqdec X (FS A)) as [HeqX|HneqX];
      try (right; intros; left; intro H; contradict HneqX;
           rewrite Heql in H; injection H; tauto).
    rewrite HeqX in Heql. destruct (strIsFml_dec (antec (conclRule r'))) as [Hfml|Hnfml].
    - left. exists Y, pl, r', l'. tauto.
    - right. intros.
        destruct (list_eq_dec dertree_eq_dec l [pl0; Der (FS A ⊢ suc) r'0 l'0]) as [H|];
        try (now left). rewrite H in Heql. injection Heql. intros _ Heqr'0 _ _.
        rewrite Heqr'0. right. assumption.
  Qed.


  Lemma right_cut_dec : forall l : list (dertree),
    {pl & {pr & {suc & {A | l = [pl; pr] /\ conclDT pr = FS A ⊢ suc}}}} +
    {forall pl pr suc A, l <> [pl; pr] \/ conclDT pr <> FS A ⊢ suc}.
  Proof.
    intro l. destruct (list_2_elems_dec l) as [Hl|Hnl]; try (right; intros; left; apply Hnl).
    destruct Hl as (pl & pr & Heql). destruct (conclDT pr) eqn:Heqconcpr.
    destruct (strIsFml_dec X) as [HXfml|HnXfml].
    - left. destruct (strIsFml_sig _ HXfml) as [A HA].
      rewrite HA in Heqconcpr. exists pl, pr, Y, A. tauto.
    - right. intros pl0 pr0 suc A.
      destruct (list_eq_dec dertree_eq_dec [pl0; pr0] [pl; pr]) as [Heqplpr|Hneqplpr];
        try (left; rewrite Heql; intro H; rewrite H in Hneqplpr; contradiction).
      injection Heqplpr. intros Heqpr0 Heqpl0. rewrite Heqpr0, Heqpl0.
      right. rewrite Heqconcpr. intro Hctr. contradict HnXfml.
      injection Hctr. intros _ HeqX. rewrite HeqX. constructor.
  Qed.

  Proposition nocut_dec : forall dt : dertree, {nocut dt} + {~ nocut dt}.
  Proof.
    intro dt. destruct dt.
    - now left.
    - simpl. destruct (rule_eq_dec r CUT).
      + right. intro. contradiction.
      + now left.
  Qed.

  Lemma nocut_impl_cut (fmls : formula -> Prop) : forall dt, nocut dt -> cutOnFmls fmls dt.
  Proof.
    intros dt H. destruct dt; try tauto. simpl in H. now left.
  Qed.

  Lemma nocut_impl_LP [phi : formula] : forall (dt : dertree), nocut dt -> cutIsLP phi dt.
  Proof.
    intros dt H. destruct dt; try tauto. simpl in H. now left.
  Qed.

  Lemma nocut_impl_LRP [phi : formula] : forall (dt : dertree), nocut dt -> cutIsLRP phi dt.
  Proof.
    intros dt H. destruct dt; try (split; tauto). simpl in H. split; now left.
  Qed.

  Lemma nocut_dep_rule [s1 s2 r l1 l2] :
    nocut (Der s1 r l1) -> nocut (Der s2 r l2).
  Proof. auto. Qed.

  Lemma cut_dep_rules (s1 s2 : sequent) (r : rule) (l : list dertree) (fmls : formula -> Prop) :
    cutOnFmls fmls (Der s1 r l) -> cutOnFmls fmls (Der s2 r l).
  Proof. intro H. destruct H; [now left | now right]. Qed.

  Lemma allDT_cut_dep_rules [s1 s2 : sequent] [r : rule] [l : list dertree] [fmls : formula -> Prop] :
    allDT (cutOnFmls fmls) (Der s1 r l) -> allDT (cutOnFmls fmls) (Der s2 r l).
  Proof. intro H. rewrite allDT_Der in H. split; tauto. Qed.


  (* Yet another mutually inductive definition for derivability
     respecting some cutOnFmls *)

  Inductive deriv_cofseq (DC : DISPCALC) (P : formula -> Prop) : sequent -> Type :=
  | deriv_cofseq_ext : forall ps c r, r ∈ DC -> ruleInst r (ps, c)
                         -> r <> CUT \/ (exists sl sr Y A, P A /\ ps = [sl; sr] /\ sr = FS A ⊢ Y)
                         -> deriv_cofseqs DC P ps -> deriv_cofseq DC P c
  with
    deriv_cofseqs (DC : DISPCALC) (P : formula -> Prop) : list sequent -> Type :=
  | deriv_cofseqs_nil : deriv_cofseqs DC P []
  | deriv_cofseqs_cons : forall c cs, deriv_cofseq DC P c -> deriv_cofseqs DC P cs
                                      -> deriv_cofseqs DC P (c :: cs).


  Inductive deriv_cofprseq (DC : DISPCALC) (P : formula -> Prop) (prems : list sequent) : sequent -> Type :=
  | deriv_cofprseq_prem : forall c, c ∈ prems -> deriv_cofprseq DC P prems c
  | deriv_cofprseq_ext : forall ps c r, r ∈ DC -> ruleInst r (ps, c)
                         -> r <> CUT \/ (exists sl sr Y A, P A /\ ps = [sl; sr] /\ sr = FS A ⊢ Y)
                         -> deriv_cofprseqs DC P prems ps -> deriv_cofprseq DC P prems c
  with
    deriv_cofprseqs (DC : DISPCALC) (P : formula -> Prop) (prems : list sequent) : list sequent -> Type :=
  | deriv_cofprseqs_nil : deriv_cofprseqs DC P prems []
  | deriv_cofprseqs_cons : forall c cs, deriv_cofprseq DC P prems c -> deriv_cofprseqs DC P prems cs
                                      -> deriv_cofprseqs DC P prems (c :: cs).


  Scheme deriv_cofseq_mut_ind := Minimality for deriv_cofseq Sort Prop
      with deriv_cofseqs_mut_ind := Minimality for deriv_cofseqs Sort Prop.

  Scheme deriv_cofseq_mut_rect := Minimality for deriv_cofseq Sort Type
      with deriv_cofseqs_mut_rect := Minimality for deriv_cofseqs Sort Type.


  Scheme deriv_cofprseq_mut_ind := Minimality for deriv_cofprseq Sort Prop
      with deriv_cofprseqs_mut_ind := Minimality for deriv_cofprseqs Sort Prop.

  Scheme deriv_cofprseq_mut_rect := Minimality for deriv_cofprseq Sort Type
      with deriv_cofprseqs_mut_rect := Minimality for deriv_cofprseqs Sort Type.

  Definition deriv_ncprseq (DC : DISPCALC) := deriv_cofprseq DC (fun _ => False).

  Lemma ForallT_deriv_cofseqs (DC : DISPCALC) (P : formula -> Prop) :
    forall cs, ForallT (deriv_cofseq DC P) cs -> deriv_cofseqs DC P cs.
  Proof.
    induction cs as [|c cs]; intro Hall; try apply deriv_cofseqs_nil.
    apply deriv_cofseqs_cons.
    - apply ForallT_inv in Hall. assumption.
    - apply IHcs. apply ForallT_inv_tail in Hall. assumption.
  Defined.

  Lemma ForallT_deriv_cofseqs_iff (DC : DISPCALC) (P : formula -> Prop) :
    forall cs, ForallT (deriv_cofseq DC P) cs <+> deriv_cofseqs DC P cs.
  Proof.
    intros cs. split; try apply ForallT_deriv_cofseqs.
    revert cs. apply (deriv_cofseqs_mut_rect _ _ (deriv_cofseq DC P)
                                                 (ForallT (deriv_cofseq DC P))).
    - intros ps c r Hexr Hwfr Hcof Hders Hall.
      eapply deriv_cofseq_ext; eassumption.
    - apply ForallT_nil.
    - intros c cs Hder _ Hders Hallders.
      apply ForallT_cons; assumption.
  Defined.

  Lemma ForallT_deriv_cofprseqs (DC : DISPCALC) (P : formula -> Prop) (ps : list sequent) :
    forall cs, ForallT (deriv_cofprseq DC P ps) cs -> deriv_cofprseqs DC P ps cs.
  Proof.
    induction cs as [|c cs]; intro Hall; try apply deriv_cofprseqs_nil.
    apply deriv_cofprseqs_cons.
    - apply ForallT_inv in Hall. assumption.
    - apply IHcs. apply ForallT_inv_tail in Hall. assumption.
  Defined.


  Lemma deriv_cofseq_iff (DC : DISPCALC) (P : formula -> Prop) :
    forall s, deriv_cofseq DC P s <+>
         {d : dertree | proper DC d /\ conclDT d = s /\ allDT (cutOnFmls P) d}.
  Proof.
    intro s. split.
    - revert s.
      apply (deriv_cofseq_mut_rect DC P
               (fun s => {d : dertree | proper DC d /\ conclDT d = s /\ allDT (cutOnFmls P) d})
               (fun ls => {ld : list dertree | Forall (proper DC) ld /\
                                             map conclDT ld = ls /\
                                             Forall (allDT (cutOnFmls P)) ld})).
      + intros ps c r Hexr Hwfr Hcof Hders [ld [Hprold [Hconcld Hcofld]]].
        exists (Der c r ld). split; [|split].
        * apply proper_Der; try assumption. rewrite Hconcld. assumption.
        * reflexivity.
        * rewrite allDT_Der. rewrite allDTs_Forall. split; [|assumption].
          simpl. destruct (eqdec r CUT) as [Heqr|Hneqr]; [|left; assumption].
          right. destruct Hcof as [Hcof|Hcof]; [contradiction|].
          destruct Hcof as (sl & sr & Y & [A [PA [Heqps Heqsr]]]).
          rewrite Heqps in Hconcld. destruct_list_easy ld d.
          injection Hconcld. intros Heqd0 Heqd. rewrite Heqsr in Heqd0.
          exists d, d0, Y, A. repeat split; assumption.
      + exists []. repeat split; apply Forall_nil.
      + intros c cs Hder [d [Hprod [Hconcd Hcofd]]] Hders [ld [Hprold [Hconcld Hcofld]]].
        exists (d :: ld). repeat split.
        * apply Forall_cons; assumption.
        * simpl. rewrite Hconcd, Hconcld. reflexivity.
        * apply Forall_cons; assumption.
    - intros [d [Hprod [Hconcd Hcofd]]]. rewrite <- Hconcd.
      clear s Hconcd. induction d as [|s r l IH];
        [exfalso; apply (not_proper_Unf _ Hprod)|].
      pose proof (properUp Hprod) as Hprol.
      pose proof (allDTUp Hcofd) as Hcofl.
      simpl in Hprol, Hcofl |- *.
      apply Forall_ForallT in Hprol, Hcofl.
      apply (ForallT_mp Hprol), (ForallT_mp Hcofl) in IH.
      apply ForallT_map, ForallT_deriv_cofseqs in IH.
      eapply deriv_cofseq_ext; try apply Hprod; try assumption.
      apply allDT_root in Hcofd.
      destruct (eqdec r CUT) as [Heqr|Hneqr]; [|left; assumption].
      right. destruct Hcofd as [Hcofd|Hcofd]; [contradiction|].
      destruct Hcofd as (dl & dr & Y & [A [PA [Heql Heqdr]]]).
      exists (conclDT dl), (conclDT dr), Y, A. repeat split; try assumption.
      rewrite Heql. reflexivity.
  Defined.


  Lemma deriv_cofseqs_iff (DC : DISPCALC) (P : formula -> Prop) :
    forall ls, deriv_cofseqs DC P ls <+>
         {ld : list dertree | Forall (proper DC) ld /\ map conclDT ld = ls /\
                              Forall (allDT (cutOnFmls P)) ld}.
  Proof.
    intro ls. split.
    - revert ls.
      apply (deriv_cofseqs_mut_rect DC P
               (fun s => {d : dertree | proper DC d /\ conclDT d = s /\ allDT (cutOnFmls P) d})
               (fun ls => {ld : list dertree | Forall (proper DC) ld /\
                                             map conclDT ld = ls /\
                                             Forall (allDT (cutOnFmls P)) ld})).
      + intros ps c r Hexr Hwfr Hcof Hders [ld [Hprold [Hconcld Hcofld]]].
        exists (Der c r ld). split; [|split].
        * apply proper_Der; try assumption. rewrite Hconcld. assumption.
        * reflexivity.
        * rewrite allDT_Der. rewrite allDTs_Forall. split; [|assumption].
          simpl. destruct (eqdec r CUT) as [Heqr|Hneqr]; [|left; assumption].
          right. destruct Hcof as [Hcof|Hcof]; [contradiction|].
          destruct Hcof as (sl & sr & Y & [A [PA [Heqps Heqsr]]]).
          rewrite Heqps in Hconcld. destruct_list_easy ld d.
          injection Hconcld. intros Heqd0 Heqd. rewrite Heqsr in Heqd0.
          exists d, d0, Y, A. repeat split; assumption.
      + exists []. repeat split; apply Forall_nil.
      + intros c cs Hder [d [Hprod [Hconcd Hcofd]]] Hders [ld [Hprold [Hconcld Hcofld]]].
        exists (d :: ld). repeat split.
        * apply Forall_cons; assumption.
        * simpl. rewrite Hconcd, Hconcld. reflexivity.
        * apply Forall_cons; assumption.
    - intros [ld [Hprold [Hconcld Hcofld]]].
      apply ForallT_deriv_cofseqs_iff.
      eapply ForallT_act. intro s. apply deriv_cofseq_iff.
      apply ForallT_forall. intros s Hs.
      rewrite <- Hconcld in Hs. apply in_map_inv_sig in Hs.
      destruct Hs as [d [Hconcd Hd]].
      rewrite Forall_forall in Hprold, Hcofld.
      exists d. split; [|split]; try apply Hprold; try apply Hcofld; assumption.
  Defined.

  Lemma deriv_cofprseq_weak (DC : DISPCALC) (P : formula -> Prop) (ps ps' : list sequent) (c : sequent) :
    ps ⊆ ps' -> deriv_cofprseq DC P ps c -> deriv_cofprseq DC P ps' c.
  Proof.
    intro Hinc. revert c.
    apply (deriv_cofprseq_mut_rect _ _ _ (deriv_cofprseq DC P ps') (deriv_cofprseqs DC P ps')).
    - intros c Hc. apply deriv_cofprseq_prem. apply Hinc. assumption.
    - intros cs c r Hexr Hwfr Hcof Hders Hders'.
      eapply deriv_cofprseq_ext; eassumption.
    - apply deriv_cofprseqs_nil.
    - intros c cs Hder Hder' Hders Hders'.
      eapply deriv_cofprseqs_cons; assumption.
  Defined.

  Lemma deriv_ncprseq_impl_deriv_cofprseq (DC : DISPCALC) (P : formula -> Prop) (ps : list sequent) (c : sequent) :
    deriv_ncprseq DC ps c -> deriv_cofprseq DC P ps c.
  Proof.
    revert c.
    apply (deriv_cofprseq_mut_rect _ _ _ (deriv_cofprseq DC P ps) (deriv_cofprseqs DC P ps)).
    - intros c Hc. apply deriv_cofprseq_prem. assumption.
    - intros ss c r Hexr Hwfr Hnc Hdersnc Hders.
      eapply deriv_cofprseq_ext; try eassumption.
      destruct Hnc as [Hneqr|HF]; [now left|].
      right. destruct HF as (sl & sr & Y & A & H). tauto.
    - apply deriv_cofprseqs_nil.
    - intros. apply deriv_cofprseqs_cons; assumption.
  Defined.

  Lemma deriv_cofseq_tran_afs (DC : DISPCALC) (P : formula -> Prop) (ps : list sequent) (c : sequent) (afs : afsSubst) :
    deriv_ncprseq DC ps c
    -> deriv_cofseqs DC P (map (seqSubst afs) ps) -> deriv_cofseq DC P (seqSubst afs c).
  Proof.
    intros Hder Hders. revert c Hder.
    apply (deriv_cofprseq_mut_rect _ _ _ (comp (deriv_cofseq DC P) (seqSubst afs))
             (comp (deriv_cofseqs DC P) (map (seqSubst afs)))).
    - intros c Hc. apply ForallT_deriv_cofseqs_iff in Hders.
      rewrite ForallT_forall in Hders.
      apply Hders. apply in_map. assumption.
    - intros ss c r Hexr Hwfr Hcof Hpsders Hssders.
      apply (deriv_cofseq_ext _ _ (map (seqSubst afs) ss) _ r);
      try assumption.
      eapply ruleInst_tran; try eassumption.
      exists afs. reflexivity.
      destruct Hcof as [Hneqr|[sl [sr [Y [A HP]]]]]; [now left|tauto].
    - apply deriv_cofseqs_nil.
    - intros. apply deriv_cofseqs_cons; assumption.
  Defined.


  (* Belnap conditions *)

  Section BelnapConditions.

    Variable DC : DISPCALC.

    Definition isipsubfml (A B : formula) : Prop := B ∈ (ipse A).

    Definition C1_one (r : rule) : Prop :=
      Forall (fun s => incl (seqFmls s) (listsubexprs (seqFmls (conclRule r))) /\
                    incl (seqSVs s) (seqSVs (conclRule r))) (premsRule r).

    Definition C3_one (r : rule) : Prop := NoDup (seqSVs (conclRule r)).

    Definition C4_one (r : rule) : Prop :=
      forall p b s, p ∈ premsRule r ->
               s ∈ seqSVsSgn (conclRule r) b ->
               s ∉ seqSVsSgn p (negb b).

    Definition C5_one (r : rule) : Prop := seqNoSSF (conclRule r).

    Definition bprops (r : rule) : Prop := C3_one r /\ C4_one r /\ C5_one r.

    Definition C345 : Prop := forall r, r ∈ DC -> bprops r.

    Definition C1 : Prop :=
      forall r, r ∈ DC ->
      Forall (fun s => seqFmls s ⊆ listsubexprs (seqFmls (conclRule r)) /\
                    seqSVs s ⊆ seqSVs (conclRule r)) (premsRule r).
    Definition C3 : Prop := forall r, r ∈ DC -> NoDup (seqSVs (conclRule r)).
    Definition C4 : Prop :=
      forall r, r ∈ DC ->
      forall p b s, p ∈ premsRule r ->
               s ∈ seqSVsSgn (conclRule r) b ->
               s ∉ seqSVsSgn p (negb b).
    Definition C5 : Prop :=
      forall r, r ∈ DC ->
      match (conclRule r) with
        X ⊢ Y => (strIsFml X \/ ~ strCtnsFml X) /\ (strIsFml Y \/ ~ strCtnsFml Y)
      end.
    Definition C8 : Type :=
      forall M dt, proper DC dt -> cutIsLRP M dt -> allNextDTs nocut dt ->
              {dt' | proper DC dt' /\ conclDT dt' = conclDT dt /\
                     allDT (cutOnFmls (isipsubfml M)) dt'}.
 
  End BelnapConditions.
  
  Lemma str_fmls_subst_iff : forall X afs A,
    A ∈ strFmls (strSubst afs X) <->
      A ∈ map (fmlSubst (fst afs)) (strFmls X) \/
      A ∈ fold_right (fun x => app (strFmls (snd afs x))) [] (strSVs X).
  Proof.
    intro X. pattern X. revert X. apply ipse_rect.
    intros X IH afs A. rewrite strSubst_eq, (strFmls_eq X), (strSVs_eq X).
    destruct (Var_dec SV X) as [[v Hv]|HnSV];
      destruct (Var_dec FS X) as [[B HB]|HnFS].
    - rewrite Hv in HB. contradict HB. apply SV_FS_disc.
    - simpl. rewrite app_nil_r. rewrite Hv.
      rewrite (Var_ipse SV). simpl. tauto.
    - rewrite strFmls_FS, HB, (Var_ipse FS). simpl. tauto.
    - rewrite strFmls_eq. rewrite Var_dec_not_Var.
      2:{ apply (not_Var_conn FS); try assumption. apply map_length. }
      rewrite ipse_conn; try apply map_length.
      split.
      + intro H. apply In_fold_right_app in H.
        destruct H as [Y' [HinY' HY']].
        apply in_map_iff in HinY'. destruct HinY' as [X' [HeqY' HX']].
        rewrite <- HeqY' in HY'. apply IH in HY'.
        destruct HY' as [HY'|HY'].
        * left. apply in_map_iff in HY'.
          destruct HY' as [B [HeqA HB]].
          apply in_map_iff. exists B. split; [assumption|].
          apply In_fold_right_app_iff. exists X'. tauto.
        * right. apply In_fold_right_app_iff in HY'.
          destruct HY' as [v [Hinv Hv]].
          apply In_fold_right_app_iff. exists v. split; [|assumption].
          apply In_fold_right_app_iff. exists X'. tauto.
        * assumption.
      + intros [H|H].
        * apply in_map_iff in H. destruct H as [B [HeqA HB]].
          apply In_fold_right_app_iff in HB. destruct HB as [X' [HX' HB]].
          apply In_fold_right_app_iff. exists (strSubst afs X'). split.
         -- apply in_map_iff. exists X'. tauto.
         -- apply IH; try assumption.
            left. apply in_map_iff. exists B. tauto.
        * apply In_fold_right_app_iff in H.
          destruct H as [v [Hv HA]].
          apply In_fold_right_app_iff in Hv.
          destruct Hv as [X' [HX' Hv]].
          apply In_fold_right_app_iff.
          exists (strSubst afs X'). split.
         -- apply in_map_iff. exists X'. tauto.
         -- apply IH; try assumption.
            right. apply In_fold_right_app_iff. exists v. tauto.
  Qed.

  Lemma seq_fmls_subst_iff : forall s afs A,
    A ∈ seqFmls (seqSubst afs s) <->
      A ∈ map (fmlSubst (fst afs)) (seqFmls s) \/
      A ∈ fold_right (fun x => app (strFmls (snd afs x))) [] (seqSVs s).
  Proof.
    intros s afs v. destruct s. unfold seqFmls, seqSVs. simpl.
    rewrite in_app_iff. repeat rewrite str_fmls_subst_iff.
    repeat rewrite map_app. repeat rewrite In_fold_right_app_iff.
    repeat setoid_rewrite in_app_iff.
    split.
    - intros [[H|H]|[H|H]]; try tauto;
        try (destruct H as [V [H H0]]; right; exists V; tauto).
    - intros [[H|H]|H]; try tauto.
      destruct H as [V [[H|H] H0]]. left. right. exists V. tauto.
      right. right. exists V. tauto.
  Qed.

  Lemma str_SVs_subst_iff : forall X afs v,
    v ∈ strSVs (strSubst afs X) <->
    v ∈ fold_right (fun x => app (strSVs (snd afs x))) [] (strSVs X).
  Proof.
    intro X. pattern X. revert X. apply ipse_rect.
    intros X IH afs v. rewrite strSubst_eq, (strSVs_eq X).
    destruct (Var_dec SV X) as [[w Hw]|HnSV];
      destruct (Var_dec FS X) as [[A HA]|HnFS].
    - rewrite Hw in HA. contradict HA. apply SV_FS_disc.
    - simpl. rewrite app_nil_r. tauto.
    - rewrite strSVs_FS, HA, (Var_ipse FS). simpl. tauto.
    - rewrite strSVs_eq. rewrite Var_dec_not_Var.
      2:{ apply (not_Var_conn SV); [apply map_length|assumption]. }
      rewrite ipse_conn; try apply map_length.
      split.
      + intro H. apply In_fold_right_app_iff in H.
        destruct H as [Y' [HY' Hv]].
        apply in_map_iff in HY'. destruct HY' as [X' [HeqY' HX']].
        rewrite <- HeqY' in Hv. apply IH in Hv; try assumption.
        apply In_fold_right_app_iff in Hv.
        destruct Hv as [w [Hw Hv]].
        apply In_fold_right_app_iff. exists w. split; try assumption.
        apply In_fold_right_app_iff. exists X'. tauto.
      + intro H. apply In_fold_right_app_iff in H.
        destruct H as [w [Hw Hv]].
        apply In_fold_right_app_iff in Hw.
        destruct Hw as [X' [Hx' Hw]].
        apply In_fold_right_app_iff.
        exists (strSubst afs X'). split.
        * apply in_map_iff. exists X'. tauto.
        * apply IH; try assumption.
          apply In_fold_right_app_iff. exists w. tauto.
  Qed.

  Lemma seq_SVs_subst_iff : forall s pfs v,
    v ∈ seqSVs (seqSubst pfs s) <->
    v ∈ fold_right (fun x => app (strSVs (snd pfs x))) [] (seqSVs s).
  Proof.
    intros s pfs v. destruct s. unfold seqSVs. simpl.
    rewrite in_app_iff.
    repeat rewrite str_SVs_subst_iff.
    repeat rewrite In_fold_right_app_iff.
    setoid_rewrite in_app_iff. split.
    - intro H. destruct H; destruct H as [x Hx]; exists x; tauto.
    - intro H. destruct H as [x [[Hx|Hx] Hv]]; [left | right]; exists x; tauto.
  Qed.

  Lemma C1_ruleInst : forall r r', ruleInst r r' -> C1_one r -> C1_one r'.
  Proof.
    intros r r' Hr' HC1. destruct Hr' as [pfs Hpfs]. unfold C1_one in HC1 |- *.
    rewrite Forall_forall in HC1 |- *.
    rewrite Hpfs, premsRule_ruleSubst, conclRule_ruleSubst.
    intros s Hins. rewrite in_map_iff in Hins.
    destruct Hins as [t [Heqs Hint]]. rewrite <- Heqs.
    specialize (HC1 t Hint). destruct HC1 as [Hfmls HSVs]. split.
    - intros A HinA. apply seq_fmls_subst_iff in HinA.
      unfold listsubexprs. apply In_fold_right_app_iff.
      destruct HinA as [HinA|HinA].
      + rewrite in_map_iff in HinA. destruct HinA as [B [HeqA HinB]].
        apply Hfmls in HinB. unfold listsubexprs in HinB.
        apply In_fold_right_app_iff in HinB.
        destruct HinB as [C [HinC HinB]].
        set (D := fmlSubst (fst pfs) C). exists D. split.
        * apply seq_fmls_subst_iff. left. apply in_map. assumption.
        * rewrite <- HeqA. apply In_subexprs_subst. assumption.
      + rewrite In_fold_right_app_iff in HinA.
        destruct HinA as [v [Hinv HinA]].
        apply HSVs in Hinv. exists A. split.
        * apply seq_fmls_subst_iff. right.
          rewrite In_fold_right_app_iff. exists v. tauto.
        * apply subexprs_refl.
    - intro v. repeat (rewrite seq_SVs_subst_iff, In_fold_right_app_iff).
      intro Hinv. destruct Hinv as [w [Hinw Hinv]].
      apply HSVs in Hinw. exists w. tauto.
  Qed.

  
  (* strrep X Y b X' Y' iff Y' can be obtained from X' by replacing some instances of
     X with sign b in X' by Y (possibly 0, possibly all of them) *)
  Inductive strrep (X Y : structr) : bool -> structr -> structr -> Prop :=
  | strrep_same : forall b Z, strrep X Y b Z Z
  | strrep_two : strrep X Y true X Y
  | strrep_conn : forall b Z l, length (ipse Z) = length l ->
                           (forall t, t ∈ zip pair (zip pair (sgnips Z) (ipse Z)) l ->
                           strrep X Y (nxorb b (fst (fst t))) (snd (fst t)) (snd t)) ->
                           strrep X Y b Z (conn Z l).

  Inductive seqrep (X Y : structr) (b : bool) : sequent -> sequent -> Prop :=
  | seqrep_intr : forall X0a Y0a X0s Y0s, strrep X Y (negb b) X0a Y0a -> strrep X Y b X0s Y0s ->
                                 seqrep X Y b (X0a ⊢ X0s) (Y0a ⊢ Y0s).

  Inductive seqreps (X Y : structr) (b : bool) : list sequent -> list sequent -> Prop :=
  | seqreps_nil  : seqreps X Y b [] []
  | seqreps_cons : forall X0 Y0 X0l Y0l, seqrep X Y b X0 Y0 -> seqreps X Y b X0l Y0l ->
                                seqreps X Y b (X0 :: X0l) (Y0 :: Y0l).


  Lemma strrep_conn_inv (X Y Z W : structr) (b : bool) :
    strrep X Y b Z W -> Z <> W -> (Z, W) <> (X, Y) ->
    conn Z = conn W /\ length (ipse Z) = length (ipse W) /\
      forall t, t ∈ zip pair (zip pair (sgnips Z) (ipse Z)) (ipse W) ->
           strrep X Y (nxorb b (fst (fst t))) (snd (fst t)) (snd t).
  Proof.
    intros Hrep HneqZ HneqZW. inversion Hrep; [| |split; [|split]].
    - contradiction.
    - rewrite H0, H1 in HneqZW. contradiction.
    - rewrite conn_conn; [reflexivity|].
      apply eq_sym. assumption.
    - rewrite ipse_conn; try (apply eq_sym; assumption). assumption.
    - rewrite ipse_conn; try (apply eq_sym; assumption). assumption.
  Qed.


  Lemma seqrep_same_ant [A Y UA VA UY VY] :
    seqrep (FS A) Y true (UA ⊢ VA) (UY ⊢ VY) -> UA = FS A -> UA = UY.
  Proof.
    intros Hseqrep HeqUA. rewrite HeqUA in Hseqrep.
    inversion Hseqrep. inversion H2. assumption.
    rewrite HeqUA.
    rewrite (conn_ipse (FS A)) at 1.
    rewrite (Var_ipse FS) in H5 |- *. destruct l;
      try discriminate. reflexivity.
  Qed.

  Lemma seqrep_trans_suc [A Y UA VA UY VY] :
    seqrep (FS A) Y true (UA ⊢ VA) (UY ⊢ VY) -> VA = FS A -> VA <> VY -> VY = Y.
  Proof.
    intros Hsrep HeqVA HneqVA. rewrite HeqVA in Hsrep.
    inversion Hsrep. inversion H4. rewrite HeqVA, <- H7 in HneqVA.
    contradiction. reflexivity. contradict HneqVA.
    rewrite HeqVA, <- H9.
    rewrite (conn_ipse (FS A)) at 1.
    rewrite (Var_ipse FS) in H5 |- *. destruct l;
      try discriminate. reflexivity.
  Qed.

  Lemma seqrep_same_suc [A Y UA VA UY VY] :
    seqrep (FS A) Y false (UA ⊢ VA) (UY ⊢ VY) -> VA = FS A -> VA = VY.
  Proof.
    intros Hseqrep HeqVA. rewrite HeqVA in Hseqrep.
    inversion Hseqrep. inversion H4. assumption.
    rewrite HeqVA.    
    rewrite (conn_ipse (FS A)) at 1.
    rewrite (Var_ipse FS) in H5 |- *. destruct l;
      try discriminate. reflexivity.
  Qed.

  Lemma seqrep_trans_ant [A Y UA VA UY VY] :
    seqrep (FS A) Y false (UA ⊢ VA) (UY ⊢ VY) -> UA = FS A -> UA <> UY -> UY = Y.
  Proof.
    intros Hsrep HeqUA HneqUA. rewrite HeqUA in Hsrep.
    inversion Hsrep. inversion H2. rewrite HeqUA, <- H7 in HneqUA.
    contradiction. reflexivity. contradict HneqUA.
    rewrite HeqUA, <- H9.
    rewrite (conn_ipse (FS A)) at 1.
    rewrite (Var_ipse FS) in H5 |- *. destruct l;
      try discriminate. reflexivity.
  Qed.

  Lemma seqreps_forall {A : Type} {l : list A} {X Y pn f g} :
    seqreps X Y pn (map f l) (map g l) <->
      Forall (fun a => seqrep X Y pn (f a) (g a)) l.
  Proof.
    induction l.
    - split; intro; constructor.
    - simpl. split.
      + intro H. inversion H. constructor; try assumption.
        apply IHl. assumption.
      + intro H. inversion H. constructor; try assumption.
        apply IHl. assumption.
  Qed.

  Lemma seqrep_strrep {X Y pn ant1 suc1 ant2 suc2} :
    seqrep X Y pn (ant1 ⊢ suc1) (ant2 ⊢ suc2) ->
      strrep X Y (negb pn) ant1 ant2 /\ strrep X Y pn suc1 suc2.
  Proof.
    intro H. inversion H. tauto.
  Qed.

  Lemma strrepFmlEq {b A Y B Z} :
    strrep (FS A) Y b (FS B) Z ->
    (B = A /\ Z = Y /\ b = true) \/ Z = FS B.
  Proof.
    intro H. inversion H.
    - right. reflexivity.
    - left. apply (Var_inj FS), eq_sym in H2. tauto.
    - right.
      rewrite (conn_ipse (FS B)) at 2.
      rewrite (Var_ipse FS) in H0 |- *. destruct l;
      try discriminate. reflexivity.
  Qed.


  Definition defSubs (ls : list string) (sub1 sub2 : @sSubst structr) : sSubst :=
    fun s => if (in_dec string_dec s ls) then sub1 s else sub2 s.

  Lemma defSubs_norm {af : @afSubst formula} {s1 s2 : @sSubst structr} {seq : sequent} :
    seqSubst (af, defSubs (seqSVs seq) s1 s2) seq = seqSubst (af, s1) seq.
  Proof.
    destruct af as [a f]. apply seqSubst_fun_agree_iff. repeat split.
    intros x Hx. unfold defSubs.
    destruct (in_dec string_dec x (seqSVs seq)); [reflexivity | contradiction].
  Qed.

  Lemma defSubs_agree_sub1 {l sub1 sub2} :
    fun_agree (defSubs l sub1 sub2) sub1 l.
  Proof.
    intros x Hx. unfold defSubs.
    destruct (in_dec string_dec x l); [reflexivity | contradiction].
  Qed.

  Lemma defSubs_agree_sub2 {l sub1 sub2} :
    forall p, p ∉ l -> defSubs l sub1 sub2 p = sub2 p.
  Proof.
    intros x Hx. unfold defSubs.
    destruct (in_dec string_dec x l); [contradiction | reflexivity].
  Qed.

  Definition sSubstfor (af : afSubst) (concl conclY : sequent) :=
  {sub : sSubst | seqSubst (af, sub) concl = conclY}.

  Definition stepSub (afs : afsSubst) (concl conclY : sequent)
    (ssub : sSubstfor (fst afs) concl conclY) : afsSubst :=
    match afs with (af, suba) => (af, defSubs (seqSVs concl) (proj1_sig ssub) suba) end.

  Lemma stepSub_norm {afs concl conclY ssub} :
    seqSubst (stepSub afs concl conclY ssub) concl = conclY.
  Proof.
    unfold stepSub. destruct ssub as [sub Hsub]. destruct afs as [ [p f] s]. simpl.
    rewrite <- Hsub. apply defSubs_norm.
  Qed.



  (* If two structures have distinct structure variables and do not contain
     any formula, then there is always a substitution that fills the roles of
     two distinct substitutions for the two structures. *)
  Lemma comSub_ie [pat1 pat2 new1 new2 : structr] [af : afSubst] [sub1 sub2 : sSubst] :
    distinct (strSVs pat1) (strSVs pat2) ->
    strSubst (af, sub1) pat1 = new1 -> strSubst (af, sub2) pat2 = new2 ->
      {suby | strSubst (af, suby) pat1 = new1 /\ strSubst (af, suby) pat2 = new2}.
  Proof.
    intros empty subeq1 subeq2.
    rewrite <- subeq1, <- subeq2.
    exists (defSubs (strSVs pat1) sub1 sub2). destruct af as [p f].
    split; apply strSubst_fun_agree_iff; repeat split.
    - apply defSubs_agree_sub1.
    - intros V HV. apply defSubs_agree_sub2. contradict HV. apply empty. assumption.
  Qed.

  (* Same thing but for an arbitrarily finite number of structures. *)
  Lemma comSubn (lXY : list (structr * structr)) (ls : list sSubst) (af : afSubst) :
    distinct_all (map (comp strSVs fst) lXY) ->
    Forall2 (fun XY s => strSubst (af, s) (fst XY) = (snd XY)) lXY ls ->
      {S : sSubst | Forall (fun XY => strSubst (af, S) (fst XY) = (snd XY)) lXY}.
  Proof.
    revert ls. induction lXY as [|XY lXY];
      [exists (fun _ => SV ""); apply Forall_nil|].
    intros ls Hdist Hall2. simpl in Hdist.
    unfold comp in Hdist at 1. simpl in Hdist.
    apply NoDupA_cons_inv in Hdist.
    destruct Hdist as [HnInA Hdist].
    pose proof (Forall2_length Hall2) as Hlen.
    destruct ls as [|s ls]; try discriminate.
    apply Forall2_cons_iff in Hall2.
    destruct Hall2 as [Heq Hall2].
    destruct XY as [X' Y']. simpl in *.
    destruct (IHlXY ls) as [s' Hs']; try assumption.
    exists (fun x => if in_dec eqdec x (list_union lXY (comp strSVs fst))
             then s' x else s x).
    apply Forall_cons.
    - simpl. destruct af as [a f].
      rewrite <- Heq. apply strSubst_fun_agree_iff.
      split; [|split]; try apply fun_agree_refl.
      intros x Hx. destruct (in_dec string_dec x
        (list_union lXY (comp strSVs fst))) as [Hin|Hnin]; try reflexivity.
      rewrite union_map in Hin. apply In_union in Hin.
      destruct Hin as [l [Hl Hxl]].
      contradict HnInA. apply InA_alt.
      exists l. split; try assumption. exists x. tauto.
    - apply Forall_forall. intros [X Y] HinXY. simpl.
      rewrite Forall_forall in Hs'.
      specialize (Hs' (X, Y) HinXY). simpl in Hs'.
      rewrite <- Hs'. destruct af as [a f].
      apply strSubst_fun_agree_iff.
      split; [|split]; try apply fun_agree_refl.
      intros x Hx. destruct (in_dec string_dec x
        (list_union lXY (comp strSVs fst))) as [Hin|Hnin]; try reflexivity.
      contradict Hnin. apply In_union_iff.
      exists (X, Y). split; assumption.
  Defined.
                          

  Lemma SF_str_sub [A : formula] [X Y : structr] [af : afSubst] [s : sSubst] :
    ~ strCtnsFml X -> NoDup (strSVs X) ->
    forall b Z, strrep (FS A) Y b (strSubst (af, s) X) Z ->
      {s' | strSubst (af, s') X = Z}.
  Proof.
    pattern X. revert X. apply ipse_rect.
    intros X IH HnoFml HND b Z Hrep.
    destruct (eqdec (strSubst (af, s) X) Z) as [HeqZ|HneqZ];
      [|destruct (eqdec (strSubst (af, s) X, Z) (FS A, Y)) as [HeqXZ|HneqXZ];
        [rewrite strSubst_eq in Hrep, HeqXZ;
         destruct (Var_dec SV X) as [[v Hv]|HnSV];
         [|destruct (Var_dec FS X) as [[B HB]|HnFS]] |
        rewrite strSubst_eq in Hrep, HneqZ, HneqXZ;
        rewrite strSVs_eq in HND;
         destruct (Var_dec SV X) as [[v Hv]|HnSV];
         [|destruct (Var_dec FS X) as [[B HB]|HnFS]]]].
    - exists s. assumption.
    - exists (fun _ => Z). rewrite Hv, strSubst_eq.
      rewrite Var_dec_Var. reflexivity.
    - contradict HnoFml. rewrite HB. apply CtnsVar_isVar.
    - injection HeqXZ. intros HeqZ HeqX.
      rewrite conn_ipse in HeqX.
      apply conn_inj in HeqX; try apply map_length; try reflexivity.
      destruct HeqX as [Heqconn Heqipse].
      rewrite (Var_ipse FS) in Heqipse.
      contradict HnoFml. rewrite conn_ipse.
      rewrite Heqconn. destruct (ipse X); try discriminate.
      rewrite <- (Var_ipse FS A), <- conn_ipse. apply CtnsVar_isVar.
    - exists (fun _ => Z). rewrite Hv, strSubst_eq.
      rewrite Var_dec_Var. reflexivity.
    - contradict HnoFml. rewrite HB. apply CtnsVar_isVar.
    - apply strrep_conn_inv in Hrep; try assumption.
      destruct Hrep as [Heqconn [Hlen Hrep]].
      rewrite conn_conn in Heqconn; try apply map_length.
      rewrite ipse_conn in Hlen; try apply map_length.
      rewrite map_length in Hlen.
      rewrite sgnips_conn, ipse_conn in Hrep; try apply map_length.
      assert (ForallT (fun X'Z' => {s' | strSubst (af, s') (fst X'Z') = snd X'Z'})
                      (zip pair (ipse X) (ipse Z))) as Hall.
      { apply ForallT_forall. intros [X' Z'] HinX'Z'.
        pose proof (in_zip_pair_fst HinX'Z') as HinX'. simpl in HinX'.
        apply (zip_pair_in_map_l (strSubst (af, s))) in HinX'Z'.
        apply (in_zip_pair_23_sig_1 (sgnips X)) in HinX'Z';
          try rewrite map_length; try apply sgnips_length; try assumption.
        destruct HinX'Z' as [b' Hin].
        specialize (Hrep _ Hin). simpl in Hrep.
        simpl. apply IH with (nxorb b b').
        - assumption.
        - contradict HnoFml. apply (CtnsVar_inips _ _ X'); assumption.
        - apply (NoDup_union _ _ X') in HND; assumption.
        - assumption. }        
      apply ForallT_sig_elim in Hall.
      destruct Hall as [ls Hls]. apply comSubn in Hls.
      + destruct Hls as [S HS]. exists S. rewrite strSubst_eq.
        rewrite (Var_dec_not_Var SV), (Var_dec_not_Var FS); try assumption.
        rewrite Heqconn. rewrite conn_ipse. apply f_equal.
        apply Forall_zip_pair_map_fst, Forall_eq_zip_pair in HS;
          try apply map_length; try assumption;
          try (rewrite map_length; assumption).
      + unfold comp. rewrite <- map_map, map_fst_zip_pair; try assumption.
        apply NoDup_union_distinct. assumption.
  Defined.

  Lemma exSub [A : formula] [pat Y stra stry : structr] [af : afSubst] [suba : sSubst] [pn : bool] :
      ~ (strCtnsFml pat) ->
      strSubst (af, suba) pat = stra -> NoDup (strSVs pat) ->
      strrep (FS A) Y pn stra stry ->
        {suby | strSubst (af, suby) pat = stry}.
  Proof.
    intros. rewrite <- H0 in H2. apply (SF_str_sub H H1 _ _ H2).
  Qed.

  Lemma seqExSub1 {pat seqa seqy af suba pn A Y} :
    ~ (seqCtnsFml pat) -> seqSubst (af, suba) pat = seqa ->
    NoDup (seqSVs pat) -> seqrep (FS A) Y pn seqa seqy ->
      sSubstfor af pat seqy.
  Proof.
    intros Hnctsfml Hsubst Hnodup Hseqrep.
    destruct pat as [pant psuc]. destruct seqa as [aant asuc]. destruct seqy as [yant ysuc].
    destruct (not_or _ _ Hnctsfml) as [Hncfpant Hncfpsuc].
    destruct ((proj1 seqSubst_strSubst) Hsubst) as [Hsubpant Hsubpsuc].
    destruct (NoDup_seqSVs_strSVs Hnodup) as [Hnduppant Hnduppsuc].
    destruct (seqrep_strrep Hseqrep) as [Hreppant Hreppsuc].
    destruct (exSub Hncfpant Hsubpant Hnduppant Hreppant) as [sub1 Hsub1].
    destruct (exSub Hncfpsuc Hsubpsuc Hnduppsuc Hreppsuc) as [sub2 Hsub2].
    exists (defSubs (strSVs pant) sub1 sub2). simpl.
    apply Sequent_eq_iff. destruct af as [p f]. rewrite <- Hsub1, <- Hsub2. split.
    - apply strSubst_fun_agree_iff. split; try split; try apply fun_agree_refl.
      intros S HS. unfold defSubs. destruct (in_dec string_dec S (strSVs pant));
      [reflexivity | contradiction].
    - apply strSubst_fun_agree_iff. split; try split; try apply fun_agree_refl.
      intros S HS. unfold defSubs. destruct (in_dec string_dec S (strSVs pant));
      try reflexivity. exfalso. contradict HS.
      apply (NoDup_app_distinct _ _ Hnodup). assumption.
  Defined.

  Lemma seqExSub2 [pant psuc aant asuc yant ysuc : structr] [pat seqa seqy : sequent]
    [af : afSubst] [suba : sSubst] (A : formula) (Y : structr) (pn : bool) :
    pat = pant ⊢ psuc ->
    seqa = aant ⊢ asuc -> seqy = yant ⊢ ysuc ->
    (strCtnsFml pant -> strIsFml pant) ->
    (strCtnsFml psuc -> strIsFml psuc) ->
    (strIsFml pant -> aant = FS A -> aant = yant) ->
    (strIsFml psuc -> asuc = FS A -> asuc = ysuc) ->
    seqSubst (af, suba) pat = seqa ->
    NoDup (seqSVs pat) -> seqrep (FS A) Y pn seqa seqy ->
      sSubstfor af pat seqy.
  Proof.
    intros Heqpat Heqseqa Heqseqy Hfmlpant Hfmlpsuc Hant Hsuc Hsubpat Hnodup Hseqrep.
    destruct (strCtnsFml_dec pant) as [Hcfpant|Hncfpant];
    destruct (strCtnsFml_dec psuc) as [Hcfpsuc|Hncfpsuc].
    4: { eapply seqExSub1; try eassumption. rewrite Heqpat. simpl. tauto. }
    all: rewrite Heqpat in Hsubpat, Hnodup;
      rewrite Heqseqa in Hsubpat, Hseqrep; rewrite Heqseqy in Hseqrep;
      destruct ((proj1 seqSubst_strSubst) Hsubpat) as [Hsubpant Hsubpsuc];
      destruct (NoDup_seqSVs_strSVs Hnodup) as [Hnoduppant Hnoduppsuc];
      destruct (seqrep_strrep Hseqrep) as [Hrepant Hrepsuc].
    - exists suba. specialize (Hfmlpant Hcfpant). specialize (Hfmlpsuc Hcfpsuc).
      specialize (Hant Hfmlpant). specialize (Hsuc Hfmlpsuc).      
      rewrite Heqpat, Heqseqy, Hsubpat.
      pose proof (subst_strIsFml Hsubpant Hfmlpant) as Hfmlaant.
      pose proof (subst_strIsFml Hsubpsuc Hfmlpsuc) as Hfmlasuc.
      destruct Hfmlaant as [B]. destruct Hfmlasuc as [C].
      apply strrepFmlEq in Hrepant, Hrepsuc.
      destruct Hrepant as [ [HeqB _] | Heqyant];
        [rewrite (Hant (f_equal FS HeqB)) | rewrite Heqyant].
      all: destruct Hrepsuc as [ [HeqC _] | Heqysuc];
        [rewrite (Hsuc (f_equal FS HeqC)) | rewrite Heqysuc]; reflexivity.
    - destruct (exSub Hncfpsuc Hsubpsuc Hnoduppsuc Hrepsuc) as [suby Hsuby].
      exists suby. specialize (Hfmlpant Hcfpant). specialize (Hant Hfmlpant).
      rewrite Heqpat, Heqseqy. simpl.
      rewrite Hsuby, (strSubst_fml suby suba Hfmlpant), Hsubpant.
      pose proof (subst_strIsFml Hsubpant Hfmlpant) as Hfmlaant.
      destruct Hfmlaant as [B].
      destruct (strrepFmlEq Hrepant) as [ [HeqB _] | Heqyant];
        [rewrite <- (Hant (f_equal FS HeqB)) |
         rewrite Heqyant]; reflexivity.
    - destruct (exSub Hncfpant Hsubpant Hnoduppant Hrepant) as [suby Hsuby].
      exists suby. specialize (Hfmlpsuc Hcfpsuc). specialize (Hsuc Hfmlpsuc).
      rewrite Heqpat, Heqseqy. simpl.
      rewrite Hsuby, (strSubst_fml suby suba Hfmlpsuc), Hsubpsuc.
      pose proof (subst_strIsFml Hsubpsuc Hfmlpsuc) as Hfmlasuc.
      destruct Hfmlasuc as [B].
      destruct (strrepFmlEq Hrepsuc) as [ [HeqB _] | Heqysuc];
        [rewrite <- (Hsuc (f_equal FS HeqB)) |
         rewrite Heqysuc]; reflexivity.
  Defined.

End Cuts.


Class BELNAP `{SL : STRLANG} (DC : DISPCALC) := {
    has_CUT : CUT ∈ DC;
    C3_holds : C3 DC;
    C4_holds : C4 DC;
    C5_holds : C5 DC;
    C8_holds : C8 DC }.
