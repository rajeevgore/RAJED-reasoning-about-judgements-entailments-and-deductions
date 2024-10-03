Require Import utils.
Require Import nnf.
Require Import closure.
Require Import semantics.
Require Import seqt.
Require Import ptree.
Require Import proper.

Require Import Arith.
Require Import Nat.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Wellfounded.
Require Import Lia.

Require Import Classical.



Set Implicit Arguments.




Section Unravelling.

  Variable Tl : ltree.
  Hypothesis gpt : gproper (l_root Tl).

  Definition alternate_choice (p : list ptree) (x c1 c2 : ptree) :=
    if even (count_occ ptree_eqdec p x) then c1 else c2.
  
  Lemma alternate_choice_or (p : list ptree) (x c1 c2 : ptree) :
    alternate_choice p x c1 c2 = c1 \/
    alternate_choice p x c1 c2 = c2.
  Proof.
  unfold alternate_choice.
  destruct (even (count_occ ptree_eqdec p x));
  [now left | now right].
  Qed.

  Definition proj_ss [A : Type] [P : A -> Prop] [B : Prop]
  (x : {a : A | P a} + {B}) : option A :=
    match x with
    | inleft (exist _ a pa) => Some a
    | inright b             => None
    end.

  Record psgu (prev curr : (list ptree) * ptree) : Prop :=
  { sgu_child      : ~ t_isloop (snd prev) ->
      is_child (snd curr) (snd prev);
    sgu_loop       : t_isloop (snd prev) ->
      proj_ss ((l_looper Tl) (snd prev)) = Some (snd curr);
    sgu_trail_eq    : fst curr = fst prev ++ [snd prev];
    sgu_alt_choice : forall c1 c2 fs phi, snd prev = talt c1 c2 fs phi ->
      snd curr = alternate_choice (fst prev) (snd prev) c1 c2 }.

  Definition return_succ_gen_unravel (prev : list ptree * ptree) :=
    {u : (list ptree) * ptree | snd u <=/ l_root Tl /\ psgu prev u}.
  
  Definition succ_gen_unravel
    (prev : {u : (list ptree) * ptree | snd u <=/ l_root Tl}) :
    return_succ_gen_unravel (proj1_sig prev).
  Proof.
  refine (
  let u := (proj1_sig prev) in let p := fst u in
  let x := snd u in let xlert := proj2_sig prev in
  match x as x' return x = x' -> return_succ_gen_unravel (proj1_sig prev) with
  | talpha c _ _   => fun Heqx => exist _ (p ++ [x], c) _
  | tbeta1 c _ _   => fun Heqx => exist _ (p ++ [x], c) _
  | tbeta2 c _ _   => fun Heqx => exist _ (p ++ [x], c) _
  | talt c1 c2 _ _ => fun Heqx =>
      exist _ (p ++ [x], alternate_choice p x c1 c2) _
  | tjump c _      => fun Heqx => exist _ (p ++ [x], c) _
  | tloop fs       => fun Heqx =>
      let lofx := l_looper Tl x in
      match lofx as lofx' return lofx = lofx' ->
      return_succ_gen_unravel (proj1_sig prev) with
      | inleft (exist _ c Hpl) => fun Heqlof =>
          exist _ (p ++ [x], c) _
      | inright Hctr => _
      end eq_refl
  end eq_refl
  ).
  all: try split; try (apply child_desceq with x; try assumption;
  rewrite Heqx; ((now left) || (now right) || reflexivity));
  try (simpl; destruct Hpl as [H H0]; destruct H; now left);
  try (exfalso; destruct Hctr;
    [contradiction | (contradict H; rewrite Heqx; apply I)]);
  try (constructor; simpl; fold u x; rewrite Heqx;
    try (tauto || contradiction || discriminate);
    intro; reflexivity).
  - destruct (alternate_choice_or p x c1 c2) as [Heq|Heq];
    rewrite Heq; apply child_desceq with x; try assumption;
    rewrite Heqx; [now left | now right].
  - constructor; simpl; fold u x; rewrite Heqx;
    try (tauto || contradiction || discriminate);
    rewrite <- Heqx.
    + intro. destruct (alternate_choice_or p x c1 c2) as [Heq|Heq];
      rewrite Heq; rewrite Heqx; [now left | now right].
    + intros c1' c2' fs phi Heq. rewrite Heqx in Heq.
      injection Heq. intros _ _ Heqc2 Heqc1.
      rewrite <- Heqc1, <- Heqc2. reflexivity.
  - constructor; simpl; fold u x; rewrite Heqx;
    try (tauto || contradiction || discriminate);
    try (simpl; tauto).
    intro H; clear H. rewrite <- Heqx. fold lofx. rewrite Heqlof.
    simpl. reflexivity.
  Defined.

  Fixpoint gen_unravel (n : nat) :
    {u : (list ptree) * ptree | snd u <=/ l_root Tl} :=
  match n with
  | 0   => exist _ ([], (l_root Tl)) desceq_refl
  | S n => let sgu := succ_gen_unravel (gen_unravel n) in
      exist _ (proj1_sig sgu) (proj1 (proj2_sig sgu))
  end.

  Definition trail_unravel (n : nat) : list ptree :=
    fst (proj1_sig (gen_unravel n)).

  Definition unravel (n : nat) : ptree :=
    snd (proj1_sig (gen_unravel n)).

  Lemma unravel_desceq_rt :
    forall n, unravel n <=/ l_root Tl.
  Proof.
  intro n. unfold unravel.
  destruct (gen_unravel n) as [(p, x) xlert].
  simpl. assumption.
  Qed.

  Lemma unravel_child : forall [n],
    ~ t_isloop (unravel n) -> is_child (unravel (S n)) (unravel n).
  Proof.
  intros n Hnlp. unfold unravel at 1. simpl.
  destruct (succ_gen_unravel (gen_unravel n)) as [u [xlert pu]].
  simpl. apply (sgu_child pu Hnlp).
  Qed.

  Lemma unravel_loop : forall [n],
    t_isloop (unravel n) ->
      proj_ss (l_looper Tl (unravel n)) = Some (unravel (S n)).
  Proof.
  intro n. pose proof (eq_refl (unravel (S n))) as H.
  unfold unravel at 2 in H. simpl in H.
  destruct (succ_gen_unravel (gen_unravel n)) as [u [xlert pu]].
  simpl in H. rewrite H.
  pose proof (sgu_loop pu) as H0. fold (unravel n) in H0. simpl in H0.
  assumption.
  Qed.

  Lemma unravel_loop_target : forall [n],
    t_isloop (unravel n) ->
    loop_target (unravel n) (unravel (S n)) (l_root Tl).
  Proof.
  intros n H. apply unravel_loop in H.
  destruct (l_looper Tl (unravel n)) as [x|]; try discriminate.
  destruct x as [x px]. simpl in H. injection H.
  intro Heqx. rewrite Heqx in px. assumption.
  Qed.

  Lemma unravel_alt_choice : forall [n c1 c2 fs phi],
    unravel n = talt c1 c2 fs phi ->
    unravel (S n) = alternate_choice (trail_unravel n)
    (unravel n) c1 c2.
  Proof.
  intros n c1 c2 fs phi Hequn. unfold unravel at 1. simpl.
  destruct (succ_gen_unravel (gen_unravel n)) as [[p x] [xlert psgu]].
  simpl. pose proof (sgu_alt_choice psgu Hequn). assumption.
  Qed.

  Lemma trail_unravel_succ_eq : forall n,
    trail_unravel (S n) = trail_unravel n ++ [unravel n].
  Proof.
  intro n. unfold trail_unravel. simpl.
  destruct (succ_gen_unravel (gen_unravel n)) as [[p x] [xlert pu]].
  simpl. apply (sgu_trail_eq pu).
  Qed.

  Fixpoint unravel_from_ql (n r : nat) : list ptree :=
    match r with
    | 0    => []
    | S r' => unravel n :: unravel_from_ql (S n) r'
    end.
  
  Definition unravel_from_to (n m : nat) : list ptree :=
    unravel_from_ql n (m - n).
  
  Lemma unravel_from_to_eq_cons : forall n m, m > n ->
    unravel_from_to n m = unravel n :: unravel_from_to (S n) m.
  Proof.
  intros n m mgtn. unfold unravel_from_to at 1.
  destruct (m - n) as [|d] eqn:Heqmn; try lia.
  simpl. assert (d = m - (S n)) as Heqd. { lia. }
  rewrite Heqd. reflexivity.
  Qed.

  Lemma unravel_from_to_same : forall n, unravel_from_to n n = [].
  Proof.
  intro n. unfold unravel_from_to. rewrite Nat.sub_diag. reflexivity.
  Qed.

  Lemma unravel_from_to_succ_eq : forall n,
    unravel_from_to n (S n) = [unravel n].
  Proof.
  intro n. unfold unravel_from_to.
  rewrite Nat.sub_succ_l; try apply le_n.
  rewrite Nat.sub_diag. simpl. reflexivity.
  Qed.

  Lemma unravel_from_to_split : forall n k m, n <= k <= m ->
    unravel_from_to n m = unravel_from_to n k ++ unravel_from_to k m.
  Proof.
  intros n k m [nlek klem]. fold (k >= n) in nlek. revert k nlek m klem.
  apply (induction_from_rank n (fun x => forall m, x <= m ->
  unravel_from_to n m = unravel_from_to n x ++ unravel_from_to x m)).
  - intros m nlem. rewrite unravel_from_to_same. simpl. reflexivity.
  - intros k kgen IHk. intros m Sklem.
    rewrite (IHk (S k)); try lia.
    rewrite unravel_from_to_succ_eq.
    rewrite <- app_assoc. simpl.
    rewrite <- unravel_from_to_eq_cons; try lia.
    apply IHk. lia.
  Qed.

  Lemma unravel_from_to_eq_app : forall n m, m >= n ->
    unravel_from_to n (S m) = unravel_from_to n m ++ [unravel m].
  Proof.
  intros n m mgen.
  rewrite (@unravel_from_to_split n m (S m)); try lia.
  rewrite unravel_from_to_succ_eq. reflexivity.
  Qed.
  
  Lemma unravel_from_to_in_between : forall n m x,
    In x (unravel_from_to n m) -> exists k, n <= k < m /\ x = unravel k.
  Proof.
  assert (forall d n m x, d = m - n -> In x (unravel_from_ql n d) ->
  exists k : nat, n <= k < m /\ x = unravel k) as H.
  { induction d; try contradiction.
  intros n m x HeqSd Hx. simpl in Hx.
  destruct Hx as [Hx|Hx].
  - exists n. split; try lia. apply eq_sym. assumption.
  - destruct (IHd (S n) m x) as [k [Snkm Hk]];
    try (lia || assumption). exists k. split; [lia|assumption]. }
  intros n m x Hx. apply (H (m - n)); [reflexivity|assumption].
  Qed.

  Lemma unravel_from_to_between_in : forall n m k,
    n <= k < m -> In (unravel k) (unravel_from_to n m).
  Proof.
  intros n. assert (forall m, m >= n -> forall k, n <= k < m ->
  In (unravel k) (unravel_from_to n m)) as H.
  { apply (induction_from_rank n (fun m =>
  forall k, n <= k < m -> In (unravel k) (unravel_from_to n m))).
  - intro k. lia.
  - intros m mgen IHm k [nlek kltSm].
    rewrite unravel_from_to_eq_app; try assumption. apply in_app_iff.
    apply Arith_prebase.lt_n_Sm_le in kltSm.
    destruct (le_lt_eq_dec _ _ kltSm) as [klt|keqm].
    + left. apply IHm. exact (conj nlek klt).
    + right. left. rewrite keqm. reflexivity. }
  intros m k nkm. apply H; lia.
  Qed.

  Lemma trail_unravel_eq_app_from_to : forall m n, m >= n ->
    trail_unravel m = trail_unravel n ++ unravel_from_to n m.
  Proof.
  intros m n. revert m. apply induction_from_rank.
  - rewrite unravel_from_to_same, app_nil_r. reflexivity.
  - intros m mgen IHm. rewrite trail_unravel_succ_eq.
    rewrite unravel_from_to_eq_app; try assumption.
    rewrite IHm. rewrite app_assoc. reflexivity.
  Qed.


  Lemma proper_unravel :
    forall n, proper (unravel n).
  Proof.
  intro n. apply (l_desceq_proper gpt (unravel_desceq_rt n)).
  Qed.


  (* Infinite Occurrence *)

  Definition occ_inf [A : Type] (f : nat -> A) (x : A) :=
    forall n, exists m, m >= n /\ f m = x.
  
  Definition occ_inf_unr := occ_inf unravel.

  Lemma unravel_first_reocc : forall n, occ_inf_unr (unravel n) ->
    exists m, m > n /\ unravel m = unravel n /\
    forall k, n < k < m -> unravel k <> unravel n.
  Proof.
  intros n oiun.
  assert (forall p, p >= n ->
  (forall k, n < k <= p -> unravel k <> unravel n) \/
  (exists m, n < m <= p /\ unravel m = unravel n /\
    (forall k : nat, n < k < m -> unravel k <> unravel n))) as H.
  {
  apply (induction_from_rank n); try (left; lia).
  intros p pgen IHp. destruct IHp as [IHp|IHp].
  - destruct (ptree_eqdec (unravel (S p)) (unravel n))
    as [Heq|Hneq].
    + right. exists (S p). split; try lia.
      split; try assumption.
      intros k nkSp. apply IHp. lia.
    + left. intros k [nltk kleSp].
      destruct (le_lt_eq_dec _ _ kleSp) as [kltSp|keqSp].
      * apply IHp. lia.
      * rewrite keqSp. assumption.
  - right. destruct IHp as [m [nltlep Hm]].
    exists m. split; [lia|assumption].
  }
  destruct (oiun (S n)) as [p [pgeSn Hequp]].
  specialize (H p (Le.le_Sn_le_stt _ _ pgeSn)).
  destruct H as [H|H].
  - contradict Hequp. apply H. lia.
  - destruct H as [m [nltlep Hm]].
    exists m. split; try lia. assumption.
  Qed.

  (* Requires XM *)
  Lemma unravel_eve_all_occ_inf :
    exists n, forall m, m >= n -> occ_inf_unr (unravel m).
  Proof.
  destruct (list_specification (fun x => ~ occ_inf_unr x)
  (all_nodes (l_root Tl))) as [l Hl].
  assert (forall x, In x l -> exists n,
  forall m, m >= n -> unravel m <> x) as Hlwk.
  { intros x Hx. apply Hl in Hx. destruct Hx as [_ Hx].
  apply not_all_ex_not in Hx.
  setoid_rewrite not_ex_all_not_iff in Hx.
  setoid_rewrite not_and_or_iff in Hx.
  setoid_rewrite or_to_imply_iff in Hx.
  assumption. }
  destruct (map_exists _ _ Hlwk) as [l' Hl'].
  exists (list_max l'). intros m mgemax.
  apply NNPP. intro Hctr.
  assert (In (unravel m) l) as Huminl.
  { apply Hl. split; try assumption.
  apply desceq_in_all_nodes. apply unravel_desceq_rt. }
  destruct (Hl' _ Huminl) as [n [Hninl' Hn]].
  pose proof (eq_refl (unravel m)) as H. contradict H.
  apply Hn. apply Nat.le_trans with (list_max l');
  try assumption. apply list_max_ge_all. assumption.
  Qed.

  (* Requires XM *)
  Lemma unravel_ex_occ_inf : exists x, occ_inf_unr x.
  Proof.
  destruct unravel_eve_all_occ_inf as [n Hn].
  exists (unravel n). apply Hn. apply le_n.
  Qed.


  Lemma unravel_occ_inf_child :
    forall x y, occ_inf_unr x -> is_child y x -> occ_inf_unr y.
  Proof.
  intros x y oix Hch. destruct x as [c fs xi|c fs xi|c fs xi|
  c1 c2 fs xi|c fs|fs] eqn:Heqx; try (
  intro n; destruct (oix n) as [m [mgen Hequm]]; rewrite Hch;
  exists (S m); split; try lia; assert (~ t_isloop (unravel m))
  as nlpum; [(rewrite Hequm; tauto) |
  (pose proof (unravel_child nlpum) as H;
  rewrite Hequm in H; assumption)]); try contradiction.

  intro n. destruct (oix n) as [m [mgen urmeq]].
  pose proof (unravel_alt_choice urmeq) as HequSm.
  destruct Hch as [Hch|Hch].
  - unfold alternate_choice in HequSm.
    destruct (even (count_occ ptree_eqdec (trail_unravel m) (unravel m)))
    eqn:Heqeven.
    + exists (S m). split; try lia. rewrite HequSm, Hch. reflexivity.
    + rewrite <- urmeq in oix.
      destruct (unravel_first_reocc m oix) as [l [llt [urleq lnot]]].
      exists (S l). split; try lia.
      rewrite urmeq in urleq.
      pose proof (unravel_alt_choice urleq) as HequSl.
      unfold alternate_choice in HequSl.
      rewrite (@trail_unravel_eq_app_from_to l m) in HequSl; try lia.
      rewrite (unravel_from_to_eq_cons llt) in HequSl.
      rewrite count_occ_app in HequSl. simpl in HequSl.
      rewrite urleq, <- urmeq in HequSl.
      destruct (ptree_eqdec (unravel m) (unravel m));
      try contradiction.
      assert (count_occ ptree_eqdec (unravel_from_to (S m) l)
      (unravel m) = 0) as Hcoeq0.
      { apply count_occ_not_In. intro Hctr.
      apply unravel_from_to_in_between in Hctr.
      destruct Hctr as [k [Smkl urmequrk]]. apply eq_sym in urmequrk.
      contradict urmequrk. apply lnot. lia. }
      rewrite Hcoeq0 in HequSl.
      rewrite Nat.add_comm in HequSl.
      rewrite Nat.even_succ in HequSl.
      unfold Nat.odd in HequSl.
      rewrite Heqeven in HequSl.
      simpl in HequSl.
      rewrite HequSl, Hch. reflexivity.
  - unfold alternate_choice in HequSm.
    destruct (even (count_occ ptree_eqdec (trail_unravel m) (unravel m)))
    eqn:Heqeven.
    + rewrite <- urmeq in oix.
      destruct (unravel_first_reocc m oix) as [l [llt [urleq lnot]]].
      exists (S l). split; try lia.
      rewrite urmeq in urleq.
      pose proof (unravel_alt_choice urleq) as HequSl.
      unfold alternate_choice in HequSl.
      rewrite (@trail_unravel_eq_app_from_to l m) in HequSl; try lia.
      rewrite (unravel_from_to_eq_cons llt) in HequSl.
      rewrite count_occ_app in HequSl. simpl in HequSl.
      rewrite urleq, <- urmeq in HequSl.
      destruct (ptree_eqdec (unravel m) (unravel m));
      try contradiction.
      assert (count_occ ptree_eqdec (unravel_from_to (S m) l)
      (unravel m) = 0) as Hcoeq0.
      { apply count_occ_not_In. intro Hctr.
      apply unravel_from_to_in_between in Hctr.
      destruct Hctr as [k [Smkl urmequrk]]. apply eq_sym in urmequrk.
      contradict urmequrk. apply lnot. lia. }
      rewrite Hcoeq0 in HequSl.
      rewrite Nat.add_comm in HequSl.
      rewrite Nat.even_succ in HequSl.
      unfold Nat.odd in HequSl.
      rewrite Heqeven in HequSl.
      simpl in HequSl.
      rewrite HequSl, Hch. reflexivity.
    + exists (S m). split; try lia. rewrite HequSm, Hch. reflexivity.
  Qed.

  Lemma unravel_same_succ : forall m n, ~ t_isalt (unravel m) ->
    unravel m = unravel n -> unravel (S m) = unravel (S n).
  Proof.
  intros m n nalt urmneq.
  destruct (unravel m) as [c fs xi|c fs xi|c fs xi|
  c1 c2 fs xi|c fs|fs] eqn:Hequrm.
  - assert (~ t_isloop (unravel m)) as nlpurm. { rewrite Hequrm. tauto. }
    assert (~ t_isloop (unravel n)) as nlpurn. { rewrite <- urmneq. tauto. }
    pose proof (unravel_child nlpurm) as Hchm.
    pose proof (unravel_child nlpurn) as Hchn.
    rewrite Hequrm in Hchm. rewrite <- urmneq in Hchn.
    rewrite Hchm, Hchn. reflexivity.
  - assert (~ t_isloop (unravel m)) as nlpurm. { rewrite Hequrm. tauto. }
    assert (~ t_isloop (unravel n)) as nlpurn. { rewrite <- urmneq. tauto. }
    pose proof (unravel_child nlpurm) as Hchm.
    pose proof (unravel_child nlpurn) as Hchn.
    rewrite Hequrm in Hchm. rewrite <- urmneq in Hchn.
    rewrite Hchm, Hchn. reflexivity.
  - assert (~ t_isloop (unravel m)) as nlpurm. { rewrite Hequrm. tauto. }
    assert (~ t_isloop (unravel n)) as nlpurn. { rewrite <- urmneq. tauto. }
    pose proof (unravel_child nlpurm) as Hchm.
    pose proof (unravel_child nlpurn) as Hchn.
    rewrite Hequrm in Hchm. rewrite <- urmneq in Hchn.
    rewrite Hchm, Hchn. reflexivity.
  - contradict nalt. apply I.
  - assert (~ t_isloop (unravel m)) as nlpurm. { rewrite Hequrm. tauto. }
    assert (~ t_isloop (unravel n)) as nlpurn. { rewrite <- urmneq. tauto. }
    pose proof (unravel_child nlpurm) as Hchm.
    pose proof (unravel_child nlpurn) as Hchn.
    rewrite Hequrm in Hchm. rewrite <- urmneq in Hchn.
    rewrite Hchm, Hchn. reflexivity.
  - assert (t_isloop (unravel m)) as lpurm. { rewrite Hequrm. exact I. }
    assert (t_isloop (unravel n)) as lpurn. { rewrite <- urmneq. exact I. }
    pose proof (unravel_loop lpurm) as Heqm.
    pose proof (unravel_loop lpurn) as Heqn.
    rewrite Hequrm, urmneq in Heqm. rewrite Heqm in Heqn. injection Heqn. tauto.
  Qed.

  Lemma unravel_occ_inf_loop :
    forall x, occ_inf_unr x -> t_isloop x ->
    exists y, (proj_ss (l_looper Tl x) = Some y) /\ occ_inf_unr y.
  Proof.
  intros x oix Hlpx. destruct x as [| | | | |fs]; try contradiction.
  destruct (oix 0) as [n [nge0 urneq]].
  exists (unravel (S n)). split.
  - rewrite <- urneq. apply (@unravel_loop n). rewrite urneq. apply I.
  - intro m. destruct (oix m) as [k [kgem urkeq]].
    exists (S k). split; try lia.
    apply unravel_same_succ.
    + rewrite urkeq. simpl. tauto.
    + rewrite urneq, urkeq. reflexivity.
  Qed.

  Lemma isloop_dec : forall x, {t_isloop x} + {~ t_isloop x}.
  Proof.
  intro x. destruct x; simpl;
  ((now left) || (now right)).
  Qed.

  Lemma unravel_root_not_occ_inf : ~ occ_inf_unr (l_root Tl).
  Proof.
  assert (forall n, n >= 1 -> unravel n <> l_root Tl) as H.
  { intros n nge1. apply not_eq_sym.
  destruct n as [|n]; try lia.
  destruct (isloop_dec (unravel n)) as [Hlp|Hnlp].
  - apply desc_not_eq. apply (unravel_loop_target Hlp).
  - apply desc_not_eq. 
    apply desc_desceq_desc with (unravel n).
    + left. apply (unravel_child Hnlp).
    + apply unravel_desceq_rt. }
  intro oirt. destruct (oirt 1) as [n [nge1 Hctr]].
  contradict Hctr. apply H. assumption.
  Qed.

  Lemma unravel_occ_inf_desc_rt :
    forall x, occ_inf_unr x -> x </ (l_root Tl).
  Proof.
  intros x oix. destruct (oix 0) as [n [_ Hequn]].
  rewrite <- Hequn.
  destruct (unravel_desceq_rt n) as [|Heq]; try assumption.
  contradict oix. rewrite <- Hequn, Heq.
  apply unravel_root_not_occ_inf.
  Qed.

  Lemma unravel_occ_inf_proper :
    forall x, occ_inf_unr x -> proper x.
  Proof.
  intros x oix.
  apply ((proj2 gpt) _ (unravel_occ_inf_desc_rt oix)).
  Qed.

  Lemma proj_looper_loop_target : forall x y,
    proj_ss (l_looper Tl x) = Some y ->
    loop_target x y (l_root Tl).
  Proof.
  intros x y H.
  destruct (l_looper Tl x) as [y'|Hctr]; try discriminate.
  destruct y' as [y' ply]. simpl in H.
  injection H. intro Heqy. rewrite Heqy in ply.
  assumption.
  Qed.

  (* Requires XM *)
  Lemma unravel_occ_inf_anc :
    exists x, occ_inf_unr x /\ t_c x = true /\
    forall y, (occ_inf_unr y /\ t_c y = true) -> t_d x <= t_d y.
  Proof.
  destruct (list_specification (fun x => occ_inf_unr x /\
  t_c x = true) (all_nodes (l_root Tl))) as [l Hl].
  destruct (@list_min_ex (map t_d l)) as [d [Hdin Hdeq]].
  - assert (forall x, occ_inf_unr x -> exists y,
    occ_inf_unr y /\ t_c y = true) as Htrav.
    { induction x as [c IHc fs xi|c IHc fs xi|c IHc fs xi
    |c1 IHc1 c2 IHc2 fs xi|c IHc fs|fs].
    - set (x := talpha c fs xi). intro H. apply IHc.
      apply unravel_occ_inf_child with x;
        try reflexivity; try assumption.
    - set (x := tbeta1 c fs xi). intro H. apply IHc.
      apply unravel_occ_inf_child with x;
        try reflexivity; try assumption.
    - set (x := tbeta2 c fs xi). intro H. apply IHc.
      apply unravel_occ_inf_child with x;
        try reflexivity; try assumption.
    - set (x := talt c1 c2 fs xi). intro H. apply IHc1.
      apply unravel_occ_inf_child with x;
       try (left; reflexivity); try assumption.
    - set (x := tjump c fs). intro H. apply IHc.
      apply unravel_occ_inf_child with x;
        try reflexivity; try assumption.
    - set (x := tloop fs). intro H.
      destruct (@unravel_occ_inf_loop x H I) as [y [ply oiy]].
      apply proj_looper_loop_target in ply.
      destruct ply as [_ [_ [coy _]]].
      exists y. split; assumption.
      }
    destruct unravel_ex_occ_inf as [x0 oix0].
    destruct (Htrav x0 oix0) as [x [oix cox]].
    intro Hctr. apply map_eq_nil in Hctr.
    fold (In x []). rewrite <- Hctr. apply Hl.
    split; try (split; assumption).
    apply desceq_in_all_nodes. left.
    apply unravel_occ_inf_desc_rt. assumption.
  - apply in_map_iff in Hdin. destruct Hdin as [x [Hdxeq Hxin]].
    exists x. destruct (proj1 (Hl x) Hxin) as [_ [oix cox]].
    repeat (split; try assumption).
    intros y [oiy coy]. rewrite Hdxeq, Hdeq.
    apply list_min_le_all. apply in_map_iff.
    exists y. split; try reflexivity.
    apply Hl. split; try (split; assumption).
    apply desceq_in_all_nodes. left.
    apply unravel_occ_inf_desc_rt. assumption.
  Qed.


  Lemma unful_persist :
    forall i phi psi, In (unt phi psi) (t_G (unravel i)) ->
    (forall j, j >= i -> ~ In psi (t_G (unravel j))) ->
    forall j, j >= i -> (In (unt phi psi) (t_G (unravel j)) \/
    In (and phi (next (unt phi psi))) (t_G (unravel j)) \/
    In (next (unt phi psi)) (t_G (unravel j))).
  Proof.
  intros i phi psi Hin Hnful. apply induction_from_rank;
  try now left. intros j jgei IHj.
  pose proof (proper_unravel j) as px.
  remember (unravel j) as x eqn:Hequj. apply eq_sym in Hequj.
  tree_dest_with_eqns x; try rename phi0 into xi; simpl in Hprin; try clear Heqset.
  - pose proof (False_ind _ : ~ t_isloop (talpha c fs xi)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. rewrite Hch.
    destruct IHj as [IHj|[IHj|IHj]].
    + left. unfold t_G. rewrite Heqsec.
      simpl. right. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
    + destruct (nnf_eqdec (and phi (next (unt phi psi))) xi)
      as [Heq|Hneq].
      * right. right. unfold t_G. rewrite Heqsec. simpl.
        right. left. rewrite <- Heq. simpl. reflexivity.
      * right. left. unfold t_G. rewrite Heqsec. simpl.
        right. right. fold (t_G x).
        apply in_in_remove; assumption.
    + right. right. unfold t_G. rewrite Heqsec.
      simpl. right. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
  - pose proof (False_ind _ : ~ t_isloop (tbeta1 c fs xi)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. rewrite Hch.
    destruct IHj as [IHj|[IHj|IHj]].
    + destruct (nnf_eqdec (unt phi psi) xi)
      as [Heq|Hneq].
      * pose proof (Hnful _ (Nat.le_le_succ_r _ _ jgei)) as H.
        contradict H. rewrite Hch.
        unfold t_G. rewrite Heqsec. simpl. left. rewrite <- Heq.
        simpl. reflexivity.
      * left. unfold t_G. rewrite Heqsec. simpl.
        right. fold (t_G x).
        apply in_in_remove; assumption.
    + right. left. unfold t_G. rewrite Heqsec.
      simpl. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
    + right. right. unfold t_G. rewrite Heqsec.
      simpl. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
  - pose proof (False_ind _ : ~ t_isloop (tbeta2 c fs xi)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. rewrite Hch.
    destruct IHj as [IHj|[IHj|IHj]].
    + destruct (nnf_eqdec (unt phi psi) xi)
      as [Heq|Hneq].
      * right. left. unfold t_G. rewrite Heqsec.
        simpl. left. rewrite <- Heq. simpl. reflexivity.
      * left. unfold t_G. rewrite Heqsec. simpl.
        right. fold (t_G x).
        apply in_in_remove; assumption.
    + right. left. unfold t_G. rewrite Heqsec.
      simpl. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
    + right. right. unfold t_G. rewrite Heqsec.
      simpl. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
  - pose proof (False_ind _ : ~ t_isloop (talt c1 c2 fs xi)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. destruct Hch as [Hch|Hch].
    + rewrite Hch. destruct IHj as [IHj|[IHj|IHj]].
      * destruct (nnf_eqdec (unt phi psi) xi)
        as [Heq|Hneq].
      -- pose proof (Hnful _ (Nat.le_le_succ_r _ _ jgei)) as H.
          contradict H. rewrite Hch.
          unfold t_G. rewrite Heqsec1. simpl. left.
          rewrite <- Heq. simpl. reflexivity.
      -- left. unfold t_G. rewrite Heqsec1. simpl.
          right. fold (t_G x).
          apply in_in_remove; assumption.
      * right. left. unfold t_G. rewrite Heqsec1.
        simpl. right. fold (t_G x).
        apply in_in_remove; try assumption.
        intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
      * right. right. unfold t_G. rewrite Heqsec1.
        simpl. right. fold (t_G x).
        apply in_in_remove; try assumption.
        intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
    + rewrite Hch. destruct IHj as [IHj|[IHj|IHj]].
      * destruct (nnf_eqdec (unt phi psi) xi)
        as [Heq|Hneq].
      -- right. left. unfold t_G. rewrite Heqsec2.
          simpl. left. rewrite <- Heq.
          simpl. reflexivity.
      -- left. unfold t_G. rewrite Heqsec2. simpl.
          right. fold (t_G x).
          apply in_in_remove; assumption.
      * right. left. unfold t_G. rewrite Heqsec2.
        simpl. right. fold (t_G x).
        apply in_in_remove; try assumption.
        intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
      * right. right. unfold t_G. rewrite Heqsec2.
        simpl. right. fold (t_G x).
        apply in_in_remove; try assumption.
        intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
  - pose proof (False_ind _ : ~ t_isloop (tjump c fs)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. rewrite Hch.
    destruct IHj as [IHj|[IHj|IHj]].
    + apply (sc_no_beta (state_has_sc px I)) in IHj.
      contradict IHj. exact I.
    + apply (sc_no_alpha (state_has_sc px I)) in IHj.
      contradict IHj. exact I.
    + left. unfold t_G. rewrite Heqsec. simpl.
      fold (t_G x). apply in_next_in_unnext.
      assumption.
  - pose proof (I : t_isloop (tloop fs)) as Hlpuj.
    rewrite <- Hequj in Hlpuj.
    destruct (unravel_loop_target Hlpuj) as [_ [_ [_ Heqset]]].
    destruct IHj as [IHj|[IHj|IHj]].
    + apply (sc_no_beta (state_has_sc px I)) in IHj.
      contradict IHj. exact I.
    + apply (sc_no_alpha (state_has_sc px I)) in IHj.
      contradict IHj. exact I.
    + left. apply (eqset_in_iff Heqset).
      apply in_next_in_unnext. rewrite Hequj.
      assumption.
  Qed.

  Corollary unful_persist_in_state :
    forall i phi psi, In (unt phi psi) (t_G (unravel i)) ->
    (forall j, j >= i -> ~ In psi (t_G (unravel j))) ->
    forall j, j >= i -> t_isstate (unravel j) ->
    In (next (unt phi psi)) (t_G (unravel j)).
  Proof.
  intros i phi psi Hin Hnful j jgei stx.
  set (x := unravel j) in *.
  pose proof (proper_unravel j) as px.
  destruct (unful_persist _ _ Hin Hnful jgei) as [H|[H|H]].
  - apply (sc_no_beta (state_has_sc px stx)) in H.
    contradict H. exact I.
  - apply (sc_no_alpha (state_has_sc px stx)) in H.
    contradict H. exact I.
  - assumption.
  Qed.

  (* Requires XM *)
  (* This is the main proof of soundness,
  inspired by Florian Widmann's PhD *)
  Theorem unravel_ev_fulfilled :
    forall i phi psi, In (unt phi psi) (t_G (unravel i)) ->
    exists k, k >= i /\ In psi (t_G (unravel k)).
  Proof.
  intros i phi psi Hin. apply not_all_not_ex. intro Hnful.
  setoid_rewrite not_and_or_iff in Hnful.
  setoid_rewrite or_to_imply_iff in Hnful.
  pose proof (unful_persist_in_state _ _ Hin Hnful) as Hstate.
  destruct unravel_occ_inf_anc as [xh [oixh [coxh dxhle]]].
  assert (forall x, occ_inf_unr x ->
  In (unt phi psi) (t_uev x) /\ t_lp x >= t_d xh) as H.
  { intros x oix. pose proof (unravel_occ_inf_proper oix) as px.
    tree_ind_with_eqns x; try rename phi0 into xi;
      try (pose proof (unravel_occ_inf_child c oix eq_refl) as oic;
           pose proof (unravel_occ_inf_proper oic) as pc;
           specialize (IHc oic pc));
      try (pose proof (unravel_occ_inf_child c1 oix (or_introl eq_refl)) as oic1;
           pose proof (unravel_occ_inf_proper oic1) as pc1;
           specialize (IHc1 oic1 pc1));
      try (pose proof (unravel_occ_inf_child c2 oix (or_intror eq_refl)) as oic2;
           pose proof (unravel_occ_inf_proper oic2) as pc2;
           specialize (IHc2 oic2 pc2)).
  - destruct IHc as [Hinuevc Hlpcge].
    rewrite Hequev, Heqlp. tauto.
  - destruct IHc as [Hinuevc Hlpcge].
    assert (unt phi psi <> xi) as Hneqxi.
    { intro Hctr. destruct (oic i) as [j [jgei Hequj]].
    pose proof (Hnful j jgei) as H. contradict H.
    rewrite Hequj. unfold t_G. rewrite Heqsec. simpl. rewrite <- Hctr. now left. }
    rewrite Hequev, Heqlp. split.
    + apply (in_in_remove nnf_eqdec _ Hneqxi Hinuevc).
    + assumption.
  - destruct IHc as [Hinuevc Hlpcge].
    rewrite Hequev, Heqlp. tauto.
  - destruct IHc1 as [Hinuevc1 Hlpc1ge].
    destruct IHc2 as [Hinuevc2 Hlpc2ge].
    assert (unt phi psi <> xi) as Hneqxi.
    { intro Hctr. destruct (oic1 i) as [j [jgei Hequj]].
    pose proof (Hnful j jgei) as H. contradict H.
    rewrite Hequj. unfold t_G. rewrite Heqsec1. simpl.  rewrite <- Hctr. now left. }
    split.
    + rewrite Hequev. apply set_inter_intro.
      * apply (in_in_remove nnf_eqdec _ Hneqxi Hinuevc1).
      * assumption.
    + rewrite Heqlp. apply Nat.min_glb; assumption.
  - destruct IHc as [Hinuevc Hlpcge].
    rewrite Hequev, Heqlp. split; try assumption.
  - destruct (unravel_occ_inf_loop oix I) as [c [plc oic]].
    apply proj_looper_loop_target in plc.
    destruct plc as [_ [Heqdc [coc _]]].
    pose proof (dxhle c (conj oic coc)) as Hdcge.
    rewrite Hequev, <- Heqdc. split; try assumption.
    apply unt_in_get_unts. apply in_next_in_unnext.
    destruct (oix i) as [j [jgei Hequj]].
    rewrite <- Hequj. apply Hstate; try assumption.
    rewrite Hequj. exact I. }
  specialize (H xh oixh).
  pose proof (no_unful_case (proj1 gpt)
  (unravel_occ_inf_desc_rt oixh) coxh) as H0.
  destruct H0 as [H0|H0].
  - fold (In (unt phi psi) []). rewrite <- H0. tauto.
  - lia.
  Qed.

End Unravelling.
