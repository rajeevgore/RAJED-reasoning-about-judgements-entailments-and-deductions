Require Import utils.
Require Import nnf.
Require Import closure.

Require Import String.
Open Scope string_scope.
Require Import Bool.
Require Import Arith.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Program.
Require Import Lia.


Set Implicit Arguments.


Record doseqt : Set :=
{ s_G : list nnf;
  s_H : list (nat * list nnf);
  s_d : nat;
  s_c : bool;
  s_R : list nnf }.

Definition seqt_eqdec (s t : doseqt) : {s = t} + {s <> t}.
Proof.
decide equality; try (apply list_eq_dec; apply nnf_eqdec).
- apply bool_dec.
- apply Nat.eq_dec.
- apply list_eq_dec. decide equality.
  + apply list_eq_dec; apply nnf_eqdec.
  + apply Nat.eq_dec.
Defined.

Record regular (s : doseqt) : Prop :=
{ nodup_H     : NoDupA (@eqset nnf) (map snd (s_H s));
  G_incl_R    : incl (s_G s) (cl_list (s_R s));
  H_incl_R    : forall l, In l (map snd (s_H s)) -> incl l (cl_list (s_R s));
  earlier_H   : forall h, In h (s_H s) -> 0 < fst h <= s_d s;
  same_d_HeqG : s_c s = true -> forall h, In h (s_H s) ->
    fst h = s_d s -> snd h = s_G s }.

Definition rdoseqt := {s | regular s}.

Record upseqt :=
{ s_uev : list nnf;
  s_lp  : nat }.

Definition upseqt_eqdec (s t : upseqt) : {s = t} + {s <> t}.
Proof.
decide equality.
- apply Nat.eq_dec.
- apply list_eq_dec; apply nnf_eqdec.
Defined.

Definition full_seqt : Set := doseqt * upseqt.

Definition full_seqt_eqdec (fs1 fs2 : full_seqt) : {fs1 = fs2} + {fs1 <> fs2}.
Proof.
decide equality; [apply upseqt_eqdec | apply seqt_eqdec].
Defined.

Definition df_seqt : doseqt :=
  {| s_G := []; s_H := []; s_d := O; s_c := false; s_R := [] |}.

Definition df_upseqt : upseqt := {| s_uev := []; s_lp := O |}.

Definition df_fseqt := (df_seqt, df_upseqt).



Definition alpha_child (phi : nnf) (s : doseqt) : doseqt :=
{|
  s_G := nnf_alpha1 phi :: nnf_alpha2 phi :: remove_nnf phi (s_G s);
  s_H := s_H s;
  s_d := s_d s;
  s_c := false;
  s_R := s_R s
|}.

Definition get_alpha_seqt (s : doseqt) :
  {phi : nnf | In phi (s_G s) /\ nnf_isalpha phi} +
  {forall phi, In phi (s_G s) -> ~ nnf_isalpha phi}.
Proof.
destruct (get_alpha (s_G s)) as [phi|H]; [now left | now right].
Defined.

Theorem alpha_child_pseqt [phi : nnf] (Hphi : nnf_isalpha phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) :
    regular (alpha_child phi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *. constructor.
- simpl. apply (nodup_H pse).
- simpl.
  destruct (@in_cl_list_alpha phi (s_R s) Hphi) as [Ha1 Ha2].
  { apply (G_incl_R pse). assumption. }
  intros psi H. destruct H as [H|[H|H]];
  try (rewrite <- H; assumption).
  apply (G_incl_R pse). apply in_remove with nnf_eqdec phi.
  assumption.
- simpl. apply (H_incl_R pse).
- simpl. apply (earlier_H pse).
- simpl. discriminate.
Qed.

Definition alpha_child_sseqt [phi : nnf] (Hphi : nnf_isalpha phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) : rdoseqt :=
  exist _ (alpha_child phi (`ss)) (alpha_child_pseqt Hphi ss Hin).




Definition beta1_child (phi : nnf) (s : doseqt) : doseqt :=
{|
  s_G := nnf_beta1 phi :: remove_nnf phi (s_G s);
  s_H := s_H s;
  s_d := s_d s;
  s_c := false;
  s_R := s_R s
|}.

Definition beta2_child (phi : nnf) (s : doseqt) : doseqt :=
{|
  s_G := nnf_beta2 phi :: remove_nnf phi (s_G s);
  s_H := s_H s;
  s_d := s_d s;
  s_c := false;
  s_R := s_R s
|}.

Definition get_beta_seqt (s : doseqt) :
  {phi : nnf | In phi (s_G s) /\ nnf_isbeta phi} +
  {forall phi, In phi (s_G s) -> ~ nnf_isbeta phi}.
Proof.
destruct (get_beta (s_G s)) as [phi|H]; [now left | now right].
Defined.

Theorem beta1_child_pseqt [phi : nnf] (Hphi : nnf_isbeta phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) :
    regular (beta1_child phi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *. constructor.
- simpl. apply (nodup_H pse).
- simpl.
  destruct (@in_cl_list_beta phi (s_R s) Hphi) as [Ha1 Ha2].
  { apply (G_incl_R pse). apply Hin. }
  intros psi H. destruct H as [H|H]; try (rewrite <- H; assumption).
  apply (G_incl_R pse). apply in_remove with nnf_eqdec phi.
  assumption.
- simpl. apply (H_incl_R pse).
- simpl. apply (earlier_H pse).
- simpl. discriminate.
Qed.

Theorem beta2_child_pseqt [phi : nnf] (Hphi : nnf_isbeta phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) :
    regular (beta2_child phi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *. constructor.
- simpl. apply (nodup_H pse).
- simpl.
  destruct (@in_cl_list_beta phi (s_R s) Hphi) as [Ha1 Ha2].
  { apply (G_incl_R pse). apply Hin. }
  intros psi H. destruct H as [H|H]; try (rewrite <- H; assumption).
  apply (G_incl_R pse). apply in_remove with nnf_eqdec phi.
  assumption.
- simpl. apply (H_incl_R pse).
- simpl. apply (earlier_H pse).
- simpl. discriminate.
Qed.

Definition beta1_child_sseqt [phi : nnf] (Hphi : nnf_isbeta phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) : rdoseqt :=
  exist _ (beta1_child phi (`ss)) (beta1_child_pseqt Hphi ss Hin).

Definition beta2_child_sseqt [phi : nnf] (Hphi : nnf_isbeta phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) : rdoseqt :=
  exist _ (beta2_child phi (`ss)) (beta2_child_pseqt Hphi ss Hin).



Definition get_contra : forall G : list nnf,
  {s : string | In (var s) G /\ In (neg s) G} +
  {forall s, In (var s) G -> ~ In (neg s) G}.
Proof.
induction G as [|phi G'].
- right. simpl. tauto.
- destruct IHG' as [Hl|Hr].
  * left. destruct Hl as [n Hn].
    exists n. split; simpl; right; tauto.
  * destruct phi as [m|m| | | | |]; try (
    right; intros n H; destruct H as [H|H]; [discriminate|(
    specialize (Hr n H); intro H0; destruct H0;
    [discriminate|contradiction])]).
    + destruct (in_dec nnf_eqdec (neg m) G') as [Hin|Hnin].
     -- left. exists m. split; [(now left)|(now right)].
     -- right. intros n H. destruct H as [H|H].
       ** injection H. intro Heq. rewrite <- Heq. intro Hctr.
          destruct Hctr; [discriminate|contradiction].
       ** specialize (Hr n H). intro Hctr.
          destruct Hctr; [discriminate|contradiction].
    + destruct (in_dec nnf_eqdec (var m) G') as [Hin|Hnin].
     -- left. exists m. split; [(now right)|(now left)].
     -- right. intros n H. destruct H as [H|H]; try discriminate.
        destruct (string_dec m n) as [Heq|Hneq].
       ** rewrite <- Heq in H. contradiction.
       ** specialize (Hr n H). intro Hctr. destruct Hctr as [Hctr|Hctr];
          try contradiction. injection Hctr. contradiction.
Defined.



Definition get_next : forall G : list nnf,
  {exists phi, In (next phi) G} + {forall phi, ~ In (next phi) G}.
Proof.
induction G as [|phi G'].
- now right.
- destruct IHG' as [Hl|Hr].
  * left. destruct Hl as [psi Hin]. exists psi. now right.
  * destruct phi; try (right; intros psi H; specialize (Hr psi);
    destruct H; [discriminate|contradiction]).
    left. exists phi. now left.
Defined.


Fixpoint unnext (G : list nnf) : list nnf :=
  match G with
  | []                => []
  | (next phi) :: Gtl => phi :: unnext Gtl
  | _ :: Gtl           => unnext Gtl
  end.

Lemma in_unnext_in_next [G] :
  forall phi, In phi (unnext G) -> In (next phi) G.
Proof.
induction G as [|psi Gtl].
- simpl. tauto.
- destruct psi;
  try (simpl; intros phi H; right; apply IHGtl; assumption).
  simpl. intros phi H. destruct H as [H|H].
  * rewrite H. now left.
  * right. apply IHGtl. assumption.
Qed.

Lemma in_next_in_unnext [G] :
  forall phi, In (next phi) G -> In phi (unnext G).
Proof.
induction G as [|psi Gtl].
- simpl. tauto.
- destruct psi; try (simpl; intros phi H;
  destruct H; try discriminate; apply IHGtl; assumption).
  simpl. intros phi H. destruct H as [H|H].
  * injection H. tauto.
  * right. apply IHGtl. assumption.
Qed.

Definition jump_child (s : doseqt) : doseqt :=
{|
  s_G := unnext (s_G s);
  s_H := (S (s_d s), unnext (s_G s)) :: (s_H s);
  s_d := S (s_d s);
  s_c := true;
  s_R := s_R s
|}.

Definition not_blocked_seqt (s : doseqt) : Prop :=
  ~ InA (@eqset nnf) (unnext (s_G s)) (map snd (s_H s)).

Record state_conditions (s : doseqt) : Prop :=
{ sc_no_contra : forall n, In (var n) (s_G s) -> ~ In (neg n) (s_G s);
  sc_no_alpha  : forall phi, In phi (s_G s) -> ~ nnf_isalpha phi;
  sc_no_beta   : forall phi, In phi (s_G s) -> ~ nnf_isbeta phi }.

Definition blocker_seqt (h : nat * list nnf) (s : doseqt) : Prop :=
  In h (s_H s) /\ eqset (snd h) (unnext (s_G s)).

Definition get_blocker : forall (D : list nnf) (H : list (nat * (list nnf))),
  {h | In h H /\ eqset (snd h) D} +
  {~ InA (@eqset nnf) D (map snd H)}.
Proof.
induction H as [|(d, L) H'].
- now right.
- destruct IHH' as [Hl|Hr].
  * left. destruct Hl as [h Hh]. exists h. destruct Hh as [Hin Hsnd].
    split; [now right|assumption].
  * destruct (eqset_dec nnf_eqdec L D) as [Heq|Hneq].
    + left. exists (d, L). split; [now left|tauto].
    + right. simpl. intro Hin. inversion Hin.
     -- contradict Hneq. apply eqset_sym. assumption.
     -- contradiction.
Defined.

Definition get_blocker_seqt (s : doseqt) :
  {h | blocker_seqt h s} + {not_blocked_seqt s}.
Proof.
destruct (get_blocker (unnext (s_G s)) (s_H s)) as [[h Hh]|Hnin].
- left. exists h. split; tauto.
- right. assumption.
Defined.

Theorem jump_child_pseqt (ss : rdoseqt) (sc : state_conditions (`ss))
  (nb : not_blocked_seqt (`ss)) : regular (jump_child (`ss)).
Proof.
destruct ss as [s pse]. simpl in sc |- *.
assert (incl (unnext (s_G s)) (cl_list (s_R s))) as GRsec.
{ pose proof (G_incl_R pse) as GRse.
simpl. intros phi Hphi. apply in_cl_list_next.
apply GRse. apply in_unnext_in_next. assumption. }
constructor.
- pose proof (nodup_H pse) as NDse.
  constructor 2; fold (map snd (s_H s)); simpl;
  [apply nb | assumption].
- apply GRsec.
- pose proof (H_incl_R pse) as HRse.
  simpl. intros l Hl. destruct Hl as [Hl|Hl].
  * rewrite <- Hl. simpl. apply GRsec.
  * apply HRse. assumption.
- simpl. intros h Hh. destruct Hh as [Hh|Hh].
  * rewrite <- Hh. simpl. lia.
  * apply (earlier_H pse) in Hh. lia.
- intro H; clear H. simpl. intros h Hh.
  destruct Hh as [Hh|Hh].
  * intro H; clear H. rewrite <- Hh. simpl. reflexivity.
  * apply (earlier_H pse) in Hh. lia.
Qed.

Definition jump_child_sseqt (ss : rdoseqt) (sc : state_conditions (`ss))
(nb : not_blocked_seqt (`ss)) : rdoseqt :=
  exist _ (jump_child (`ss)) (jump_child_pseqt ss sc nb).

Fixpoint get_unts (G : list nnf) : list nnf :=
  match G with
  | []             => []
  | unt phi psi :: Gtl => unt phi psi :: get_unts Gtl
  | _ :: Gtl       => get_unts Gtl
  end.

Lemma unt_in_get_unts : forall phi psi G,
  In (unt phi psi) G -> In (unt phi psi) (get_unts G).
Proof.
intros phi psi. induction G as [|xi G].
- contradiction.
- intro H. destruct H as [H|H].
  + rewrite H. simpl. now left.
  + destruct xi; simpl; try apply (IHG H).
    right. apply (IHG H).
Qed.

Lemma unt_only_get_unts [G] : forall xi, In xi (get_unts G) ->
  exists phi psi, xi = unt phi psi.
Proof.
induction G as [|chi Gtl].
- simpl. tauto.
- intros xi Hxi. destruct chi; simpl in Hxi;
  try (apply (IHGtl _ Hxi)).
  destruct Hxi as [Hxi|Hxi].
  * exists chi1, chi2. rewrite Hxi. reflexivity.
  * apply IHGtl. assumption.
Qed.

Lemma get_unts_in : forall G xi, In xi (get_unts G) -> In xi G.
Proof.
induction G as [|phi G].
- simpl. tauto.
- intros xi Hxi. simpl in Hxi. destruct phi;
  try (right; apply IHG; assumption).
  destruct Hxi as [Hxi|Hxi].
  + now left.
  + right. apply IHG. assumption.
Qed.
