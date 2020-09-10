Require Import ssreflect.

Require Import genT.
Require Import ddT.
Require Import dd_fc.
Require Import List_lemmasT.
Require Import lntT lntacsT lntlsT lntbRT lntmtacsT.
Require Import lntb1LT lntb2LT.
Require Import lntkt_exchT.
Require Import lnt_weakeningT.
Require Import lnt_contractionT.
Require Import existsT.
Require Import lnt_weakeningT lnt_contraction_mrT.
Require Import ind_lex.
Require Import contractedT.
Require Import structural_equivalence.
Require Import merge.




Definition can_gen_cut {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns1 ns2 :=
  forall G1 G2 G3 seq1 seq2 (d : dir) Γ1 Γ2 Δ1 Δ2 A,
    ns1 = G1 ++ [(seq1, d)] -> seq1 = pair Γ1 (Δ1++[A]) ->
    ns2 = G2 ++ [(seq2, d)] -> seq2 = pair (Γ2++[A]) Δ2 ->
    merge G1 G2 G3 ->
    struct_equiv_str G1 G2 ->
    derrec rules (fun _ => False) (G3 ++ [(Γ1++Γ2, Δ1++Δ2, d)]).

Definition can_gen_cut_simpl {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns1 ns2 :=
  forall G seq1 seq2 (d : dir) Γ1 Γ2 Δ1 Δ2 A,
    ns1 = G ++ [(seq1, d)] -> seq1 = pair Γ1 (Δ1++[A]) ->
    ns2 = G ++ [(seq2, d)] -> seq2 = pair (Γ2++[A]) Δ2 ->
    derrec rules (fun _ => False) (G ++ [(Γ1++Γ2, Δ1++Δ2, d)]).


(* ----------------- *)
(* CUT ADMISSIBILITY *)
(* ----------------- *)

Definition ht := derrec_height.


Definition size {V : Set} (A : PropF V) := 0.
Print LNSKt_rules.
Print prop.
Print princrule_pfc.
Print derrec.


Parameter V : Set.
Parameter p q : V.
Definition P := Var p.
Definition Q := Var q.
Print PropF.
Check (dlNil (@LNSKt_rules V) (fun _ => False)).
Definition d0 := (dlNil (@LNSKt_rules V) (fun _ => False)).
Print derI.
Print LNSKt_rules.

Definition d1 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) [([Imp P Q ; Q ; P], [Q], fwd)].
  eapply derI.
  eapply prop.
  rewrite <- app_nil_l.
  rewrite <- nslcext_def.
  eapply NSlcctxt.
  eapply Sctxt_eq;
  [ | rewrite cons_singleton;  rewrite (cons_singleton _ Q);  reflexivity |
    rewrite <- (app_nil_l [Q]); rewrite <- (app_nil_r [Q]); reflexivity | ..].
  eapply Id_pfc.
  reflexivity.
  apply dlNil.
Qed.

Definition d1' : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) (nslcext [] fwd (seqext [Imp P Q] [P] [] [] ([Q],[Q]))). 
  eapply derI.
  eapply prop.
  eapply NSlcctxt.
  eapply Sctxt.
  eapply Id_pfc.
  apply dlNil.
Qed.

Definition d1'' : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) [([Imp P Q ; Q ; P], [Q], fwd)].
  rewrite <- app_nil_l.
  rewrite <- nslcext_def.
  rewrite cons_singleton.
  rewrite <- (app_nil_l [Q]).
  rewrite <- (app_nil_r [Q]).
  rewrite (cons_singleton _ Q).
  rewrite <- seqext_def.
  apply d1'.
Qed.

Definition d2 : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False) [([Imp P Q ; P], [Q ; P], fwd)].
  eapply derI.
  eapply prop.
  rewrite <- app_nil_l.
  rewrite <- nslcext_def.
  eapply NSlcctxt.
  eapply Sctxt_eq;
  [ | erewrite app_nil_r; rewrite cons_singleton; reflexivity |
    erewrite app_nil_r; rewrite cons_singleton; reflexivity |..].
  eapply Id_pfc.
  reflexivity.
  apply dlNil.
Qed.

Definition d3 : derrec (LNSKt_rules (V:=V)) (fun _ => False) [([Imp P Q; P], [Q], fwd)].
  eapply derI.
  eapply prop.
  rewrite <- app_nil_l.
  rewrite <- nslcext_def.
  eapply NSlcctxt.
  eapply Sctxt_eq.
  eapply ImpL_pfc.
  rewrite cons_singleton.
  rewrite <- (app_nil_l (_ ++ [P])).
  reflexivity.
  simpl. erewrite app_nil_r. reflexivity.
  reflexivity.
  eapply dlCons. eapply d1.
  eapply dlCons. eapply d2.
  eapply dlNil.
Qed.

Inductive principal1 {V : Set} {rules : rlsT (list (rel (list (PropF V)) * dir))}
          {prems} {G} (D : derrec rules prems G) (A : PropF V) :=
| princ_prop  


Definition principal' {V : Set} {rules : rlsT (list (rel (list (PropF V)) * dir))}
           {prems : X -> Type} {G} (D : @derrec X rules prems G) (A : PropF V) := True.

Definition SR_wb_fwd (n m : nat) := forall {V : Set} rules
    G Γ Δ H Σ Π I (A : PropF V)
  (D1 : derrec rules (fun _ => False) (G ++ [(Γ, Δ ++ [WBox A],fwd)]))
  (D2 : derrec rules (fun _ => False) (H ++ [(Σ ++ [WBox A], Π, fwd)] ++ I)),
        principal D1 (WBox A) ->
        ((ht _ _ _ _ D1) + (ht _ _ _ _ D2))%nat <= m ->
        merge G H I ->
        (exists (D3 : derrec rules (fun _ => False)
                       (I ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++
                           [([],[A],fwd)] )), True) ->
        size (WBox A) <= n ->
        exists (D4 : derrec rules (fun _ => False)
                       (I ++ [(Γ ++ Σ, Δ ++ Π, fwd)] ++ I )), True .

Definition SR_wb_bac (n m : nat) := forall {V : Set} rules
    G Γ Δ H Σ Π I (A : PropF V)
  (D1 : derrec rules (fun _ => False) (G ++ [(Γ, Δ ++ [WBox A],bac)]))
  (D2 : derrec rules (fun _ => False) (H ++ [(Σ ++ [WBox A], Π, bac)] ++ I)),
        principal D1 (WBox A) ->
        ((ht _ _ _ _ D1) + (ht _ _ _ _ D2))%nat <= m ->
        merge G H I ->
        (exists (D3 : derrec rules (fun _ => False)
                       (I ++ [(Γ ++ Σ, Δ ++ Π, bac)] ++
                           [([],[A],fwd)] )), True) ->
        size (WBox A) <= n ->
        exists (D4 : derrec rules (fun _ => False)
                       (I ++ [(Γ ++ Σ, Δ ++ Π, bac)] ++ I )), True .


Theorem Lemma_Sixteen :





(* TODO: To fill in proof, based off Lemma 16 of paper. *)
Theorem LNSKt_cut_admissibility : forall (V : Set) ns1 ns2
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) ns1)
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) ns2),
      can_gen_cut (@LNSKt_rules V) ns1 ns2.
Admitted.

(* Follows from LNSKt_cut_admissibility. *)
Theorem LNSKt_cut_admissibility_simpl : forall (V : Set) ns1 ns2
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) ns1)
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) ns2),
    can_gen_cut_simpl (@LNSKt_rules V) ns1 ns2.
Proof.
  intros. unfold can_gen_cut_simpl.
  intros. subst.
  destruct (@merge_ex V _ _ (struct_equiv_weak_refl G)) as [G3 HG3].  
  eapply derrec_mergeL.
  eassumption.
  eapply LNSKt_cut_admissibility in D2. 2 : exact D1.
  unfold can_gen_cut in D2.
  eapply D2; try reflexivity.
  assumption.
  apply struct_equiv_str_refl.
Qed.


(* --------------- *)
(* CUT ELIMINATION *)
(* --------------- *)

Inductive Cut_rule {V : Set} : rlsT (list (rel (list (PropF V)) * dir)) :=
| Cut : forall Γ1 Γ2 Δ1 Δ2 d A, Cut_rule ([[(Γ1,Δ1++[A],d)]] ++ [[(Γ2++[A],Δ2,d)]]) [(Γ1++Γ2,Δ1++Δ2, d)].

(* LNSKt with cut: rules "WithOut Cut" (_woc) and "With Cut" (_wc). *)
Inductive LNSKt_cut_rules {V : Set} : rlsT (list (rel (list (PropF V)) * dir)) :=
| LNSKt_rules_woc : forall ps c, LNSKt_rules ps c -> LNSKt_cut_rules ps c
| LNSKt_rules_wc  : forall ps c, nslclrule (@Cut_rule V) ps c -> LNSKt_cut_rules ps c.

Lemma dersrec_derrec_height : forall {V : Set} rules ps p 
    (ds : dersrec rules (fun _ : list (rel (list (PropF V)) * dir) => False) ps)
    (d  : derrec  rules (fun _ : list (rel (list (PropF V)) * dir) => False) p),
    in_dersrec d ds ->
    derrec_height d <= dersrec_height ds.
Proof.
  intros V rules ps p ds d Hin.
  eapply le_dersrec_height.
  2 : eapply le_n.
  assumption.
Qed.

Lemma dersrecD_forall_in_dersrec : forall (X : Type) (rs : list X -> X -> Type) (ps : X -> Type) (cs : list X) (ds : dersrec rs ps cs) (c : X),
    InT c cs -> (existsT2 d : derrec rs ps c, in_dersrec d ds).
Proof.
  induction ds; intros c Hin.
  inversion Hin.
  inversion Hin.
  + subst. exists d. constructor.
  + subst. eapply IHds in X0. destruct X0 as [d2 Hin2].
    exists d2. constructor 2. eapply Hin2.
Qed.

(* Add to ddT.v *)

Lemma dersrec_double: forall X rules prems c1 c2,
  iffT (dersrec rules prems [c1;c2]) ((derrec rules prems (c1 : X)) * (derrec rules prems (c2 : X))).
Proof.
  intros. split; intros H.
  split; (eapply dersrecD_forall; [apply H |]).
  constructor 1. reflexivity.
  constructor 2. constructor 1. reflexivity.
  eapply dersrecI_forall. intros c Hc.
  inversion Hc as [ | ? ? H2]; subst. apply H.
  inversion H2 as [ | ? ? H3]; subst. apply H.
  inversion H3.
Qed.

Definition dersrec_doubleD X rs ps c1 c2 := iffT_D1 (@dersrec_double X rs ps c1 c2).

Lemma dersrec_double_verb: forall X rules prems c1 c2 (d : (dersrec rules prems [c1;c2])),
    existsT2 (d1 : (derrec rules prems (c1 : X))) (d2 : (derrec rules prems (c2 : X))),
      in_dersrec d1 d * in_dersrec d2 d.
Proof.
  intros.
  assert (InT c1 [c1;c2]) as Hin1. constructor. reflexivity.
  assert (InT c2 [c1;c2]) as Hin2. constructor 2. constructor. reflexivity.
  eapply dersrecD_forall_in_dersrec in Hin1.
  destruct Hin1 as [d1 Hin1]. exists d1.
  eapply dersrecD_forall_in_dersrec in Hin2.
  destruct Hin2 as [d2 Hin2]. exists d2.
  split. apply Hin1. apply Hin2.
Qed.

Theorem LNSKt_cut_elimination :
  forall {V : Set} ns,
    derrec (@LNSKt_cut_rules V) (fun _ => False) ns ->
    derrec (@LNSKt_rules V) (fun _ => False) ns.
Proof.
  intros V ns H.
  remember (derrec_height H) as n.
  revert Heqn. revert H. revert ns.
  induction n using lt_wf_indT. 
  destruct n.
  +{ intros ns H Heqn. destruct H. contradiction.
     simpl in Heqn. discriminate.
   }
  +{ intros ns H Heqn. remember H as H'.
     destruct H. contradiction.
     simpl in *. rewrite HeqH' in Heqn. inversion Heqn as [Heqn2].
     rewrite <- HeqH' in Heqn.
     inversion l.
     ++{ subst c ps0. eapply derI. apply X0.
         apply dersrecI_forall.
         intros p Hin.
(*         pose proof (dersrecD_forall d Hin) as d3. *)
         pose proof (dersrecD_forall_in_dersrec _ _ _ _ d _ Hin) as [d2 Hin2].
         eapply (X (derrec_height d2)). 2 : reflexivity.
         rewrite Heqn2.
         apply Lt.le_lt_n_Sm.
         eapply le_dersrec_height. exact Hin2.
         apply le_n.
       }
     ++{ subst c ps0.
         inversion X0. subst concl ps. inversion H.
         (* At this point d isn't of the right form I think, so I think that the Cut_rule definition is incorrect. *)
         subst ps0 c. clear H. clear X0.
         pose proof (dersrec_double_verb _ _ _ _ _ d) as [d1 [d2 [Hin1 Hin2]]].
         pose proof (@merge_ex V) as XX.
         edestruct XX as [G3 HG3].
         eapply struct_equiv_weak_refl.
         eapply derrec_mergeL.
         exact HG3.
         eapply LNSKt_cut_admissibility; [ | | reflexivity | reflexivity | reflexivity | reflexivity | exact HG3 | ..].
         +++{ eapply X. 2 : reflexivity. Unshelve.
              3:{ exact d1. }
              apply Lt.le_lt_n_Sm. rewrite Heqn2.
              eapply dersrec_derrec_height. 
              assumption.
            }
         +++{ eapply X. 2 : reflexivity. Unshelve. 2:{ exact d2. }
              apply Lt.le_lt_n_Sm. rewrite Heqn2.
              eapply dersrec_derrec_height.
              assumption.
            }
         +++{ simpl. apply struct_equiv_str_refl.
            }
       }
   }
Defined.

Print Assumptions LNSKt_cut_elimination. 
