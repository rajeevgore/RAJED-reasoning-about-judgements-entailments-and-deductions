Add LoadPath "../general".
Require Import ssreflect.
Require Import Lia.

Require Import gen genT.
Require Import ddT.
Require Import dd_fc.
Require Import List_lemmasT.
Require Import gen_tacs lntT lntacsT lntlsT lntbRT lntmtacsT.
Require Import lntb1LT lntb2LT.
Require Import lntkt_exchT.
Require Import lnt_weakeningT.
Require Import lnt_contractionT.
Require Import existsT.
Require Import lnt_weakeningT lnt_contraction_mrT.
Require Import ind_lex.
Require Import contractedT weakenedT.
Require Import structural_equivalence.
Require Import merge.
Require Import lnt_gen_initT.
Require Import size principal.
Require Import cut_setup.
Require Import Lemma_Sixteen.

Set Implicit Arguments.


Theorem LNSKt_cut_admissibility : forall (V : Set) ns1 ns2
  (D1 : derrec (@LNSKt_rules V) (fun _ => False) ns1)
  (D2 : derrec (@LNSKt_rules V) (fun _ => False) ns2),
    can_gen_cut (@LNSKt_rules V) ns1 ns2.
Proof.
  unfold can_gen_cut.
  intros.
  destruct (Lemma_Sixteen (fsize(A), ((dp D1) + (dp D2))%nat))
           as [[[LS1 LS2] LS3] LS4].
  unfold SL in LS4. unfold SL_pre in LS4.
  subst.
  rewrite <- app_nil_r. rewrite <- app_assoc.
  eapply LS4. 
  apply PeanoNat.Nat.le_refl.
  apply PeanoNat.Nat.le_refl.
  eassumption. eassumption.
Defined.

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
  rewrite <- (app_nil_r Γ2).
  rewrite <- (app_nil_r Δ1).
  rewrite <- app_assoc.
  eapply D2; try reflexivity.
  assumption.
  apply struct_equiv_str_refl.
Qed.


(* --------------- *)
(* CUT ELIMINATION *)
(* --------------- *)

Inductive Cut_rule {V : Set} : rlsT (list (rel (list (PropF V)) * dir)) :=
| Cut : forall Γ Δ1 Δ2 Σ1 Σ2 Π d A, Cut_rule ([[(Γ,Δ1++[A]++Δ2,d)]] ++ [[(Σ1++[A]++Σ2,Π,d)]]) [(Γ++Σ1++Σ2,Δ1++Δ2++Π,d)].

(* LNSKt with cut: rules "WithOut Cut" (_woc) and "With Cut" (_wc). *)
Inductive LNSKt_cut_rules {V : Set} : rlsT (list (rel (list (PropF V)) * dir)) :=
| LNSKt_rules_woc : forall ps c, LNSKt_rules ps c -> LNSKt_cut_rules ps c
| LNSKt_rules_wc  : forall ps c, nslclrule (@Cut_rule V) ps c -> LNSKt_cut_rules ps c.


Theorem LNSKt_cut_elimination :
  forall {V : Set} ns,
    derrec (@LNSKt_cut_rules V) (fun _ => False) ns ->
    derrec (@LNSKt_rules V) (fun _ => False) ns.
Proof.
  intros V ns H.
  remember (derrec_height H) as n.
  revert Heqn. revert H. revert ns.
  induction n using lt_wf_indT.
(*  induction n using lt_wf_indT. *)
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
         pose proof (@dersrecD_forall_in_dersrec _ _ _ _ d _ Hin) as [d2 Hin2].
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
         pose proof (@dersrec_double_verb _ _ _ _ _ d) as [d1 [d2 [Hin1 Hin2]]].
         pose proof (@merge_ex V) as XX.
         edestruct XX as [G3 HG3].
         eapply struct_equiv_weak_refl.
         eapply derrec_mergeL.
         exact HG3.
         eapply LNSKt_cut_admissibility; [ | | reflexivity | reflexivity | reflexivity | reflexivity | exact HG3 | ..].
         +++{ eapply X. 2 : reflexivity. Unshelve.
              3:{ exact d1. }
              apply Lt.le_lt_n_Sm. rewrite Heqn2.
              eapply dersrec_derrec_height_le. 
              assumption.
            }
         +++{ eapply X. 2 : reflexivity. Unshelve. 2:{ exact d2. }
              apply Lt.le_lt_n_Sm. rewrite Heqn2.
              eapply dersrec_derrec_height_le.
              assumption.
            }
         +++{ simpl. apply struct_equiv_str_refl.
            }
       }
   }
Defined.

Print Assumptions LNSKt_cut_elimination. 


