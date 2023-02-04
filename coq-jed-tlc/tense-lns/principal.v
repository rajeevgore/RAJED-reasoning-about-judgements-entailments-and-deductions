Add LoadPath "../general".
Require Import ssreflect.
Require Import Lia.

Require Import existsT.
Require Import gen genT gen_seq.
Require Import ddT.
Require Import dd_fc.
Require Import List_lemmasT.
Require Import lntT lntacsT lntmtacsT.
Require Import lntkt_exchT.
Require Import lnt_weakeningT.
Require Import lnt_contraction_mrT.
(*
Require Import lntlsT lntbRT lntb1LT lntb2LT.
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

 *)


Require Import size.
 
Set Implicit Arguments.


Inductive principal_ImpR {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) Γ1 Γ2 Δ1 Δ2 :=
| princ_ImpR_I G' H B C d
   (D2 : dersrec rules prems H)
   (rl : rules H G)  :
    G = G' ++ [(Γ1++Γ2,Δ1++[A]++Δ2,d)] ->
    A = Imp B C ->
    H =  (map (nslcext G' d) (map (seqext Γ1 Γ2 Δ1 Δ2)
                                          [([B],[Imp B C; C])]  )) ->
    D = derI _ rl D2 ->
    principal_ImpR D A Γ1 Γ2 Δ1 Δ2. 

Inductive principal_ImpL {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) Γ1 Γ2 Δ1 Δ2 :=
| princ_ImpL_I G' H B C d
   (D2 : dersrec rules prems H)
   (rl : rules H G)  :
    G = G' ++ [(Γ1++[A]++Γ2,Δ1++Δ2,d)] ->
    A = Imp B C ->
    H =  (map (nslcext G' d) (map (seqext Γ1 Γ2 Δ1 Δ2)
                                  [ ([Imp B C ; C], []) ; ([Imp B C],[B]) ] )) ->
    D = derI _ rl D2 ->
    principal_ImpL D A Γ1 Γ2 Δ1 Δ2.

Inductive principal_Id_pfc {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ1 Γ2 Δ1 Δ2 : list (PropF V)) :=
| princ_Id_pfc_I G' H p (d:dir)
   (D2 : dersrec rules prems H)
   (rl : rules H G)  :
    G = G' ++ [(Γ1++[A]++Γ2,Δ1++[A]++Δ2,d)] ->
    A = Var p ->
    H = [] ->
    D = derI _ rl D2 ->
    principal_Id_pfc D A Γ1 Γ2 Δ1 Δ2.

Inductive principal_BotL_pfc {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ1 Γ2 Δ : list (PropF V)) :=
| princ_BotL_pfc_I G' H (d:dir) 
   (D2 : dersrec rules prems H)
   (rl : rules H G)  :
    G = G' ++ [(Γ1++[A]++Γ2,Δ,d)] ->
    A = (Bot V) ->
    H = [] ->
    D = derI _ rl D2 ->
    principal_BotL_pfc D A Γ1 Γ2 Δ. 

Inductive principal_WBox2Rs {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) Γ Δ1 Δ2 :=
| princ_WB2Rs_I G' H B
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ, Δ1 ++ [A] ++ Δ2, fwd)] ->
    A = WBox B ->
    H = (map (nslclext G') [ [(Γ, Δ1 ++ [WBox B] ++ Δ2, fwd) ; (@nil (PropF V), [B], fwd) ]] ) ->
         D = derI _ rl D2 ->
         principal_WBox2Rs D A Γ Δ1 Δ2.

Inductive principal_BBox2Rs {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) Γ Δ1 Δ2 :=
| princ_BB2Rs_I G' H B
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ, Δ1 ++ [A] ++ Δ2, bac)] ->
    A = BBox B ->
    H = (map (nslclext G') [ [(Γ, Δ1 ++ [BBox B] ++ Δ2, bac) ; (@nil (PropF V), [B], bac) ]] ) ->
         D = derI _ rl D2 ->
         principal_BBox2Rs D A Γ Δ1 Δ2.

Inductive principal_WBox1Rs {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ Δ1 Δ2 Σ Π1 Π2 : list (PropF V)) :=
| princ_WB1Rs_I G' H B d
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ, Δ1 ++ Δ2, d) ; (Σ, Π1 ++ [A] ++ Π2, bac)] ->
    A = WBox B ->
    H = (map (nslclext G') [
               [(Γ, Δ1 ++ [B] ++ Δ2, d) ; (Σ, Π1 ++ [WBox B] ++ Π2, bac)] ;
               [(Γ, Δ1 ++ Δ2, d) ; (Σ, Π1 ++ [WBox B] ++ Π2, bac) ; ([],[B],fwd)] ]) ->
    D = derI _ rl D2 ->
    principal_WBox1Rs D A Γ Δ1 Δ2 Σ Π1 Π2.

Inductive principal_BBox1Rs {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ Δ1 Δ2 Σ Π1 Π2 : list (PropF V)) :=
| princ_BB1Rs_I G' H B d
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ, Δ1 ++ Δ2, d) ; (Σ, Π1 ++ [A] ++ Π2, fwd)] ->
    A = BBox B ->
    H = (map (nslclext G') [
               [(Γ, Δ1 ++ [B] ++ Δ2, d) ; (Σ, Π1 ++ [BBox B] ++ Π2, fwd)] ;
               [(Γ, Δ1 ++ Δ2, d) ; (Σ, Π1 ++ [BBox B] ++ Π2, fwd) ; ([],[B],bac)] ]) ->
    D = derI _ rl D2 ->
    principal_BBox1Rs D A Γ Δ1 Δ2 Σ Π1 Π2.

Inductive principal_WBox2Ls {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ1 Γ2 Δ Σ1 Σ2 Π : list (PropF V)) :=
| princ_WB2Ls_I G' H B d
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ1 ++ Γ2, Δ, d) ; (Σ1 ++ [A] ++ Σ2, Π, bac)] ->
    A = WBox B ->
    H = (map (nslclext G') [
               [(Γ1 ++ [B] ++ Γ2, Δ, d)]]) ->
    D = derI _ rl D2 ->
    principal_WBox2Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π.


Inductive np_WB2Ls_wf {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V)
          I J
          (Φ1 Φ2 Ξ : list (PropF V)) (d : dir) : Type :=
| np_WB2Ls_wf_I : G = I ++ [(Φ1 ++ [A] ++ Φ2, Ξ, d)] ++ J ->
                  np_WB2Ls_wf D A I J Φ1 Φ2 Ξ d.

Inductive not_principal_WBox2Ls_pre {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V)
         (I J : list (list (PropF V) * list (PropF V) * dir))
          (Φ1 Φ2 Ξ : list (PropF V)) (d : dir) : Type :=
| nprinc_WB2Ls_nwb : not_wbox A ->
                     not_principal_WBox2Ls_pre D A I J Φ1 Φ2 Ξ d
| nprinc_WB2Ls_dir : d = fwd ->
                     not_principal_WBox2Ls_pre D A I J Φ1 Φ2 Ξ d
| nprinc_WB2Ls_not_last : J <> [] ->
                          not_principal_WBox2Ls_pre D A I J Φ1 Φ2 Ξ d
| nprinc_WB2Ls_last_not_princ_fml (G' : list (list (PropF V) * list (PropF V) * dir)) H B d2 Γ1 Γ2 Σ1 Σ2 Δ Π
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ1 ++ Γ2, Δ, d2) ; (Σ1 ++ [WBox B] ++ Σ2, Π, bac)] ->
    H = (map (nslclext G') [
               [(Γ1 ++ [B] ++ Γ2, Δ, d)]]) ->
    D = derI _ rl D2 ->
    d = bac ->
    J = [] ->
    A <> WBox B ->
    not_principal_WBox2Ls_pre D A I J Φ1 Φ2 Ξ d
| nprinc_WB2Ls_last_princ G' H B d2 Γ1 Γ2 Σ1 Σ2 Δ Π
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ1 ++ Γ2, Δ, d2) ; (Σ1 ++ [WBox B] ++ Σ2, Π, bac)] ->
    H = (map (nslclext G') [
               [(Γ1 ++ [B] ++ Γ2, Δ, d)]]) ->
    D = derI _ rl D2 ->
    d = bac ->
    J = [] ->
    A = WBox B ->
    Σ1 <> Φ1 ->
    not_principal_WBox2Ls_pre D A I J Φ1 Φ2 Ξ d.

Inductive not_principal_WBox2Ls {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V)
         (I J : list (list (PropF V) * list (PropF V) * dir))
         (Φ1 Φ2 Ξ : list (PropF V)) (d : dir) : Type :=
| np_wb2L_wf : np_WB2Ls_wf D A I J Φ1 Φ2 Ξ d ->
               not_principal_WBox2Ls_pre D A I J Φ1 Φ2 Ξ d ->
               not_principal_WBox2Ls D A I J Φ1 Φ2 Ξ d.

Inductive principal_BBox2Ls {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ1 Γ2 Δ Σ1 Σ2 Π : list (PropF V)) :=
| princ_BB2Ls_I G' H B d
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ1 ++ Γ2, Δ, d) ; (Σ1 ++ [A] ++ Σ2, Π, fwd)] ->
    A = BBox B ->
    H = (map (nslclext G') [
               [(Γ1 ++ [B] ++ Γ2, Δ, d)]]) ->
    D = derI _ rl D2 ->
    principal_BBox2Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π.

Inductive principal_WBox1Ls {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ1 Γ2 Δ Σ1 Σ2 Π : list (PropF V)) :=
| princ_WB1Ls_I G' H B d
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ1 ++ [A] ++ Γ2, Δ, d) ; (Σ1 ++ Σ2, Π, fwd)] ->
    A = WBox B ->
    H = (map (nslclext G') [
               [(Γ1 ++ [WBox B] ++ Γ2, Δ, d) ;
                  (Σ1 ++ [B] ++ Σ2, Π, fwd)]]) ->
    D = derI _ rl D2 ->
    principal_WBox1Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π.

Inductive principal_BBox1Ls {V : Set} {rules prems G} (D : derrec rules prems G) (A : PropF V) (Γ1 Γ2 Δ Σ1 Σ2 Π : list (PropF V)) :=
| princ_BB1Ls_I G' H B d
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    G = G' ++ [(Γ1 ++ [A] ++ Γ2, Δ, d) ; (Σ1 ++ Σ2, Π, bac)] ->
    A = BBox B ->
    H = (map (nslclext G') [
               [(Γ1 ++ [BBox B] ++ Γ2, Δ, d) ;
                  (Σ1 ++ [B] ++ Σ2, Π, bac)]]) ->
    D = derI _ rl D2 ->
    principal_BBox1Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π.

Inductive principal_WBR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G)
          (A : PropF V) (Γ Δ1 Δ2 : list (PropF V))  :=
| princ_WB1Rs Σ Π1 Π2 : principal_WBox1Rs D A Σ Π1 Π2 Γ Δ1 Δ2 ->
                           principal_WBR D A Γ Δ1 Δ2
| princ_WB2Rs : principal_WBox2Rs D A Γ Δ1 Δ2 ->
                   principal_WBR D A Γ Δ1 Δ2.

Inductive principal_BBR {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G)
          (A : PropF V) (Γ Δ1 Δ2 : list (PropF V)) :=
| princ_BB1Rs Σ Π1 Π2 : principal_BBox1Rs D A Σ Π1 Π2 Γ Δ1 Δ2 ->
                           principal_BBR D A Γ Δ1 Δ2
| princ_BB2Rs : principal_BBox2Rs D A Γ Δ1 Δ2 ->
                   principal_BBR D A Γ Δ1 Δ2.

Inductive principal_not_box_R  {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G)
          (A : PropF V) (Γ Δ1 Δ2 : list (PropF V)) :=
| princ_nb_Id Γ1 Γ2 : Γ = Γ1 ++ [A] ++ Γ2 ->
                      principal_Id_pfc D A Γ1 Γ2 Δ1 Δ2 ->
                         principal_not_box_R D A Γ Δ1 Δ2
| princ_nb_ImpR Γ1 Γ2 : Γ = Γ1 ++ Γ2 ->
                        principal_ImpR D A Γ1 Γ2 Δ1 Δ2 ->
                     principal_not_box_R D A Γ Δ1 Δ2.

(*
Inductive principal_not_box_R  {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G)
          (A : PropF V) (Γ Δ1 Δ2 : list (PropF V)) :=
| princ_nb_Id Γ1 Γ2 : Γ = Γ1 ++ [A] ++ Γ2 -> principal_Id_pfc D A Γ1 Γ2 Δ1 Δ2 ->
                         principal_not_box_R D A Γ Δ1 Δ2
| princ_nb_ImpR Γ1 Γ2 : Γ = Γ1 ++ [A] ++ Γ2 -> principal_ImpR D A Γ1 Γ2 Δ1 Δ2 ->
                     principal_not_box_R D A Γ Δ1 Δ2.

 *)

Inductive last_rule_EW {V : Set} {rules prems G} (D : derrec rules prems G) :=
| lr_EW H (H' : list (rel (list (PropF V)) * dir)) seq
    (D2 : dersrec rules prems H)
    (rl : rules H G) :
    H = [H'] ->
    G = H' ++ [seq] ->
    D = derI _ rl D2 ->
    last_rule_EW D.


Lemma principal_WBR_fwd:
  forall {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G)
         A Γ Δ1 Δ2 H Σ Π,                                
    principal_WBR D A Γ Δ1 Δ2 ->
    G = (H ++ [(Σ,Π,fwd)]) ->
    principal_WBox2Rs D A Γ Δ1 Δ2.
Proof.
  intros until 0; intros Hprinc Heq.
  inversion Hprinc.
  inversion X.  subst.
  change (G' ++ [_ ; _]) with (G' ++ [(Σ0, Π1 ++ Π2, d)] ++ [(Γ, Δ1 ++ [WBox B] ++ Δ2, bac)] ) in H1.
  rewrite app_assoc in H1. 
  eapply tail_inv_singleton in H1.
  destruct H1 as [H1 H2].
  inversion H2.
  inversion X. assumption.
Qed.

Lemma principal_WBR_bac:
  forall {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G)
         A Γ Δ1 Δ2 H Σ Π,                                
    principal_WBR D A Γ Δ1 Δ2 ->
    G = (H ++ [(Σ,Π,bac)]) ->
    existsT2 Σ Π1 Π2, principal_WBox1Rs D A Σ Π1 Π2 Γ Δ1 Δ2.
Proof.
  intros until 0; intros Hprinc Heq.
  inversion Hprinc.
  do 3 eexists. eassumption.
  inversion X.  subst.
  change (G' ++ [_ ; _]) with (G' ++ [(Σ0, Π1 ++ Π2, d)] ++ [(Γ, Δ1 ++ [WBox B] ++ Δ2, bac)] ) in H1.
  rewrite app_assoc in H1. 
  eapply tail_inv_singleton in H1.
  destruct H1 as [H1 H2].
  inversion H2.
Qed.

Lemma principal_BBR_fwd:
  forall {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G)
         A Γ Δ1 Δ2 H Σ Π,                                
    principal_BBR D A Γ Δ1 Δ2 ->
    G = (H ++ [(Σ,Π,fwd)]) ->
    existsT2 Σ Π1 Π2, principal_BBox1Rs D A Σ Π1 Π2 Γ Δ1 Δ2.
Proof.
  intros until 0; intros Hprinc Heq.
  inversion Hprinc.
  do 3 eexists. eassumption.
  inversion X.  subst.
  change (G' ++ [_ ; _]) with (G' ++ [(Σ0, Π1 ++ Π2, d)] ++ [(Γ, Δ1 ++ [BBox B] ++ Δ2, bac)] ) in H1.
  rewrite app_assoc in H1. 
  eapply tail_inv_singleton in H1.
  destruct H1 as [H1 H2].
  inversion H2.
Qed.

Lemma principal_BBR_bac:
  forall {V : Set} {G} (D : derrec (@LNSKt_rules V) (fun _ => False) G)
         A Γ Δ1 Δ2 H Σ Π,                                
    principal_BBR D A Γ Δ1 Δ2 ->
    G = (H ++ [(Σ,Π,bac)]) ->
    principal_BBox2Rs D A Γ Δ1 Δ2.
Proof.
  intros until 0; intros Hprinc Heq.
  inversion Hprinc.
  inversion X.  subst.
  change (G' ++ [_ ; _]) with (G' ++ [(Σ0, Π1 ++ Π2, d)] ++ [(Γ, Δ1 ++ [BBox B] ++ Δ2, fwd)] ) in H1.
  rewrite app_assoc in H1. 
  eapply tail_inv_singleton in H1.
  destruct H1 as [H1 H2].
  inversion H2.
  inversion X. assumption.
Qed.


Lemma principal_LNSKt_rules : forall {V : Set} {G}
                                     (D : derrec (@LNSKt_rules V) (fun _ => False) G), 
    
    (existsT2 A Γ1 Γ2 Δ1 Δ2, principal_ImpL D A Γ1 Γ2 Δ1 Δ2) +
    (existsT2 A Γ1 Γ2 Δ1 Δ2, principal_ImpR D A Γ1 Γ2 Δ1 Δ2) +
    (existsT2 A Γ1 Γ2 Δ1 Δ2, principal_Id_pfc D A Γ1 Γ2 Δ1 Δ2) +
    (existsT2 A Γ1 Γ2 Δ, principal_BotL_pfc D A Γ1 Γ2 Δ) +
    (existsT2 A Γ1 Γ2 Δ Σ1 Σ2 Π, principal_WBox1Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π) +
    (existsT2 A Γ1 Γ2 Δ Σ1 Σ2 Π, principal_WBox2Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π) +
    (existsT2 A Γ Δ1 Δ2 Σ Π1 Π2, principal_WBox1Rs D A Γ Δ1 Δ2 Σ Π1 Π2) +
    (existsT2 A Γ Δ1 Δ2, principal_WBox2Rs D A Γ Δ1 Δ2) +
    (existsT2 A Γ1 Γ2 Δ Σ1 Σ2 Π, principal_BBox1Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π) +
    (existsT2 A Γ1 Γ2 Δ Σ1 Σ2 Π, principal_BBox2Ls D A Γ1 Γ2 Δ Σ1 Σ2 Π) +
    (existsT2 A Γ Δ1 Δ2 Σ Π1 Π2, principal_BBox1Rs D A Γ Δ1 Δ2 Σ Π1 Π2) +
    (existsT2 A Γ Δ1 Δ2, principal_BBox2Rs D A Γ Δ1 Δ2) +
    last_rule_EW D.
Proof.
  intros V G D.
  remember D as D'.
  destruct D' as [| ps concl rl Ds]. contradiction.
  inversion rl as [ ps' c' nsrl | ps' c' nsrl | ps' c' nsrl | ps' c' nsrl | ps' c' nsrl | ps' c' nsrl ]; [
    subst ps' c'; inversion nsrl as [ps' c' G rl2]; subst ps concl; inversion rl2; try subst c' ps'  .. |
    subst ps' c'; inversion nsrl as [ps' c' G d rl2]; subst ps concl; inversion rl2 as [ps c ? ? ? ? rl3]; try subst c' ps'].

     do 5 left. right. do 4 eexists.
     econstructor; reflexivity.
     do 1 left. right. do 4 eexists.
     econstructor; reflexivity.

    
     do 6 left. right. do 7 eexists.
     econstructor; reflexivity.
     do 2 left. right. do 7 eexists.
     econstructor; reflexivity.

     do 7 left. right. do 7 eexists.
     econstructor; reflexivity.
     do 3 left. right. do 7 eexists.
     econstructor; reflexivity.

     do 8 left. right. do 7 eexists.
     econstructor; reflexivity.
     do 4 left. right. do 7 eexists.
     econstructor; reflexivity.

     unfold nslclext in Ds. simpl in Ds.
     right. econstructor.
     reflexivity.
     unfold nslclext. rewrite <- (app_nil_r G) at 1.
     reflexivity. reflexivity.

     inversion rl3; subst ps c.
     do 10 left. right. do 5 eexists.
     econstructor; reflexivity.
     unfold nslcext in Ds. unfold seqext in Ds.
     simpl in Ds.
     do 11 left. right. do 5 eexists.
     econstructor; reflexivity.
     do 12 left. do 5 eexists.
     econstructor; reflexivity.
     do 9 left. right. do 4 eexists.
     econstructor; reflexivity.
Qed.

Inductive last_rule_one_antitoneL {V : Set} {G rules prems} (D : derrec rules prems G)
            H I A (Γ1 Γ2 Δ : list (PropF V)) (d : dir) : Type :=
| lr_one_at G' I' Γ1' Γ2' Δ'
            (rl : rules [G'] G)
            (D2 : dersrec rules prems [G']) :
    G = H ++ [(Γ1 ++ [A] ++ Γ2, Δ, d)] ++ I ->
    G' = H ++ [(Γ1' ++ [A] ++ Γ2', Δ', d)] ++ I' ->
    (forall B, InT B Γ1 -> InT B Γ1') ->
    (forall B, InT B Γ2 -> InT B Γ2') ->
    (forall B, InT B Δ -> InT B Δ') ->
    D = derI _ rl D2 ->
    last_rule_one_antitoneL D H I A Γ1 Γ2 Δ d.


Lemma principal_ImpR_last_rule_one_antitoneL : forall {V : Set} {rules prems G} (D : derrec rules prems G)
                  H I Γ1 Γ2 Δ Σ1 Σ2 Π1 Π2 (A B : PropF V) (d : dir),
          A <> B ->
          G = H ++ [(Γ1 ++ [A] ++ Γ2, Δ, d)] ++ I ->
        principal_ImpR D B Σ1 Σ2 Π1 Π2 -> 
          last_rule_one_antitoneL D H I A Γ1 Γ2 Δ d.
Proof.
  intros until 0.
  intros Hnot Heq Hprinc.
  inversion Hprinc.
  subst.
  apply partition_2_2T in H1.
  sD. destruct H1; discriminate.
  subst. unfold nslcext in *. unfold seqext in *.
  simpl in *.

  inversion H2.
  destruct (list_insert1 _ _ _ _ A B0 H1) as [l1 [l2 [[Hleq Hin1] Hin2]]].
  econstructor.
  6:{ reflexivity. }
  rewrite app_nil_r. reflexivity.
  rewrite Hleq.
  erewrite app_nil_r.
  subst d. reflexivity.
  assumption.
  assumption.
  subst.
  intros B HB.
  eapply InT_appE in HB.
  destruct HB as [HB | HB].
  apply InT_appL. assumption.
  apply InT_appR.
  inversion HB. subst. econstructor. reflexivity.
  subst. econstructor 2. econstructor 2.
  assumption.

  subst.
  econstructor. reflexivity.
  5 :{ reflexivity. }
  unfold nslcext. simpl.
  rewrite <- app_assoc. simpl.
  reflexivity.
  all : firstorder.
Qed.
