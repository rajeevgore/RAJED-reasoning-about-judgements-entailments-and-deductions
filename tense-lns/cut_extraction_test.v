Require Import cut.
Require Import Extraction.

Extraction Language Haskell.

(* Extraction works, but takes a while. *)
Time Extraction LNSKt_cut_elimination.


(*
lNSKt_cut_elimination :: (List (Prod (Rel (List (PropF a1))) Dir)) -> (Derrec
                         (List (Prod (Rel (List (PropF a1))) Dir))
                         (LNSKt_cut_rules a1) ()) -> Derrec
                         (List (Prod (Rel (List (PropF a1))) Dir)) 
                         (LNSKt_rules a1) ()
lNSKt_cut_elimination ns h =
  let {n = derrec_height ns h} in
  lt_wf_indT n (\n0 x _ h0 _ ->
    case n0 of {
     O -> false_rect;
     S n1 ->
      case h0 of {
       DpI _ _ -> false_rect;
       DerI ps concl l d ->
        let {
         _evar_0_ = \_ ->
          eq_rect_r (dersrec_height ps d)
            (case l of {
              LNSKt_rules_woc ps0 c x0 ->
               eq_rect_r ps (\_ ->
                 eq_rect_r concl (\x1 -> DerI ps concl x1
                   (dersrecI_forall ps (\p hin ->
                     let {x2 = dersrecD_forall_in_dersrec ps d p hin} in
                     case x2 of {
                      ExistT d2 _ -> x (derrec_height p d2) __ p d2 __}))) c) ps0
                 __ x0;
              LNSKt_rules_wc ps0 c x0 ->
               eq_rect_r ps (\_ ->
                 eq_rect_r concl (\x1 ->
                   case x1 of {
                    NSlclctxt ps1 c0 g h1 ->
                     eq_rect (map (nslclext g) ps1) (\_ ->
                       eq_rect (nslclext g c0) (\h2 ->
                         eq_rect (nslclext g c0) (\l0 h' _ _ x2 ->
                           eq_rect (map (nslclext g) ps1) (\l1 d0 _ _ x3 ->
                             case h2 of {
                              Cut _UU0393_ _UU0394_1 _UU0394_2 _UU03a3_1 _UU03a3_2
                               _UU03a0_ d1 a ->
                               eq_rect
                                 (app (Cons (Cons (Pair (Pair _UU0393_
                                   (app _UU0394_1 (app (Cons a Nil) _UU0394_2)))
                                   d1) Nil) Nil) (Cons (Cons (Pair (Pair
                                   (app _UU03a3_1 (app (Cons a Nil) _UU03a3_2))
                                   _UU03a0_) d1) Nil) Nil)) (\_ ->
                                 eq_rect (Cons (Pair (Pair
                                   (app _UU0393_ (app _UU03a3_1 _UU03a3_2))
                                   (app _UU0394_1 (app _UU0394_2 _UU03a0_))) d1)
                                   Nil)
                                   (eq_rect
                                     (app (Cons (Cons (Pair (Pair _UU0393_
                                       (app _UU0394_1 (app (Cons a Nil) _UU0394_2)))
                                       d1) Nil) Nil) (Cons (Cons (Pair (Pair
                                       (app _UU03a3_1 (app (Cons a Nil) _UU03a3_2))
                                       _UU03a0_) d1) Nil) Nil))
                                     (\d2 l2 x4 _ _ h3 ->
                                     eq_rect (Cons (Pair (Pair
                                       (app _UU0393_ (app _UU03a3_1 _UU03a3_2))
                                       (app _UU0394_1 (app _UU0394_2 _UU03a0_)))
                                       d1) Nil) (\_ _ _ _ _ _ ->
                                       let {
                                        x5 = dersrec_double_verb
                                               (nslclext g (Cons (Pair (Pair
                                                 _UU0393_
                                                 (app _UU0394_1
                                                   (app (Cons a Nil) _UU0394_2)))
                                                 d1) Nil))
                                               (nslclext g (Cons (Pair (Pair
                                                 (app _UU03a3_1
                                                   (app (Cons a Nil) _UU03a3_2))
                                                 _UU03a0_) d1) Nil)) d2}
                                       in
                                       case x5 of {
                                        ExistT d3 s ->
                                         case s of {
                                          ExistT d4 _ ->
                                           let {
                                            s0 = merge_ex g g
                                                   (struct_equiv_weak_refl g)}
                                           in
                                           case s0 of {
                                            ExistT g3 hG3 ->
                                             derrec_mergeL g (Cons (Pair (Pair
                                               (app _UU0393_
                                                 (app _UU03a3_1 _UU03a3_2))
                                               (app _UU0394_1
                                                 (app _UU0394_2 _UU03a0_))) d1)
                                               Nil) g3 hG3
                                               (lNSKt_cut_admissibility
                                                 (app g (Cons (Pair (Pair _UU0393_
                                                   (app _UU0394_1
                                                     (app (Cons a Nil) _UU0394_2)))
                                                   d1) Nil))
                                                 (app g (Cons (Pair (Pair
                                                   (app _UU03a3_1
                                                     (app (Cons a Nil) _UU03a3_2))
                                                   _UU03a0_) d1) Nil))
                                                 (x
                                                   (derrec_height
                                                     (app g (Cons (Pair (Pair
                                                      _UU0393_ 
                                                      (app _UU0394_1 ...)) d1)
                                                      Nil)) d3) __
                                                   (app g (Cons (Pair (Pair
                                                     _UU0393_
                                                     (app _UU0394_1
                                                      (app (Cons a Nil) _UU0394_2)))
                                                     d1) Nil)) d3 __)
                                                 (x
                                                   (derrec_height
                                                     (app g (Cons (Pair (Pair
                                                      (app _UU03a3_1 ...) _UU03a0_)
                                                      d1) Nil)) d4) __
                                                   (app g (Cons (Pair (Pair
                                                     (app _UU03a3_1
                                                      (app (Cons a Nil) _UU03a3_2))
                                                     _UU03a0_) d1) Nil)) d4 __) g g
                                                 g3 (Pair _UU0393_
                                                 (app _UU0394_1
                                                   (app (Cons a Nil) _UU0394_2)))
                                                 (Pair
                                                 (app _UU03a3_1
                                                   (app (Cons a Nil) _UU03a3_2))
                                                 _UU03a0_) d1 _UU0393_ _UU0394_1
                                                 _UU0394_2 _UU03a3_1 _UU03a3_2
                                                 _UU03a0_ a hG3
                                                 (struct_equiv_str_refl g))}}}) c0
                                       l2 h' __ h3 __ x4) ps1 d0 l1 x3 __ __ h2) c0)
                                 ps1 __}) ps l0 d __ __ x2) concl l h0 __ __ x1)
                         concl) ps __ h1}) c) ps0 __ x0}) n1}
        in
        eq_rect_r (DerI ps concl l d) _evar_0_ h0 __}}) ns h __


<infomsg>Finished transaction in 47.135 secs (46.625u,0.156s) (successful)
</infomsg>
*)