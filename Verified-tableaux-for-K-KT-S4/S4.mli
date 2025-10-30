
type __ = Obj.t

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

type nnf =
| Var of string
| Neg of string
| And of nnf * nnf
| Or of nnf * nnf
| Box of nnf
| Dia of nnf

val nnf_eqdec : nnf -> nnf -> bool

val neg_nnf : nnf -> nnf

val remove_nnf : nnf -> nnf list -> nnf list

val get_contra : nnf list -> string option

val get_and : nnf list -> (nnf*nnf) option

val get_or : nnf list -> (nnf*nnf) option

val get_box : nnf list -> nnf option

type fml =
| Varf of string
| Negf of fml
| Andf of fml * fml
| Orf of fml * fml
| Implf of fml * fml
| Boxf of fml
| Diaf of fml

val to_nnf : fml -> nnf

val filter_undia : nnf list -> nnf list -> nnf list

type seqt = { s_G : nnf list; s_S : nnf list; s_H : (nat*nnf) list;
              s_d : nat; s_c : bool; s_R : nnf list }

type sseqt = seqt

val and_child : nnf -> nnf -> seqt -> seqt

val and_child_sseqt : nnf -> nnf -> sseqt -> sseqt

val or_child_left : nnf -> nnf -> seqt -> seqt

val or_child_right : nnf -> nnf -> seqt -> seqt

val or_child_left_sseqt : nnf -> nnf -> sseqt -> sseqt

val or_child_right_sseqt : nnf -> nnf -> sseqt -> sseqt

val box_child_new : nnf -> seqt -> seqt

val box_child_new_sseqt : nnf -> sseqt -> sseqt

val box_child_dup : nnf -> seqt -> seqt

val box_child_dup_sseqt : nnf -> sseqt -> sseqt

val dia_child : nnf -> seqt -> seqt

val unmodal_seqt : seqt -> seqt list

type treem =
| Mcons of treem list * seqt * (nat*nnf) list * nnf list

val tm_children : treem -> treem list

val tm_req : treem -> (nat*nnf) list

val tm_htk : treem -> nnf list

val get_contra_seqt : seqt -> string option

val get_and_seqt : seqt -> (nnf*nnf) option

val get_or_seqt : seqt -> (nnf*nnf) option

val get_box_seqt : seqt -> nnf option

type open_info = treem

type node =
| Open of open_info
| Closed

val contra_rule_seqt : seqt -> string -> node

val and_rule_seqt : nnf -> nnf -> sseqt -> node -> node

val open_rule_seqt : nnf -> nnf -> sseqt -> open_info -> node

val or_rule_seqt : nnf -> nnf -> sseqt -> node -> node

val box_dup_rule_seqt : nnf -> sseqt -> node -> node

val box_new_rule_seqt : nnf -> sseqt -> node -> node

type dia_rule_return = (treem list, seqt) sum

val dia_rule : (sseqt -> __ -> node) -> seqt list -> dia_rule_return

val nnf_eqsnd : nnf -> (nat*nnf) -> bool

val dia_rule_loop : (nat*nnf) list -> nnf list -> nnf list -> (nat*nnf) list

val unmodal_batch_to_treem : sseqt -> treem list -> open_info

val tableau : sseqt -> node

val mk_root : nnf list -> seqt

val mk_root_sseqt : nnf list -> sseqt

val tableau_sat : nnf list -> bool

val fml_tableau_sat : fml list -> bool

val is_sat : fml -> bool
