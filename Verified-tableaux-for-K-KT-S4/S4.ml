
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y



type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y::l0 -> let s = h y a in if s then true else in_dec h a l0

(** val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove eq_dec x = function
| [] -> []
| y::tl -> if eq_dec x y then remove eq_dec x tl else y::(remove eq_dec x tl)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x::tl -> if f x then Some x else find f tl

type nnf =
| Var of string
| Neg of string
| And of nnf * nnf
| Or of nnf * nnf
| Box of nnf
| Dia of nnf

(** val nnf_eqdec : nnf -> nnf -> bool **)

let rec nnf_eqdec n x =
  match n with
  | Var p -> (match x with
              | Var p0 -> (=) p p0
              | _ -> false)
  | Neg p -> (match x with
              | Neg p0 -> (=) p p0
              | _ -> false)
  | And (phi, psi) ->
    (match x with
     | And (phi0, psi0) ->
       if nnf_eqdec phi phi0 then nnf_eqdec psi psi0 else false
     | _ -> false)
  | Or (phi, psi) ->
    (match x with
     | Or (phi0, psi0) ->
       if nnf_eqdec phi phi0 then nnf_eqdec psi psi0 else false
     | _ -> false)
  | Box phi -> (match x with
                | Box phi0 -> nnf_eqdec phi phi0
                | _ -> false)
  | Dia phi -> (match x with
                | Dia phi0 -> nnf_eqdec phi phi0
                | _ -> false)

(** val neg_nnf : nnf -> nnf **)

let rec neg_nnf = function
| Var p -> Neg p
| Neg p -> Var p
| And (phi, psi) -> Or ((neg_nnf phi), (neg_nnf psi))
| Or (phi, psi) -> And ((neg_nnf phi), (neg_nnf psi))
| Box phi -> Dia (neg_nnf phi)
| Dia phi -> Box (neg_nnf phi)

(** val remove_nnf : nnf -> nnf list -> nnf list **)

let remove_nnf =
  remove nnf_eqdec

(** val get_contra : nnf list -> string option **)

let rec get_contra = function
| [] -> None
| y::l0 ->
  (match get_contra l0 with
   | Some a -> Some a
   | None ->
     (match y with
      | Var p ->
        let s = in_dec nnf_eqdec (Neg p) l0 in if s then Some p else None
      | Neg p ->
        let s = in_dec nnf_eqdec (Var p) l0 in if s then Some p else None
      | _ -> None))

(** val get_and : nnf list -> (nnf*nnf) option **)

let rec get_and = function
| [] -> None
| y::l0 ->
  (match get_and l0 with
   | Some a -> Some a
   | None -> (match y with
              | And (phi, psi) -> Some (phi,psi)
              | _ -> None))

(** val get_or : nnf list -> (nnf*nnf) option **)

let rec get_or = function
| [] -> None
| y::l0 ->
  (match get_or l0 with
   | Some a -> Some a
   | None -> (match y with
              | Or (phi, psi) -> Some (phi,psi)
              | _ -> None))

(** val get_box : nnf list -> nnf option **)

let rec get_box = function
| [] -> None
| y::l0 ->
  (match get_box l0 with
   | Some a -> Some a
   | None -> (match y with
              | Box phi -> Some phi
              | _ -> None))

type fml =
| Varf of string
| Negf of fml
| Andf of fml * fml
| Orf of fml * fml
| Implf of fml * fml
| Boxf of fml
| Diaf of fml

(** val to_nnf : fml -> nnf **)

let rec to_nnf = function
| Varf p -> Var p
| Negf phi -> neg_nnf (to_nnf phi)
| Andf (phi, psi) -> And ((to_nnf phi), (to_nnf psi))
| Orf (phi, psi) -> Or ((to_nnf phi), (to_nnf psi))
| Implf (phi, psi) -> Or ((neg_nnf (to_nnf phi)), (to_nnf psi))
| Boxf phi -> Box (to_nnf phi)
| Diaf phi -> Dia (to_nnf phi)

(** val filter_undia : nnf list -> nnf list -> nnf list **)

let rec filter_undia l1 = function
| [] -> []
| n::tl ->
  (match n with
   | Dia phi ->
     if in_dec nnf_eqdec phi l1
     then filter_undia l1 tl
     else phi::(filter_undia l1 tl)
   | _ -> filter_undia l1 tl)

type seqt = { s_G : nnf list; s_S : nnf list; s_H : (nat*nnf) list;
              s_d : nat; s_c : bool; s_R : nnf list }

type sseqt = seqt

(** val and_child : nnf -> nnf -> seqt -> seqt **)

let and_child phi psi s =
  { s_G = (phi::(psi::(remove_nnf (And (phi, psi)) s.s_G))); s_S = s.s_S;
    s_H = s.s_H; s_d = s.s_d; s_c = false; s_R = s.s_R }

(** val and_child_sseqt : nnf -> nnf -> sseqt -> sseqt **)

let and_child_sseqt =
  and_child

(** val or_child_left : nnf -> nnf -> seqt -> seqt **)

let or_child_left phi psi s =
  { s_G = (phi::(remove_nnf (Or (phi, psi)) s.s_G)); s_S = s.s_S; s_H =
    s.s_H; s_d = s.s_d; s_c = false; s_R = s.s_R }

(** val or_child_right : nnf -> nnf -> seqt -> seqt **)

let or_child_right phi psi s =
  { s_G = (psi::(remove_nnf (Or (phi, psi)) s.s_G)); s_S = s.s_S; s_H =
    s.s_H; s_d = s.s_d; s_c = false; s_R = s.s_R }

(** val or_child_left_sseqt : nnf -> nnf -> sseqt -> sseqt **)

let or_child_left_sseqt =
  or_child_left

(** val or_child_right_sseqt : nnf -> nnf -> sseqt -> sseqt **)

let or_child_right_sseqt =
  or_child_right

(** val box_child_new : nnf -> seqt -> seqt **)

let box_child_new phi s =
  { s_G = (phi::(remove_nnf (Box phi) s.s_G)); s_S = ((Box phi)::s.s_S);
    s_H = []; s_d = s.s_d; s_c = false; s_R = s.s_R }

(** val box_child_new_sseqt : nnf -> sseqt -> sseqt **)

let box_child_new_sseqt =
  box_child_new

(** val box_child_dup : nnf -> seqt -> seqt **)

let box_child_dup phi s =
  { s_G = (phi::(remove_nnf (Box phi) s.s_G)); s_S = s.s_S; s_H = s.s_H;
    s_d = s.s_d; s_c = false; s_R = s.s_R }

(** val box_child_dup_sseqt : nnf -> sseqt -> sseqt **)

let box_child_dup_sseqt =
  box_child_dup

(** val dia_child : nnf -> seqt -> seqt **)

let dia_child phi s =
  { s_G = (phi::s.s_S); s_S = s.s_S; s_H = (((S s.s_d),phi)::s.s_H); s_d = (S
    s.s_d); s_c = true; s_R = s.s_R }

(** val unmodal_seqt : seqt -> seqt list **)

let unmodal_seqt s =
  map (fun phi -> dia_child phi s) (filter_undia (map snd s.s_H) s.s_G)

type treem =
| Mcons of treem list * seqt * (nat*nnf) list * nnf list

(** val tm_children : treem -> treem list **)

let tm_children = function
| Mcons (l, _, _, _) -> l

(** val tm_req : treem -> (nat*nnf) list **)

let tm_req = function
| Mcons (_, _, req, _) -> req

(** val tm_htk : treem -> nnf list **)

let tm_htk = function
| Mcons (_, _, _, htk) -> htk

(** val get_contra_seqt : seqt -> string option **)

let get_contra_seqt se =
  get_contra se.s_G

(** val get_and_seqt : seqt -> (nnf*nnf) option **)

let get_and_seqt se =
  get_and se.s_G

(** val get_or_seqt : seqt -> (nnf*nnf) option **)

let get_or_seqt se =
  get_or se.s_G

(** val get_box_seqt : seqt -> nnf option **)

let get_box_seqt se =
  get_box se.s_G

type open_info = treem

type node =
| Open of open_info
| Closed

(** val contra_rule_seqt : seqt -> string -> node **)

let contra_rule_seqt _ _ =
  Closed

(** val and_rule_seqt : nnf -> nnf -> sseqt -> node -> node **)

let and_rule_seqt phi psi ss = function
| Open w ->
  Open (Mcons ((tm_children w), ss, (tm_req w), ((And (phi,
    psi))::(tm_htk w))))
| Closed -> Closed

(** val open_rule_seqt : nnf -> nnf -> sseqt -> open_info -> node **)

let open_rule_seqt phi psi ss w =
  Open (Mcons ((tm_children w), ss, (tm_req w), ((Or (phi,
    psi))::(tm_htk w))))

(** val or_rule_seqt : nnf -> nnf -> sseqt -> node -> node **)

let or_rule_seqt phi psi ss = function
| Open w ->
  Open (Mcons ((tm_children w), ss, (tm_req w), ((Or (phi,
    psi))::(tm_htk w))))
| Closed -> Closed

(** val box_dup_rule_seqt : nnf -> sseqt -> node -> node **)

let box_dup_rule_seqt phi ss = function
| Open w ->
  Open (Mcons ((tm_children w), ss, (tm_req w), ((Box phi)::(tm_htk w))))
| Closed -> Closed

(** val box_new_rule_seqt : nnf -> sseqt -> node -> node **)

let box_new_rule_seqt phi ss = function
| Open w ->
  Open (Mcons ((tm_children w), ss, (tm_req w), ((Box phi)::(tm_htk w))))
| Closed -> Closed

type dia_rule_return = (treem list, seqt) sum

(** val dia_rule : (sseqt -> __ -> node) -> seqt list -> dia_rule_return **)

let rec dia_rule f = function
| [] -> Inl []
| g::ltl ->
  (match f g __ with
   | Open o ->
     (match dia_rule f ltl with
      | Inl s -> Inl (o::s)
      | Inr s -> Inr s)
   | Closed -> Inr g)

(** val nnf_eqsnd : nnf -> (nat*nnf) -> bool **)

let nnf_eqsnd phi p =
  if nnf_eqdec (snd p) phi then true else false

(** val dia_rule_loop :
    (nat*nnf) list -> nnf list -> nnf list -> (nat*nnf) list **)

let rec dia_rule_loop h b = function
| [] -> []
| n::gtl ->
  (match n with
   | Dia phi ->
     (match find (nnf_eqsnd phi) h with
      | Some p -> p::(dia_rule_loop h b gtl)
      | None -> dia_rule_loop h b gtl)
   | _ -> dia_rule_loop h b gtl)

(** val unmodal_batch_to_treem : sseqt -> treem list -> open_info **)

let unmodal_batch_to_treem ss h =
  Mcons (h, ss, (dia_rule_loop ss.s_H ss.s_S ss.s_G), ss.s_G)

(** val tableau : sseqt -> node **)

let rec tableau x =
  let filtered_var = get_contra_seqt x in
  (match filtered_var with
   | Some s -> contra_rule_seqt x s
   | None ->
     let filtered_var0 = get_and_seqt x in
     (match filtered_var0 with
      | Some s ->
        let phi,psi = s in
        and_rule_seqt (fst (phi,psi)) (snd (phi,psi)) x
          (tableau (and_child_sseqt (fst (phi,psi)) (snd (phi,psi)) x))
      | None ->
        let filtered_var1 = get_or_seqt x in
        (match filtered_var1 with
         | Some s ->
           let phi,psi = s in
           let filtered_var2 =
             tableau (or_child_left_sseqt (fst (phi,psi)) (snd (phi,psi)) x)
           in
           (match filtered_var2 with
            | Open w -> open_rule_seqt (fst (phi,psi)) (snd (phi,psi)) x w
            | Closed ->
              or_rule_seqt (fst (phi,psi)) (snd (phi,psi)) x
                (tableau
                  (or_child_right_sseqt (fst (phi,psi)) (snd (phi,psi)) x)))
         | None ->
           let filtered_var2 = get_box_seqt x in
           (match filtered_var2 with
            | Some s ->
              let filtered_var3 = in_dec nnf_eqdec (Box s) x.s_S in
              if filtered_var3
              then box_dup_rule_seqt s x (tableau (box_child_dup_sseqt s x))
              else box_new_rule_seqt s x (tableau (box_child_new_sseqt s x))
            | None ->
              let filtered_var3 =
                dia_rule (fun x0 _ -> tableau x0) (unmodal_seqt x)
              in
              (match filtered_var3 with
               | Inl bl -> Open (unmodal_batch_to_treem x bl)
               | Inr _ -> Closed)))))

(** val mk_root : nnf list -> seqt **)

let mk_root g =
  { s_G = g; s_S = []; s_H = []; s_d = O; s_c = false; s_R = g }

(** val mk_root_sseqt : nnf list -> sseqt **)

let mk_root_sseqt =
  mk_root

(** val tableau_sat : nnf list -> bool **)

let tableau_sat g =
  match tableau (mk_root_sseqt g) with
  | Open _ -> true
  | Closed -> false

(** val fml_tableau_sat : fml list -> bool **)

let fml_tableau_sat g =
  tableau_sat (map to_nnf g)

(** val is_sat : fml -> bool **)

let is_sat phi =
  fml_tableau_sat (phi::[])
