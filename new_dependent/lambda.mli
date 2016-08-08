type ident = string
type name = 
  | Global of ident
  | Bound of int 
  | Quote of int
  | Hole of int

type 'a binder

type inTm =
  | Abs of inTm binder
  | Inv of exTm
  | Pi of (inTm * inTm) binder
  | Star
  | Zero
  | Succ of inTm
  | Nat
  | Liste of inTm 
  | Nil
  | Cons of inTm * inTm 
  | Vec of inTm * inTm
  | DNil of inTm
  | DCons of inTm * inTm 
  | Id of inTm * inTm * inTm
  | Refl   
  | Bool
  | True 
  | False	
  | Pair of inTm * inTm 
  | Sig of (inTm * inTm) binder
and exTm = 
  | Label of ident * inTm 
  | Ann of inTm * inTm 
  | Var of name 
  | Appl of exTm * inTm
  | Iter of inTm * inTm * inTm * inTm  
  | Transp of inTm * inTm * inTm * inTm * inTm * inTm 
  | P0 of exTm
  | P1 of exTm 
  | DFold of inTm * inTm * inTm * inTm * inTm * inTm 
  | Fold of inTm * inTm * inTm * inTm * inTm 
  | Ifte of inTm * inTm * inTm * inTm 

type value 
and neutral

val read : string -> inTm
val def_is_in_the_liste_inTm : (name * inTm * inTm) list -> string -> inTm
val freevars_inTm : inTm -> name list -> name list
val check_if_no_hole_inTm : inTm -> bool
val pretty_print_inTm : inTm -> string list -> string
val subst_inTm : inTm -> inTm -> inTm 
val abstract : name -> inTm -> inTm 
val change_name_var : inTm -> string -> string -> inTm 
val gen_hole : unit -> string 
val replace_hole : inTm -> name -> inTm -> inTm
val big_step_eval_inTm : inTm -> value list -> value
val value_to_inTm : int -> value -> inTm 
val equal : inTm -> inTm -> bool
val check_if_no_elem_inTm : inTm list -> inTm -> bool
val check : inTm -> inTm -> bool





