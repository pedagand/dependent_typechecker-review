open Tactics
open Zipper
open Compiler

let rec main ((Loc(t,p)),d) =   
  let () = Printf.printf "%s\n" (pretty_print_state_proof (Loc(t,p),d)) in
  let () = Printf.printf "\ndebug_pointeur def %s\n" (string_of_int d.pointeur) in
  let arbre = ((choose_tactic ()) (Loc(t,p),d)) in 
  (* ici je mettrais les traitements post techniques *)
  main arbre
	 


(* be carefull always init pointeur to 1 *)
let defi = {def = "";patAct = Clause_Top;pointeur = 1}

let arbre = main ((Loc(Section([]),Node([],Top,[]))),defi)
