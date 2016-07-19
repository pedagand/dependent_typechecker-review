open Tactics
open Zipper

let rec main (Loc(t,p)) = 
  let () = Printf.printf "%s\n" (pretty_print_state_proof (Loc(t,p))) in
  match p with 
  | Node([],Top,[]) -> main (procedure_start_definition (Loc(t,p)))
  | _ -> let arbre = ((choose_tactic ())(Loc(t,p))) in 
	 (* ici je mettrais les traitements post techniques *)
	 main arbre
	 




let arbre = main (Loc(Section([]),Node([],Top,[])))
