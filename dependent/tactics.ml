open Zipper
open Lambda
open Sexplib


(* permet de crée un type à partir du type donné par l'utilisateur *)
let rec create_uper_type typ = 
  match typ with 
  | Pi(n,s,t) -> Pi(n,s,(create_uper_type t))
  | Nat -> Star
  | _ -> failwith "create_uper_type : only for pi at the moment"

(* permet à partir d'un type ainsi que du return du type initial de crée un terme *)
let rec create_uper_terme typ return = 
  match typ with 
  | Pi(n,s,t) -> Abs(n,create_uper_terme t return)
  | Star -> return
  | _ -> failwith "create_uper_terme : Only for pi at the moment "

(* permet de parcourir un pi type jusqu'au bout afin d'en connaitre le type de retour *)
let rec find_return_type typ = 
  match typ with 
  | Pi(n,s,t) -> find_return_type t 
  | x -> x

(* fonction prenant un argument un type et son nom . Celle ci retourne une location avec le uper_type générer en haut de 
l'arbre et le curseur sur un noeud donné en entrée *)
let init_definition typ name = 
  let return = find_return_type typ in 
  let () = Printf.printf "\nreturn : %s" (pretty_print_inTm return []) in
  let new_typ = create_uper_type typ in 
  let () = Printf.printf "\nnew_type : %s" (pretty_print_inTm new_typ []) in
  let new_term = create_uper_terme new_typ return in
  let () = Printf.printf "\nnew_term : %s" (pretty_print_inTm new_term []) in
  let new_name = String.uppercase name in 
  Definition(new_name,Complete(new_typ,new_term))
  
let parse_definition def = 
  match def with 
  | Sexp.List[Sexp.Atom name;terme] -> 
     Definition(name,Incomplete((parse_term [] terme),Hole_inTm(0)))
  | _ -> failwith "parse_definition : it seem's that your def is not good"

let procedure_start_definition arbre= 
  let () = Printf.printf "\n\nEntrer une nouvelle définition à prouver : \n" in 
  let typ_not_parsed = read_line () in
  let second_def = parse_definition (Sexp.of_string typ_not_parsed) in
  match second_def with 
  | Definition(name,Incomplete(typ,terme)) -> 
     let first_def = Section([Item(init_definition typ name)]) in          
     let arbre = (go_down(go_right(insert_right arbre first_def))) in 
     let arbre = (go_down(go_right(insert_right arbre (Section([Item(second_def)]))))) in 
     arbre
  | _ -> failwith "procedure_start_definition : something goes wrong during the creation of the definition"


(* ---------------- Routines de demande de saisies pour l'utilisateur ----------------------- *)
let ask_variable_name = 
  let () = Printf.printf "\n Please Choose a name for the var, (you can press enter and it will try to find a name for the var\n" in
  let var = read_line () in var
  
     





(* -------------- Ensemble des tactics ------------ *)
let intro (Loc(t,p)) = 
  let var = ask_variable_name in 
  let var = begin if var = "" 
		  then failwith "Intro : Enter doesnt work" (* modifier afin de crée une variable *)
		  else var 
	    end in 
  match t with 
  | Item(Variable(name,terme)) -> failwith "intro : You can't intro something which is not a def"
  | Item(Definition(name,Incomplete(typ,terme))) -> 
     let terme = replace_hole_inTm terme (Abs(Global var,Hole_inTm 1)) 1 in 
     let arbre = replace_item (Loc(t,p)) Item(terme) in
     let arbre = insert_right arbre (Section([terme])) in 
	 failwith
  | Item(Intermediaire(typ,terme)) -> failwith "don't know yet"
  | _ -> failwith "intro : this case is supposed to be impossible" 
			    

  

let rec main (Loc(t,p)) = 
  let () = Printf.printf "Start the programme \n%s\n" (pretty_print_location (go_to_the_top(Loc(t,p)))) in
  match p with 
  | Node([],Top,[]) -> main (procedure_start_definition (Loc(t,p)))
  | _ -> let () = Printf.printf "\nChoose a tactic \n" in
	 () 


let arbre = main (Loc(Section([]),Node([],Top,[])))
  
  


(*let intro (Loc(t,p)) = 
  let () = Printf.printf "\n Please put a name for the variable : \n" in 
  let variable = read_line () in *)
  
			 
	   

