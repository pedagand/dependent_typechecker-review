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
  | _ -> failwith "create_uper_terme : it's good enought"

(* permet de parcourir un pi type jusqu'au bout afin d'en connaitre le type de retour *)
let rec find_return_type typ = 
  match typ with 
  | Pi(n,s,t) -> find_return_type t 
  | x -> x

(* fonction prenant un argument un type et son nom . Celle ci retourne une location avec le uper_type générer en haut de 
l'arbre et le curseur sur un noeud donné en entrée *)
let init_definition typ name = 
  let return = find_return_type typ in 
  let new_type = create_uper_type typ in 
  let new_term = create_uper_terme typ return in
  let new_name = String.uppercase name in 
  Definition(new_name,Complete(new_type,new_term))
  
let parse_definition def = 
  match def with 
  | Sexp.List[Sexp.Atom name;terme] -> 
     Definition(name,Incomplete((parse_term [] terme),Hole_inTm(0)))
  | _ -> failwith "parse_definition : it seem's that your def is not good"

let procedure_start_definition = 
  let () = Printf.printf "\n\nEntrer une nouvelle définition à prouver : \n" in 
  let typ_not_parsed = read_line () in
  let second_def = parse_definition (Sexp.of_string typ_not_parsed) in
  match second_def with 
  | Definition(name,Incomplete(typ,terme)) -> 
     let first_def = init_definition typ name in
     failwith "lol"
  | _ -> failwith "lol"
  

let rec main (Loc(t,p)) = 
  match p with 
  | Top -> Loc(procedure_start_definition,Top)
  
  


(*let intro (Loc(t,p)) = 
  let () = Printf.printf "\n Please put a name for the variable : \n" in 
  let variable = read_line () in *)
  
			 
	   

