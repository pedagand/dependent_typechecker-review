open Lambda

(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "zipper.ml";;
*)

(* le premier inTm correpond au type et le second au terme *)
type definition = 
  | Complete of inTm * inTm 
  | Incomplete of inTm * inTm 

(* le premier inTm correspond au type et le second au terme *)
type noeud = 
  | Variable of string * inTm 
  | Definition of string * definition
  | Intermediaire of inTm * inTm 

type tree =
  | Item of noeud     
  | Section of tree list

type path =
  | Top
  | Node of tree list * path * tree list
  
type location = Loc of tree * path
  
(* -----------------Fonctions d'affichage-------------- *)
let pretty_print_definition def = 
  match def with 
  | Complete(typ,terme) -> "type ::" ^ pretty_print_inTm typ [] ^ "terme ::" ^ pretty_print_inTm terme []
  | Incomplete(typ,terme) -> "type ::" ^ pretty_print_inTm typ [] ^ "terme ::" ^ pretty_print_inTm terme []

let pretty_print_item_debug item = 
  match item with 
  | Item(Variable(name,term)) -> "(Var " ^ name ^ " : " ^ pretty_print_inTm term [] ^ ")"
  | Item(Definition(name,def)) -> "(Def " ^ name ^ " : " ^ pretty_print_definition def ^ ")"
  | Item(Intermediaire(typ,terme)) -> "(Inter " ^ pretty_print_inTm typ [] ^ " " ^ pretty_print_inTm terme [] ^ ")"
  | Section(x) -> failwith "pretty_print_inTm : can't print a section" 

let rec pretty_print_tree_liste tree_liste = 
  match tree_liste with 
  | [] -> ""
  | Item(x) :: suite -> pretty_print_item_debug (Item(x)) ^ " ; " ^ pretty_print_tree_liste suite
  | Section(x) :: suite -> pretty_print_tree (Section(x))
and pretty_print_tree sec =
  match sec with 
  | Section(y) -> "\n[" ^ pretty_print_tree_liste y ^ "]\n"
  | Item(x) -> "\n[" ^ pretty_print_item_debug (Item(x)) ^ "]\n"

let rec pretty_print_node nod = 
  match nod with 
  | Node(left,up,right) -> "(left " ^ pretty_print_tree_liste left ^ ")(up " ^ pretty_print_node up ^ ")(right " ^ 
					pretty_print_tree_liste right ^ ")"
  | Top -> "Top"


let pretty_print_location loc = 
  match loc with 
  | Loc(pointeur,Top) -> "\nZip : " ^ pretty_print_tree pointeur ^ "Top\n"
  | Loc(pointeur,chemin) -> "Zip : \n" ^ pretty_print_tree pointeur ^ "\n Path : \n" ^ pretty_print_node chemin

		     

											 



(* permet de retrouver le type d'une variable dans la section si celle ci existe *)
(* let rec find_var_section sec var = 
   match sec with 
   | Section([]) -> failwith "find_var_section : can't find the var, reach empty list" 
   | Section(elem :: suite) -> 
      begin
       match elem with 
       | Item(Variable(name,typ)) -> if var = name 
				     then typ
				     else find_var_section (Section(suite)) var
       | _ -> find_var_section (Section(suite)) var
      end
   | _ -> failwith "find_var_section : need to give a section not an item"

let rec find_var (Loc(t,p)) var = 
  match t with 
  | Item(Variable(name,typ)) -> if var = name 
				then typ 
				else find_var 
 *)




  
  
(* -----------Fonctions de navigation---------------*)
let go_left (Loc(t,p)) = match p with
  | Top -> failwith "left of top"
  | Node(l::left,up,right) -> Loc(l,Node(left,up,t::right))
  | Node([],up,right) -> failwith "left of first"
				  
let go_right (Loc(t,p)) = match p with
  | Top -> failwith "right of top"
  | Node(left,up,r::right) -> Loc(r,Node(t::left,up,right))
  | _ -> failwith "right of last"
		  
		  
let go_up (Loc(t,p)) = match p with
  | Top -> failwith "up of top"
  | Node(left,up,right) -> Loc(Section((List.rev left) @ (t::right)),up)
			      
let go_down (Loc(t,p)) = match t with
    Item(_) -> failwith "down of item"
  | Section(t1::trees) -> Loc(t1,Node([],p,trees))
  | _ -> failwith "down of empty"

(* To print a location we need a function that return the location at the top of the entiere tree *)
let rec go_to_the_top (Loc(t,p)) = 
  match p with 
    Top -> (Loc(t,p))
  | _ -> go_up (Loc(t,p))


(* -----------Fonctions de recherche --------------- *)

(* Fonctions permettants de récupérer l'ensemble des définitions terminée à partir d'une position *)
let rec get_def_item it env = 
  match it with 
  | Definition(name,Complete(typ,terme)) -> ((name,typ,terme) :: env)
  | _ -> env 
and get_def_tree_liste tree_liste env = 
  match tree_liste with 
  | [] -> env 
  | Item(Definition(name,Complete(typ,terme))) :: [] -> ((name,typ,terme) :: env)
  | Item(Definition(name,Complete(typ,terme))) :: suite -> get_def_tree_liste suite ((name,typ,terme) :: env)
  | other :: suite -> get_def_tree_liste suite env
and get_def (Loc(t,p)) env = 
  match t,p with 
  | (Section(x),Top) -> get_def_tree_liste x env
  | (Item(x),Top) -> get_def_item x env
  | (Section(x),p) -> get_def (go_up (Loc(t,p))) (get_def_tree_liste x env)
  | (Item(x),p) -> get_def (go_up (Loc(t,p))) (get_def_item x env)

let rec print_def env = 
  match env with 
  | [] -> ""
  | (name,typ,terme) :: suite -> "(" ^ name ^ " :: " ^ pretty_print_inTm typ [] ^ " : " ^ pretty_print_inTm terme []
				 ^ ")" ^ print_def suite

(* A TEEEEEEEEEEESSSSSSSSSSSSSSSSSTTTTTTTTTTTTTTTEEEEEEEEEERRRRRRRRR *)
let get_and_print_def arbre = 
  let env = get_def arbre [] in 
  print_def env


(* Fonctions permettants de crée une liste de paires (name,type) *)
let rec get_env_item it env= 
  match it with 
  | Variable(name,typ) -> ((name,typ) :: env)
  | _ -> env
and get_env_tree_liste tree_liste env = 
  match tree_liste with 
  | (Item(Variable(name,typ))) :: [] -> ((name,typ) :: env)
  | (Item(Variable(name,typ))) :: suite -> get_env_tree_liste suite ((name,typ) :: env) 
  | other :: suite -> get_env_tree_liste suite env
  | [] -> env
and get_env (Loc(t,p)) env =
  match t,p with 
  | (Section(x),Top) -> get_env_tree_liste x env
  | (Item(x),Top) -> get_env_item x env
  | (Section(x),p) -> get_env (go_up (Loc(t,p))) (get_env_tree_liste x env)
  | (Item(x),p) -> get_env (go_up (Loc(t,p))) (get_env_item x env)
		    
(* Fonctions permettants d'afficher une liste de paires (name,type) *)

let rec print_env env = 
  match env with 
  | [] -> ""
  | (name,typ) :: suite -> "(" ^ name ^ " : " ^ pretty_print_inTm typ [] ^ ") " ^ print_env suite

let get_and_print_env arbre = 
  let env = get_env arbre [] in 
  print_env env

(* affichage avec l'environnement de la preuve ect *)
let pretty_print_item item = 
  match item with 
  | Item(Variable(name,term)) -> "(Var " ^ name ^ " : " ^ pretty_print_inTm term [] ^ ")"
  | Item(Definition(name,def)) -> "(Def " ^ name ^ " : " ^ pretty_print_definition def ^ ")"
  | Item(Intermediaire(typ,terme)) -> "(Inter " ^ pretty_print_inTm typ [] ^ " : " ^ pretty_print_inTm terme [] ^ ")"
  | Section(x) -> failwith "pretty_print_inTm : can't print a section" 
let pretty_print_state_proof (Loc(t,p)) = 
  let env = get_and_print_env (Loc(t,p)) in
  match t with 
  | Item(x) -> "---------Environment : ------------\n" ^ 
		 env ^ 
		   "\n----------Current goal ------------\n" ^    
		   pretty_print_item (Item(x)) 
  | _ -> "It seem's that your on nothing, try to navigate ...." 
	
  






		 
(*------------------Fonctions de manipulation --------------*)

let replace_item (Loc(t,p)) tsub = 
  match t with 
  | Item(_) -> Loc(tsub,p)
  | _ -> failwith "replac_item : you are supposed to change an item" 

let complete_focus_terme (Loc(t,p)) tsub num = 
  match t with 
  | Item(Intermediaire(typ,terme)) -> Loc(Item(Intermediaire(typ,(replace_hole_inTm terme tsub num))),p)
  | Item(Definition(name,Complete(typ,terme))) -> Loc(Item(Definition(name,Complete(typ,(replace_hole_inTm terme tsub num)))),p)
  | Item(Definition(name,Incomplete(typ,terme))) -> Loc(Item(Definition(name,Incomplete(typ,(replace_hole_inTm terme tsub num)))),p)
  | _ -> failwith "complete_focus_terme : you can't get the type of something else than an item"

let get_type_focus (Loc(t,p)) = 
  match t with 
  | Item(Intermediaire(typ,terme)) -> typ
  | Item(Definition(name,Complete(typ,terme))) -> typ
  | Item(Definition(name,Incomplete(typ,terme))) -> typ
  | _ -> failwith "get_type_focus : you can't get the type of something else than an item"

let get_terme_focus (Loc(t,p)) = 
  match t with 
  | Item(Intermediaire(typ,terme)) -> terme
  | Item(Definition(name,Complete(typ,terme))) -> terme
  | Item(Definition(name,Incomplete(typ,terme))) -> terme
  | _ -> failwith "get_terme_focus : you can't get the type of something else than an item"
 

let insert_right (Loc(t,p)) r = match p with
    Top -> failwith "insert of top"
  | Node(left,up,right) -> Loc(t,Node(left,up,r::right))

let insert_left (Loc(t,p)) l = match p with
Top -> failwith "insert of top"
| Node(left,up,right) -> Loc(t,Node(l::left,up,right))

let insert_down (Loc(t,p)) t1 = 
  match t with
  | Item(_) -> failwith "down of item"
  | Section(sons) -> Loc(t1,Node([],p,sons))

let delete (Loc(_,p)) = match p with
Top -> failwith "delete of top"
| Node(left,up,r::right) -> Loc(r,Node(left,up,right))
| Node(l::left,up,[]) -> Loc(l,Node(left,up,[]))
| Node([],up,[]) -> Loc(Section[],up)


(* ----------------Fonctions de recherche------------------ *)


