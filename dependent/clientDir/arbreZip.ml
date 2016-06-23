open Lambda 
(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "arbre_zip.ml";;
 *)

(* Ce fichier contient l'ensemble des définitions de types ainsi que des fonctions permettants au client de naviguer dans une preuve *)


type view = 
  {    
    goal : string;
    preuve : string;
    hypo : string;
    validate : bool;
  }


let rec pretty_print_view g = 
  g.hypo ^ "\n==============\n |- " ^ g.goal ^ " : " ^ g.preuve ^ "      "


type tree =
  Item of view
  | Section of tree list

type path =
  Top
  | Node of tree list * path * tree list

type location = Loc of tree * path



let go_left (Loc(t,p)) = 
  match p with
    Top -> (Loc(t,p))
  | Node(l::left,up,right) -> Loc(l,Node(left,up,t::right))
  | Node([],up,right) -> (Loc(t,p))

let go_right (Loc(t,p)) = match p with
    Top -> (Loc(t,p))
  | Node(left,up,r::right) -> Loc(r,Node(t::left,up,right))
  | Node(left,up,[]) -> (Loc(t,p))

let go_up (Loc(t,p)) = match p with
    Top -> (Loc(t,p))
  | Node(left,up,right) -> Loc(Section((List.rev left) @ (t::right)),up)

let go_down (Loc(t,p)) = match t with
    Item(_) -> (Loc(t,p))
  | Section(t1::trees) -> Loc(t1,Node([],p,trees))
  | _ -> (Loc(t,p))


let get_current (Loc(i,p)) = 
  match i with 
  | Item(x) -> x
  | Section(Item(x) :: reste) -> x
  | _ -> failwith "get_current : liste seems to be empty"

let change (Loc(_,p)) t = Loc(t,p)

let insert_right (Loc(t,p)) r = match p with
    Top -> failwith "insert of top"
  | Node(left,up,right) -> Loc(t,Node(left,up,r::right))

let insert_left (Loc(t,p)) l = match p with
    Top -> failwith "insert of top"
  | Node(left,up,right) -> Loc(t,Node(l::left,up,right))

let insert_down (Loc(t,p)) t1 = match t with
    Item(_) -> failwith "down of item"
  | Section(sons) -> Loc(t1,Node([],p,sons))

let rec go_full_left (Loc(t,p)) = 
  match p with
    Top -> (Loc(t,p))
  | Node(l::left,up,right) -> go_full_left(Loc(l,Node(left,up,t::right)))
  | Node([],up,right) -> (Loc(t,p))

let go_back_proof (Loc(t,p)) = 
  match p with 
    Top -> (Loc(t,p))
  | Node(left,up,right) -> go_right(Loc(Section((List.rev left) @ (t::right)),up))

let go_down_proof (Loc(t,p)) = 
  let arbre_left = go_full_left (Loc(t,p)) in 
  (go_down arbre_left)

    
let rec do_n_shifting n direction arbre = 
  match n with 
  | 0 -> arbre
  | 100 -> go_back_proof(arbre)
  | _ -> 
     begin 
       match direction with
       | "left" -> do_n_shifting (n - 1) "left" (go_left arbre)
       | "right" ->do_n_shifting (n - 1) "right" (go_right arbre)
       | "up" -> do_n_shifting (n - 1) "up" (go_up arbre)
       | "down" -> do_n_shifting (n - 1) "down" (go_down arbre)
       | _ -> failwith "do_n-shifting not a good direction" 
     end
			   
  

let rec check_if_section_validate (Loc(i,p)) = 
  match (i,p) with 
  | ((Item x),(Node(left,up,[]))) -> if x.validate 
				     then true 
				     else false
  | ((Item x),(Node(left,up,right))) -> if x.validate 
					then check_if_section_validate (go_right (Loc(i,p)))
					else false
  | _ -> false


(* --------- Fonction d'affichage pour le débug -------- *)




let rec go_to_the_top (Loc(t,p)) = 
  match p with 
    Top -> (Loc(t,p))
  | Node(left,up,right) -> go_to_the_top(Loc(Section((List.rev left) @ (t::right)),up))

(* le i permet lors de l'affichage de numéroté les différentes view de la section *)
let rec pretty_print_section (Loc(t,p)) i= 
  match t with 
  | Item(x) -> failwith "not possible"
  | Section(Item(x) :: []) ->  string_of_int i ^ pretty_print_view x ^ "||||" 
  | Section(Section(x) :: []) -> "way to go down : " ^ string_of_int i ^ "||||"
  | Section(Item(x) :: left) ->  string_of_int i ^ pretty_print_view x ^ "||||" ^ pretty_print_section (go_right (Loc(t,p))) (i + 1)
  | Section(Section(x) :: left) -> "way to go down : " ^ string_of_int i ^ "||||"
  | _ -> failwith "pretty_print_section : this is not a good utilisation of this" 

			     


let rec pretty_print_location (Loc(t,p)) = 
  match p with
  | Top -> pretty_print_tree t 
  | Node(left,up,r::right) -> pretty_print_tree t ^ pretty_print_location (go_right ((Loc(t,p))))
  | Node(left,up,[]) -> pretty_print_tree t ^ "\n\n" ^ pretty_print_location (go_down ((Loc(t,p))))
and pretty_print_tree t = 
  match t with 
  | Item(x) -> pretty_print_view x
  | Section(x::suite) -> pretty_print_tree x ^ pretty_print_tree (Section(suite)) 
  | _ -> ""
