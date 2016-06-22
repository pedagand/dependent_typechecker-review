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

let pretty_print_view g = 
  g.hypo ^ "\n==============\n |- " ^ g.goal ^ " : " ^ g.preuve ^ "\n"


type tree =
  Item of view
  | Section of tree list

type path =
  Top
  | Node of tree list * path * tree list

type location = Loc of tree * path



let go_left (Loc(t,p)) = match p with
    Top -> failwith "left of top"
  | Node(l::left,up,right) -> Loc(l,Node(left,up,t::right))
  | Node([],up,right) -> (Loc(t,p))

let go_right (Loc(t,p)) = match p with
    Top -> failwith "right of top"
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



(* --------- Fonction d'affichage pour le débug -------- *)




let rec go_to_the_top (Loc(t,p)) = 
  match p with 
    Top -> (Loc(t,p))
  | Node(left,up,right) -> go_to_the_top(Loc(Section((List.rev left) @ (t::right)),up))



let rec pretty_print_location (Loc(t,p)) = 
  match p with
  | Top -> pretty_print_tree t 
  | Node(left,up,r::right) -> pretty_print_tree t ^ pretty_print_location (go_right ((Loc(t,p))))
  | Node(left,up,[]) -> pretty_print_tree t ^ pretty_print_location (go_down ((Loc(t,p))))
and pretty_print_tree t = 
  match t with 
  | Item(x) -> pretty_print_view x
  | Section(x::suite) -> pretty_print_tree x ^ pretty_print_tree (Section(suite))
  | _ -> ""
