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
  | Node([],up,right) -> failwith "left of first"

let go_right (Loc(t,p)) = match p with
    Top -> failwith "right of top"
  | Node(left,up,r::right) -> Loc(r,Node(t::left,up,right))
  | _ -> failwith "right of last"

let go_up (Loc(t,p)) = match p with
    Top -> failwith "up of top"
  | Node(left,up,right) -> Loc(Section((List.rev left) @ (t::right)),up)

let go_down (Loc(t,p)) = match t with
    Item(_) -> failwith "down of item"
  | Section(t1::trees) -> Loc(t1,Node([],p,trees))
  | _ -> failwith "down of empty"

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

