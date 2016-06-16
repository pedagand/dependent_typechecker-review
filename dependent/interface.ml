open Lambda 

(* ce fichier représente le client de l'assistant de preuve *)
(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "interface.ml";;
*)

(* this is a tree with zipper structure for better navigation in the proof *)
type tree = 
  | Item of inTm 
  | Section of tree list

type path = 
  | Top 
  | Node of tree list * path * tree list 

type location = 
 | Proof of tree * path

let go_left (Proof(t,p)) =
  match p with 
  | Top -> failwith "fin de l'arbre"
  | Node(l::left,up,right) -> Proof(l,Node(left,up,t::right))
  | Node([],up,right) -> failwith "left of first"

let go_right (Proof(t,p)) = 
  match p with 
  | Top -> failwith "fin de l'arbre"
  | Node(left,up,r::right) -> Proof(r,Node(t::left,up,right))
  | Node(left,up,[]) -> failwith "left of first"

let go_up (Proof(t,p)) = 
  match p with
  | Top -> failwith "up of top"
  | Node(left,up,right) -> Proof(Section((List.rev left) @ (t::right)),up)

let go_down (Proof(t,p)) = 
  match t with
  |Item(_) -> failwith "down of item"
  | Section(t1::trees) -> Proof(t1,Node([],p,trees))
  | _ -> failwith "down of empty"



(* message de présentation *)

let () = Printf.printf "\n\n-------------------------------\n"; 
	 Printf.printf "      interface cool       \n";
	 Printf.printf "-------------------------------\n"; 
	 Printf.printf "\n\n Entrer un type à prouver:     \n"

(*lecture de la preuve *)
let type_to_proove = read_line ()



let rec main finish =
  match finish with
  | 1 -> let () = Printf.printf "\nput your next tactique\n"  in
     let tactic = read_line () in
	 let () = Printf.printf "%s" tactic in
	 (* ici j'appliquerai la tactique *)
	 if true 
	 then main 1
	 else main 0
  | _ -> ()

  



let () = main 1



		       
