open Lambda 

(* ce fichier représente le client de l'assistant de preuve *)
(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "interface.ml";;
*)


type proof = 
  | Verif of inTm 
  | Synth of exTm


(* fonction pour gerer les flux d'entrées sortie avec le serveur qui ne sert a rien
il faut changer le délire *)
(* pour changer cela il faut juste que je modifie mon type contexte dans 
le rapport au lieu que ce soit une string il faut que ce soit la représentation 
concrète c'est à dire une liste de inTm *)
let string_to_context str = 
  List.map (fun x -> Str.split (Str.regexp ",") x) (Str.split (Str.regexp ";") str)


(* let read_stream deb =  *)
(*   | Report(Success(s),Contexte(c),Steps(e),Error(er)) ->  *)
     
  



(* this is a tree with zipper structure for better navigation in the proof *)
type tree = 
  | Item of proof
  | Section of tree list

type path = 
  | Top 
  | Node of tree list * path * tree list 

type location = 
 | Loc of tree * path





let go_left (Loc(t,p)) =
  match p with 
  | Top -> failwith "fin de l'arbre"
(* ici le nouveau Node crée dans la location on met l comme nouvelle position 
car la liste de gauche dans un node est renversée *)
  | Node(l::left,up,right) -> Loc(l,Node(left,up,t::right))
  | Node([],up,right) -> failwith "left of first"

let go_right (Loc(t,p)) = 
  match p with 
  | Top -> failwith "fin de l'arbre"
  | Node(left,up,r::right) -> Loc(r,Node(t::left,up,right))
  | Node(left,up,[]) -> failwith "left of first"

let go_up (Loc(t,p)) = 
  match p with
  | Top -> failwith "up of top"
  | Node(left,up,right) -> Loc(Section((List.rev left) @ (t::right)),up)

let go_down (Loc(t,p)) = 
  match t with
  |Item(_) -> failwith "down of item"
  | Section(t1::trees) -> Loc(t1,Node([],p,trees))
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



		       
