open Lambda 

(* ce fichier représente le client de l'assistant de preuve *)
(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "interface.ml";;
*)

(* Au final pour que ce soit réellement une architecture rest il serait 
judicieux que le client n'ai aucune informations quand à la représentation
concrète des termes ect.. il ne devrait manipuler que des chaines de caractères
et recevoir de nouvelles chaines *)

type goal_c = 
  {
    theoreme : string;
    preuve : string;
    hypo : string;
    validate : bool;
  }


(* this is a tree with zipper structure for better navigation in the proof *)
type tree = 
  | Item of goal_c
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




(* 
type goal_c = 
  {
    theoreme : string;
    preuve : string;
    hypo : string;
    validate : bool;
  }
 *)

(* -------------------Fonctions pour manipuler la structure de goal_c --------------*)
let init_goal_c = {theoreme = ""; preuve = ""; hypo = ""; validate = false }

let concat_goal_theoreme g str = {theoreme = g.theoreme ^ str; preuve = g.preuve; hypo = g.hypo; validate = g.validate }
let concat_goal_preuve g str = {theoreme = g.theoreme; preuve = g.preuve ^ str; hypo = g.hypo; validate = g.validate }
let concat_goal_hypo g str = {theoreme = g.theoreme; preuve = g.preuve; hypo = g.hypo  ^ str; validate = g.validate }
let validate_goal_hypo g = {theoreme = g.theoreme; preuve = g.preuve; hypo = g.hypo; validate = true } 
let unvalidate_goal_hypo g = {theoreme = g.theoreme; preuve = g.preuve; hypo = g.hypo; validate = false } 

let pretty_print_goal_c g = 
  g.hypo ^ "\n==========" ^ g.theoreme ^ " |- " ^ g.preuve

let create_request g tact var = 
  "((goal " ^ g.theoreme ^ ") (env (" ^ g.hypo ^ ") " ^ g.preuve ^ " " ^ tact ^ " " ^ var ")"







(* fonctions simulant une requete réseau *)
let send_to_serv str = 
  Serveur.main str


(* ça reprend tout bien c'est pas mal *)
let receive_answer = 
  let file = open_in "reponse_serv.txt" in 
  input_line file
  
		   

(* passage en mode impératif afin d'initialiser l'interface pour que cela soit beau *)
(* message de présentation *)

let () = Printf.printf "\n\n-------------------------------\n"; 
	 Printf.printf "      interface cool       \n";
	 Printf.printf "-------------------------------\n"; 
	 Printf.printf "\n\n Entrer un type à prouver:     \n"

(*lecture de la preuve *)


let type_to_proove = read (read_line ())			       





let rec main finish =
  match finish with
  | "lol" -> let () = Printf.printf "\nput your next tactique\n"  in
     let tactic = read_line () in
	 let () = Printf.printf "%s" tactic in
	 (* ici j'appliquerai la tactique *)
	 if true 
	 then main "lol"
	 else main "l"
  | _ -> ()


(* a faire en rentrant de la pause, implémenter l'ensemble des fonctions du papier zipper j'en aurais besoin et commencer a bien faire 
le main du client *)
  



let () = main "lol"



		       
