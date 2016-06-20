open Lambda 
open Sexplib

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

type view = 
  {    
    goal : string;
    preuve : string;
    hypo : string;
    validate : bool;
  }


(* -------------------Fonctions pour manipuler la structure de goal_c --------------*)
let init_view = {goal = "()"; preuve = "()"; hypo = "()"; validate = false }
let init_view_arg g p h v = {goal = g; preuve = p; hypo = h; validate = v }


let concat_view_goal g str = {goal = g.goal ^ str; preuve = g.preuve; hypo = g.hypo; validate = g.validate }
let concat_view_preuve g str = {goal = g.goal; preuve = g.preuve ^ str; hypo = g.hypo; validate = g.validate }
let concat_view_hypo g str = {goal = g.goal; preuve = g.preuve; hypo = g.hypo  ^ str; validate = g.validate }
let validate_view g = {goal = g.goal; preuve = g.preuve; hypo = g.hypo; validate = true } 
let unvalidate_view_hypo g = {goal = g.goal; preuve = g.preuve; hypo = g.hypo; validate = false } 

let pretty_print_view g = 
  g.hypo ^ "\n==========" ^ g.goal ^ " |- " ^ g.preuve

let create_request g tact var = 
  "((goal " ^ g.goal ^ ") (env (" ^ g.hypo ^ ")) " ^ g.preuve ^ " " ^ tact ^ " " ^ var ^ ")"


(* fonctions simulant une requete réseau *)
let send_to_serv str = 
  Serveur.main str


(* problème à régler, si le fichier de texte à lire n'existe pas il n'éxécute pas le programme *)
let receive_answer = 
  let file = open_in "reponse_serv.txt" in 
  input_line file

(* il faut que je rajoute il champ de validation dans la réponse du serveur donc modifier cette fonction par la suite *)
let parse_answer str= 
  match str with 
  | Sexp.List[g;e;t;b] -> 
     init_view_arg (Sexp.to_string g) (Sexp.to_string t) (Sexp.to_string e) (if (Sexp.to_string b) = "true" then true else false)
  | _ -> failwith ("pase_answer not good answer" ^ Sexp.to_string str)
     
  
		   

(* passage en mode impératif afin d'initialiser l'interface pour que cela soit beau *)
(* message de présentation *)

let () = Printf.printf "\n\n-------------------------------\n"; 
	 Printf.printf "      interface cool       \n";
	 Printf.printf "-------------------------------\n"; 
	 Printf.printf "\n\n Entrer un type à prouver:     \n"

(*lecture de la preuve *)
let type_to_proove = read_line ()

let intial_view = init_view_arg type_to_proove "(? lol)" "" false

(* this main is in progress it is not finish but it's for testing the REST architecture *)
let rec main current_view : view=
  let () = Printf.printf "\n%s\n" (pretty_print_view current_view);
	   Printf.printf "\nput your next tactique\n" in
  let tactic = read_line () in 
  let () = Printf.printf "\nput a name for the variable\n"  in
  let var = read_line () in 
  let request = create_request current_view tactic var in 
  let () = send_to_serv request in
  let answer = parse_answer (Sexp.of_string receive_answer) in
  if answer.validate
  then answer
  else main answer
  

(*


type view = 
  {    
    goal : string;
    preuve : string;
    hypo : string;
    validate : bool;
  }

 *)

(* a faire en rentrant de la pause, implémenter l'ensemble des fonctions du papier zipper j'en aurais besoin et commencer a bien faire 
le main du client *)
  
let res  = main intial_view



		       
