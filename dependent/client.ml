open Lambda 
open Sexplib
open ArbreZip


(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "client.ml";;
*)

(* fichier client 2.0 *)





(* fonctions d'initialisations des view ainsi que de l'initialisation d'un arbre *)
let init_view = {goal = "()"; preuve = "()"; hypo = "()"; validate = false }
let init_view_arg g p h v = {goal = g; preuve = p; hypo = h; validate = v }

let init_location (first_view : view) = 
  Loc(Item(first_view),Top)





let pretty_print_view g = 
  g.hypo ^ "\n==============\n" ^ g.goal ^ " |- " ^ g.preuve


(* fonctions permettant la communication avec le serveur *)

let create_request g tact var = 
  "((goal " ^ g.goal ^ ") (env (" ^ g.hypo ^ ")) " ^ g.preuve ^ " " ^ tact ^ " " ^ var ^ ")"

let send_to_serv str = 
  Serveur.main str

let rec parse_answer_env str = 
  match str with 
  | Sexp.List [Sexp.Atom "env"; Sexp.List l] -> 
     (string_of_list (List.map create_string_couples l))
  | _ -> failwith "parse_env Request doesn't have the good shape"
and create_string_couples str = 
  match str with 
  | Sexp.List[Sexp.Atom a; Sexp.Atom "," ;t] -> 
     "(" ^  a ^ " , " ^ (pretty_print_inTm (parse_term [] t) []) ^ ")"
  | _ -> failwith "create_hypo Request doesn't have the good shape"
and string_of_list li = 
  match li with 
  | [] -> ""
  | x :: reste -> x ^ " " ^ string_of_list reste
and parse_answer_goal str = 
  match str with 
  | Sexp.List[Sexp.Atom "goal";l] ->
     pretty_print_inTm (parse_term [] l) [] 
  | _ -> failwith "parse_goal Request doesn't have the good shape"

(* parse_answer retourne une liste de views, il faut ensuite prendre cette liste et l'insérer dans une section *)		  
let parse_answer str= 
  match str with 
  | Sexp.List[Sexp.Atom "true"] -> (init_view_arg "" "" "" true) :: []
  | Sexp.List[Sexp.Atom "false"] -> (init_view_arg "" "" "" false) :: [] 
  | Sexp.List[Sexp.List[Sexp.Atom "goal";g];e;t;b] -> 
     let li = init_view_arg (pretty_print_inTm (parse_term [] g) [])
			    (pretty_print_inTm (parse_term [] t) [])
			    (parse_answer_env e) 
			    (if (Sexp.to_string b) = "true" then true else false) in 
     let () = Printf.printf "\n env = %s\n" (Sexp.to_string e) in 
     li :: []
  | Sexp.List[Sexp.List[Sexp.Atom "goals";Sexp.List goals_l];e;t;b] -> 
     let goals_liste = List.map (function x -> (pretty_print_inTm (parse_term [] x) [])) goals_l in 
     List.map (function x -> init_view_arg x (pretty_print_inTm (parse_term [] t) [])
					   (parse_answer_env e)
					   (if (Sexp.to_string b) = "true" then true else false)) goals_liste
  | _ -> failwith ("\nparse_answer not good answer : " ^ Sexp.to_string str)



(* lorsque l'on insère une nouvelle sections de goals on la place tout à gauche (cela permet de descendre plus rapidement dans la preuve) *)
let rec insert_answer_in_tree (Loc(t,p)) elem = 
  match p with
    Top -> failwith "left of top"
  | Node(l::left,up,right) -> insert_answer_in_tree (Loc(l,Node(left,up,t::right))) elem
  | Node([],up,right) -> insert_left (Loc(t,p)) elem


(* transforme une liste de view en une section pour insérer dans l'arbre *)
let liste_view_to_section lst = 
  List.map (fun x -> Item(x)) lst 


(* ------------------------------Debut du main du programme-------------------------- *)

let () = Printf.printf "\n\n-------------------------------\n"; 
	 Printf.printf "      MotoroLoL        \n";
	 Printf.printf "-------------------------------\n"; 
	 Printf.printf "\n\n Entrer un théorème à prouver     \n"
let type_to_proove = read_line ()

let arbre = ref (init_location (init_view_arg type_to_proove "(? init)" "" false))

let rec main  =		
  let () = Printf.printf "\n%s\n" (pretty_print_view (get_current !arbre));
	   Printf.printf "\nput your next tactique or left,right,up,down to navigate throught the proof\n" in
  let tactic_or_navig = read_line () in 
    match tactic_or_navig with
    | "left" -> let () = arbre := go_left (!arbre) in main
    | "right" -> let () = arbre := go_right (!arbre) in main
    | "up" -> let () = arbre := go_up (!arbre) in main 
    | "down" -> let () = arbre := go_down (!arbre) in main 
    | _ -> 
  let () = Printf.printf "\nput the options of your tactic (if no option type no)\n"  in
  let opt = read_line () in 
  let request = create_request (get_current !arbre) tactic_or_navig opt in 
  let () = send_to_serv request in
  let receive_answer = 
    begin 
      let file = open_in "reponse_serv.txt" in   
      let res = input_line file in 
      let () = close_in file in 
      res
    end in 
  failwith
 (* let ()  = arbre := (parse_answer (Sexp.of_string receive_answer)) in )*)
  


				












