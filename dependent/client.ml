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
  Loc(Section(Item(first_view) :: []),(Node([],Top,[])))




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
     li :: []
  | Sexp.List[Sexp.List[Sexp.Atom "goals";Sexp.List goals_l];e;t;b] -> 
     let goals_liste = List.map (function x -> (pretty_print_inTm (parse_term [] x) [])) goals_l in 
     List.map (function x -> init_view_arg x (pretty_print_inTm (What("1")) [])
					   (parse_answer_env e)
					   (if (Sexp.to_string b) = "true" then true else false)) goals_liste
  | Sexp.List[Sexp.Atom "validate";t] -> (init_view_arg "" (pretty_print_inTm (parse_term [] t) []) "" true) :: []
  | _ -> failwith ("\nparse_answer not good answer : " ^ Sexp.to_string str)



(* lorsque l'on insère une nouvelle sections de goals on la place tout à gauche (cela permet de descendre plus rapidement dans la preuve) *)
let rec insert_answer_in_tree (Loc(t,p)) elem = 
  match p with
    Top -> failwith "insert_answer_in_tree : can't on top"
  | Node(l::left,up,right) -> insert_answer_in_tree (go_left (Loc(t,p))) elem
  | Node([],up,right) -> insert_left (Loc(t,p)) elem


(* transforme une liste de view en une section pour insérer dans l'arbre *)
let liste_view_to_section lst = 
  Section(List.map (fun x -> Item(x)) lst)


(* fonctions permettant de gérer les statégies différentes *)
let differente_strat strat = 
  match strat with 
  | "split_ifte" -> let () = Printf.printf "With split ifte you need a predicate of type B -> *\n" in 
		    let pred = read_line () in 
		    pred 
  | _ -> "" 



(* ------------------------------Debut du main du programme-------------------------- *)

let () = Printf.printf "\n\n-------------------------------\n"; 
	 Printf.printf "      MotoroLoL        \n";
	 Printf.printf "-------------------------------\n"; 
	 Printf.printf "\n\n Entrer un théorème à prouver     \n"
let type_to_proove = read_line ()

let arbre = init_location (init_view_arg type_to_proove "(? init)" "" false)


let rec main arbre =		
  if check_if_section_validate(go_full_left arbre)
  then let () = Printf.printf "\nterme final : %s \n " (get_current arbre).preuve  in main (go_up arbre)
  else 
    (* on va vérifier que l'on est pas positionné sur une section, si l'on est sur une section on demande au mec de choisir quelle preuve il veut utiliser *)
    let section_or_item = 
      begin match arbre with 
	    | (Loc(Item(x),p)) -> false 
	    | (Loc(Section(x),p)) -> true
	end in 
    if section_or_item
    then  let () = Printf.printf "\n%s\n" (pretty_print_section arbre 0) in 
	 let () = Printf.printf "Now choose wich goal to focus\n" in 
	 let n_goal = int_of_string(read_line ()) in	  
	 main (go_down (do_n_shifting n_goal "right" (go_full_left arbre)))
    else
    let () =  Printf.printf "\n%s\n" (pretty_print_view (get_current arbre)); 
	    Printf.printf "\nput your next tactique or left,right,up,down to navigate throught the proof\n" in
  let tactic_or_navig = read_line () in 
    match tactic_or_navig with
    | "left" -> let arbre = (go_left arbre) in main arbre 
    | "right" -> let arbre = (go_right arbre) in main arbre
    | "up" -> let arbre = (go_back_proof arbre) in main arbre 
    | "down" -> let arbre = (go_down_proof arbre) in main arbre
    | "print" -> let () = Printf.printf "\narbre :\n  %s\n" (pretty_print_location(go_to_the_top arbre)) in main arbre
    | _ -> 
       let options = differente_strat tactic_or_navig in 
       let () = Printf.printf "\nput the options of your tactic (if no options press enter)\n"  in
       let opt = read_line () in 
       let opt_for_request = if options = ""
			     then opt
			     else 
			       begin
				 if opt = "" then options else "(" ^ opt ^ " " ^ options ^ ")"
			       end in 
       let request = create_request (get_current arbre) tactic_or_navig opt_for_request  in  
       let () = Printf.printf "\nrequest : %s\n" request in
       let () = send_to_serv request in 
       let receive_answer = 
	 begin 
	   let file = open_in "reponse_serv.txt" in   
	   let res = input_line file in 
	   let () = close_in file in 
	   res
	 end in 
       let () = Printf.printf "\nréponse reçu : %s\n" (receive_answer) in
       let new_arbre = insert_answer_in_tree arbre (liste_view_to_section(parse_answer (Sexp.of_string receive_answer))) in   
       main (go_down (go_left new_arbre))
	    
	    
let x = main arbre
