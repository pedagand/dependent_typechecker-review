open Lambda 
open Tactics
open Sexplib

(*
  To load in the OCaml toplevel:
  #use "topfind";;  
  #require "sexplib";;
  #use "tactics.ml";;
*)



(* J'ai oublié le plus important dans la requete c'est la tactique....... il faut que je modifie les fonctions en fonction*) 
type request = 
  | R_goal of goal
  | R_environment of environment
  | R_terme of inTm
  | R_tactique of string (* a méditer demain mais je pense que string c'est le mieux comme ça je fais des fonctions séparées *)
		    (* ou alors petite idée je peux mettre le type des tactiques (c'est à dire goal -> goal) et comme ça directement depuis
le parseur je peux detecté quelle est la tactique et donc crée un élément du type R_tactique(avec une fct a l'intérieur) *)
  | Request of request * request * request


(* ------------------------------Parsing and pretty printing fonctions------------------------ *)

let rec parse_env str = 
  match str with 
  | Sexp.List [Sexp.Atom "env"; Sexp.List l] -> 
     List.map create_hypo_couple l
  | _ -> failwith "Request doesn't have the good shape"
and create_hypo_couple str = 
  match str with 
  | Sexp.List[Sexp.Atom a; Sexp.Atom "," ;t] -> 
     Couple(a,(parse_term [] t))
  | _ -> failwith "Request doesn't have the good shape"
and parse_goal str = 
  match str with 
  | Sexp.List[Sexp.Atom "goal";l] ->
     parse_term [] l
  | _ -> failwith "Request doesn't have the good shape"
and parse_global str = 
  match str with 
  | Sexp.List[g;e;t] -> 
     Request(R_goal(Goal(parse_goal g)),
	    R_environment(Env(parse_env e)),
	    R_terme(parse_term [] t))
  | _ -> failwith "bad request 404" 

let read_request str = parse_global (Sexp.of_string str)

let rec pretty_print_env envi = 
  match envi with 
  | Env(Couple(a,b) :: []) -> 
     (pretty_print_hypo_couple a b)
  | Env(Couple(a,b) :: rest) -> 
     (pretty_print_hypo_couple a b) ^ " " ^  
       (pretty_print_env (Env (rest)))
  | Env([]) -> ""
and pretty_print_hypo_couple a b = 
  "(" ^ a ^ " , " ^ (pretty_print_inTm b []) ^ ")"
and pretty_print_goal g = 
  match g with 
  | Goal x -> pretty_print_inTm x []
and pretty_print_global gl = 
  match gl with  
  | Request (R_goal(g),R_environment(e),R_terme(t)) -> "((goal " ^ 
			 pretty_print_goal g ^ ") (env " ^ 
			   pretty_print_env e ^ ") " ^ 
			     pretty_print_inTm t [] ^ ")"  
  | _ -> failwith "You can't print something else than a request"




(* ----------------------------Le main du serveur---------------------------*)
(* Ca va etre une fonction qui prend une string en entrée qui fait ensuite appelle aux différentes fonctions afin d'obtenir un type request
bien formé.
Une fois celui ci crée, il faut maintenant *)




 



	    

  
