open Lambda

(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #require "sexplib";;
  #use "tactics.ml";;
*)


(* En gros pour que ce soit compatible avec le délire des API REST, ce que je vais faire, 
l'utilisateur il à l'ensemble de sa preuve, il peut naviguer dedans, et quand il veut appliquer 
une stratégie, il suffit d'envoyer l'ensemble des informations suivantes au serveur, le type (goal
subgoal) en cour, les hypothèses et le nom de la tactique que l'on désire, le client reçoit ensuite
le résultat générer par le type checker... 
Et donc au final tout ce qui est déplacement au sein de la preuve c'est en locale et on intéroge par
requete le type checker.
Petite idée, avec cette mise en place cela permettrait de crée une stratégie super puissante, 
le serveur gardant en mémoire une grosse base de donées de théorèmes qu'il a prouvés, tu met 
"finditforme" et après (meme si ça prend du temps, c'est la solution de parresse) le serveur cherche
dans sa base si il trouve quelque chose correspondant à ta requete, et si il ne l'a pas et que tu 
arrive à la résoudre il la rajoutera. *)

(* pour l'instant je pense représenté les tactiques avec des fonctions et non pas un type par contre il faut que ces fonctions soient toutes
du meme type, c'est à dire goal -> goal *)

(* 
type request = 
  | R_goal of goal
  | R_environment of environment
  | R_terme of inTm
  | Request of request * request * request
 *)


(* Types nécéssaires à la création du moteur *)
type goal = 
  | Goal of inTm (* il faut que le goal soit une value étant donné que c'est le type et que l'on souhaite travailler avec des types 
de forme normale *)

type hypothesis =
  | Couple of string * inTm 
			 
type environment =
  | Env of hypothesis list
		       



(* le type de base des tactiques est ((hyp * go * term * string) -> (hyp * go * term) *)
let rec env_to_liste env = 
  match env with 
  | Env(Couple(str,elem)::[]) -> [(str,elem)]
  | Env([]) -> []
  | Env(Couple(str,elem)::suite) -> (str,elem) :: (env_to_liste (Env(suite)))



let intro env go (term : inTm) (var : string) = 
  match (env,go,term,var) with 
  | (Env(x),Goal(g),t,v) -> 
     begin 
     match g with 
     | Pi(n,s,t) -> (Goal(t),Env(Couple(var,s)::x),Abs(Global(var),What(gensym ())),false)
     | _ -> failwith ("intro : you can't intro something of the type " ^ pretty_print_inTm g [])
     end



let axiome env go (term : inTm) (var : string) = 
  match (env,go,term,var) with 
  | (Env(x),Goal(g),t,v) -> 
     let env_liste = env_to_liste (Env(x)) in
     begin 
       match (x,g) with 
       | ([],go) -> failwith "axiome : you can't axiome something when context is empty"
       | (e,go) -> 
     end 
     

