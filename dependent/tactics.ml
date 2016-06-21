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
  | Goals of goal list
  | Vide

type hypothesis =
  | Couple of string * inTm 
			 
type environment =
  | Env of hypothesis list
		       



(* le type de base des tactiques est ((hyp * go * term * string) ->  *)
let rec env_to_liste env = 
  match env with 
  | Env(Couple(str,elem)::[]) -> [(Global(str),(big_step_eval_inTm elem []))]
  | Env([]) -> []
  | Env(Couple(str,elem)::suite) -> (Global(str),(big_step_eval_inTm elem [])) :: (env_to_liste (Env(suite)))



let intro env go (term : inTm) (var : string) = 
  match (env,go,term,var) with 
  | (Env(x),Goal(g),t,v) -> 
     begin 
     match g with 
     | Pi(n,s,t) -> (Goal(t),Env(Couple(var,s)::x),Abs(Global(var),What(gensym ())),false)
     | _ -> failwith ("intro : you can't intro something of the type " ^ pretty_print_inTm g [])
     end
  | _ -> failwith "intro : intro is not call with good args" 



let axiome env go (term : inTm) (var : string) = 
  match (env,go,term,var) with 
  | (Env(x),Goal(g),t,v) -> 
     let env_liste = env_to_liste (Env(x)) in
     begin 
       match (x,g) with 
       | ([],go) -> failwith "axiome : you can't axiome something when context is empty"
       | (e,go) -> if (List.assoc (Global(v)) env_liste) = big_step_eval_inTm g [] 
		   then (Vide,Env(x),Inv(FVar(Global(v))),true)
		   else failwith "axiome : there is no variable you mentioned in the context with the good type"
     end 
  | _ -> failwith "axiome : is not call with good args"  


(* pour cette stratégie je vais avoir besoin de crée un type de réponse particulière qui permet d'indiquer au client qu'il à plusieurs 
goal à satisfaires à la suite *)
(* let construct env go (term : inTm) (var : string) = 
  match (env,go,term,var) with 
     | (Env(x),Goal(g),t,v) -> 
	begin 
	  match 
	end 
     | (Env(x),Vide,t,v) -> failwith "construct : goal must not be Vide"  *)
    
(* réfléxions avant la pause *)
(* Enfaite j'ai un type view sur le client et justement je devrais faire un arbre de view, quand une view est terminée alors elle contient
le terme qu'il faut mettre à cet endroit. Etant donné que dans l'arbre tous les goals présent dans une meme section signifie que ce sont 
différents goal mais pour construire le meme terme, et grace au curseur on va pouvoir se déplacer dans les différentes view. 
Ca va etre la version 2.0 du client. *)
