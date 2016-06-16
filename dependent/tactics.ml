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



