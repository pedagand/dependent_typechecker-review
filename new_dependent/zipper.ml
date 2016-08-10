open Lambda


(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "zipper.ml";;
*)

(* le premier inTm correpond au type et le second au terme *)
(* le string permet de stocker la definition que l'on va par la suite stocker dans les fichiers *) 
type definition = 
  | Complete of inTm * inTm 
  | Incomplete of inTm * inTm

(* le premier inTm correspond au type et le second au terme *)
(* je rajoute un int pour dire quel fils il est *)


type noeud = 
  | Variable of string * inTm
  | Definition of string * definition * string
  | Intermediaire of int * inTm * inTm * string

type tree =
  | Item of noeud     
  | Section of tree list

type path =
  | Top
  | Node of tree list * path * tree list
  
type location = Loc of tree * path

let compteur_hypothesis = ref 0

let gen_hypothesis init =  
  if init 
  then fun () -> compteur_hypothesis := 0; "H" ^ string_of_int  !compteur_hypothesis  
  else fun () -> compteur_hypothesis := !compteur_hypothesis + 1; "H" ^ string_of_int  !compteur_hypothesis  

  
  
(* -----------------Fonctions d'affichage-------------- *)

let pretty_print_definition def = 
  match def with 
  | Complete(typ,terme) -> "Complete \n goal : " ^ pretty_print_inTm typ [] ^ "\n " ^ pretty_print_inTm terme []
  | Incomplete(typ,terme) -> "Incomplete \n goal : " ^ pretty_print_inTm typ [] ^ "\n" ^ pretty_print_inTm terme []

let pretty_print_item_debug item = 
  match item with 
  | Item(Variable(name,term)) -> "(Var " ^ name ^ " : " ^ pretty_print_inTm term [] ^ ")"
  | Item(Definition(name,def,save)) -> "(Def " ^ name ^ " \n " ^ pretty_print_definition def ^ ")"
  | Item(Intermediaire(n,typ,terme,save)) -> "(Inter " ^ string_of_int n ^ " " ^ pretty_print_inTm typ [] ^ " " ^ pretty_print_inTm terme [] ^ ")"
  | Section(x) -> failwith "pretty_print_inTm_user : can't print a section" 

let rec pretty_print_tree_liste tree_liste = 
  match tree_liste with 
  | [] -> ""
  | Item(x) :: suite -> pretty_print_item_debug (Item(x)) ^ " ; " ^ pretty_print_tree_liste suite
  | Section(x) :: suite -> pretty_print_tree (Section(x)) ^ " ; " ^ pretty_print_tree_liste suite
and pretty_print_tree sec =
  match sec with 
  | Section(y) -> "\n[" ^ pretty_print_tree_liste y ^ "]\n"
  | Item(x) -> "\n[" ^ pretty_print_item_debug (Item(x)) ^ "]\n"

let rec pretty_print_node nod = 
  match nod with 
  | Node(left,up,right) -> "(left " ^ pretty_print_tree_liste left ^ ")(up " ^ pretty_print_node up ^ ")(right " ^ 
					pretty_print_tree_liste right ^ ")"
  | Top -> "Top"


let pretty_print_location (Loc(t,p),d) = 
  match Loc(t,p) with 
  | Loc(pointeur,Top) -> "\nZip : " ^ pretty_print_tree pointeur ^ "Top\n"
  | Loc(pointeur,chemin) -> "Zip : \n" ^ pretty_print_tree pointeur ^ "\n Path : \n" ^ pretty_print_node chemin






(* Fonction avec effets de bords nécéssaire pour l'affichage *)
let print_to_screen_location (Loc(t,p),d) = 
  let () = Printf.printf "\nstart printing : \n %s \nstop printing\n" (pretty_print_location (Loc(t,p),d)) in 
  (Loc(t,p),d)
		     
let get_terme_item (Loc(t,p),d) = 
  match Loc(t,p) with 
  | Loc(Item(Variable(name,typ)),t) -> failwith ("get_terme_item : this is a variable it don't have terme" ^ name)
  | Loc(Item(Definition(name,Incomplete(typ,terme),save)),t) -> terme     
  | Loc(Item(Intermediaire(n,typ,terme,save)),t) -> terme     
  | Loc(Item(Definition(name,Complete(typ,terme),save)),t) -> terme     
  | _ -> failwith "get item : it's not possible to get this..." 
let get_type_item (Loc(t,p),d) = 
  match Loc(t,p) with 
  | Loc(Item(Variable(name,typ)),t) -> typ
  | Loc(Item(Definition(name,Incomplete(typ,terme),save)),t) -> typ
  | Loc(Item(Intermediaire(n,typ,terme,save)),t) -> typ
  | Loc(Item(Definition(name,Complete(typ,terme),save)),t) -> typ
  | _ -> failwith "get_type_item : it's not possible to get this..." 
let get_num_Inter (Loc(t,p),d) = 
  match Loc(t,p) with 					
  | Loc(Item(Intermediaire(n,typ,terme,save)),t) -> n
  | _ -> failwith "get_num_Inter : you can't ask for a num if you are no on Inter" 					 

(* fonctions permettants de savoir quand s'arreter *)
let know_def_inter (Loc(t,p),d) = 
  match Loc(t,p) with 
  | Loc(Item(Variable(name,typ)),t) -> failwith "know_def_inter: this case is supposed to be impossible"
  | Loc(Item(Definition(name,Incomplete(typ,terme),save)),t) -> false
  | Loc(Item(Intermediaire(n,typ,terme,save)),t) -> true
  | _ -> failwith "know_def_inter: this case is supposed to be impossible"

  
  
(* -----------Fonctions de navigation---------------*)
let go_left (Loc(t,p),d) = match p with
  | Top -> failwith "left of top"
  | Node(l::left,up,right) -> (Loc(l,Node(left,up,t::right)),d)
  | Node([],up,right) -> failwith "left of first"
				  
let go_right (Loc(t,p),d) = match p with
  | Top -> failwith "right of top"
  | Node(left,up,r::right) -> (Loc(r,Node(t::left,up,right)),d)
  | _ -> (Loc(t,p),d) (* failwith "right of last" *) (* je teste de faire marcher le programme sans les failwith *)
		  
		  
let go_up ((Loc(t,p)),d) = match p with
  | Top -> failwith "up of top"
  | Node(left,up,right) -> (Loc(Section((List.rev left) @ (t::right)),up),d)
			      
let go_down (Loc(t,p),d) = match t with
    Item(_) -> (Loc(t,p),d) (* failwith "down of item" *)
  | Section(t1::trees) -> (Loc(t1,Node([],p,trees)),d)
  | _ -> (Loc(t,p),d) (* failwith "down of empty" *)

let rec go_n_son (Loc(t,p),d) n = match n with    
  | 0 -> go_down (Loc(t,p),d)
  | n -> go_n_son (go_right (Loc(t,p),d)) (n-1)

  
		 

(* To print a location we need a function that return the location at the top of the entiere tree *)
let rec go_to_the_top (Loc(t,p),d) = 
  match p with 
    Top -> (Loc(t,p),d)
  | _ -> go_up (Loc(t,p),d)


(* pour le down faire attention, ça il faut donner un numéro du nombre de lefts a faire, ce qui nécéssitera donc une fonction permettant
de compter le nombre de fils *)
let rec go_full_left (Loc(t,p),d) = 
  match p with 
  | Node([],up,right) -> (Loc(t,p),d)
  | Node(left,up,right) -> go_full_left (go_left (Loc(t,p),d))
  | Top -> failwith "go_full_left : can't go left of a top"  

let rec go_right_count (Loc(t,p),d) n = 
  match p with 
  | Node(left,up,[]) -> n
  | Node(left,up,right) -> go_right_count (go_right (Loc(t,p),d)) (n + 1)
  | Top -> failwith "cont_son : can't count on a top" 
and count_son (Loc(t,p),d) =   
  go_right_count (go_full_left (Loc(t,p),d)) 0

  
  

(* Etant donné ma structuration de l'arbre, il suffit de remonter puis de faire un shift a gauche?*)
let rec stop_when_def_inter (Loc(t,p),d) =   
  match (Loc(t,p)) with 
  | Loc(_,Top) -> (Loc(t,p),d)
  | Loc(Item(Variable(name,terme)),p) -> stop_when_def_inter (go_up (Loc(t,p),d))
  | Loc(Item(Definition(name,terme,save)),p) -> (Loc(t,p),d)
  | Loc(Item(Intermediaire(n,name,terme,save)),p) -> (Loc(t,p),d)
  | Loc(Section(x),p) -> stop_when_def_inter (go_full_left (Loc(t,p),d))

let proof_up (Loc(t,p),d) = 
  let arbre = go_up (Loc(t,p),d) in 
  stop_when_def_inter arbre

let rec go_right_n_times (Loc(t,p),d) n = 
  match n with 
  | 0 -> (Loc(t,p),d)
  | n -> go_right_n_times (go_right (Loc(t,p),d)) (n-1)
let go_down_n_son (Loc(t,p),d) n =  
  let arbre = go_down (Loc(t,p),d)  in
  go_right_n_times arbre n


let proof_down (Loc(t,p),d) = 
  let () = Printf.printf "\n Put the number of the son where you wan't to go\n" in 
  let num = read_line () in 
  go_down_n_son (Loc(t,p),d) (int_of_string num)

(*fonction préliminaire permettant de descendre dans l'arbre tous les PI pour la creation de userDef *)
let rec go_down_until_pi (Loc(t,p),d) = 
  match t with
  | Item(Variable(name,terme)) -> go_down_until_pi(go_down(go_right(Loc(t,p),d)))
  | Item(Definition(typ,terme,save)) -> go_down_until_pi(go_down(go_right(Loc(t,p),d)))
  | Item(Intermediaire(n,typ,terme,save)) -> begin 
      match typ with 
      | Pi(_,(_,_)) -> go_down_until_pi(go_down(go_right(Loc(t,p),d)))
      | _ -> (Loc(t,p),d)
    end
  | _ -> failwith "supposed not to append" 









(* -----------Fonctions de recherche --------------- *)
   
(* Fonctions permettants de récupérer l'ensemble des définitions terminée à partir d'une position *)
let rec get_def_item it env = 
  match it with 
  | Definition(name,Complete(typ,terme),save) -> ((name,typ,terme) :: env)
  | _ -> env 
and get_def_tree_liste tree_liste env = 
  match tree_liste with 
  | [] -> env 
  | Item(Definition(name,Complete(typ,terme),save)) :: [] -> ((name,typ,terme) :: env)
  | Item(Definition(name,Complete(typ,terme),save)) :: suite -> get_def_tree_liste suite ((name,typ,terme) :: env)
  | other :: suite -> get_def_tree_liste suite env
and get_def (Loc(t,p),d) env = 
  match t,p with 
  | (Section(x),Top) -> get_def_tree_liste x env
  | (Item(x),Top) -> get_def_item x env
  | (Section(x),p) -> get_def (go_up(Loc(t,p),d)) (get_def_tree_liste x env)
  | (Item(x),p) -> get_def (go_up(Loc(t,p),d)) (get_def_item x env)

let rec print_def env = 
  match env with 
  | [] -> ""
  | (name,typ,terme) :: suite -> "(" ^ name ^ " :: " ^ pretty_print_inTm typ [] ^ " : " ^ pretty_print_inTm terme []
				 ^ ")\n" ^ print_def suite

 
(* A TEEEEEEEEEEESSSSSSSSSSSSSSSSSTTTTTTTTTTTTTTTEEEEEEEEEERRRRRRRRR *)
let get_and_print_def (Loc(t,p),d) = 
  let env = get_def (Loc(t,p),d) [] in 
  print_def env

  
  
  
  






(* Fonctions permettants de crée une liste de paires (name,type) *)
let rec get_env_item it env= 
  match it with 
  | Variable(name,typ) -> ((name,typ) :: env)
  | _ -> env
and get_env_tree_liste tree_liste env = 
  match tree_liste with 
  | (Item(Variable(name,typ))) :: [] -> ((name,typ) :: env)
  | (Item(Variable(name,typ))) :: suite -> get_env_tree_liste suite ((name,typ) :: env) 
  | other :: suite -> get_env_tree_liste suite env
  | [] -> env
and get_env (Loc(t,p),d) env =
  match t,p with 
  | (Section(x),Top) -> get_env_tree_liste x env
  | (Item(x),Top) -> get_env_item x env
  | (Section(x),p) -> get_env (go_up (Loc(t,p),d)) (get_env_tree_liste x env)
  | (Item(x),p) -> get_env (go_up (Loc(t,p),d)) (get_env_item x env)
		    
let rec return_type_var_env env var = 
  match env with 
  | [] -> failwith "returne_type_var_env : la variable ne fait pas partis de l'environement" 
  | (name,typ) :: suite -> if name = var then typ else return_type_var_env suite var
(* Fonctions permettants d'afficher une liste de paires (name,type) *)

let rec print_env env = 
  match env with 
  | [] -> ""
  | (name,typ) :: suite -> "(" ^ name ^ " : " ^ pretty_print_inTm typ [] ^ ") " ^ print_env suite

let get_and_print_env (Loc(t,p),d) = 
  let env = get_env (Loc(t,p),d) [] in 
  print_env env

let rec is_in_env env var = 
  match env with 
  | [] -> false
  | (name,typ) :: suite -> if name = var then true else is_in_env suite var



(* affichage avec l'environnement de la preuve ect *)
let pretty_print_item item = 
  match item with 
  | Item(Variable(name,term)) -> "(Var " ^ name ^ " \n " ^ pretty_print_inTm term [] ^ ")"
  | Item(Definition(name,def,save)) -> "(Def " ^ name ^ " \n " ^ pretty_print_definition def ^ ")"
  | Item(Intermediaire(n,typ,terme,save)) -> "(Inter \n goal: " ^ pretty_print_inTm typ [] ^ "\n" ^ pretty_print_inTm terme [] ^ ")"
  | Section(x) -> failwith "pretty_print_inTm_user : can't print a section" 
let rec pretty_print_tree_liste tree_liste n= 
  match tree_liste with 
  | [] -> "" 
  | Item(x) :: suite -> "\n" ^ string_of_int n ^ " : \n" ^ pretty_print_item (Item(x)) ^ "\n" ^ pretty_print_tree_liste suite (n + 1)
  | Section(x) :: suite -> "\n " ^ string_of_int n ^ " Section \n" ^ pretty_print_tree_liste suite (n+1)
let pretty_print_state_proof (Loc(t,p),d) = 
  let () = Printf.printf "\n state proof enter \n" in 
  let env = get_and_print_env (Loc(t,p),d) in
  let () = Printf.printf "\n we have env " in 
  match t with 
  | Item(x) -> "---------Environment : ------------\n" ^ 
		 env ^ 
		   "\n----------Current goal ------------\n" ^    
		   pretty_print_item (Item(x)) 
  | Section(x) -> pretty_print_tree_liste x 0 
	
 



		 
(*------------------Fonctions de manipulation --------------*)


let replace_item (Loc(t,p),d) tsub = 
  match t with 
  | Item(_) -> (Loc(tsub,p),d)
  | _ -> failwith "replac_item : you are supposed to change an item" 

let complete_focus_terme (Loc(t,p),d) tsub name_hole = 
  match t with 
  | Item(Intermediaire(n,typ,terme,save)) -> (Loc(Item(Intermediaire(n,typ,(replace_hole terme name_hole tsub),save)),p),d)
  | Item(Definition(name,Complete(typ,terme),save)) -> (Loc(Item(Definition(name,Complete(typ,(replace_hole terme name_hole tsub)),save)),p),d)
  | Item(Definition(name,Incomplete(typ,terme),save)) -> 
     (Loc(Item(Definition(name,Incomplete(typ,(replace_hole terme name_hole tsub)),save)),p),d)
  | _ -> failwith "complete_focus_terme : you can't get the type of something else than an item"

let get_type_focus debug_string (Loc(t,p),d) = 
  match t with 
  | Item(Intermediaire(n,typ,terme,save)) -> typ
  | Item(Definition(name,Complete(typ,terme),save)) -> typ
  | Item(Definition(name,Incomplete(typ,terme),save)) -> typ
  | Section(x) -> failwith ("get_type_focus : This is a section " ^ pretty_print_tree (Section(x)))
  | _ -> failwith ("get_type_focus : you can't get the type of something else than an item " ^ debug_string)

let get_terme_focus (Loc(t,p),d) = 
  match t with 
  | Item(Intermediaire(n,typ,terme,save)) -> terme
  | Item(Definition(name,Complete(typ,terme),save)) -> terme
  | Item(Definition(name,Incomplete(typ,terme),save)) -> terme
  | _ -> failwith "get_terme_focus : you can't get the type of something else than an item"
 

let insert_right (Loc(t,p),d) r = match p with
    Top -> failwith "insert of top"
  | Node(left,up,right) -> (Loc(t,Node(left,up,r::right)),d)

let insert_left (Loc(t,p),d) l = match p with
Top -> failwith "insert of top"
| Node(left,up,right) -> (Loc(t,Node(l::left,up,right)),d)

let insert_down (Loc(t,p),d) t1 = 
  match t with
  | Item(_) -> failwith "down of item"
  | Section(sons) -> (Loc(t1,Node([],p,sons)),d)


(* mettre les elements dans le sens normale de leur insertion, exemple : en argument liste [1;2;3] ils seront rangés en [1];[2];[3] *)
let rec insert_some_right (Loc(t,p),d) liste_section_or_item = 
  match liste_section_or_item with 
  | [] -> (Loc(t,p),d)
  | elem :: suite -> let (Loc(t,p),d) = insert_right (Loc(t,p),d) elem in 
		     insert_some_right (Loc(t,p),d) suite 

(* la fonction de delete tente tout d'abord de positionner le curseur a droite, sinon a gauche et sinon crée une section vide *)
let delete (Loc(_,p),d) = match p with
Top -> failwith "delete of top"
| Node(left,up,r::right) -> (Loc(r,Node(left,up,right)),d)
| Node(l::left,up,[]) -> (Loc(l,Node(left,up,[])),d)
| Node([],up,[]) -> (Loc(Section[],up),d)

      


(* ----------------Fonctions d'écrasement ------------------ *)
(* prend un noeud en cour, vérifie si celui ci est complétement bouché et le remonte dans le trou du dessus (le noeud en dessous  *)

(* Apres la pause, il va falloir faire en sorte que a chaque fois avant de travailler sur un terme, si celui ci ne contient plus de trou appeler cette fonction, et justement celle ci ne dois pas buguer si on ne l'appel pas avec un terme n'ayant pas de trou, elle doit quand meme le remonter *)
(* Vieille version *)
(*
let verif_and_push_up_item (Loc(t,p)) =   
  let terme_type = 
    begin 
  match t with 
  | Item(Intermediaire(n,typ,terme)) -> (typ,terme)
  | Item(Definition(name,Complete(typ,terme))) -> (typ,terme)
  | Item(Definition(name,Incomplete(typ,terme))) -> (typ,terme)
  | _ -> failwith "push_to_the_max : must not append" 
    end in 
  let terme = 
    begin 
      match terme_type with | (typ,terme) -> terme
    end in 
  if check_if_no_hole_inTm terme 
  then 
    (* ici petit up pour supprimer l'ensemble de la section *)
     let arbre = proof_up (Loc(t,p)) (* arbre *) in (* LOl *) 
(*     let () = Printf.printf "\n %s \n Quel est le trou à remplir ?\n" (pretty_print_state_proof arbre) in *)
    let trou = get_num_Inter (Loc(t,p)) (* int_of_string (read_line ())*) in 
    let terme_sup = begin 
	match arbre with 
	| Loc(Item(Intermediaire(n,typ,terme_sup)),p) -> (terme_sup,"inter",typ)
	| Loc(Item(Definition(name,Incomplete(typ,terme_sup))),p) -> (terme_sup,name,typ)
	| _ -> failwith "push_to_the_max : this kinds of things must not append"
      end in 
    let arbre = 
      begin
	match terme_sup with 
	| (x,"inter",typ) -> replace_item arbre (Item(Intermediaire(1,(* ce num cest juste pour pas buguer *)typ,replace_hole_inTm x terme trou)))
	| (x,name,typ) -> replace_item arbre (Item(Definition(name,Incomplete(typ,replace_hole_inTm x terme trou))))	       
    end in 
    arbre    
  else (Loc(t,p))
 *)






let rec verif_and_push_up_item (Loc(t,p),d) =     
  let terme_to_put = get_terme_item (Loc(t,p),d) in   
  let typ_terme_to_put = get_type_item (Loc(t,p),d) in (* TODO :: ici il faut faire une annotation *)
  if check_if_no_hole_inTm terme_to_put && know_def_inter (Loc(t,p),d)
  then     
    begin 
    let trou = get_num_Inter (Loc(t,p),d) in 
    let arbre = proof_up (Loc(t,p),d) in 
    let terme_to_fullfill = get_terme_item arbre in 
    let terme = replace_hole terme_to_fullfill trou (Ann(terme_to_put,typ_terme_to_put)) in 
    let arbre = 
      begin 
	match arbre with 
	| (Loc(Item(Intermediaire(n,x,y,save)),p),d) -> replace_item arbre (Item(Intermediaire(n,x,terme,save)))
	| (Loc(Item(Definition(name,Incomplete(typ,terme_sup),save)),p),d) -> 
	   replace_item arbre (Item(Definition(name,Incomplete(typ,terme),save)))
	| _ -> failwith "verif_and_push_up_item : this case is supposed to be impossible" 
      end in 
    verif_and_push_up_item arbre
    end
  else (Loc(t,p),d)
  


