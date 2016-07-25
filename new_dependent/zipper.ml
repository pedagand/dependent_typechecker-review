open Lambda

(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "zipper.ml";;
*)

(* le premier inTm correpond au type et le second au terme *)
type definition = 
  | Complete of inTm * inTm
  | Incomplete of inTm * inTm

(* le premier inTm correspond au type et le second au terme *)
(* je rajoute un int pour dire quel fils il est *)
type noeud = 
  | Variable of string * inTm 
  | Definition of string * definition
  | Intermediaire of int * inTm * inTm 

type tree =
  | Item of noeud     
  | Section of tree list

type path =
  | Top
  | Node of tree list * path * tree list
  
type location = Loc of tree * path

  
(* -----------------Fonctions d'affichage-------------- *)
let rec pretty_print_inTm_user terme l = 
  match terme with 
  | Ref(name) -> name
  | Hole_inTm(x) -> "(_ " ^ string_of_int x ^ ")"
  | Abs(Global(str),x) -> "(lambda " ^ str ^ " " ^ pretty_print_inTm_user x (str :: l) ^ ")"
  | Abs(_,x) -> failwith "Pretty print Abs first arg must be a global"
  | Inv (x) ->  pretty_print_exTm_user x l
  | Pi (Global(str),s,t) -> "(pi " ^ str ^ " " ^ pretty_print_inTm_user s l ^ " " ^ pretty_print_inTm_user t (str :: l) ^ ")"
  | Pi (_,s,t) -> failwith "Pretty print Pi first arg must be a global"
  | Sig(Global(str),a,b) -> "(sig " ^ str ^ " " ^ pretty_print_inTm_user a l ^ " " ^ pretty_print_inTm_user b (str :: l) ^ ")"
  | Sig(_,a,b) -> failwith "Pretty print Sig first arg must be a global"
  | Star -> "*"
  | Succ n -> "(succ " ^ pretty_print_inTm_user n l ^ ")"
  | Zero -> "zero"
  | Nat -> "N" 
  | Bool -> "B"
  | True -> "true"
  | False -> "false"
  | Pair(a,b) -> "(" ^ pretty_print_inTm_user a l ^ " , " ^ pretty_print_inTm_user b l ^ ")"
  | Liste(alpha) -> "(liste " ^ pretty_print_inTm_user alpha l ^ ")"
  | Nil(alpha) -> "(nil " ^ pretty_print_inTm_user alpha l ^ ")"
  | Cons(a,xs) -> "(cons " ^ pretty_print_inTm_user a l ^ " " ^ pretty_print_inTm_user xs l ^ ")"
  | Vec(alpha,n) -> "(vec " ^ pretty_print_inTm_user alpha l ^ " " ^ pretty_print_inTm_user n l ^ ")"
  | DNil(alpha) -> "(dnil " ^ pretty_print_inTm_user alpha l ^ ")"
  | DCons(a,xs) -> "(dcons " ^ pretty_print_inTm_user a l ^ " " ^ pretty_print_inTm_user xs l ^ ")"
  | What(s)-> "(? " ^ s ^ ")"
  | Id(bA,a,b) -> "(id " ^ pretty_print_inTm_user bA l ^ " " ^ pretty_print_inTm_user a l ^ " " ^ pretty_print_inTm_user b l ^ ")"
  | Refl(a) -> "(refl " ^ pretty_print_inTm_user a l ^ ")"

and pretty_print_exTm_user t l =
  match t with 
  | Hole_exTm(x) -> "(_ " ^ string_of_int x ^ ")"
  | Ann(x,y) -> pretty_print_inTm_user x l 
  | BVar(x) -> begin 
      try List.nth l x with 
	| Failure("nth") ->  failwith ("Pretty_print_exTm BVar: something goes wrong list is to short BVar de " ^ string_of_int x) 
	| _ -> List.nth l x
    end
  | FVar (Global x) ->  x
  | FVar (Quote x) -> string_of_int x 
  | FVar (Bound x) -> string_of_int x
  | Etiquette(x) -> x
  | Appl(x,y) -> "(" ^ pretty_print_exTm_user x l ^ " " ^ pretty_print_inTm_user y l ^ ")"
  | Iter(p,n,f,z) -> "(iter " ^ pretty_print_inTm_user p l ^ " " ^ pretty_print_inTm_user n l ^ " " ^ pretty_print_inTm_user f l ^ " " ^ pretty_print_inTm_user z l ^ ")"
  | Ifte(p,c,tHen,eLse) -> "(ifte " ^ pretty_print_inTm_user p l ^ " " ^ pretty_print_inTm_user c l ^ " " ^ pretty_print_inTm_user tHen l ^ " " ^ pretty_print_inTm_user eLse l ^ ")"
  | P0(x) -> "(p0 " ^ pretty_print_exTm_user x l ^ ")"
  | P1(x) -> "(p1 " ^ pretty_print_exTm_user x l ^ ")"
  |  DFold(alpha,p,n,xs,f,a) -> "(dfold " ^ pretty_print_inTm_user alpha l ^ " " ^ pretty_print_inTm_user p l ^ " " ^pretty_print_inTm_user n l ^ 
				 " " ^ pretty_print_inTm_user xs l ^ " " ^ pretty_print_inTm_user f l ^ " " ^ pretty_print_inTm_user a l ^ ")"
  | Trans(bA,p,a,b,q,x) -> "(trans " ^ pretty_print_inTm_user bA l ^ " " ^pretty_print_inTm_user p l ^ " " ^pretty_print_inTm_user a l ^ " " ^
			     pretty_print_inTm_user b l ^ " " ^pretty_print_inTm_user q l ^ " " ^pretty_print_inTm_user x l ^ ")"
  | Fold(bA,alpha,xs,f,a) -> "(fold " ^ pretty_print_inTm_user bA l ^ " " ^ pretty_print_inTm_user alpha l ^ " " ^ pretty_print_inTm_user xs l ^ "  " ^ pretty_print_inTm_user f l ^ " " ^
			 pretty_print_inTm_user a l ^ ")"


let pretty_print_definition def = 
  match def with 
  | Complete(typ,terme) -> "Complete \n goal : " ^ pretty_print_inTm_user typ [] ^ "\n " ^ pretty_print_inTm_user terme []
  | Incomplete(typ,terme) -> "Incomplete \n goal : " ^ pretty_print_inTm_user typ [] ^ "\n" ^ pretty_print_inTm_user terme []

let pretty_print_item_debug item = 
  match item with 
  | Item(Variable(name,term)) -> "(Var " ^ name ^ " : " ^ pretty_print_inTm_user term [] ^ ")"
  | Item(Definition(name,def)) -> "(Def " ^ name ^ " \n " ^ pretty_print_definition def ^ ")"
  | Item(Intermediaire(n,typ,terme)) -> "(Inter " ^ string_of_int n ^ " " ^ pretty_print_inTm_user typ [] ^ " " ^ pretty_print_inTm_user terme [] ^ ")"
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


let pretty_print_location loc = 
  match loc with 
  | Loc(pointeur,Top) -> "\nZip : " ^ pretty_print_tree pointeur ^ "Top\n"
  | Loc(pointeur,chemin) -> "Zip : \n" ^ pretty_print_tree pointeur ^ "\n Path : \n" ^ pretty_print_node chemin






(* Fonction avec effets de bords nécéssaire pour l'affichage *)
let print_to_screen_location loc = 
  let () = Printf.printf "\nstart printing : \n %s \nstop printing\n" (pretty_print_location loc) in 
  loc
		     
let get_terme_item tree = 
  match tree with 
  | Loc(Item(Variable(name,typ)),t) -> failwith "this is a variable it don't have terme" 
  | Loc(Item(Definition(name,Incomplete(typ,terme))),t) -> terme     
  | Loc(Item(Intermediaire(n,typ,terme)),t) -> terme     
  | _ -> failwith "get item : it's not possible to get this..." 
let get_type_item tree = 
  match tree with 
  | Loc(Item(Variable(name,typ)),t) -> typ
  | Loc(Item(Definition(name,Incomplete(typ,terme))),t) -> typ
  | Loc(Item(Intermediaire(n,typ,terme)),t) -> typ
  | _ -> failwith "get_type_item : it's not possible to get this..." 
let get_num_Inter tree = 
  match tree with 					
  | Loc(Item(Intermediaire(n,typ,terme)),t) -> n
  | _ -> failwith "get_num_Inter : you can't ask for a num if you are no on Inter" 					 

(* fonctions permettants de savoir quand s'arreter *)
let know_def_inter tree = 
  match tree with 
  | Loc(Item(Variable(name,typ)),t) -> failwith "know_def_inter: this case is supposed to be impossible"
  | Loc(Item(Definition(name,Incomplete(typ,terme))),t) -> false
  | Loc(Item(Intermediaire(n,typ,terme)),t) -> true
  | _ -> failwith "know_def_inter: this case is supposed to be impossible"

  
  
(* -----------Fonctions de navigation---------------*)
let go_left (Loc(t,p)) = match p with
  | Top -> failwith "left of top"
  | Node(l::left,up,right) -> Loc(l,Node(left,up,t::right))
  | Node([],up,right) -> failwith "left of first"
				  
let go_right (Loc(t,p)) = match p with
  | Top -> failwith "right of top"
  | Node(left,up,r::right) -> Loc(r,Node(t::left,up,right))
  | _ -> failwith "right of last"
		  
		  
let go_up (Loc(t,p)) = match p with
  | Top -> failwith "up of top"
  | Node(left,up,right) -> Loc(Section((List.rev left) @ (t::right)),up)
			      
let go_down (Loc(t,p)) = match t with
    Item(_) -> failwith "down of item"
  | Section(t1::trees) -> Loc(t1,Node([],p,trees))
  | _ -> failwith "down of empty"

let rec go_n_son (Loc(t,p)) n = match n with    
  | 0 -> go_down (Loc(t,p))
  | n -> go_n_son (go_right (Loc(t,p))) (n-1)

(* To print a location we need a function that return the location at the top of the entiere tree *)
let rec go_to_the_top (Loc(t,p)) = 
  match p with 
    Top -> (Loc(t,p))
  | _ -> go_up (Loc(t,p))


(* pour le down faire attention, ça il faut donner un numéro du nombre de lefts a faire, ce qui nécéssitera donc une fonction permettant
de compter le nombre de fils *)
let rec go_full_left (Loc(t,p)) = 
  match p with 
  | Node([],up,right) -> (Loc(t,p))
  | Node(left,up,right) -> go_full_left (go_left (Loc(t,p)))
  | Top -> failwith "go_full_left : can't go left of a top"  

(* Etant donné ma structuration de l'arbre, il suffit de remonter puis de faire un shift a gauche?*)
let rec stop_when_def_inter arbre =   
  match arbre with 
  | Loc(_,Top) -> arbre
  | Loc(Item(Variable(name,terme)),p) -> stop_when_def_inter (go_up arbre)
  | Loc(Item(Definition(name,terme)),p) -> arbre
  | Loc(Item(Intermediaire(n,name,terme)),p) -> arbre
  | Loc(Section(x),p) -> stop_when_def_inter (go_full_left arbre)

let proof_up arbre = 
  let arbre = go_up arbre in 
  stop_when_def_inter arbre

let rec go_right_n_times (Loc(t,p)) n = 
  match n with 
  | 0 -> (Loc(t,p))
  | n -> go_right_n_times (go_right (Loc(t,p))) (n-1)
let go_down_n_son arbre n =  
  let arbre = go_down arbre  in
  go_right_n_times arbre n


let proof_down arbre = 
  let () = Printf.printf "\n Put the number of the son where you wan't to go\n" in 
  let num = read_line () in 
  go_down_n_son arbre (int_of_string num)

(*fonction préliminaire permettant de descendre dans l'arbre tous les PI pour la creation de userDef *)
let rec go_down_until_pi (Loc(t,p)) = 
  match t with
  | Item(Variable(name,terme)) -> go_down_until_pi(go_down(go_right(Loc(t,p))))
  | Item(Definition(typ,terme)) -> go_down_until_pi(go_down(go_right(Loc(t,p))))
  | Item(Intermediaire(n,typ,terme)) -> begin 
      match typ with 
      | Pi(_,_,_) -> go_down_until_pi(go_down(go_right(Loc(t,p))))
      | _ -> (Loc(t,p))
    end
  | _ -> failwith "supposed not to append" 









(* -----------Fonctions de recherche --------------- *)
   
(* Fonctions permettants de récupérer l'ensemble des définitions terminée à partir d'une position *)
let rec get_def_item it env = 
  match it with 
  | Definition(name,Complete(typ,terme)) -> ((name,typ,terme) :: env)
  | _ -> env 
and get_def_tree_liste tree_liste env = 
  match tree_liste with 
  | [] -> env 
  | Item(Definition(name,Complete(typ,terme))) :: [] -> ((name,typ,terme) :: env)
  | Item(Definition(name,Complete(typ,terme))) :: suite -> get_def_tree_liste suite ((name,typ,terme) :: env)
  | other :: suite -> get_def_tree_liste suite env
and get_def (Loc(t,p)) env = 
  match t,p with 
  | (Section(x),Top) -> get_def_tree_liste x env
  | (Item(x),Top) -> get_def_item x env
  | (Section(x),p) -> get_def (go_up(Loc(t,p))) (get_def_tree_liste x env)
  | (Item(x),p) -> get_def (go_up(Loc(t,p))) (get_def_item x env)

let rec print_def env = 
  match env with 
  | [] -> ""
  | (name,typ,terme) :: suite -> "(" ^ name ^ " :: " ^ pretty_print_inTm_user typ [] ^ " : " ^ pretty_print_inTm_user terme []
				 ^ ")\n" ^ print_def suite

 
(* A TEEEEEEEEEEESSSSSSSSSSSSSSSSSTTTTTTTTTTTTTTTEEEEEEEEEERRRRRRRRR *)
let get_and_print_def arbre = 
  let env = get_def arbre [] in 
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
and get_env (Loc(t,p)) env =
  match t,p with 
  | (Section(x),Top) -> get_env_tree_liste x env
  | (Item(x),Top) -> get_env_item x env
  | (Section(x),p) -> get_env (go_up (Loc(t,p))) (get_env_tree_liste x env)
  | (Item(x),p) -> get_env (go_up (Loc(t,p))) (get_env_item x env)
		    
let rec return_type_var_env env var = 
  match env with 
  | [] -> failwith "returne_type_var_env : la variable ne fait pas partis de l'environement" 
  | (name,typ) :: suite -> if name = var then typ else return_type_var_env suite var
(* Fonctions permettants d'afficher une liste de paires (name,type) *)

let rec print_env env = 
  match env with 
  | [] -> ""
  | (name,typ) :: suite -> "(" ^ name ^ " : " ^ pretty_print_inTm_user typ [] ^ ") " ^ print_env suite

let get_and_print_env arbre = 
  let env = get_env arbre [] in 
  print_env env

let rec is_in_env env var = 
  match env with 
  | [] -> false
  | (name,typ) :: suite -> if name = var then true else is_in_env suite var



(* affichage avec l'environnement de la preuve ect *)
let pretty_print_item item = 
  match item with 
  | Item(Variable(name,term)) -> "(Var " ^ name ^ " \n " ^ pretty_print_inTm_user term [] ^ ")"
  | Item(Definition(name,def)) -> "(Def " ^ name ^ " \n " ^ pretty_print_definition def ^ ")"
  | Item(Intermediaire(n,typ,terme)) -> "(Inter \n goal: " ^ pretty_print_inTm_user typ [] ^ "\n" ^ pretty_print_inTm_user terme [] ^ ")"
  | Section(x) -> failwith "pretty_print_inTm_user : can't print a section" 
let rec pretty_print_tree_liste tree_liste n= 
  match tree_liste with 
  | [] -> "" 
  | Item(x) :: suite -> "\n" ^ string_of_int n ^ " : \n" ^ pretty_print_item (Item(x)) ^ "\n" ^ pretty_print_tree_liste suite (n + 1)
  | Section(x) :: suite -> "\n " ^ string_of_int n ^ " Section \n" ^ pretty_print_tree_liste suite (n+1)
let pretty_print_state_proof (Loc(t,p)) = 
  let env = get_and_print_env (Loc(t,p)) in
  match t with 
  | Item(x) -> "---------Environment : ------------\n" ^ 
		 env ^ 
		   "\n----------Current goal ------------\n" ^    
		   pretty_print_item (Item(x)) 
  | Section(x) -> pretty_print_tree_liste x 0 
	
  






		 
(*------------------Fonctions de manipulation --------------*)


let replace_item (Loc(t,p)) tsub = 
  match t with 
  | Item(_) -> Loc(tsub,p)
  | _ -> failwith "replac_item : you are supposed to change an item" 

let complete_focus_terme (Loc(t,p)) tsub num = 
  match t with 
  | Item(Intermediaire(n,typ,terme)) -> Loc(Item(Intermediaire(n,typ,(replace_hole_inTm terme tsub num))),p)
  | Item(Definition(name,Complete(typ,terme))) -> Loc(Item(Definition(name,Complete(typ,(replace_hole_inTm terme tsub num)))),p)
  | Item(Definition(name,Incomplete(typ,terme))) -> Loc(Item(Definition(name,Incomplete(typ,(replace_hole_inTm terme tsub num)))),p)
  | _ -> failwith "complete_focus_terme : you can't get the type of something else than an item"

let get_type_focus (Loc(t,p)) = 
  match t with 
  | Item(Intermediaire(n,typ,terme)) -> typ
  | Item(Definition(name,Complete(typ,terme))) -> typ
  | Item(Definition(name,Incomplete(typ,terme))) -> typ
  | _ -> failwith "get_type_focus : you can't get the type of something else than an item"

let get_terme_focus (Loc(t,p)) = 
  match t with 
  | Item(Intermediaire(n,typ,terme)) -> terme
  | Item(Definition(name,Complete(typ,terme))) -> terme
  | Item(Definition(name,Incomplete(typ,terme))) -> terme
  | _ -> failwith "get_terme_focus : you can't get the type of something else than an item"
 

let insert_right (Loc(t,p)) r = match p with
    Top -> failwith "insert of top"
  | Node(left,up,right) -> Loc(t,Node(left,up,r::right))

let insert_left (Loc(t,p)) l = match p with
Top -> failwith "insert of top"
| Node(left,up,right) -> Loc(t,Node(l::left,up,right))

let insert_down (Loc(t,p)) t1 = 
  match t with
  | Item(_) -> failwith "down of item"
  | Section(sons) -> Loc(t1,Node([],p,sons))


(* mettre les elements dans le sens normale de leur insertion, exemple : en argument liste [1;2;3] ils seront rangés en [1];[2];[3] *)
let rec insert_some_right (Loc(t,p)) liste_section_or_item = 
  match liste_section_or_item with 
  | [] -> (Loc(t,p))
  | elem :: suite -> insert_some_right (insert_right (Loc(t,p)) elem) suite 

(* la fonction de delete tente tout d'abord de positionner le curseur a droite, sinon a gauche et sinon crée une section vide *)
let delete (Loc(_,p)) = match p with
Top -> failwith "delete of top"
| Node(left,up,r::right) -> Loc(r,Node(left,up,right))
| Node(l::left,up,[]) -> Loc(l,Node(left,up,[]))
| Node([],up,[]) -> Loc(Section[],up)

      


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

let rec verif_and_push_up_item (Loc(t,p)) =     
  let terme_to_put = get_terme_item (Loc(t,p)) in   
  if check_if_no_hole_inTm terme_to_put && know_def_inter (Loc(t,p))
  then     
    begin 
    let trou = get_num_Inter (Loc(t,p)) in 
    let arbre = proof_up (Loc(t,p)) in 
    let terme_to_fullfill = get_terme_item arbre in 
    let terme = replace_hole_inTm terme_to_fullfill terme_to_put trou in 
    let arbre = 
      begin 
	match arbre with 
	| Loc(Item(Intermediaire(n,x,y)),p) -> replace_item arbre (Item(Intermediaire(n,x,terme)))
	| Loc(Item(Definition(name,Incomplete(typ,terme_sup))),p) -> replace_item arbre (Item(Definition(name,Incomplete(typ,terme))))
	| _ -> failwith "verif_and_push_up_item : this case is supposed to be impossible" 
      end in 
    verif_and_push_up_item arbre
    end
  else (Loc(t,p))  
  


