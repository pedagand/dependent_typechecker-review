open Zipper
open Lambda
open Sexplib


(*-----------------------Fonctions pour crée le Upper type------------------------*)
(* permet de crée un type à partir du type donné par l'utilisateur *)
let rec create_uper_type typ = 
  match typ with 
  | Pi(n,s,t) -> Pi(n,s,(create_uper_type t))
  | Nat -> Star
  | _ -> failwith "create_uper_type : only for pi at the moment"

(* permet à partir d'un type ainsi que du return du type initial de crée un terme *)
let rec modifie_return_terme typ return = 
  match typ with 
  | Pi(n,s,t) -> Abs(n,modifie_return_terme t return)
  | Star -> return
  | _ -> failwith "create_uper_terme : Only for pi at the moment "

let rec modifie_return_type typ return = 
  match typ with
  | Pi(n,s,t) -> Pi(n,s,(modifie_return_type t return))
  | Nat -> return
  | _ -> failwith "modifie_return_type : mettre a jour la fonction au fur et à mesure pour quelle accepte tous les types"


(* permet de parcourir un pi type jusqu'au bout afin d'en connaitre le type de retour *)
let rec find_return_type typ = 
  match typ with 
  | Pi(n,s,t) -> find_return_type t 
  | x -> x

(* permet de donner la liste des variables présentes dans le théorème *)
let rec liste_me_var terme = 
  match terme with 
  | Pi(Global(name),s,t) -> let () = Printf.printf "there is a var %s" name in name :: (liste_me_var t)
  | _ -> let () = Printf.printf "there is no var ...." in []


let create_upper_name name typ = 
  String.uppercase name
(*------------------------------------Fin------------------------------*)
  


(* prend un terme, calcule sa liste de variable et retourne l'application de celui ci *)
(* let make_application terme typ liste_var =  *)
(*   let () = Printf.printf "\nLISTE DE VAR  %s \n" (List.fold_right (fun x y -> x ^ " " ^ y) liste_var "") in  *)
(*   if liste_var = [] then terme  *)
(*   else Inv(List.fold_left (fun x y -> Appl(x,Inv(FVar(Global(y))))) (Ann(terme,typ)) liste_var) *)
let make_application (terme : exTm) liste_var =
  let () = Printf.printf "\nLISTE DE VAR  %s \n" (List.fold_right (fun x y -> x ^ " " ^ y) liste_var "") in
  if liste_var = [] then terme
  else List.fold_left (fun x y -> Appl(x,Inv(FVar(Global(y))))) terme liste_var



(* fonction prenant un argument un type et son nom . Celle ci retourne une location avec le uper_type générer en haut de 
l'arbre et le curseur sur un noeud donné en entrée *)
let init_definition typ name = 
  let return = find_return_type typ in 
  let () = Printf.printf "\nreturn : %s" (pretty_print_inTm return []) in
  let new_typ = create_uper_type typ in 
  let () = Printf.printf "\nnew_type : %s" (pretty_print_inTm new_typ []) in
  let new_term = modifie_return_terme new_typ return in
  let () = Printf.printf "\nnew_term : %s" (pretty_print_inTm new_term []) in
  let new_name = create_upper_name name new_typ  in 
  let () = Printf.printf "\nnew_name : %s\n" new_name in
  Definition(new_name,Complete(new_typ,new_term))
  
let parse_definition def refe = 
  match def with 
  | Sexp.List[Sexp.Atom name;terme] -> let terme = parse_term [] terme in 
     Definition(name,Incomplete(terme,Hole_inTm(1)))
  | _ -> failwith "parse_definition : it seem's that your def is not good"

let procedure_start_definition arbre= 
  let () = Printf.printf "\n\nEntrer une nouvelle définition à prouver : \n" in 
  let typ_not_parsed = read_line () in
  let second_def = parse_definition (Sexp.of_string typ_not_parsed) "" in
  match second_def with 
  | Definition(name,Incomplete(typ,terme)) -> 
     let defi = init_definition typ name in 
     let first_def = Section([Item(defi)]) in      
     let arbre = (go_down(go_right(insert_right arbre first_def))) in 
     let first_def_type = begin 
	 match defi with 
	 | Definition(new_name,Complete(new_typ,new_term)) -> new_typ
	 | _ -> failwith "procedure_start_definition : it's impossible"
       end in 
      let liste_var = liste_me_var first_def_type in  
      let second_def = begin
	  match second_def with 
	  | Definition(name,Incomplete(typ,term)) -> Definition(name,Incomplete(
									 modifie_return_type typ (Inv(
											       (make_application 
												 (Etiquette(create_upper_name name typ))
												  liste_var))),term))
	  | _ -> failwith "procedure_start_definition : if this case happend i eat myself"
	end in
      let arbre = (go_down(go_right(insert_right arbre (Section([Item(second_def)]))))) in 
      arbre
  | _ -> failwith "procedure_start_definition : something goes wrong during the creation of the definition"


(* ---------------- Routines de demande de saisies pour l'utilisateur ----------------------- *)
(* transformer toutes les fonctions de la sorte *)
let rec ask_variable_name ()= 
  let () = Printf.printf "\n Please Choose a name for the var, (you can press enter and it will try to find a name for the var\n" in
  let var = read_line () in begin 
      match var with 
      | "" -> ask_variable_name ()
      | _ -> var
      end 
  
let ask_predicat typ =
  let () = Printf.printf "\n Please give the predicate you wan't to use for this split of type : %s \n" typ in 
  let pred = read_line () in pred

let ask_terme () =
  let () = Printf.printf "\n Please give the terme you wan't to use \n" in 
  let terme = read_line () in terme


let ask_induct_var () = 
  let () = Printf.printf "\n Please give the name of the variable you wan't to use for this split \n" in 
  let var = read_line () in var 

let ask_the_hole terme name = 
  let () = Printf.printf "\n The current terme is %s in which hole do you wan't to put your %s " (pretty_print_inTm terme []) name in 
  let hole = read_line () in hole 
let ask_the_son () = 
  let () = Printf.printf "\n Please choose the son where you wan't to go" in 
  let son = read_line () in 
  int_of_string son 


(* -------------- Ensemble des tactics ------------ *)
let intro (Loc(t,p)) = 
  let var = ask_variable_name () in 
  let terme_and_type = begin 
      match t with 
  | Item(Variable(name,terme)) -> failwith "intro : You can't intro something which is not a def"
  | Item(Definition(name,Incomplete(typ,terme))) -> 
     ((replace_hole_inTm terme (Abs(Global var,Hole_inTm 1)) 1),typ)
  | Item(Intermediaire(n,typ,terme)) -> 
     ((replace_hole_inTm terme (Abs(Global var,Hole_inTm 1)) 1),typ)
  | _ -> failwith "intro : this case is supposed to be impossible" 
    end in 
  let var_type = begin match terme_and_type with 
		       | (_,Pi(x,s,t)) -> s
		       | _ -> failwith "intro : you can't intro something which is not an intro" 
		 end in 
  (* je fais bien la substitution donc pas de soucis *)
  let new_type = begin match terme_and_type with 
		       | (_,Pi(x,s,t)) -> substitution_inTm t (FVar x) 0
		       | _ -> failwith "intro : you can't intro something which is not an intro"
  end in 
  let new_terme = begin match terme_and_type with 
  | (terme,_) -> terme
  end in 
  let arbre = complete_focus_terme (Loc(t,p)) new_terme 1 in
  let new_var = Item(Variable(var,var_type)) in
  let arbre = go_down(go_right(insert_right arbre (Section([new_var])))) in
  let new_son = Item(Intermediaire(1,new_type,Hole_inTm(1))) in 
  go_down(go_right(insert_right arbre (Section([new_son]))))

let intro_auto (Loc(t,p)) = 
  let typ = get_type_item (Loc(t,p)) in 
  let name_var = 
    begin 
      match typ with 
      | (Pi(Global(x),s,t)) -> x
      | _ -> failwith "intro_auto : it's not possible to intro something else then a pi" 
    end in 
  let typ_var = 
    begin
      match typ with 
      | (Pi(x,s,t)) -> s
      | _ -> failwith "intro_auto : it's not possible to intro something else then a pi"
    end in 
  let new_typ = 
    begin
      match typ with 
      | (Pi(x,s,t)) -> t
      | _ -> failwith "intro_auto : it's not possible to intro something else then a pi"
    end in 
  let new_terme = Abs(Global(name_var),Hole_inTm 1) in 
  let arbre = complete_focus_terme (Loc(t,p)) new_terme 1 in
  let new_var = Item(Variable(name_var,typ_var)) in
  let arbre = go_down(go_right(insert_right arbre (Section([new_var])))) in
  let new_son = Item(Intermediaire(1,new_typ,Hole_inTm(1))) in 
  go_down(go_right(insert_right arbre (Section([new_son]))))

let rec intros arbre = 
  let typ = get_type_item arbre in 
  begin
    match typ with 
    | (Pi(x,s,t)) -> intros (intro_auto arbre)
    | _ -> arbre
  end
  

let axiome (Loc(t,p)) = 
  let var = ask_variable_name () in   
  let env = get_env (Loc(t,p)) [] in 
  if is_in_env env var 
  then begin 
    let new_arbre = 
      begin 
      match (Loc(t,p)) with 
      | (Loc(Item(Variable(name,terme)),p)) -> failwith "axiome : You can't intro something which is not a def or intermediaire"
      | (Loc(Item(Definition(name,Incomplete(typ,terme))),p)) -> 
	 (Loc(Item(Definition(name,Incomplete(typ,(replace_hole_inTm terme (Inv(FVar (Global(var)))) 1)))),p))
      | (Loc(Item(Intermediaire(n,typ,terme)),p)) -> 
	 (Loc(Item(Intermediaire(n,typ,(replace_hole_inTm terme (Inv(FVar (Global(var)))) 1))),p))
      | _ -> failwith "axiome : this case is supposed to be impossible" 
      end in 
    verif_and_push_up_item new_arbre
    end 
  else (Loc(t,p))

let check (Loc(t,p)) = 
  let typ = begin 
      match t with 
      | Item(Definition(name,Incomplete(typ,terme))) -> typ
      | _ -> failwith "check : you can't check something else than an incomplete definition" 
    end in 
  let terme = 
    begin 
      match t with 
      | Item(Definition(name,Incomplete(typ,terme))) -> terme
      | _ -> failwith "check : you can't check something else than an incomplete definition" 
    end in 
  let name = 
    begin 
      match t with 
      | Item(Definition(name,Incomplete(typ,terme))) -> name
      | _ -> failwith "check : you can't check something else than an incomplete definition" 
    end in 
  if check_if_no_hole_inTm terme 
  then begin
      let final_terme = replace_etiquette_inTm terme (get_def (Loc(t,p)) []) in 
      let final_terme = read (pretty_print_inTm final_terme []) in (* ici c'est le petit tricks, il faut quand meme que j'en parle a pierre *)
      let final_type = replace_etiquette_inTm typ (get_def (Loc(t,p)) []) in 
      let final_type = read (pretty_print_inTm final_type []) in (* ici c'est le petit tricks, il faut quand meme que j'en parle a pierre *)
      let res_check = res_debug(check [] final_terme (big_step_eval_inTm final_type []) "") in 
      if res_check 
      then replace_item (Loc(t,p)) (Item(Definition(name,Complete(final_type,final_terme))))
      else let () = Printf.printf "\nIt Seems that your term is not well checked \n
				   the terme is : %s \n
				   and the type is : %s\n" (pretty_print_inTm final_terme []) (pretty_print_inTm final_type []) in 
	   (Loc(t,p))
    end
  else failwith "check : you can't check if there are at least one hole in your term" 

(* old version of split iter *)
(* let split_iter (Loc(t,p)) =  *)
(*   let predicat = read (ask_predicat "(Pi x N *\)") in   *)
(*   let induct_var = ask_induct_var () in  *)
(*   (\* on construit les deux nouveaux goals à partir du prédicat *\) *)
(*   let first_goal = Section([Item(Intermediaire(Inv(Appl(Ann(predicat,Pi(Global"x",Nat,Star)),Zero)),Hole_inTm(1)))]) in *)
(*   let second_goal = Section([Item(Intermediaire(Pi(Global"x",Nat,Pi(Global"y",Inv(Appl(Ann(predicat,Pi(Global"x",Nat,Star)),Inv(BVar 0))), *)
(* 					Inv(Appl(Ann(predicat,Pi(Global"x",Nat,Star)),Succ(Inv(BVar 0)))))),Hole_inTm(1)))]) in  *)
(*   let terme = get_terme_item t in  *)
(*   (\*  let typ = get_type_item t in  *\) *)
(*   let hole = int_of_string (ask_the_hole terme "iter") in   *)
(*   (\* ici on va modifier le terme sur le focus pour le transformer en Iter avec deux trous *\) *)
(*   let new_terme = Inv(Iter(predicat,Inv(FVar(Global induct_var)),Hole_inTm(1),Hole_inTm(2))) in    *)
(*   let arbre = complete_focus_terme (Loc(t,p)) new_terme hole in *)
(*   (\* maintenant on va insérer dans l'arbre deux nouvelles sections correspondants au deux nouveux goals *\) *)
(*   let arbre = insert_some_right arbre [first_goal;second_goal] in  *)
(*   arbre *)

(* on sait que le prédicat iter est de type (pi x N Star ) *)
let create_iter_predicat returneType var_induct = 
  let predicat = Abs(Global "x",returneType) in 
  bound_var_inTm predicat 0 var_induct  
  
  
  

let split_iter (Loc(t,p)) induct_var = 
  let returne_type  = get_type_focus (Loc(t,p)) in 
  let predicat = create_iter_predicat returne_type induct_var in    
  let first_goal_type = value_to_inTm 0 (big_step_eval_inTm (Inv(Appl(Ann(predicat,Pi(Global"x",Nat,Star)),Zero))) []) in 
  let second_goal_type = value_to_inTm 0 (big_step_eval_inTm 
					      (Pi(Global"x",Nat,Pi(Global"y",Inv(Appl(Ann(predicat,Pi(Global"x",Nat,Star)),Inv(BVar 0))),
					Inv(Appl(Ann(predicat,Pi(Global"x",Nat,Star)),Succ(Inv(BVar 1)))))))
					     []) in 
  let first_goal = Section([Item(Intermediaire(1,first_goal_type,Hole_inTm(1)))]) in 
  let second_goal = Section([Item(Intermediaire(2,second_goal_type,Hole_inTm(1)))]) in
  let terme = get_terme_item (Loc(t,p)) in  
  let hole = int_of_string (ask_the_hole terme "iter") in
  (* ici on va modifier le terme sur le focus pour le transformer en Iter avec deux trous *)
  let new_terme = Inv(Iter(predicat,Inv(FVar(Global induct_var)),Hole_inTm(1),Hole_inTm(2))) in
  let arbre = complete_focus_terme (Loc(t,p)) new_terme hole in
  (* maintenant on va insérer dans l'arbre deux nouvelles sections correspondants au deux nouveux goals *)
  let arbre = insert_some_right arbre [first_goal;second_goal] in
  arbre

(* let split_list (Loc(t,p)) induct_var = *)
  
  
  

let split (Loc(t,p)) = 
  let env = get_env (Loc(t,p)) [] in 
  let induct_var = ask_induct_var () in
  let var_type = return_type_var_env env induct_var in 
  begin 
  match var_type with 
  | Nat -> split_iter (Loc(t,p)) induct_var
  | _ -> failwith "split : you split on a var that has not a type recognise by the program"
  end
  
  

let return (Loc(t,p)) = 
  let terme = get_terme_item (Loc(t,p)) in 
  let terme_push = read (ask_terme ()) in 
  let hole = int_of_string (ask_the_hole terme "iter") in    
  let arbre = complete_focus_terme (Loc(t,p)) terme_push hole in
  arbre
  
  
let nothing (Loc(t,p)) = (Loc(t,p))
  
  
let son (Loc(t,p)) = 
  let num = ask_the_son () in 
  go_n_son (Loc(t,p)) num
  


let verif (Loc(t,p)) = 
  verif_and_push_up_item (Loc(t,p))

let def (Loc(t,p)) = 
  procedure_start_definition (Loc(t,p))

let contexte_def (Loc(t,p)) = 
  let () = Printf.printf "\nEnsemble des definitions : %s\n" (get_and_print_def (Loc(t,p))) in 
  (Loc(t,p))

  
  
(* --------------Fonctions de manipulation de tactiques ----------------- *)			    
let choose_tactic () = 
  let () = Printf.printf "\n Choisir une tactique \n" in
  let tactic  = read_line () in
  match tactic with 
  | "intro" -> intro
  | "intros" -> intros
  | "up" -> proof_up 
  | "little up" -> go_up
  | "down" -> proof_down
  | "son" -> son
  | "left" -> go_left
  | "right" -> go_right
  | "print" -> print_to_screen_location
  | "axiome" -> axiome
  | "verif" -> verif
  | "def" -> def
  | "check" -> check
  | "contexte def" -> contexte_def
 (* faire une fonction ou d'abord on écrit split ce qui appelle celle ci et ensuite on redirige (juste pour pas surgarger cette fonction *)
  | "split" -> split
  | "return" -> return
			
  | _ -> nothing

(* --------------Idées-------------------*)
(* - Une tactique permettant de sauvegarder l'ensemble des définitions complètes dans un fichier et donc une tactique pour faire le chemin
inverse, importer des definitions depuis un fichier *)
  

		  
  


(*let intro (Loc(t,p)) = 
  let () = Printf.printf "\n Please put a name for the variable : \n" in 
  let variable = read_line () in *)
  
			 
	   
