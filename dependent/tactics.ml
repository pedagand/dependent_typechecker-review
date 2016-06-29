open Zipper
open Lambda
open Sexplib


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
  | Pi(Global(name),s,t) -> name :: (liste_me_var t)
  | _ -> []

let create_upper_name name typ = 
  (String.uppercase name) ^ "_" ^ (List.fold_right (fun x y -> x ^ "_" ^ y) (liste_me_var typ) "")

(* prend un terme, calcule sa liste de variable et retourne l'application de celui ci *)
let make_application terme typ = 
  let liste_var = liste_me_var terme in
  if liste_var = [] then terme 
  else Inv(List.fold_left (fun x y -> Appl(x,Inv(FVar(Global(y))))) (Ann(terme,typ)) liste_var)



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
     let first_def = Section([Item(init_definition typ name)]) in      
     let arbre = (go_down(go_right(insert_right arbre first_def))) in 
     let second_def = begin
	 match second_def with 
	 | Definition(name,Incomplete(typ,term)) -> Definition(name,Incomplete(
									modifie_return_type typ (Ref(create_upper_name name typ)),term))
	 | _ -> failwith "procedure_start_definition : if this case happend i eat myself"
	 end in
     let arbre = (go_down(go_right(insert_right arbre (Section([Item(second_def)]))))) in 
     arbre
  | _ -> failwith "procedure_start_definition : something goes wrong during the creation of the definition"


(* ---------------- Routines de demande de saisies pour l'utilisateur ----------------------- *)
let ask_variable_name ()= 
  let () = Printf.printf "\n Please Choose a name for the var, (you can press enter and it will try to find a name for the var\n" in
  let var = read_line () in var
  
     





(* -------------- Ensemble des tactics ------------ *)
let intro (Loc(t,p)) = 
  let var = ask_variable_name () in 
  let var = begin if var = "" 
		  then failwith "Intro : Enter doesnt work" (* modifier afin de crée une variable *)
		  else var 
	    end in 
  let terme_and_type = begin 
      match t with 
  | Item(Variable(name,terme)) -> failwith "intro : You can't intro something which is not a def"
  | Item(Definition(name,Incomplete(typ,terme))) -> 
     ((replace_hole_inTm terme (Abs(Global var,Hole_inTm 1)) 1),typ)
  | Item(Intermediaire(typ,terme)) -> 
     ((replace_hole_inTm terme (Abs(Global var,Hole_inTm 1)) 1),typ)
  | _ -> failwith "intro : this case is supposed to be impossible" 
    end in 
  let var_type = begin match terme_and_type with 
		       | (_,Pi(x,s,t)) -> s
		       | _ -> failwith "intro : you can't intro something which is not an intro" 
		 end in 
  let new_type = begin match terme_and_type with 
		       | (_,Pi(x,s,t)) -> t
		       | _ -> failwith "intro : you can't intro something which is not an intro"
  end in 
  let new_terme = begin match terme_and_type with 
  | (terme,_) -> terme
  end in 
  let arbre = complete_focus_terme (Loc(t,p)) new_terme 1 in
  let new_var = Item(Variable(var,var_type)) in
  let arbre = go_down(go_right(insert_right arbre (Section([new_var])))) in
  let new_son = Item(Intermediaire(new_type,Hole_inTm(1))) in 
  go_down(go_right(insert_right arbre (Section([new_son]))))

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
      | (Loc(Item(Intermediaire(typ,terme)),p)) -> 
	 (Loc(Item(Intermediaire(typ,(replace_hole_inTm terme (Inv(FVar (Global(var)))) 1))),p))
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
      | Item(Definition(name,Incomplete(typ,terme))) -> typ
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
      let final_terme = replace_ref_inTm terme (get_def (Loc(t,p)) []) in 
      let final_terme = read (pretty_print_inTm final_terme []) in (* ici c'est le petit trics, il faut quand meme que j'en parle a pierre *)
      let res_check = res_debug(check [] final_terme (big_step_eval_inTm typ []) "") in 
      if res_check 
      then replace_item (Loc(t,p)) (Item(Definition(name,Complete(typ,final_terme))))
      else let () = Printf.printf "\nIt Seems that your term is not well checked \n" in 
	   (Loc(t,p))
    end
  else failwith "check : you can't check if there are at least one hole in your term" 

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
  | "up" -> proof_up 
  | "down" -> proof_down
  | "left" -> go_left
  | "right" -> go_right
  | "print" -> print_to_screen_location
  | "axiome" -> axiome
  | "verif" -> verif
  | "def" -> def
  | "check" -> check
  | "contexte def" -> contexte_def
  | _ -> failwith "you tactic doesnt exist yet but you can create it if you wan't" 


  

		  
  


(*let intro (Loc(t,p)) = 
  let () = Printf.printf "\n Please put a name for the variable : \n" in 
  let variable = read_line () in *)
  
			 
	   

