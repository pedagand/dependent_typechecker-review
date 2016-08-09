open Zipper
open Lambda
open Sexplib
open Compiler

(*-----------------------Fonctions pour crée le Upper type------------------------*)
(* permet de crée un type à partir du type donné par l'utilisateur *)
let rec create_uper_type typ = 
  match typ with 
  | Pi(n,(s,t)) -> Pi(n,(s,(create_uper_type t)))
  | Nat -> Star
  | Bool -> Star
  | Liste(alpha) -> Star
  | _ -> failwith "create_uper_type : only for pi at the moment"

(* permet à partir d'un type ainsi que du return du type initial de crée un terme *)
let rec modifie_return_terme typ return = 
  match typ with 
  | Pi(n,(s,t)) -> Abs(n,(modifie_return_terme t return))
  | Star -> return
  | _ -> failwith "create_uper_terme : Only for pi at the moment "

let rec modifie_return_type typ return = 
  match typ with
  | Pi(n,(s,t)) -> Pi(n,(s,(modifie_return_type t return)))
  | Nat -> return
  | Bool -> return
  | Liste(alpha) -> return
  | _ -> failwith "modifie_return_type : mettre a jour la fonction au fur et à mesure pour quelle accepte tous les types"


(* permet de parcourir un pi type jusqu'au bout afin d'en connaitre le type de retour *)
let rec find_return_type typ = 
  match typ with 
  | Pi(n,(s,t)) -> let t = subst_inTm (Pi(n,(s,t))) (Var(Global(n))) in 
                   find_return_type t 
  | x -> let () = Printf.printf "find_return_type : %s \n" (pretty_print_inTm x []) in  x

(* permet de donner la liste des variables présentes dans le théorème *)
let rec liste_me_var terme = 
  match terme with 
  | Pi(name,(s,t)) -> let () = Printf.printf "there is a var %s" name in name :: (liste_me_var t)
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
  else List.fold_left (fun x y -> Appl(x,Inv(Var(Global(y))))) terme liste_var

let make_application_terme (terme : exTm) liste_terme = 
  if liste_terme = [] then terme
  else List.fold_left (fun x y -> Appl(x,y)) terme liste_terme 



(* fonction prenant un argument un type et son nom . Celle ci retourne Defintion avec le uper_type générer en haut de 
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
  let new_save = "(def (" ^ name ^ (pretty_print_inTm new_typ []) ^ ")"in
  Definition(new_name,Complete(new_typ,new_term),new_save) 

let parse_definition def refe = 
  match def with 
  | Sexp.List[Sexp.Atom name;terme] -> let terme = read (Sexp.to_string terme) in 
     Definition(name,Incomplete(terme,Inv(Var(Hole 1))),"")
  | _ -> failwith "parse_definition : it seem's that your def is not good"


(* ---------------- Routines de demande de saisies pour l'utilisateur ----------------------- *)
(* transformer toutes les fonctions de la sorte *)
let rec ask_variable_name ()= 
  let () = Printf.printf "\n Please Choose a name for the var, (you can press enter and it will try to find a name for the var\n" in
  let var = read_line () in begin 
      match var with 
      | "" -> ask_variable_name ()
      | _ -> var
      end 
  
let rec ask_liste_var l = 
  let () = Printf.printf "\nPut a var per line\n" in 
  let var = read_line () in
  match var with 
  | "" -> l
  | str -> ask_liste_var (var :: l)

let rec ask_liste_terme l = 
  let () = Printf.printf "\nPut a terme per line\n" in 
  let var = read_line () in  
  match var with 
  | "" -> l
  | str -> let var = read var in ask_liste_terme (var :: l)

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
  let () = Printf.printf "\n In which hole do you wan't to put your terme" in 
  let hole = read_line () in hole 
let ask_the_son () = 
  let () = Printf.printf "\n Please choose the son where you wan't to go" in 
  let son = read_line () in 
  int_of_string son 


(* -------------- Ensemble des tactics ------------ *)
let intro (Loc(t,p),d) = 
  let var = ask_variable_name () in 
  let terme_and_type = begin 
      match t with 
  | Item(Variable(name,terme)) -> failwith "intro : You can't intro something which is not a def"
  | Item(Definition(name,Incomplete(typ,terme),save)) -> 
     (replace_hole terme 1 (Ann(Abs(var,Inv(Var(Hole 1))),typ)),typ)
  | Item(Intermediaire(n,typ,terme,save)) -> 
     (replace_hole terme 1 (Ann(Abs(var,Inv(Var(Hole 1))),typ)),typ)
  | _ -> failwith "intro : this case is supposed to be impossible" 
    end in 
  let var_type = begin match terme_and_type with 
		       | (_,Pi(x,(s,t))) -> s
		       | _ -> failwith "intro : you can't intro something which is not an intro" 
		 end in 
  (* je fais bien la substitution donc pas de soucis *)
  let new_type = begin match terme_and_type with 
		       | (_,Pi(x,(s,t))) -> subst_inTm (Pi(x,(s,t))) (Var (Global x))
		       | _ -> failwith "intro : you can't intro something which is not an intro"
  end in 
  let new_terme = begin match terme_and_type with 
  | (terme,_) -> terme
  end in 
  let arbre = complete_focus_terme (Loc(t,p),d) (Ann(new_terme,new_type)) 1 in
  let new_var = Item(Variable(var,var_type)) in
  let arbre = go_down(go_right(insert_right arbre (Section([new_var])))) in
  let new_son = Item(Intermediaire(1,new_type,Inv(Var(Hole 1)),"")) in 
  go_down(go_right(insert_right arbre (Section([new_son]))))

let intro_auto (Loc(t,p),d) = 
  let () = Printf.printf "\n enter in intro auto" in
  let typ = get_type_item (Loc(t,p),d) in 
  let name_var = 
    begin 
      match typ with 
      | (Pi(x,(s,t))) -> x
      | _ -> failwith "intro_auto : it's not possible to intro something else then a pi" 
    end in 
  let typ_var = 
    begin
      match typ with 
      | (Pi(x,(s,t))) -> s
      | _ -> failwith "intro_auto : it's not possible to intro something else then a pi"
    end in 
  let new_typ = 
    begin
      match typ with 
      | (Pi(x,(s,t))) -> let () = Printf.printf "\nbefore subst %s" (pretty_print_inTm (Pi(x,(s,t))) []) in 
                         let res = subst_inTm (Pi(x,(s,t))) (Var (Global x)) in 
                         let () = Printf.printf "\n after subst %s" (pretty_print_inTm res []) in 
                         res
      | _ -> failwith "intro_auto : it's not possible to intro something else then a pi"
    end in 
  let new_terme = Abs(name_var,Inv(Var(Hole 1))) in 
  let arbre = complete_focus_terme (Loc(t,p),d) (Ann(new_terme,new_typ)) 1 in
  let new_var = Item(Variable(name_var,typ_var)) in
  let arbre = go_down(go_right(insert_right arbre (Section([new_var])))) in
  let new_son = Item(Intermediaire(1,new_typ,Inv(Var(Hole 1)),"")) in 
  let () = Printf.printf "\nfinish intro auto" in
  go_down(go_right(insert_right arbre (Section([new_son]))))

let rec intros (Loc(t,p),d) = 
  let () = Printf.printf "\nEnter in intro" in 
  let typ = get_type_item (Loc(t,p),d) in 
  let terme = get_terme_item (Loc(t,p),d) in
  let already_complete = 
    begin 
      match terme with 
      | Abs(name,suite) -> true
      | _ -> false
    end in 
  if already_complete 
  then let () = Printf.printf "Intros Already complete\n" in (go_down (go_right (Loc(t,p),d))) (* ici je peux rajouter une intro ? *)
  else let () = Printf.printf "intro : not complete" in 
  begin
    match typ with 
    | (Pi(x,(s,tp))) -> intros (intro_auto (Loc(t,p),d)) 
    | _ -> (Loc(t,p),d)
  end


let procedure_start_definition typ_not_parsed (Loc(t,p),d) = 
  let d = set_def_userDef d typ_not_parsed in
  let d = set_pointeur_userDef d 1 in
  let second_def = parse_definition (Sexp.of_string typ_not_parsed) "" in
  match second_def with 
  | Definition(name,Incomplete(typ,terme),save) -> 
     let defi = init_definition typ name in  
     let first_def = Section([Item(defi)]) in      
     let arbre = (go_down(go_right(insert_right (Loc(t,p),d) first_def))) in 
     let first_def_type = begin 
	 match defi with 
	 | Definition(new_name,Complete(new_typ,new_term),save) -> new_typ
	 | _ -> failwith "procedure_start_definition : it's impossible"
       end in 
      let liste_var = liste_me_var first_def_type in  
      let second_def = begin
	  match second_def with 
	  | Definition(name,Incomplete(typ,term),save) -> Definition(name,Incomplete(
									 modifie_return_type typ (Inv(
											       (make_application 
												 (Var(Global(create_upper_name name typ)))
												  liste_var))),term),save)
	  | _ -> failwith "procedure_start_definition : if this case happend i eat myself"
	end in
      let arbre = (go_down(go_right(insert_right arbre (Section([Item(second_def)]))))) in 
      let (Loc(t,p),d) = intros arbre in
      let d = set_patAct_userDef d (Clause(Pattern(get_type_item (Loc(t,p),d)),Hole(1))) in
      (Loc(t,p),d)
  | _ -> failwith "procedure_start_definition : something goes wrong during the creation of the definition"

  

let axiome var (Loc(t,p),d) = 
  let env = get_env (Loc(t,p),d) [] in 
  if is_in_env env var 
  then begin 
    let new_arbre = 
      begin 
      match (Loc(t,p)) with 
      | (Loc(Item(Variable(name,terme)),p)) -> failwith "axiome : You can't intro something which is not a def or intermediaire"
      | (Loc(Item(Definition(name,Incomplete(typ,terme),save)),p)) -> 
	 (Loc(Item(Definition(name,Incomplete(typ,(replace_hole terme 1 (Var(Global(var))))),save)),p),d)
      | (Loc(Item(Intermediaire(n,typ,terme,save)),p)) -> 
	 (Loc(Item(Intermediaire(n,typ,(replace_hole terme 1 (Var (Global(var)))),save)),p),d)
      | _ -> failwith "axiome : this case is supposed to be impossible" 
      end in 
    verif_and_push_up_item new_arbre
    end 
  else (Loc(t,p),d)

let check file (Loc(t,p),d) =   
  let typ = begin 
      match t with 
      | Item(Definition(name,Incomplete(typ,terme),save)) -> typ
      | _ -> failwith "check : you can't check something else than an incomplete definition" 
    end in 
  let terme = 
    begin 
      match t with 
      | Item(Definition(name,Incomplete(typ,terme),save)) -> terme
      | _ -> failwith "check : you can't check something else than an incomplete definition" 
    end in 
  let name = 
    begin 
      match t with 
      | Item(Definition(name,Incomplete(typ,terme),save)) -> name
      | _ -> failwith "check : you can't check something else than an incomplete definition" 
    end in 
  if check_if_no_hole_inTm terme 
  then begin
      let () = Printf.printf "Check : start to make treatment\n" in
      let defs = get_def (Loc(t,p),d) [] in
      let final_terme = replace_liste_var terme defs in 
      let () = Printf.printf "Check : treatment 1\n" in
      let final_terme = read (pretty_print_inTm final_terme []) in (* ici c'est le petit tricks, il faut quand meme que j'en parle a pierre *)
      let final_terme = remove_useless_anotation_inTm final_terme in
      let final_type = replace_liste_var typ defs in 
      let () = Printf.printf "Check : treatment 2\n" in
      let final_type = read (pretty_print_inTm final_type []) in (* ici c'est le petit tricks, il faut quand meme que j'en parle a pierre *)
      let () = Printf.printf "Check : This is the env used %s\n" (print_def defs) in
      let () = Printf.printf "Check : LOL The terme juste before checking \n %s \n" (pretty_print_inTm final_terme []) in
      let () = Printf.printf "Check : just before check\n" in
      let res_check = check final_terme final_type in 
      let () = Printf.printf "Check as been proceed" in 
      if res_check 
      then let () = Printf.printf "\n%s\n" (pretty_print_def d) in
		   replace_item (Loc(t,p),d) (Item(Definition(name,Complete(final_type,final_terme),"")))
      else let () = Printf.printf "\nIt Seems that your term is not well checked \n
				   the terme is : %s \n
				   and the type is : %s\n" (pretty_print_inTm final_terme []) (pretty_print_inTm final_type []) in 
	   (Loc(t,p),d)
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
  let predicat = abstract var_induct returneType in 
  predicat

let create_bool_predicat returneType var_induct = 
  let predicat = abstract var_induct returneType in 
  predicat 
  
let create_liste_predicat returneType var_induct = 
  let predicat = abstract var_induct returneType in
  predicat
 

let fresh_var  =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c 

let split_iter (Loc(t,p),d) induct_var = 
  let var_un = fresh_var () in
  let var_deux = "H" in
  let returne_type  = get_type_focus "split iter" (Loc(t,p),d) in 
  let predicat = create_iter_predicat returne_type induct_var in    
  let second_goal_typ  = value_to_inTm 0 (big_step_eval_inTm (Inv(Appl(Ann(predicat,Pi(var_un,(Nat,Star))),Zero))) []) in 
  let first_goal_typ = value_to_inTm 0 (big_step_eval_inTm 
					      (Pi(var_un,(Nat,Pi(var_deux,(Inv(Appl(Ann(predicat,Pi("x",(Nat,Star))),Inv(Var(Bound 0)))),
					Inv(Appl(Ann(predicat,Pi("x",(Nat,Star))),Succ(Inv(Var(Bound 1))))))))))
					     []) in 
(* find_return_type typ a faire après pour les userDef EN RENTRANT DE LA PAUSE FAIRE LA FONCTION QUI ENLEVE LES TROUS DE ACT *)
  let clause_un = Clause(Pattern(find_return_type first_goal_typ),Hole(d.pointeur + 1)) in 
  let clause_deux = Clause(Pattern(find_return_type second_goal_typ),Hole(d.pointeur + 2)) in   
  let liste_clause = [clause_un;clause_deux] in
  let spl = (Split(induct_var,liste_clause)) in
  let d = set_patAct_userDef d (complete_clause d.patAct spl d.pointeur) in
(*   let d = set_pointeur_userDef d (d.pointeur + 1) in JE PENSE QUE CETTE LIGNE N4EST PAS NECESSAIRE *)
  let second_goal  = Section([Item(Intermediaire(1,first_goal_typ,Inv(Var(Hole 1)),""))]) in 
  let first_goal = Section([Item(Intermediaire(2,second_goal_typ,Inv(Var(Hole 1)),""))]) in
(*  let terme = get_terme_item (Loc(t,p)) in  
   JE TEST POUR VOIR SI EN METTANT SYST2MATIQUEMENT DANS LE 1 CA MARCHE let hole = int_of_string (ask_the_hole terme "iter") in *)
  let hole = 1 in
  (* ici on va modifier le terme sur le focus pour le transformer en Iter avec deux trous *)
  let new_terme = Iter(predicat,Inv(Var(Global induct_var)),Inv(Var(Hole 1)),Inv(Var(Hole 2))) in
  let arbre = complete_focus_terme (Loc(t,p),d) new_terme hole in
  (* maintenant on va insérer dans l'arbre deux nouvelles sections correspondants au deux nouveux goals *)
  let arbre = insert_some_right arbre [first_goal;second_goal] in
  let arbre = print_to_screen_location arbre in 
  arbre

let split_bool (Loc(t,p),d) induct_var = 
  let returne_type  = get_type_focus "split bool" (Loc(t,p),d) in 
  let predicat_type = Pi("x",(Bool,Star)) in
  let predicat = create_bool_predicat returne_type induct_var in
  let then_type = value_to_inTm 0 (big_step_eval_inTm (Inv(Appl(Ann(predicat,predicat_type),True))) []) in 
  let else_type = value_to_inTm 0 (big_step_eval_inTm (Inv(Appl(Ann(predicat,predicat_type),False))) []) in 
  let then_goal = Section([Item(Intermediaire(1,then_type,Inv(Var(Hole 1)),""))]) in 
  let else_goal = Section([Item(Intermediaire(2,else_type,Inv(Var(Hole 1)),""))]) in 
  (* start the save of the def *)
  let clause_un = Clause(Pattern(find_return_type then_type),Hole(d.pointeur + 1)) in 
  let clause_deux = Clause(Pattern(find_return_type else_type),Hole(d.pointeur + 2)) in   
  let liste_clause = [clause_un;clause_deux] in
  let spl = (Split(induct_var,liste_clause)) in
  let d = set_patAct_userDef d (complete_clause d.patAct spl d.pointeur) in
(*   let d = set_pointeur_userDef d (d.pointeur + 1) in MEME JUSTIFICATION QUE POUR SPLIT ITER *)
  (* end *)
  let hole = 1 in 
  let new_terme = Ifte(predicat,Inv(Var(Global induct_var)),Inv(Var(Hole 1)),Inv(Var(Hole 2))) in 
  let (Loc(t,p),d) = complete_focus_terme (Loc(t,p),d) new_terme hole in 
  let (Loc(t,p),d) = insert_some_right (Loc(t,p),d) [else_goal;then_goal] in
  let (Loc(t,p),d) = print_to_screen_location (Loc(t,p),d) in 
  (Loc(t,p),d)


(* alpha is the type of the list which is called with *)
let split_liste (Loc(t,p),d) induct_var alpha = 
  let returne_type = get_type_focus "split_liste" (Loc(t,p),d) in 
  let predicat_type = Pi("x",(Liste(alpha),Star)) in
  let predicat = create_liste_predicat returne_type induct_var in 
  let f_type = value_to_inTm 0 (big_step_eval_inTm (Pi("e",(alpha,
						       Pi("xs",(Liste(alpha),
							  Pi("h",(Inv(Appl(Ann(predicat,predicat_type),Inv(Var(Bound 0)))),
							     Inv(Appl(Ann(predicat,predicat_type),Cons(Inv(Var(Bound 2)),Inv(Var(Bound 1)))))))))))) []) in
  let nil_type = value_to_inTm 0 (big_step_eval_inTm (Inv(Appl(Ann(predicat,predicat_type),Nil))) []) in 
  let f_goal = Section([Item(Intermediaire(1,f_type,Inv(Var(Hole 1)),""))]) in 
  let nil_goal = Section([Item(Intermediaire(2,nil_type,Inv(Var(Hole 1)),""))]) in 
  let hole = 1 in 
  let new_terme = Fold(predicat,alpha,Inv(Var(Global(induct_var))),Inv(Var(Hole 1)),Inv(Var(Hole 2))) in 
  let arbre = complete_focus_terme (Loc(t,p),d) new_terme hole in 
  let arbre = insert_some_right arbre [nil_goal;f_goal] in 
  arbre
 
  
  
let split induct_var (Loc(t,p),d) = 
  let env = get_env (Loc(t,p),d) [] in 
  let var_type = return_type_var_env env induct_var in 
  let defs = get_def (Loc(t,p),d) [] in 
  let final_typ = value_to_inTm 0 (big_step_eval_inTm (replace_liste_var var_type defs) []) in   
  begin 
  match final_typ with 
  | Nat -> split_iter (Loc(t,p),d) induct_var
  | Bool -> split_bool (Loc(t,p),d) induct_var
  | Liste(alpha) -> split_liste (Loc(t,p),d) induct_var alpha
  | _ -> failwith "split : you split on a var that has not a type recognise by the program"
  end

(* -------------------tactiques permettants de remplir une userDefinition afin de la sauvegarder--------------------*)
(* en suspend parceque c'est le type checker qui va me les générers *)
  
  


  (* C'est un test mais a chaque fois que je vérifie un terme je vais decrémenter le compteur de 1 *)
let verif (Loc(t,p),d) = 
  let () = Printf.printf "\nEnter in the verif \n" in
  let n = get_num_Inter (Loc(t,p),d) in 
  let d = set_pointeur_userDef d (d.pointeur - n) in
  (verif_and_push_up_item (Loc(t,p),d))

let rec is_etiquette t = 
  match t with 
  | Appl(creuse,suite) -> is_etiquette creuse 
  | Var(Global(name)) -> true 
  | _ -> false
and is_tag t = 
  match t with
  | Inv(Appl(creuse,suite)) -> is_etiquette creuse
  | Succ(x) -> is_etiquette (Ann(x,Nat))
  | _ -> false

let rec find_var_with_type (Loc(t,p),d) terme = 
  let terme = terme in
  let env = get_env (Loc(t,p),d) [] in 
  find_in_env env terme
and find_in_env env terme = 
  match env with 
  | [] -> failwith "find_in_env: you return a terme that is not in the env"
  | (name,typ) :: suite -> if equal typ terme then name else find_in_env suite terme 


let return (terme : inTm) hole (Loc(t,p),d) = 
  let typ = value_to_inTm 0 (big_step_eval_inTm (get_type_focus "" (Loc(t,p),d)) []) in
  let d = set_patAct_userDef d (complete_clause d.patAct (Return terme) d.pointeur) in
  if is_tag terme
  then let () = Printf.printf "is_tag goign trhought then\n" in 
       (* let var = Inv(FVar(Global(find_var_with_type (Loc(t,p),d) terme))) in *)
       let arbre = complete_focus_terme (Loc(t,p),d) (Ann(terme,typ)) hole in 
       let () = Printf.printf "finish the return\n" in
       verif arbre
  else let () = Printf.printf "is_tag goign trhought else\n" in 
       let arbre = complete_focus_terme (Loc(t,p),d) (Ann(terme,typ)) hole in
       let () = Printf.printf "finish the return\n" in
       verif arbre
  
let son n (Loc(t,p),d) = 
  let d = set_pointeur_userDef d (d.pointeur + n) in  
  let arbre = (go_n_son (Loc(t,p),d) n) in 
  intros arbre

let eval (Loc(t,p),d) = 
  let typ = get_type_item (Loc(t,p),d) in
  let terme = Ann((get_terme_item (Loc(t,p),d)),typ) in
  let liste_terme = List.rev (ask_liste_terme []) in 
  let def = get_def (Loc(t,p),d) [] in
  let liste_terme = List.map (fun x -> replace_liste_var x def) liste_terme in
  let appl_t = make_application_terme terme liste_terme in
  let eval_t = value_to_inTm 0 (big_step_eval_inTm (Inv(appl_t)) [])  in 
  let () = Printf.printf "\nVoici l'évaluation de votre terme : \n %s \nEND EVAL\n" (pretty_print_inTm eval_t []) in
  (Loc(t,p),d)
  
let count_son_tact (Loc(t,p),d) = 
  let n = count_son (Loc(t,p),d) in 
  let () = Printf.printf "Il y a %d fils ici" n in 
  (Loc(t,p),d)

let nothing (Loc(t,p),d) = (Loc(t,p),d)
			   
(* ------------------ ici c'est pour le chargement des defintions *)
(* let rec patAct_to_terme arbre pattern_match  =  *)
(*   let goal_terme = get_type_item arbre in *)
(*   match pattern_match with  *)
(*   | [] -> arbre  *)
(*   | (Pattern(p),act) :: suite -> let liste = begin  *)
(* 				     match matching_inTm p goal_terme [] with  *)
(* 				     | Success(l) -> l *)
(* 				     | Failed ->  [] *)
(* 				   end in  *)
(* 				 begin  *)
(* 				   match act with  *)
(* 				   | Split(name,patActListe) -> patAct_to_terme (split name arbre) suite  *)
(* 				   | Return(t) -> let terme = change_name_liste t liste in  *)
(* 						  return terme 1 arbre *)
(* 				 end *)			
	   

(* ----------------------------fonctions de debug ----------------------*)
let rec pretty_print_goal_liste liste = 
  match liste with 
  | [] -> "End"
  | elem :: suite -> pretty_print_inTm elem [] ^ ";" ^ pretty_print_goal_liste suite
  
(*-----------------------------Fin--------------------------------------*)
(* i need to focus on this if i wan't to debug *)
let rec create_liste_goal l n (Loc(t,p),d) = 
  let () = Printf.printf "Enter in the create_liste_goal with n %s\n" (string_of_int n)  in
  match n with 
  | 0 -> l 
  | n -> let s = intros (go_n_son (Loc(t,p),d) n) in (* intros (go_n_son (Loc(t,p),d) n) in *)
	 let liste = (get_type_focus "create_liste_goal" s) :: l in 
	 create_liste_goal liste (n - 1) (Loc(t,p),d)
and liste_me_goal (Loc(t,p),d) = 
  let n = count_son (Loc(t,p),d) in   
  let () = Printf.printf "liste_me_goal : %s\n" (string_of_int n) in 
  begin match n with
	| 0 -> (get_type_focus "liste_me_goal" (Loc(t,p),d)) :: []
	| n -> create_liste_goal [] n (Loc(t,p),d)
  end 
    
    
(* cette fonction ira nécéssairement dans le premier but si il en existe plusieurs *)
(* let rec go_throught_lambda (Loc(t,p)) = 
  match t with 
  | Item(Variable(name,terme)) -> go_throught_lambda (go_down (go_right(Loc(t,p))))
  | Item(Intermediaire(n,name,terme)) -> 
     begin 
      match terme with 
      | Abs(nom,suite) -> go_throught_lambda (go_down (go_right (Loc(t,p))))
      | _ -> (Loc(t,p))
    end
  | _ -> go_down (Loc(t,p)) *)

(* l'argument l est le mapping obtenue par le matching lors de l'évaluation de la clause *)
let rec act_to_terme a map_match (Loc(t,p),d) = 
  let () = Printf.printf "\nact_to_terme %s \n" (pretty_print_act a) in
  match a with 
  | Return(ter) -> return ter 1 (intros (Loc(t,p),d))
  | Split(id,clause_liste) -> let induct_var = begin 
				  match change_name_liste (Inv(Var(Global(id)))) map_match with 
				  | Inv(Var(Global(x))) -> x 
				  | _ -> id
				end in 
			      let (Loc(t,p),d) = split induct_var (Loc(t,p),d) in 
			      liste_clause_to_terme clause_liste (Loc(t,p),d)
  | Hole(x) -> failwith "act_to_terme : this is not possible that a hole appear here"
and clause_to_terme c (Loc(t,p),d)= 
  match c with 
  | Clause(Pattern(pa),a) -> let () = Printf.printf "\nClause_to_term: start new clause with pattern: %s \n" (pretty_print_inTm pa []) in 
			    let l = liste_me_goal (Loc(t,p),d) in 			    
			    let () = Printf.printf "list me goal done \n" in
			    let res_match = match_pattern_goal_liste l pa 1 in 
			    let map_var = 
			      begin match res_match with 
				    | (n,Failed) -> failwith 
						  ("clause_to_terme : this pattern match no goal so fail p:" ^ pretty_print_inTm pa [] 
						  ^ " goal_liste :  " ^ pretty_print_goal_liste l)
				    | (n,Success(map_var)) -> map_var
			    end in 
			    let goal_number = 
			      begin match res_match with 
				    | (n,Failed) -> failwith "clause_to_terme : this pattern match no goal so fail"
				    | (n,Success(map_var)) -> n
			    end in 
			    (* c'est ici que je descend dans l'arbre (cela remontera tout seul avec les verif *)
			    act_to_terme a map_var ((go_n_son (Loc(t,p),d) goal_number)) (* l'erreur semble venir d'ici a cause de l'intro ??*)
  | Clause_Top -> failwith "clause_to_term : this is not supposed to happend"
and liste_clause_to_terme liste_clause (Loc(t,p),d) =
  match liste_clause with 
  | [] -> (Loc(t,p),d)
  | c :: suite -> let arbre = clause_to_terme c (Loc(t,p),d) in 
		  liste_clause_to_terme suite arbre
			    

(* faire une fonction à coté qui permet de lire les fichiers *)
let rec userDefs_to_terme l (Loc(t,p),d) =  
  match l with 
  | [] -> (Loc(t,p),d)
  | d :: suite ->
     let arbre = procedure_start_definition d.def (Loc(t,p),d) in 
     let arbre = intros arbre in 
     let arbre = clause_to_terme d.patAct arbre in 
     check "" arbre 

  
  



(* supprimer ces printf de merde *)
let def typ_not_parsed arbre = 
  procedure_start_definition typ_not_parsed arbre

let contexte_def (Loc(t,p),d) = 
  let () = Printf.printf "\nEnsemble des definitions : %s\n" (get_and_print_def (Loc(t,p),d)) in 
  (Loc(t,p),d)

let rec file_to_string f l= 
   try 
    let line = l ^ (input_line f) in  (* read line from in_channel and discard \n *)
    file_to_string f line
   with e -> l
  
(* let replace input output =
  Str.global_replace (Str.regexp_string input) output *)

(* prend un string en argument pour ouvir un flux sur celui ci *)
(* let load_def fichier (Loc(t,p)) = 
  let f = open_in fichier in
  let res = file_to_string f "" in   
  let () = close_in f in 
  let () = Printf.printf "\n%s\n" res in
  let res = replace "\t" "" res in 
  let () = Printf.printf "\n%s\n" res in
  (* maintenant il faut parser la réponse ect... *)
  let defs = read_definition res in 
  userDef_to_terme defs (Loc(t,p)) *)



 let load_def defs (Loc(t,p),d) = 
  let defs = read_definition defs in 
  userDefs_to_terme defs (Loc(t,p),d) 

let rec load_terme str (Loc(t,p),d) =
  let def = Sexp.of_string(str) in 
  let def = parse_def_terme def in
  let first_def = Section([Item(def)]) in      
  let arbre = (go_down(go_right(insert_right (Loc(t,p),d) first_def))) in   
  check "" arbre  
and parse_def_terme str  = 
  match str with 
  | Sexp.List [Sexp.Atom name; terme;typ] -> 
     let parse_terme = read (Sexp.to_string terme) in
     let parse_typ = read (Sexp.to_string typ) in 
     Definition(name,Incomplete(parse_typ,parse_terme),"")
  | _ -> failwith "your def doesn't have a good shape"

  
let rec def_to_liste str = 
  match str with 
  | Sexp.List l -> List.fold_right (fun x li -> (parse_def_terme x) :: li) l []
  | _ -> failwith "def_to_liste : your liste don't have a good shape" 
let rec load_liste_terme l (Loc(t,p),d) = 
  match l with 
  | [] -> (Loc(t,p),d)
  | elem :: suite -> 
     let first_def = Section([Item(elem)]) in      
     let arbre = (go_down(go_right(insert_right (Loc(t,p),d) first_def))) in   
     load_liste_terme suite (check "" arbre)
let load_fichier_terme str (Loc(t,p),d) = 
  let def = Sexp.of_string(str) in
  let liste_def = def_to_liste def in 
  let arbre = load_liste_terme liste_def (Loc(t,p),d) in 
  arbre
  

  
let replace_def (Loc(t,p),d) = 
  let terme = get_terme_item (Loc(t,p),d) in 
  let env = get_def (Loc(t,p),d) [] in 
  let terme = replace_liste_var terme env in 
  let () = Printf.printf "\nThis is your terme with def replaced %s \n" (pretty_print_inTm terme []) in
  (Loc(t,p),d)
  
  
  
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
  | "son" -> let n = ask_the_son () in 
	     son n
  | "left" -> go_left
  | "right" -> go_right
  | "print" -> print_to_screen_location
  | "axiome" -> let var = ask_variable_name () in axiome var
  | "verif" -> verif
  | "def" ->   let () = Printf.printf "\n\nEntrer une nouvelle définition à prouver : \n" in 
	       let typ_not_parsed = read_line () in def typ_not_parsed
  | "check" -> 	   let () = Printf.printf "Please choose a file to save your def Il faut que je complète cette partie quand je saurais faire
					   les entrées sorties\n " in 	   
		   let file = read_line () in check file
  | "contexte def" -> contexte_def
 (* faire une fonction ou d'abord on écrit split ce qui appelle celle ci et ensuite on redirige (juste pour pas surgarger cette fonction *)
  | "split" -> let induct_var = ask_induct_var () in split induct_var
  | "return" -> let () = Printf.printf "Enter the terme you wan't to push on it \n" in
		let terme = read (read_line ()) in 
		(* let () = Printf.printf "Enter the hole you wan't to complete \n" in *)
		let hole = 1 in (* int_of_string (read_line ()) in *)
		return terme hole
  | "load" -> 
     let () = Printf.printf "\nEnter the name of the filename you wan't to load\n" in 
     let fichier = read_line () in load_def fichier
  | "count son" -> count_son_tact
  | "eval" -> eval
  | "load terme" -> 
     let () = Printf.printf "\nPut the definition of the form (name (terme) (typ)) \n" in
     let str = read_line () in load_terme str
  | "load file" ->   
     let () = Printf.printf "Dans la vraie vie je vais faire de la lecture de fichier mais la cc directement le contenu du fichier" in 
     let str = read_line () in 
     load_fichier_terme str 
  | "replace def" -> replace_def
  | _ -> nothing

(* --------------Idées-------------------*)
(* - Une tactique permettant de sauvegarder l'ensemble des définitions complètes dans un fichier et donc une tactique pour faire le chemin
inverse, importer des definitions depuis un fichier *)
  

		  
  


(*let intro (Loc(t,p)) = 
  let () = Printf.printf "\n Please put a name for the variable : \n" in 
  let variable = read_line () in *)
  
			 
	   

