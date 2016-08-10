open Lambda 
open Sexplib


(* open Tactics *)

type pattern = 
  | Pattern of inTm 

(* le inTm de ce résult est une substitution *)
type matching = 
  | Success of (string * exTm) list
  | Failed


type act = 
  | Return of inTm
  | Split of string * clause list
  | Hole of int
and clause = 
  | Clause of pattern * act
  | Clause_Top

type userDefinition = 
  {    
    def : string;
    patAct : clause;
    pointeur : int;
  }


let rec complete_act a sub indice= 
  match a with 
  | Hole x -> if indice = x then sub else Hole x
  | Split(str,l) -> Split(str,(complete_clause_liste l sub indice))
  | Return(x) -> Return(x)
and complete_clause_liste l sub indice = 
  match l with 
    | [] -> []
    | Clause(p,a) :: suite -> Clause(p,(complete_act a sub indice)) :: complete_clause_liste suite sub indice
    | Clause_Top :: suite-> failwith "complete act_list this is not supposed to happend" 
and complete_clause c sub indice =
  match c with
  | Clause(p,a) -> Clause(p,(complete_act a sub indice))
  | Clause_Top -> failwith "complete_clause : this is not possible"	     


let set_def_userDef u d = 
  {def = d; patAct = u.patAct;pointeur = u.pointeur}
let set_patAct_userDef u p = 
  {def = u.def; patAct = p;pointeur = u.pointeur}
let set_pointeur_userDef u p = 
  {def = u.def; patAct = u.patAct; pointeur = p}
   
(* lors du parse on va initialiser une structure de def *)


let rec parse_clause str = 
  match str with 
  | Sexp.List [p;a] -> Clause(Pattern((* post_parsing_pattern_inTm *) (read (Sexp.to_string p))),parse_act a)
  | _ -> failwith "parse_clause : your clause don't have a good shape" 
and parse_act str = 
  match str with 
  | Sexp.List [Sexp.Atom "<="; Sexp.Atom id;Sexp.List clauses] -> 
     let liste_clause = List.fold_right (fun c suite -> (parse_clause c) :: suite) clauses [] in 
     Split(id,liste_clause)		       		 
  | Sexp.List [Sexp.Atom "->";t] -> Return(read (Sexp.to_string t))
  | _ -> failwith ("parse_act : your action don't have a good shape" ^ Sexp.to_string str)
(*and post_parsing_pattern_inTm t = 
  match t with 
  | Inv(x) -> Inv(post_parsing_pattern_exTm x)
  | _ -> failwith "post_parsing_pattern_exTm : this is not supposed to happend" *)
(*and post_parsing_pattern_exTm t = 
  match t with 
  | Appl(creuse,x) -> Appl(post_parsing_pattern_exTm creuse ,x)
  | Var(Global(x)) -> Label(x,Star) (* TODO :: faire attention cette ligne est fausse c'est juste pour bypasser l'erreur *)
  | _ -> failwith "post_parsing_pattern : it seem's that it don't work" *)


(* j'initialise le pointeur à 1!!! *)
let rec parse_type_definition str l = 
  match str with 
  | Sexp.List [Sexp.Atom "def";Sexp.List def;clause] -> 
     {def = Sexp.to_string (Sexp.List def);patAct = parse_clause clause;pointeur = 1} :: l
  | Sexp.List [elem] -> parse_type_definition elem l 
(*  | Sexp.List [Sexp.List elem; suite] -> 
     let liste = parse_type_definition (Sexp.List elem) l in 
     parse_type_definition suite liste *)
  | _ -> failwith ("parse_type_definition : your definition don't have a good shape: \n " ^ Sexp.to_string str)

let read_definition str = 
  parse_type_definition (Sexp.of_string str) []


  
     
(* dans la fonction de création des defintion dans l'arbre il faut prendre en considération le fait que ce soit une liste *)

  

(* let rec parse_def_pattern_match str = *)
(*   match str with  *)
(*   | Sexp.List [Sexp.Atom "def";Sexp.List def; Sexp.List [p;a]] ->  *)
(*      let def =   in  *)
(*      let p = Pattern(parse_term [] p) in  *)
(*      let a = parse_act a in  *)
(*      let ret = {id = id; *)
(* 		typ = typ;  *)
(* 		patAct = (p,a); *)
(* 	       } in ret *)
(*   | _ -> failwith "parse_def_pattern_match : your def don't have a good shape"  *)

(* let read_def_pattern t = parse_def_pattern_match (Sexp.of_string t) *)

let rec pretty_print_act a = 
  match a with 
  | Split(id,l) -> "(<= " ^ id ^ "\n(" ^ pretty_print_clause_liste l ^ "))"
  | Return(t) -> "(-> " ^ " " ^ pretty_print_inTm t [] ^ ")\n"
  | Hole(x) -> "_" ^ string_of_int x
and pretty_print_clause c = 
  match c with 
  | Clause(Pattern(p),a) -> "(" ^ pretty_print_inTm p [] ^ " " ^ pretty_print_act a ^ ")"
  | Clause_Top -> ""
and pretty_print_clause_liste l = 
  match l with 
  | [] -> "" 
  | elem :: suite ->  pretty_print_clause elem ^ " "^ pretty_print_clause_liste suite
and pretty_print_def userAct = 
  "(def " ^ userAct.def ^ " " ^ pretty_print_clause userAct.patAct ^ ")"

(*
let pretty_print_def userDef = 
  let id = userDef.id in 
  let typ = pretty_print_inTm userDef.typ []  in 
  let tuple_string = pretty_print_patact userDef.patAct in 	     
  let res = "(def " ^ id ^ " " ^ typ ^ " \n" ^ tuple_string ^ ")" in
  res
 *)


(* Fonctions manipulants une user_def afin de la transformer en terme *)
(* le premier est un terme faisant office de pattern et le second le terme à matcher *)
(* fonction en cour de modification *)
(* le truc de gauche c'est le pattern de l'utilisateur et a droite le terme *)
let rec matching_inTm p t (l : (string * exTm) list) =
  match (p,t) with 
  | (Abs(_,x1),Abs(_,x2)) -> matching_inTm x1 x2 l
  | (Pi(_,(x1,y1)),Pi(_,(x2,y2))) -> begin match matching_inTm x1 x2 l with
				       | Success(liste) -> matching_inTm y1 y2 liste  
				       | Failed -> Failed
				 end
  | (Sig(_,(x1,y1)),Sig(_,(x2,y2))) -> begin match matching_inTm x1 x2 l with 
					 | Success(liste) -> matching_inTm y1 y2 liste 
					 | Failed -> Failed
				   end
  | (Star,Star) -> Success(l)
  | (Zero,Zero) -> Success(l)
  | (Succ(n1),Succ(n2)) -> matching_inTm n1 n2 l
  | (Nat,Nat) -> Success(l)
  | (Bool,Bool) -> Success(l)
  | (True,True) -> Success(l)
  | (False,False) -> Success(l)
(*   | (Inv(FVar(Global name)),terme) -> Success((name,terme) :: l) Plus besoin de ce cas *)
  | (Inv(x1),Inv(x2)) -> matching_exTm x1 x2 l
  | (Pair(x1,y1),Pair(x2,y2)) -> begin match matching_inTm x1 x2 l with 
				       | Success(liste) -> matching_inTm y1 y2 liste 
				       | Failed -> Failed 
				 end
  | (Vec(x1,y1),Vec(x2,y2)) -> begin match matching_inTm x1 x2 l with 
				       | Success(liste) -> matching_inTm y1 y2 liste 
				       | Failed -> Failed 
			       end
  | (DNil x1,DNil x2) -> matching_inTm x1 x2 l
  | (DCons(x1,y1),DCons(x2,y2)) -> begin match matching_inTm x1 x2 l with 
				       | Success(liste) -> matching_inTm y1 y2 liste 
				       | Failed -> Failed 
				 end
  | (Id(x1,y1,z1),Id(x2,y2,z2)) -> begin match matching_inTm x1 x2 l with 
				       | Success(liste) -> begin match matching_inTm y1 y2 liste with 
								 | Success(liste) -> matching_inTm z1 z2 liste
								 | Failed -> Failed
							   end 
				       | Failed -> Failed 
				 end 
  | (Refl,Refl) -> Success(l)
  | (Liste(a),Liste(b))-> matching_inTm a b l
  | (Nil,Nil) -> Success(l)
  | (Cons(y1,z1),Cons(y2,z2)) -> begin match matching_inTm y1 y2 l with 
		 		       | Success(liste) -> matching_inTm z1 z2 liste 
				       | Failed -> Failed 
				 end				  
  | _ -> Failed 
and matching_exTm p t l = 
  match (p,t) with 
(*  | (Label(x1,y1),Label(x2,y2)) -> if x1 = x2 then Success(l) else Failed (* on suppose que si deux noms de labels sont égaux ils ont nécésserement le meme type *) *)
  | (Ann(x1,y1),Ann(x2,y2)) -> begin match matching_inTm x1 x2 l with 
				       | Success(liste) -> matching_inTm y1 y2 liste 
				       | Failed -> Failed 
				 end
  | (Var(Global(x1)),Var(Global(x2))) -> if x1 = x2 then Success((x1,(Var(Global x2))) :: l) else Failed 
  | (Var(x1),Var(x2)) -> if x1 = x2 then Success(l) else Failed
  | (Appl(x1,y1),Appl(x2,y2)) -> begin match matching_exTm x1 x2 l with 
				       | Success(liste) -> matching_inTm y1 y2 liste 
				       | Failed -> Failed 
				 end
  | (Iter(w1,x1,y1,z1),Iter(w2,x2,y2,z2)) -> 
     begin match matching_inTm w1 w2 l with 
	   | Success(liste) -> 
	      begin match matching_inTm x1 x2 liste with 
		    | Success(liste) -> begin 
			match matching_inTm y1 y2 liste with 
			| Success(liste) -> matching_inTm z1 z2 liste 
			| Failed -> Failed 
		      end
		    | Failed -> Failed 
	      end
	   | Failed -> Failed 
     end
  | (Ifte(w1,x1,y1,z1),Ifte(w2,x2,y2,z2)) -> 
     begin match matching_inTm w1 w2 l with 
	   | Success(liste) -> 
	      begin match matching_inTm x1 x2 liste with 
		    | Success(liste) -> begin 
			match matching_inTm y1 y2 liste with 
			| Success(liste) -> matching_inTm z1 z2 liste 
			| Failed -> Failed 
		      end
		    | Failed -> Failed 
	      end
	   | Failed -> Failed 
     end
  | (P0(x1),P0(x2)) -> matching_exTm x1 x2 l 
  | (P1(x1),P1(x2)) -> matching_exTm x1 x2 l 
  | (DFold(w1,x1,y1,z1,f1,a1),DFold(w2,x2,y2,z2,f2,a2)) ->      
     begin match matching_inTm w1 w2 l with 
	   | Success(liste) -> 
	      begin match matching_inTm x1 x2 liste with 
		    | Success(liste) -> begin 
			match matching_inTm y1 y2 liste with 
			| Success(liste) -> begin 
			    match matching_inTm z1 z2 liste with 
			    | Success(liste) -> begin 
			      match matching_inTm f1 f2 liste with 
			      | Success(liste) -> matching_inTm a1 a2 liste
			      | Failed -> Failed 
			      end 
			    | Failed -> Failed 
			  end
			| Failed -> Failed 
		      end
		    | Failed -> Failed 
	      end
	   | Failed -> Failed 
     end
  | (Fold(w1,x1,y1,z1,f1),Fold(w2,x2,y2,z2,f2)) -> 
     begin match matching_inTm w1 w2 l with 
	   | Success(liste) -> 
	      begin match matching_inTm x1 x2 liste with 
		    | Success(liste) -> begin 
			match matching_inTm y1 y2 liste with 
			| Success(liste) -> begin 
			    match matching_inTm z1 z2 liste with 
			    | Success(liste) -> matching_inTm f1 f2 liste 
			    | Failed -> Failed 
			  end
			| Failed -> Failed 
		      end
		    | Failed -> Failed 
	      end
	   | Failed -> Failed 
     end
  | _ -> Failed

(* Printf are for debug *)
let rec match_pattern_goal_liste liste_goal p n = 
  match liste_goal with 
  | [] -> let () = Printf.printf "\n match_pattern_goal_liste Now the list is empty \n" in (n,Failed)
  | g :: suite -> let () = Printf.printf "\nDebug pattern_goal_liste goal: %s pattern: %s\n" (pretty_print_inTm g []) 
					 (pretty_print_inTm p []) in 
		  begin match matching_inTm p g [] with 
			| Success(liste) -> (n,Success(liste))
			| Failed -> match_pattern_goal_liste suite p (n + 1)
		  end
  

(* a partir d'une liste permet de remplacer les elements de l'utilisateur par les réels termes *)
let rec change_name_liste terme l = 
  match l with 
  | [] -> terme
  | (name,new_terme) :: suite -> let terme = replace_var_terme terme name new_terme  in 
			     change_name_liste terme suite
	   

(* permet de transformer une liste de patAct en terme *)
(* avant de faire les returnes il faut juste remplacer l'ensemble des variables libres du terme grace a la liste obtenue*)

       
    
  
  
(* let create_terme_with_pattern p = *)
  
(* let rec match_pattern liste_p liste_q = 
  failwith "lol"

let pattern_iter typ terme = 
 *)		  		 

  
  


(*let destination = read_def_pattern "(def plus (pi m N (pi n N N)) ((plus m n) (<= m 
		   (((plus 0 n) (-> n)) (zero (-> n))))))"
let () = Printf.printf "%s" (pretty_print_def destination) *)
