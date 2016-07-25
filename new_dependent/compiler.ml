open Lambda 
open Sexplib
open Zipper
(* open Tactics *)

type pattern = 
  | Pattern of inTm 

(* le inTm de ce résult est une substitution *)
type matching = 
  | Success of (string * inTm) list
  | Failed

type act = 
  | Return of inTm 
  | Split of string * ((pattern * act) list)


type userDefinition = 
  {
    def : string;
    patAct : (pattern * act);
  }

let set_def_userDef u d = 
  {def = d; patAct = u.patAct}
let set_patAct_userDef u p = 
  {def = u.def; patAct = p}
   
(* lors du parse on va initialiser une structure de def *)

let rec parse_act str = 
  match str with 
  | Sexp.List [Sexp.Atom "<="; Sexp.Atom id; Sexp.List patact_liste ] -> 
     let liste_folder = (List.fold_right (fun couple suite -> 
				   begin 
				     match couple with 
				     | Sexp.List[p;a] -> (Pattern(parse_term [] p),parse_act a) :: suite
				     | _ -> failwith "lol"
				   end )patact_liste [])  in 
     Split(id,liste_folder)
  | Sexp.List [Sexp.Atom "->";t] -> Return(parse_term [] t)
  | _ -> failwith "parse_act : your pattern don't have a good shape" 


let rec parse_type_definition str l = 
  match str with 
  | Sexp.List [Sexp.Atom "def";Sexp.List def;Sexp.List[p;a]] -> 
     {def = Sexp.to_string (Sexp.List def);patAct = (Pattern(parse_term [] p),parse_act a)} :: l
(*   | Sexp.List [elem] -> parse_type_definition elem l 
  | Sexp.List [Sexp.List elem; suite] -> 
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

let rec pretty_print_patact l = 
  match l with 
  | (Pattern(p),a) -> "(" ^ pretty_print_inTm p [] ^ " " ^ pretty_print_act a ^ ")"
and pretty_print_patactListe l = 
  match l with 
  | [] -> "" 
  | elem :: suite ->  pretty_print_patact elem ^ " \n"^ pretty_print_patactListe suite
and pretty_print_act userAct = 
  match userAct with 
  | Return(terme) -> "(-> " ^ pretty_print_inTm terme [] ^ ")" 
  | Split(name,l) -> "(<= " ^ name ^ " \n" ^ pretty_print_patactListe l ^ ")"

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
let rec matching_inTm p t l =
  match (p,t) with 
  | (Abs(_,x1),Abs(_,x2)) -> matching_inTm x1 x2 l
  | (Pi(_,x1,y1),Pi(_,x2,y2)) -> begin match matching_inTm x1 x2 l with
				       | Success(liste) -> matching_inTm y1 y2 liste 
				       | Failed -> Failed
				 end
  | (Sig(_,x1,y1),Sig(_,x2,y2)) -> begin match matching_inTm x1 x2 l with 
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
  | (What(a),What(b)) -> Success(l)
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
  | (Refl(a),Refl(b)) -> matching_inTm a b l
  | (Liste(a),Liste(b))-> matching_inTm a b l
  | (Nil(a),Nil(b)) -> matching_inTm a b l 
  | (Cons(y1,z1),Cons(y2,z2)) -> begin match matching_inTm y1 y2 l with 
				       | Success(liste) -> matching_inTm z1 z2 liste 
				       | Failed -> Failed 
				 end				  
  | _ -> Failed 
and matching_exTm p t l = 
  match (p,t) with 
  | (Ann(x1,y1),Ann(x2,y2)) -> begin match matching_inTm x1 x2 l with 
				       | Success(liste) -> matching_inTm y1 y2 liste 
				       | Failed -> Failed 
				 end
  | (BVar(x1),BVar(x2)) -> if x1 = x2 then Success(l) else Failed 
  | (FVar(Global(user_name)),FVar(Global(name))) -> Success((user_name,Inv(FVar(Global(name)))) :: l)
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

(* a partir d'une liste permet de remplacer les elements de l'utilisateur par les réels termes *)
let rec change_name_liste terme l = 
  match l with 
  | [] -> terme
  | (name,terme) :: suite -> let terme = change_name_FVar_inTm terme name in 
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
