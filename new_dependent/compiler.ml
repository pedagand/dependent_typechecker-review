open Lambda 
open Sexplib
open Zipper
open Tactics

type pattern = 
  | Pattern of inTm 

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


let parse_type_definition str = 
  match str with 
  | Sexp.List [Sexp.Atom "def";def;Sexp.List[p;a]] -> 
     {def = Sexp.to_string def;patAct = (Pattern(parse_term [] p),parse_act a)}
  | _ -> failwith "parse_type_definition : your definition don't have a good shape"

     

  

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
let rec matching 


let rec pattern_match_to_terme arbre pattern_match = 
  let goal_terme = get_type_item arbre in
  match pattern_match with 
  | [] -> arbre 
  | () :: suite -> failwith "lol"


(* faire une fonction à coté qui permet de lire les fichiers *)
let userDef_to_terme d arbre =  
  let arbre = procedure_start_definition d.def arbre in 
  let arbre = intros arbre in 
  let arbre = pattern_match_to_terme arbre in 
  arbre
  
  
  
  
  
  
(* let create_terme_with_pattern p = *)
  
(* let rec match_pattern liste_p liste_q = 
  failwith "lol"

let pattern_iter typ terme = 
 *)		  		 

  
  


(*let destination = read_def_pattern "(def plus (pi m N (pi n N N)) ((plus m n) (<= m 
		   (((plus 0 n) (-> n)) (zero (-> n))))))"
let () = Printf.printf "%s" (pretty_print_def destination) *)
