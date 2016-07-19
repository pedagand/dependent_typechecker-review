open Zipper
open Tactics 
open Lambda 
open Sexplib


type pattern = 
  | Pattern of inTm 

type act = 
  | Return of inTm 
  | Split of string * ((pattern * act) list)


type userDefinition = 
  {
    id : string;
    typ : inTm;
    patAct : (pattern * act);
  }

   
let rec create_type listeTupleType return = 
  match listeTupleType with 
  | [] -> return
  | (name,typ) :: suite -> Pi(Global(name),typ,(create_type suite return))


(* lors du parse on va initialiser une structure de def *)

(*
let rec	parse_type_definition str env = 
  match str with 	    
  | Sexp.List 
    *)
(* permet de parser les actListes *)
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
     

  

let rec parse_def_pattern_match str =
  match str with 
  | Sexp.List [Sexp.Atom "def";Sexp.Atom id;typ; Sexp.List [p;a]] -> 
     let typ = parse_term [] typ in 
     let p = Pattern(parse_term [] p) in 
     let a = parse_act a in 
     let ret = {id = id;
		typ = typ; 
		patAct = (p,a);
	       } in ret
  | _ -> failwith "parse_def_pattern_match : your def don't have a good shape" 

let read_def_pattern t = parse_def_pattern_match (Sexp.of_string t)

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

let pretty_print_def userDef = 
  let id = userDef.id in 
  let typ = pretty_print_inTm userDef.typ []  in 
  let tuple_string = pretty_print_patact userDef.patAct in 	     
  let res = "(def " ^ id ^ " " ^ typ ^ " \n" ^ tuple_string ^ ")" in
  res



(* Fonctions manipulants une user_def afin de la transformer en terme *)
(* let userDef_to_terme d =  *)
  


let destination = read_def_pattern "(def plus (pi m N (pi n N N)) ((plus m n) (<= m 
		   (((plus 0 n) (-> n)) (zero (-> n))))))"
let () = Printf.printf "%s" (pretty_print_def destination)
