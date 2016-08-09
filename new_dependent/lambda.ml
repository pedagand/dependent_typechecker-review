open Sexplib


(* TODO :: faire dans le fichier de zipper une fonction permettant de retrouver le type d'un label *)
(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #require "sexplib";; 
  #require "oUnit";; 
  #use "lambda.ml";;
*)

type ident = string

type name =
  | Global of ident
  | Bound of int 
  | Quote of int
  | Hole of int


type 'a binder = ident * 'a

type inTm =
  | Abs of inTm binder 
  | Inv of exTm
  | Pi of (inTm * inTm) binder 
  | Star
  | Zero
  | Succ of inTm
  | Nat
  | Liste of inTm 
  | Nil
  | Cons of inTm * inTm 
  | Vec of inTm * inTm
  | DNil of inTm
  | DCons of inTm * inTm 
  | Id of inTm * inTm * inTm
  | Refl   
  | Bool
  | True 
  | False	
  | Pair of inTm * inTm 
  | Sig of (inTm * inTm) binder
and exTm = 
(*   | Label of ident * inTm * string *)
  | Ann of inTm * inTm 
  | Var of name 
  | Appl of exTm * inTm
  | Iter of inTm * inTm * inTm * inTm  
  | Transp of inTm * inTm * inTm * inTm * inTm * inTm 
  | P0 of exTm
  | P1 of exTm 
  | DFold of inTm * inTm * inTm * inTm * inTm * inTm 
  | Fold of inTm * inTm * inTm * inTm * inTm 
  | Ifte of inTm * inTm * inTm * inTm 
 



(* TODO :: faire du v_binder pour les VLam ect... *)
(* TODO :: vérifier que tous les termes ont une valeur et inversement *)
type value = 
  | VLam of (value -> value) binder
  | VNeutral of neutral 
  | VStar 
  | VPi of (value * (value -> value)) binder
  | VSig of (value * (value -> value)) binder
  | VPair of value * value
  | VNat
  | VZero
  | VSucc of value
  | VBool
  | VTrue
  | VFalse
  | VVec of value * value 
  | VDNil of value
  | VDCons of value * value 
  | VListe of value 
  | VNil
  | VCons of value * value 
  | VId of value * value * value 
  | VRefl
and neutral = 
(*  | NLabel of string * value *)
  | NFree of name 
  | NApp of neutral * value 
  | NIter of value * value * value * value
  | NIfte of value * value * value * value
  | NDFold of value * value * value * value * value * value 
  | NP0 of value
  | NP1 of value
  | NFold of value * value * value * value * value
  | NTransp of value * value * value * value * value * value  

(*=debug *) 
type debug = 
  | Report of debug * debug * debug * debug
  | Success of bool
  | Contexte of string
  | Steps of string
  | Error of string
and debug_synth = 
  | RetSynth of debug * value



(* fonction pour les rapports d'erreurs *) 
let create_report s c e er= 
  Report(Success(s),Contexte(c),Steps(e),Error(er))

let create_retSynth d v = 
  RetSynth(d,v)

let extract_context_report rep = 
  match rep with 
   | Report(Success(s),Contexte(c),Steps(e),Error(er)) -> c
   | _ -> failwith "Report don't have a good shape"

let print_report r = 
  match r with 
  | Report(Success(s),Contexte(c),Steps(e),Error(er)) -> 
     "Report : \n -Success : " ^ string_of_bool s ^ "\n" ^
       "-Contexte : " ^ c ^ "\n" ^
	 "-Steps : " ^ e ^ "\n" ^
	   "-Error : " ^ er ^ "\n" 
  | _ -> failwith "can't print something which is not a report" 

let print_report_synth r = 
  match r with 
  | RetSynth(Report(s,c,e,er),y) -> print_report (Report(s,c,e,er))
  | _ -> failwith "report synth don't have a good shape"

let res_debug d = 
  match d with 
  | Report(Success(s),Contexte(c),Steps(e),Error(er)) -> 
     s
  | _ -> failwith "report don't have the good Shape" 

let get_steps_report_synth r = 
  match r with 
  | RetSynth(Report(Success(s),c,Steps(e),er),y) -> e
  | _ -> failwith "get_steps_report : your report don't have a good shape" 

let get_steps_report r = 
  match r with 
  | Report(Success(s),Contexte(c),Steps(e),Error(er)) -> e
  | _ -> failwith "get_stepts_report : it has fail because you don't have a good shape" 
let res_debug_synth d = 
  match d with 
  | RetSynth(Report(Success(s),c,e,er),y) -> s
  | _ -> failwith "RetSynth don't have a good shape"


let ret_debug_synth d = 
  match d with 
  | RetSynth(Report(Success(s),c,e,er),y) -> y 
  | _ -> failwith "RetSynth don't have a good shape"

    
let rec parse_number entier = 
  match entier with 
  | 0 -> Zero
  | n -> Succ(parse_number (n - 1))


let rec parse_term env t = 
      match t with   
      | Sexp.Atom "*" -> Star
      | Sexp.Atom "zero" -> Zero
      | Sexp.Atom "N" -> Nat 
      | Sexp.Atom "B" -> Bool 
      | Sexp.Atom "true" -> True
      | Sexp.Atom "false" -> False
      | Sexp.Atom "nil" -> 
	 Nil
(*      | Sexp.List [Sexp.Atom"_"; Sexp.Atom num] ->
	 Hole_inTm (int_of_string num)	 *)
(*       | Sexp.List [Sexp.Atom "ref";Sexp.Atom name] -> 
	 Ref(name) *)
      | Sexp.List [Sexp.Atom "succ"; n] -> 
	 Succ(parse_term env n)
      | Sexp.List [Sexp.Atom "id";gA;a;b] -> 
	 Id((parse_term env gA),(parse_term env a),(parse_term env b))
      | Sexp.Atom "refl" -> Refl
(*      | Sexp.List [Sexp.Atom "<"; Sexp.Atom name; Sexp.Atom ":" ;typ ; Sexp.Atom ">"] -> 
         Label( *)
      | Sexp.List [Sexp.Atom "lambda"; Sexp.Atom var; body] -> 
         Abs(var,(parse_term (var::env) body))
(* 	 Abs(Global(var),(parse_term (Global(var)::env) body)) *)
      | Sexp.List [Sexp.Atom "lambda"; Sexp.List vars ; body] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser: Lambdainvalid variable") vars
	 in 
	 List.fold_right 
           (fun var b -> Abs(var,b))
           (List.map (fun x -> x) vars)
           (parse_term (List.append (List.rev ((List.map (fun x -> x) vars))) env) body)      
      | Sexp.List [Sexp.Atom "->"; s ; t ] -> 
	 Pi("NO",((parse_term env s),(parse_term ("NO" :: env) t)))
      | Sexp.List [Sexp.Atom "pi"; Sexp.Atom var ; s ; t] -> 
	 Pi(var,((parse_term env s),(parse_term (var::env) t)))        
      | Sexp.List [Sexp.Atom "pi";Sexp.List vars; s; t] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser pi invalide variable") vars 
	 in 
	 List.fold_right
	   (fun var b -> Pi(var,((parse_term (List.append (List.rev (List.map (fun x -> x) vars)) env) s),b)))
	   (List.map (fun x -> x) vars)
	   (parse_term (List.append (List.rev (List.map (fun x -> x) vars)) env) t)
      | Sexp.List [Sexp.Atom "sig"; Sexp.Atom var ;a;b] ->
	 Sig(var,((parse_term env a),(parse_term (var::env) b)))
      | Sexp.List [Sexp.Atom "sig"; Sexp.List vars;a;b] ->
	 let vars = List.map (function 
			       | Sexp.Atom v -> v 
			       | _ -> failwith "Parser sig invalide variable") vars
	 in 
	 List.fold_right 
	   (fun var b -> Sig(var,((parse_term (List.append (List.rev (List.map (fun x -> x) vars)) env) a),b)))
	   (List.map (fun x -> x) vars)
	   (parse_term (List.append (List.rev (List.map (fun x -> x) vars)) env ) t)
      | Sexp.List [a;Sexp.Atom ",";b] -> 
	 Pair((parse_term env a),(parse_term env b))
      | Sexp.List [Sexp.Atom "liste";alpha] -> 
	 Liste(parse_term env alpha)
      | Sexp.List [Sexp.Atom "cons"; a; xs] -> 
	 Cons((parse_term env a),(parse_term env xs))
      | Sexp.List [Sexp.Atom "vec";alpha; n] -> 
	 Vec((parse_term env alpha),(parse_term env n))
      | Sexp.List [Sexp.Atom "dnil";alpha] -> 
	 DNil(parse_term env alpha)
      | Sexp.List [Sexp.Atom "dcons";a;xs] -> 
	 DCons((parse_term env a),(parse_term env xs))
(* ----------------------termes librairie-------------------------------- *)
      | Sexp.List [Sexp.Atom "+";n;a] -> 
	 Inv(Appl(Appl(Ann((parse_term env (Sexp.of_string "(lambda n_plus (lambda a_plus (iter (lambda x_plus N) n_plus (lambda ni_plus (lambda x_plus (succ x_plus))) a_plus)))")),
			   parse_term env (Sexp.of_string "(-> N (-> N N))")),(parse_term env n)),(parse_term env a)))
      | Sexp.List [Sexp.Atom "mult";n;a] -> 
	 Inv(Appl(Appl(Ann((parse_term env (Sexp.of_string "(lambda n_plus (lambda a_plus (iter (lambda x_plus N) n_plus (lambda ni_plus (lambda x_plus (+ a_plus x_plus))) zero)))")),
			   parse_term env (Sexp.of_string "(-> N (-> N N))")),(parse_term env n)),(parse_term env a)))
      | Sexp.List [Sexp.Atom "pow";n;a] -> 
	 Inv(Appl(Appl(Ann((parse_term env (Sexp.of_string "(lambda n_plus (lambda a_plus (iter (lambda x_plus N) a_plus (lambda ni_plus (lambda x_plus (mult n_plus x_plus))) (succ zero))))")),
			   parse_term env (Sexp.of_string "(-> N (-> N N))")),(parse_term env n)),(parse_term env a)))
      | Sexp.List [Sexp.Atom "number";Sexp.Atom a] -> 
	 parse_number (int_of_string a)
      | _ -> Inv(parse_exTm env t)

and parse_exTm env t = 
  let rec lookup_var env n v
    = match env with
    | [] -> Var(Global v)
    | w :: env when v = w -> Var(Bound n)
    | _ :: env -> lookup_var env (n+1) v 
  in
  match t with 
(*  | Sexp.List [Sexp.Atom"_"; Sexp.Atom num] ->
     Hole_exTm (int_of_string num) *)
  | Sexp.List [Sexp.Atom "p0";x] ->
     P0(parse_exTm env x)
  | Sexp.List [Sexp.Atom "p1";x] ->
     P1(parse_exTm env x)
(*   | Sexp.List [Sexp.Atom reference] -> 
     Etiquette(reference)      *)
  | Sexp.List [Sexp.Atom "iter"; p ; n ; f ; z] ->
     Iter((parse_term env p),(parse_term env n),(parse_term env f),(parse_term env z))
  | Sexp.List [Sexp.Atom ":" ;x; t] -> 
     Ann((parse_term env x),(parse_term env t))
  | Sexp.List [Sexp.Atom "dfold";alpha;p;n;xs;f;a] -> 
     DFold((parse_term env alpha),(parse_term env p),(parse_term env n),(parse_term env xs),(parse_term env f),(parse_term env a))
  | Sexp.List [Sexp.Atom "trans"; gA;p;a;b;q;x] ->
     Transp((parse_term env gA),(parse_term env p),(parse_term env a),(parse_term env b),(parse_term env q),(parse_term env x))
  | Sexp.Atom v -> lookup_var env 0 v
  | Sexp.List [Sexp.Atom "ifte"; p;c;tHen;eLse] ->
     Ifte((parse_term env p),(parse_term env c),(parse_term env tHen),(parse_term env eLse))
  | Sexp.List [Sexp.Atom "fold";a_t;alpha;xs;f;a] -> 
     Fold((parse_term env a_t),(parse_term env alpha),(parse_term env xs),(parse_term env f),(parse_term env a))
  | Sexp.List (f::args) -> 
     List.fold_left 
       (fun x y -> Appl(x, y))
       (parse_exTm env f)
       (List.map (parse_term env) args)
  | _ -> failwith "erreur de parsing" 

let read t = parse_term [] (Sexp.of_string t)
let read_exTm t = parse_exTm [] (Sexp.of_string t)

(* prend en argument une liste de ref ainsi qu'un nom et retourne le terme associé au nom si celui ci existe *)
(*-----------LOLOLOL surement à changer quand le moment viendra---------------------*)
let rec def_is_in_the_liste_inTm (env : (name * inTm * inTm) list) name_to_find = 
  match env with 
  | [] -> failwith "def_is_in_the_liste : Dummy you call a ref wich is not present in the context ..... You can shut down your computer now" 
  | (name,typ,terme) :: suite -> 
     if name = name_to_find then terme else def_is_in_the_liste_inTm suite name_to_find
let rec def_is_in_the_liste_exTm env name_to_find = 
  match env with 
  | [] -> failwith "def_is_in_the_liste : You use a bad list" 
  | (name,typ,terme) :: suite -> 
     if name = name_to_find then Ann(terme,typ) else def_is_in_the_liste_exTm suite name_to_find


(* cette fonction retourne aussi les holes *)
let rec freevars_inTm terme l = 
  match terme with 
  | Inv x -> freevars_exTm x l
  | Abs(x,y) -> freevars_inTm y l 
  | Star -> l
  | Pi(v,(x,y)) -> freevars_inTm x l @ freevars_inTm y l
  (*=End *)
  | Sig(x,(a,b)) -> freevars_inTm a l @ freevars_inTm b l
  | Zero -> l
  | Succ n -> freevars_inTm n l
  | Nat -> l
  | Bool -> l
  | True -> l
  | False -> l
  | Pair(x,y) -> freevars_inTm x l @ freevars_inTm y l
  | Liste(alpha) -> freevars_inTm alpha l
  | Nil -> l
  | Cons(a,xs) -> freevars_inTm a l @ freevars_inTm xs l
  | Vec(alpha,n) -> freevars_inTm alpha l @ freevars_inTm n l
  | DNil(alpha) -> freevars_inTm alpha l
  | DCons(a,xs) -> freevars_inTm a l @ freevars_inTm a l
  | Id(gA,a,b) -> freevars_inTm gA l @ freevars_inTm a l @ freevars_inTm b l
  | Refl -> l
and freevars_exTm terme l = 
  match terme with 
(*   | Label(n,t) -> l *)
  | Var(Global x) -> (Global(x) :: l)
  | Var(Hole x) -> (Hole(x) :: l)
  | Var(x) -> l
  | Appl(x,y) -> freevars_exTm x l @ freevars_inTm y l
  | Ann(x,y) -> freevars_inTm x l @ freevars_inTm y l
  | Iter(p,n,f,a) -> freevars_inTm p l @ freevars_inTm n l @ freevars_inTm f l @ freevars_inTm a l
  | Ifte(p,c,tHen,eLse) -> freevars_inTm p l @ freevars_inTm c l @ freevars_inTm tHen l @ freevars_inTm eLse l
  | P0(x) -> freevars_exTm x l
  | P1(x) -> freevars_exTm x l
  | DFold(alpha,p,n,xs,f,a) -> freevars_inTm alpha l @ freevars_inTm p l @ freevars_inTm n l @
				 freevars_inTm xs l @ freevars_inTm f l @ freevars_inTm a l
  | Transp(gA,p,a,b,q,x) -> freevars_inTm gA l @ freevars_inTm p l @ freevars_inTm a l @ 
				 freevars_inTm b l @ freevars_inTm q l @ freevars_inTm x l
  | Fold(gA,alpha,xs,f,a) -> freevars_inTm gA l @ freevars_inTm alpha l @ freevars_inTm xs l @ 
				  freevars_inTm f l @ freevars_inTm a l



(* check_if_no_hole_inTm : ident liste -> inTm -> bool *)
let rec check_if_no_hole_inTm terme = 
  let l = freevars_inTm terme [] in 
  hole_in_liste l
and hole_in_liste l = 
  match l with 
  | [] -> true
  | Hole(x) :: suite -> false 
  | _ :: suite -> hole_in_liste suite
  

 
let rec pretty_print_inTm t l = 
  match t with 
  | Abs(str,x) -> "(lambda " ^ str ^ " " ^ pretty_print_inTm x (str :: l) ^ ")"
  | Inv (x) ->  pretty_print_exTm x l
  | Pi (str,(s,t)) -> "(pi " ^ str ^ " " ^ pretty_print_inTm s l ^ " " ^ pretty_print_inTm t (str :: l) ^ ")"
  | Sig(str,(a,b)) -> "(sig " ^ str ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm b (str :: l) ^ ")"
  | Star -> "*"
  | Succ n -> "(succ " ^ pretty_print_inTm n l ^ ")"
  | Zero -> "zero"
  | Nat -> "N" 
  | Bool -> "B"
  | True -> "true"
  | False -> "false"
  | Pair(a,b) -> "(" ^ pretty_print_inTm a l ^ " , " ^ pretty_print_inTm b l ^ ")"
  | Liste(alpha) -> "(liste " ^ pretty_print_inTm alpha l ^ ")"
  | Nil -> "nil"
  | Cons(a,xs) -> "(cons " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
  | Vec(alpha,n) -> "(vec " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm n l ^ ")"
  | DNil(alpha) -> "(dnil " ^ pretty_print_inTm alpha l ^ ")"
  | DCons(a,xs) -> "(dcons " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
  | Id(bA,a,b) -> "(id " ^ pretty_print_inTm bA l ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm b l ^ ")"
  | Refl -> "refl"
and pretty_print_exTm t l =
  match t with 
  | Ann(x,y) ->  "(: " ^ pretty_print_inTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | Var (Global x) -> x 
  | Var (Quote x) -> string_of_int x 
  | Var (Bound x) -> let rec print_liste_debug l =  match l with | [] -> "" | elem :: suite -> elem ^ ";" ^ print_liste_debug suite in
     begin
       try List.nth l x with 
       | Failure("nth") ->  failwith ("Pretty_print_exTm BVar: something goes wrong with var : \n "^ string_of_int x ^ "\n list : \n " ^ print_liste_debug l^ " \n is to short BVar de ") 
       | _ -> List.nth l x
     end
  | Var (Hole x) -> string_of_int x
  | Appl(x,y) -> "(" ^ pretty_print_exTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | Iter(p,n,f,z) -> "(iter " ^ pretty_print_inTm p l ^ " " ^ pretty_print_inTm n l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm z l ^ ")"
  | Ifte(p,c,tHen,eLse) -> "(ifte " ^ pretty_print_inTm p l ^ " " ^ pretty_print_inTm c l ^ " " ^ pretty_print_inTm tHen l ^ " " ^ pretty_print_inTm eLse l ^ ")"
  | P0(x) -> "(p0 " ^ pretty_print_exTm x l ^ ")"
  | P1(x) -> "(p1 " ^ pretty_print_exTm x l ^ ")"
  |  DFold(alpha,p,n,xs,f,a) -> "(dfold " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm p l ^ " " ^pretty_print_inTm n l ^ 
				 " " ^ pretty_print_inTm xs l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm a l ^ ")"
  | Transp(bA,p,a,b,q,x) -> "(trans " ^ pretty_print_inTm bA l ^ " " ^pretty_print_inTm p l ^ " " ^pretty_print_inTm a l ^ " " ^
			     pretty_print_inTm b l ^ " " ^pretty_print_inTm q l ^ " " ^pretty_print_inTm x l ^ ")"
  | Fold(bA,alpha,xs,f,a) -> "(fold " ^ pretty_print_inTm bA l ^ " " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm xs l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm a l ^ ")"

(* TODO :: a supprimer le plus vite possible *)
let pretty_print_inTm t l = 
 (*  let () = Printf.printf "\n enter pretty prin_inTm" in *)
  pretty_print_inTm t l

(* TODO :: faire une fonction qui appelle celle ci avec les bons paramètres CF tableau *)

let rec subst_inTm t tsub = 
(*   let () =  Printf.printf "\nSubst_inTm with t = %s\n and tsub = %s\n" (pretty_print_inTm t []) (pretty_print_exTm tsub []) in *)
  let ret = begin match t with 
  | Abs(name,terme) -> substitution_inTm terme tsub 0
  | Pi(name,(s,t)) -> substitution_inTm t tsub 0
  | Sig(name,(s,t)) -> substitution_inTm t tsub 0
  | _ -> failwith "subst_inTm : can't substituate if not an abstraction" end in 
(*   let () = Printf.printf "subst_inTm exit with t = %s \n" (pretty_print_inTm ret []) in  *)
  ret
and substitution_inTm t tsub var = 
  match t with 
  | Inv x -> Inv(substitution_exTm x tsub var)
  | Abs(x,y) -> Abs(x,(substitution_inTm y tsub (var+1)))
  | Star -> Star
  | Pi(v,(x,y)) -> Pi(v,((substitution_inTm x tsub var),(substitution_inTm y tsub (var+1))))
  | Sig(v,(x,y)) -> Sig(v,((substitution_inTm x tsub var),(substitution_inTm y tsub (var+1))))
  | Zero -> Zero 
  | Succ n -> Succ(substitution_inTm n tsub var)
  | Nat -> Nat
  | Bool -> Bool
  | True -> True 
  | False -> False 
  | Pair(x,y) -> Pair((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  | Liste(alpha) -> Liste(substitution_inTm alpha tsub var)
  | Nil -> Nil
  | Cons(a,xs) -> Cons((substitution_inTm a tsub var),(substitution_inTm xs tsub var))
  | Vec(alpha,n) -> Vec((substitution_inTm alpha tsub var),(substitution_inTm n tsub var))
  | DNil(alpha) -> DNil(substitution_inTm alpha tsub var)
  | DCons(a,xs) -> DCons((substitution_inTm a tsub var),(substitution_inTm a tsub var))
  | Id(gA,a,b) -> Id((substitution_inTm gA tsub var),(substitution_inTm a tsub var),(substitution_inTm b tsub var))
  | Refl -> Refl
(*=substitution_exTm *)
and substitution_exTm  t tsub var = 
  match t with 
  | Var(Bound n) -> if n = var then tsub else Var(Bound n)
  | Var(x)  -> Var(x)
(*  | Label (x,t) -> Label(x,substitution_inTm t tsub var) *)
  | Appl(x,y) -> Appl((substitution_exTm x tsub var),(substitution_inTm y tsub var))
  | Ann(x,y) -> Ann((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  (*=End *)
  | Iter(p,n,f,a) -> Iter((substitution_inTm p tsub var),(substitution_inTm n tsub var),(substitution_inTm f tsub var),(substitution_inTm a tsub var))
  | Ifte(p,c,tHen,eLse) -> Ifte((substitution_inTm p tsub var),(substitution_inTm c tsub var),(substitution_inTm tHen tsub var),(substitution_inTm eLse tsub var))
  | P0(x) -> P0(substitution_exTm x tsub var)
  | P1(x) -> P1(substitution_exTm x tsub var)
  | DFold(alpha,p,n,xs,f,a) -> DFold((substitution_inTm alpha tsub var),(substitution_inTm p tsub var),(substitution_inTm n tsub var),
				     (substitution_inTm xs tsub var),(substitution_inTm f tsub var),(substitution_inTm a tsub var))
  | Transp(gA,p,a,b,q,x) -> Transp((substitution_inTm gA tsub var),(substitution_inTm p tsub var),(substitution_inTm a tsub var),
				 (substitution_inTm b tsub var),(substitution_inTm q tsub var),(substitution_inTm x tsub var))
  | Fold(gA,alpha,xs,f,a) -> Fold((substitution_inTm gA tsub var),(substitution_inTm alpha tsub var),(substitution_inTm xs tsub var),(substitution_inTm f tsub var),
			    (substitution_inTm a tsub var))

(* Utilisation de la fonction, si on a un terme de la forme (lambda ....) et que l'on souhaite binder sur le lambda en cour il faut mettre 0 *)
(* cree une fonction  abstraction pour l'interface : ident -> inTm -> inTm binder *)
let rec abstract name terme = Abs(name,(bound_var_inTm terme 0 name))
and bound_var_inTm t i var = 
  match t with 
  | Inv x -> Inv(bound_var_exTm x i var)
  | Abs(x,y) -> Abs(x,(bound_var_inTm y (i + 1) var))
  | Star -> Star
  | Pi(v,(x,y)) -> Pi(v,((bound_var_inTm x i var),(bound_var_inTm y (i + 1) var)))
  | Sig(x,(a,b)) -> Sig(x,((bound_var_inTm a i var),(bound_var_inTm b (i + 1) var)))
  | Zero -> Zero 
  | Succ n -> Succ(bound_var_inTm n i var)
  | Nat -> Nat
  | Bool -> Bool
  | True -> True 
  | False -> False 
  | Pair(x,y) -> Pair((bound_var_inTm x i var),(bound_var_inTm y i var))
  | Liste(alpha) -> Liste(bound_var_inTm alpha i var)
  | Nil -> Nil
  | Cons(a,xs) -> Cons((bound_var_inTm a i var),(bound_var_inTm xs i var))
  | Vec(alpha,n) -> Vec((bound_var_inTm alpha i var),(bound_var_inTm n i var))
  | DNil(alpha) -> DNil(bound_var_inTm alpha i var)
  | DCons(a,xs) -> DCons((bound_var_inTm a i var),(bound_var_inTm a i var))
  | Id(gA,a,b) -> Id((bound_var_inTm gA i var),(bound_var_inTm a i var),(bound_var_inTm b i var))
  | Refl -> Refl
(*=replace_var_exTm *)
and bound_var_exTm  t i var = 
  match t with 
  | Var(Global x) -> begin if x = var then Var(Bound i) else Var(Global x) end 
  | Var(Hole(x)) -> begin if string_of_int x = var then Var(Bound i) else Var(Hole(x)) end 
  | Var(x) -> Var(x)
(*   | Label(name,term) -> Label(name,term) *)
  | Appl(x,y) -> Appl((bound_var_exTm x i var),(bound_var_inTm y i var))
  | Ann(x,y) -> Ann((bound_var_inTm x i var),(bound_var_inTm y i var))
  | Iter(p,n,f,a) -> Iter((bound_var_inTm p i var),(bound_var_inTm n i var),(bound_var_inTm f i var),(bound_var_inTm a i var))
  | Ifte(p,c,tHen,eLse) -> Ifte((bound_var_inTm p i var),(bound_var_inTm c i var),(bound_var_inTm tHen i var),(bound_var_inTm eLse i var))
  | P0(x) -> P0(bound_var_exTm x i var)
  | P1(x) -> P1(bound_var_exTm x i var)
  | DFold(alpha,p,n,xs,f,a) -> DFold((bound_var_inTm alpha i var),(bound_var_inTm p i var),(bound_var_inTm n i var),
				     (bound_var_inTm xs i var),(bound_var_inTm f i var),(bound_var_inTm a i var))
  | Transp(gA,p,a,b,q,x) -> Transp((bound_var_inTm gA i var),(bound_var_inTm p i var),(bound_var_inTm a i var),
				 (bound_var_inTm b i var),(bound_var_inTm q i var),(bound_var_inTm x i var))
  | Fold(gA,alpha,xs,f,a) -> Fold((bound_var_inTm gA i var),(bound_var_inTm alpha i var),(bound_var_inTm xs i var),(bound_var_inTm f i var),
 			    (bound_var_inTm a i var))


(* Petite macro permettant de changer le nom d'une variable libre *)
let change_name_var terme name new_name = 
  let terme = abstract name terme in 
  subst_inTm terme (Var(Global(new_name)))


let replace_var_terme terme name new_terme = 
  let terme = abstract name terme in 
  subst_inTm terme new_terme

(* prend en argument un truc du style un terme et une liste de def (string * inTm * inTm) et retourne le terme en ayant substituer les refs *)
let rec replace_liste_var terme def =
  match def with 
  | [] -> terme 
  | (name,typ,new_terme) :: suite -> replace_liste_var (replace_var_terme terme name (Ann(new_terme,typ))) suite 
          

let gen_hole =
  let c = ref 0 in
  fun () -> incr c; "_" ^ string_of_int !c  

let replace_hole terme trou new_terme = 
  let trou = string_of_int trou in
  let terme = abstract trou terme in 
  subst_inTm terme new_terme
 



let vfree n = VNeutral(NFree n)
  
let rec big_step_eval_inTm t envi = 
  match t with 
  | Inv(i) -> big_step_eval_exTm i envi
  | Abs(x,y) -> VLam(x,function arg -> (big_step_eval_inTm y (arg::envi)))
  | Star -> VStar
  | Pi (v,(x,y)) -> 
     VPi (v,((big_step_eval_inTm x envi),
	  (function arg -> (big_step_eval_inTm y (arg :: envi)))))
  | Sig (x,(a,b)) -> 
     VSig (x,((big_step_eval_inTm a envi),
	   (function arg -> (big_step_eval_inTm b (arg :: envi)))))
  | Nat -> VNat
  | Zero -> VZero
  | Succ(n) -> VSucc(big_step_eval_inTm n envi)
  | Bool -> VBool
  | True -> VTrue 
  | False -> VFalse 
  | Vec(alpha,n) -> VVec((big_step_eval_inTm alpha envi),(big_step_eval_inTm n envi))
  | DNil(alpha) -> VDNil(big_step_eval_inTm alpha envi)
  | DCons(a,xs) -> VDCons((big_step_eval_inTm a envi),(big_step_eval_inTm xs envi))
  | Id(gA,a,b) -> VId((big_step_eval_inTm gA envi),(big_step_eval_inTm a envi),(big_step_eval_inTm b envi))
  | Refl -> VRefl
  | Pair(x,y) -> VPair((big_step_eval_inTm x envi),(big_step_eval_inTm y envi))
  | Liste(a) -> VListe(big_step_eval_inTm a envi)
  | Nil -> VNil
  | Cons(xs,a) -> VCons((big_step_eval_inTm xs envi),(big_step_eval_inTm a envi))
and vapp v = 
  match v with 
  | ((VLam (x,f)),v) -> f v
  | ((VNeutral n),v) -> VNeutral(NApp(n,v))
  | _ -> failwith "must not append"   
(*=vitter *)
and vitter (p,n,f,a) =
  match n,f with
  | (VZero,VLam (name,fu)) -> a
  | (VSucc(x),VLam (name,fu)) -> vapp(fu x,(vitter (p,x,f,a)))
  | _ -> VNeutral(NIter(p,n,f,a))
(*=End *)
(*=vfold *) 
and vdfold(alpha,p,n,xs,f,a) = 
  match xs,f,n with
  | (VDNil(alphi),VLam (name,fu),VZero) -> a
  | (VDCons(elem,y),VLam (name,fu),VSucc(ni)) -> vapp(vapp(vapp(fu n,xs),elem),vdfold(alpha,p,ni,y,f,a))
  | _ -> VNeutral(NDFold(alpha,p,n,xs,f,a))
(*=End *)
and vifte(p,c,tHen,eLse) = 
  match c with 
  | VTrue -> tHen 
  | VFalse -> eLse 
  | _ -> VNeutral(NIfte(p,c,tHen,eLse))
and vfold(p,alpha,xs,f,a) = 
  match xs,f with 
  | (VNil,VLam (name,fu)) -> a 
  | (VCons(elem,suite),VLam (name,fu)) -> vapp(vapp((fu elem),suite),vfold(p,alpha,suite,f,a))
  | _ -> VNeutral(NFold(p,alpha,xs,f,a))
and big_step_eval_exTm t envi = 
  match t with
  | Ann(x,_) -> big_step_eval_inTm x envi 
  | Var(Bound v) -> List.nth envi v 
  | Var(v) -> vfree v 
  | Appl(x,y) -> vapp((big_step_eval_exTm x envi),(big_step_eval_inTm y envi))    
  | Iter(p,n,f,a) -> vitter ((big_step_eval_inTm p envi),
			     (big_step_eval_inTm n envi),
			     (big_step_eval_inTm f envi),
			     (big_step_eval_inTm a envi))
  | Ifte(p,c,tHen,eLse) -> vifte((big_step_eval_inTm p envi),
				 (big_step_eval_inTm c envi),
				 (big_step_eval_inTm tHen envi),
				 (big_step_eval_inTm eLse envi))
  | P0(p) -> let eval_p = big_step_eval_exTm p envi in
     begin 
       match eval_p with 
       | VPair(x,y) -> x
       | _ -> VNeutral(NP0(eval_p))
     end 
  | P1(p) -> let eval_p = big_step_eval_exTm p envi in
     begin 
       match eval_p with 
       | VPair(x,y) -> y
       | _ -> VNeutral(NP1(eval_p))
     end        
  | DFold(alpha,p,n,xs,f,a) -> vdfold((big_step_eval_inTm alpha envi),(big_step_eval_inTm p envi),
				      (big_step_eval_inTm n envi),(big_step_eval_inTm xs envi),
				      (big_step_eval_inTm f envi),(big_step_eval_inTm a envi))				      
  | Fold(p,alpha,xs,f,a) -> vfold((big_step_eval_inTm p envi),(big_step_eval_inTm alpha envi),(big_step_eval_inTm xs envi),
				(big_step_eval_inTm f envi),(big_step_eval_inTm a envi))
  | _ -> failwith "il manque trans" 

let boundfree i n = 
  match n with 
  | Quote k -> Var(Bound (i - k - 1))
  | x -> Var(x)

let gensym =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c


let rec value_to_inTm i v =
  match v with 
  | VLam (name,f) -> value_to_inTm (i+1) (f (vfree(Quote i)))
  | VNeutral n -> Inv(neutral_to_exTm i n)
  | VPi(var,(x,f)) -> 
		  Pi(var,
		     ((value_to_inTm i x),
		     (value_to_inTm (i+1) (f(vfree(Quote i))))))
  | VSig(var,(x,f)) -> 
		   Sig(var,
		       ((value_to_inTm i x),
		       (value_to_inTm (i+1) (f(vfree(Quote i))))))
  | VPair(x,y) -> Pair((value_to_inTm i x),(value_to_inTm i y))
  | VStar -> Star
  | VNat -> Nat
  | VZero -> Zero
  | VSucc(n) -> Succ(value_to_inTm i n)
  | VBool -> Bool 
  | VTrue -> True 
  | VFalse -> False 
  | VVec(alpha,n) -> Vec((value_to_inTm i alpha),(value_to_inTm i n))
  | VDNil(alpha) -> DNil(value_to_inTm i alpha)
  | VDCons(a,xs) -> DCons((value_to_inTm i a),(value_to_inTm i xs)) 
  | VId(gA,a,b) -> Id((value_to_inTm i gA),(value_to_inTm i a),(value_to_inTm i b))
  | VRefl -> Refl
  | VListe(a) -> Liste(value_to_inTm i a)
  | VNil -> Nil
  | VCons(a,xs) -> Cons((value_to_inTm i a),(value_to_inTm i xs)) 
and neutral_to_exTm i v = 
  match v with 
  | NFree x -> boundfree i x
  | NApp(n,x) -> Appl((neutral_to_exTm i n),(value_to_inTm i x))
  | NDFold(alpha,p,n,xs,f,a) -> DFold((value_to_inTm i alpha),(value_to_inTm i p),(value_to_inTm i n),
				      (value_to_inTm i xs),(value_to_inTm i f),(value_to_inTm i a))
  | NIter(p,n,f,a) -> Iter((value_to_inTm i p),(value_to_inTm i n),(value_to_inTm i f),(value_to_inTm i a))
  | NIfte(p,c,tHen,eLse) -> Ifte((value_to_inTm i p),(value_to_inTm i c),(value_to_inTm i tHen),(value_to_inTm i eLse))
  | NTransp(gA,p,a,b,q,x) -> Transp((value_to_inTm i gA),(value_to_inTm i p),(value_to_inTm i a),
				  (value_to_inTm i b),(value_to_inTm i q),(value_to_inTm i x))
  (* ça me plait pas du tout mais je suis un peu dans le flou la, cette annotation qui ne sert a rien *)
  | NP0(x) -> P0(Ann((value_to_inTm i x),Star))
(*   | NLabel(x,t)-> Label(x,value_to_inTm i t) *)
  | NP1(x) -> P1(Ann((value_to_inTm i x),Star))
  | NFold(p,alpha,xs,f,a) -> Fold((value_to_inTm i p),(value_to_inTm i alpha),(value_to_inTm i xs),(value_to_inTm i f),(value_to_inTm i a))



(* TODO :: faire une petite fonction qui normalise d'abord avant d'appel cette fonction *)
let rec equal t1 t2 =  
  let eval_t1 = value_to_inTm 0 (big_step_eval_inTm t1 []) in 
  let eval_t2 = value_to_inTm 0 (big_step_eval_inTm t2 []) in 
  equal_inTm eval_t1 eval_t2
and equal_inTm t1 t2 = 
  match (t1,t2) with 
  | (Abs(_,x1),Abs(_,x2)) -> equal_inTm x1 x2
  | (Pi(_,(x1,y1)),Pi(_,(x2,y2))) ->  equal_inTm x1 x2 && equal_inTm y1 y2 
  | (Sig(_,(x1,y1)),Sig(_,(x2,y2))) -> equal_inTm x1 x2 && equal_inTm y1 y2 
  | (Star,Star) -> true 
  | (Zero,Zero) -> true 
  | (Succ(n1),Succ(n2)) -> equal_inTm n1 n2
  | (Nat,Nat) -> true
  | (Bool,Bool) -> true 
  | (True,True) -> true 
  | (False,False) -> true 
  | (Inv(x1),Inv(x2)) -> equal_exTm x1 x2
  | (Pair(x1,y1),Pair(x2,y2)) -> equal_inTm x1 x2 && equal_inTm y1 y2 
  | (Vec(x1,y1),Vec(x2,y2)) -> equal_inTm x1 x2 && equal_inTm y1 y2
  | (DNil x1,DNil x2) -> equal_inTm x1 x2 
  | (DCons(x1,y1),DCons(x2,y2)) ->  equal_inTm x1 x2 && equal_inTm y1 y2 
  | (Id(x1,y1,z1),Id(x2,y2,z2)) -> equal_inTm x1 x2 && equal_inTm y1 y2 && equal_inTm z1 z2
  | (Refl,Refl) -> true 
  | (Liste(a),Liste(b))-> equal_inTm a b
  | (Nil,Nil) -> true
  | (Cons(y1,z1),Cons(y2,z2)) -> equal_inTm y1 y2 && equal_inTm z1 z2				  
  | _ -> false 
and equal_exTm t1 t2 = 
  match (t1,t2) with 
  | (Ann(x1,y1),Ann(x2,y2)) ->  equal_inTm x1 x2 && equal_inTm y1 y2 
  | (Var(x1),Var(x2)) -> x1 = x2 (* j'ai tout tester avec ocaml ça marche niquel l'égalité pour ce truc la *)
  | (Appl(x1,y1),Appl(x2,y2)) -> equal_exTm x1 x2 && equal_inTm y1 y2 
  | (Iter(w1,x1,y1,z1),Iter(w2,x2,y2,z2)) -> 
     equal_inTm w1 w2 && equal_inTm x1 x2 && equal_inTm y1 y2 && equal_inTm z1 z2 
  | (Ifte(w1,x1,y1,z1),Ifte(w2,x2,y2,z2)) -> 
     equal_inTm w1 w2 && equal_inTm x1 x2 && equal_inTm y1 y2 && equal_inTm z1 z2 
  | (P0(x1),P0(x2)) -> equal_exTm x1 x2
  | (P1(x1),P1(x2)) -> equal_exTm x1 x2
  | (DFold(alpha1,p1,n1,xs1,f1,a1),DFold(alpha2,p2,n2,xs2,f2,a2)) -> equal_inTm alpha1 alpha2 && equal_inTm p1 p2 
								     && equal_inTm p1 p2 && equal_inTm n1 n2 
								     && equal_inTm xs1 xs2 && equal_inTm f1 f2 
								     && equal_inTm a1 a2 
  | (Fold(p1,alpha1,xs1,f1,a1),Fold(p2,alpha2,xs2,f2,a2)) -> 
     equal_inTm p1 p2 && equal_inTm alpha1 alpha2 && equal_inTm xs1 xs2 && 
       equal_inTm f1 f2 && equal_inTm a1 a2  
  | _ -> false							 


let rec check_if_no_elem_inTm l terme = (* TODO :: faire cette fonction mais avec une liste de var *)
  match l with 
  | [] -> true
  | elem :: suite -> if equal elem terme then false else check_if_no_elem_inTm suite terme

 
let rec contexte_to_string contexte = 
  match contexte with 
  | [] -> "|" 	    
  | (Global s,w) :: tail -> "(" ^ s ^ "," ^ pretty_print_inTm (value_to_inTm 0 w) [] ^ ");" ^ contexte_to_string tail  
  | _ -> failwith "Must not append"




     (* TODO :: faire une fonction de type check qui prend deux termes et retourne un booléens *)
(* let check *)

let rec check inT ty = 
  let ty = big_step_eval_inTm ty [] in 
  res_debug (check_inTm [] inT ty "")
and check_inTm contexte inT ty steps = 
  match inT with
  | Abs(x,y) -> 
     begin  
       match ty with 
       | VPi(name,(s,t)) -> let freshVar = gensym () in 
		     check_inTm (((Global freshVar),s)::contexte) (substitution_inTm y (Var(Global(freshVar))) 0) (t (vfree (Global freshVar))) (pretty_print_inTm inT [] ^ ";"^ steps) 
       | _ -> create_report false (contexte_to_string contexte) steps "Abs type must be a Pi"
     end 
  | Inv(x) -> 
     let ret = synth contexte x steps in (* LOL *)
     if res_debug_synth ret
     then 
       begin 
	 if equal_inTm (value_to_inTm 0 (ty)) (value_to_inTm 0 (ret_debug_synth ret)) (* elle est ici l'erreur il faut que je 
test le retour de la synthèse *) 
	 then create_report true (contexte_to_string contexte) (get_steps_report_synth ret) "NO"
	 else create_report false (contexte_to_string contexte) (get_steps_report_synth ret) "Inv: ret and ty are not equal"
       end
     else create_report false (contexte_to_string contexte) steps ("Inv: Synth of x goes wrong \n ----Rapport du Inv---\n" ^ print_report_synth ret ^ "\n------Fin Rapport Inv---\n")
  | Star -> 
     begin 
      match ty with 
	| VStar -> create_report true (contexte_to_string contexte) steps "No"
	| _ -> create_report false (contexte_to_string contexte) steps "Star : ty must be of type Star"
     end
  | Pi (v,(s,t)) -> 
     begin 
       match ty with 
       | VStar -> let freshVar = gensym () in 
		  let check_inTm_s = check_inTm contexte s VStar steps in 
		  if res_debug(check_inTm_s)
		  then check_inTm (((Global freshVar),(big_step_eval_inTm s []))::contexte) (substitution_inTm t (Var(Global(freshVar))) 0) VStar steps
		  else create_report false (contexte_to_string contexte) steps "Pi : S is not of type Star"
       | _ -> create_report false (contexte_to_string contexte) steps "Pi : ty must be of type Star"
     end 
  |Sig(v,(s,t)) -> 
    begin 
      match ty with 
      | VStar -> let freshVar = gensym () in 
		 if res_debug(check_inTm contexte s VStar steps)
		 then check_inTm (((Global freshVar),(big_step_eval_inTm s []))::contexte) (substitution_inTm t (Var(Global(freshVar))) 0) VStar steps
		 else create_report false (contexte_to_string contexte) steps "Sig : A is not of type Star"
      | _ -> create_report false (contexte_to_string contexte) steps "Sig : ty must be of type Star"
    end 
  | Nat -> 
     begin 
       match ty with
       | VStar -> create_report true (contexte_to_string contexte) steps "No"
       | _ -> create_report false (contexte_to_string contexte) steps "Nat : ty must be VStar"
     end 
  | Zero -> 
     begin 
       match ty with 
       | VNat -> create_report true (contexte_to_string contexte) steps "No"
       | _ -> create_report false (contexte_to_string contexte) steps "Zero : ty must be VNat"
     end
  | Succ(x) -> 
     begin 
       match ty with 
	 | VNat -> check_inTm contexte x VNat (pretty_print_inTm inT [] ^ ";"^ steps)
	 | _ -> create_report false (contexte_to_string contexte) steps "Succ : ty must be VNat"
     end 
  | Bool -> 
     begin 
       match ty with 
       | VStar -> create_report true (contexte_to_string contexte) steps "No"
       | _ -> create_report false (contexte_to_string contexte) steps "Bool: ty must VStar"
     end 
  | True -> 
     begin 
       match ty with 
       | VBool -> create_report true (contexte_to_string contexte) steps "No"
       | _ -> create_report false (contexte_to_string contexte) steps "True: ty must VBool"
     end 
  | False -> 
     begin 
       match ty with 
       | VBool -> create_report true (contexte_to_string contexte) steps "No"
       | _ -> create_report false (contexte_to_string contexte) steps "False: ty must VBool"
     end 
  | Pair(x,y) -> 
     begin
       match ty with 
       | VSig(n,(a,b)) -> 
	  let check_inTm_x = check_inTm contexte x a steps in
	  let check_inTm_y = check_inTm (*pas sur a 100% de ne rien mettre dans le contexte ici à réfléchir*)
			  contexte y (b (big_step_eval_inTm x [])) steps in 
	  if res_debug(check_inTm_x) 
	  then
	    begin 
	      if res_debug(check_inTm_y) 
	      then create_report true (contexte_to_string contexte) steps "No"
	      else create_report false (contexte_to_string contexte) steps "Pair: element y of the pair as the wrong type"
	    end 
	  else create_report false (contexte_to_string contexte) steps "Pair: element x of the pair as the wrong type"
	  
       | _ -> create_report false (contexte_to_string contexte) steps "Pair: ty must VSig"
     end 
  | Vec(alpha,n) -> 
     begin        
       match ty with 
       | VStar -> let check_inTm_alpha = check_inTm contexte alpha VStar steps in
		  if res_debug(check_inTm_alpha) 
		  then check_inTm contexte n VNat steps
		  else create_report false (contexte_to_string contexte) steps "Vec : alpha must be of type star"
       | _ -> create_report false (contexte_to_string contexte) steps "Vec : ty must be VStar" 
     end
  | DNil(alpha) -> 
     begin
       match ty with
       | VVec(alpha_vec,VZero) -> if equal_inTm (value_to_inTm 0 (big_step_eval_inTm alpha [])) 
					       (value_to_inTm 0 alpha_vec)
				then create_report true (contexte_to_string contexte) steps "NO"
				else create_report false (contexte_to_string contexte) steps "DNil : Alpha must be the sames"
       | _ -> create_report false (contexte_to_string contexte) steps "Vec : ty must be a VVec"       
     end 
  | DCons(a,xs) -> 
     begin 
       match ty with 
       | VVec(alpha,VSucc(n)) -> let check_inTm_xs = check_inTm contexte xs (VVec(alpha,n)) steps in 
				 if res_debug(check_inTm_xs)
				 then check_inTm contexte a alpha steps
				 else create_report false (contexte_to_string contexte) steps "DCons : xs must be of type (VVec alpha n)"
       | _ -> create_report false (contexte_to_string contexte) steps "DCons : ty must be a VVec"
     end
  | Id(gA,a,b) -> let check_inTm_gA = check_inTm contexte gA VStar steps in 		  
		  let eval_gA = big_step_eval_inTm gA [] in 
		  let check_inTm_a = check_inTm contexte a eval_gA steps in 
		  let check_inTm_b = check_inTm contexte b eval_gA steps in 
		  if res_debug(check_inTm_gA) 
		  then 
		    begin 
		      if res_debug(check_inTm_a) 
		      then 
			begin 
			  if res_debug(check_inTm_b) 
			  then create_report true (contexte_to_string contexte) steps "NO"
			  else create_report false (contexte_to_string contexte) steps "Id : b must be of type gA"
			end 
		      else create_report false (contexte_to_string contexte) steps "Id : a must be of type gA"
		    end  
		  else create_report false (contexte_to_string contexte) steps "Id : gA must be of type Star"
  | Refl -> 
     begin
       match ty with 
       | VId(gA,ta,ba) -> create_report true (contexte_to_string contexte) steps "NO"	       
       | _ -> create_report false (contexte_to_string contexte) steps "refl : ty must be of type Id"
     end
  | Liste(alpha) -> 
     begin 
       match ty with 
       | VStar -> let check_inTm_alpha = check_inTm contexte alpha VStar steps in
		  if res_debug(check_inTm_alpha) 
		  then create_report true (contexte_to_string contexte) steps "NO"
		  else create_report false (contexte_to_string contexte) steps "Liste : alpha seems to not be of type Star"
       | _ -> create_report false (contexte_to_string contexte) steps "Liste : ty must be VStar" 
     end
  | Nil -> 
     begin 
       match ty with 
       | VListe(alpha_liste) -> create_report true (contexte_to_string contexte) steps "NO"   
       | _ -> create_report false (contexte_to_string contexte) steps "Nil : ty must be VListe"       
     end
  | Cons(a,xs) -> 
     begin 
       match ty with 
       | VListe(alpha_liste) -> let check_inTm_a = check_inTm contexte a alpha_liste steps in
				let check_inTm_xs = check_inTm contexte xs (VListe(alpha_liste)) steps in
				if res_debug(check_inTm_a) 
				then 
				  begin 
				    if res_debug(check_inTm_xs)
				    then create_report true (contexte_to_string contexte) steps "NO"
				    else create_report false (contexte_to_string contexte) steps "Cons : xs is not of type Liste(alpha)"
				  end
				else create_report false (contexte_to_string contexte) steps "Cons : a is not of type alpha"
       | _ -> create_report false (contexte_to_string contexte) steps "Cons : ty must be VListe(alpha)"
     end 
and synth contexte exT steps =
  match exT with 
  | Var(Bound x) -> 
     create_retSynth (create_report false (contexte_to_string contexte) steps "Var(Bound x) : not possible during type check_inTming") VStar
  | Var(Quote i) -> 
     create_retSynth (create_report false (contexte_to_string contexte) steps "Var(quote i) : not possible during type check_inTming") VStar
  | Var(x) -> create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (List.assoc x contexte)
(*   | Label(name,t) ->  
     create_retSynth (create_report true (contexte_to_string contexte) steps "syth : maybe you just couldn't do it") (big_step_eval_inTm t []) *)
  | P0(x) -> let synth_x = synth contexte x steps in 
	     if res_debug_synth synth_x
	     then
	       begin
		 match ret_debug_synth synth_x with 
		 | VSig(n,(a,b)) -> create_retSynth (create_report true (contexte_to_string contexte) steps "NO") a
		 | _ -> create_retSynth (create_report false (contexte_to_string contexte) steps "P0 : has to be applied to a pair") VStar
	       end 
	     else create_retSynth (create_report false (contexte_to_string contexte) steps "P0 : synth of elem don't work") VStar
  | P1(x) -> let synth_x = synth contexte x steps in 
	     if res_debug_synth synth_x
	     then
	       begin
		 match ret_debug_synth synth_x with 
		 | VSig(n,(a,b)) -> create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (b (big_step_eval_exTm (P0(x)) []))
		 | _ -> create_retSynth (create_report false (contexte_to_string contexte) steps "P0 : has to be applied to a pair") VStar
	       end 
	     else create_retSynth (create_report false (contexte_to_string contexte) steps "P0 : synth of elem don't work") VStar
  | Ann(x,t) -> let ret = check_inTm contexte t VStar (pretty_print_exTm exT [] ^ ";"^ steps) in 
		let eval_t = big_step_eval_inTm t [] in
		if res_debug(ret)
		then 
		  begin 
		    if res_debug(check_inTm contexte x eval_t (pretty_print_exTm exT [] ^ ";"))
		    then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") eval_t
		    else create_retSynth (create_report false (contexte_to_string contexte) steps "Ann : x is not of type t") VStar
		  end
		else create_retSynth (create_report false (contexte_to_string contexte) steps "Ann : t is not of type VStar") VStar
(*=End *)
(*=synth_app *) 
  | Appl(f,s) -> 
     let synth_f = synth contexte f steps in 
     if res_debug_synth synth_f 
     then
     begin
       match ret_debug_synth synth_f with 
       | VPi(name,(s_pi,fu)) -> if res_debug(check_inTm contexte s s_pi (pretty_print_exTm exT [] ^ ";"))
		     then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (fu (big_step_eval_inTm s [])) 
		     else create_retSynth (create_report false (contexte_to_string contexte) steps "Appl : s is not of type S") VStar
       | _ -> create_retSynth (create_report false (contexte_to_string contexte) steps "Appl : f is not of type Pi") VStar
     end
     else create_retSynth (create_report false (contexte_to_string contexte) steps "Appl : synth of f goes wrong") VStar
(*=End *) 
  | Iter(p,n,f,a) -> let big_p = big_step_eval_inTm p [] in
		     let big_n = big_step_eval_inTm n [] in 
		     let type_p = read "(pi x N *)" in 		     
 		     let check_inTm_p = check_inTm contexte p (big_step_eval_inTm type_p []) (pretty_print_exTm exT [] ^ ";") in    
		     let check_inTm_n = check_inTm contexte n (big_step_eval_inTm (read "N") []) (pretty_print_exTm exT [] ^ ";") in
		     let type_f = (Pi("n",(Nat,Pi("NO",((Inv(Appl(Ann(p,type_p),Inv(Var(Bound 0))))),(Inv(Appl(Ann(p,type_p),Succ(Inv(Var(Bound 1))))))))))) in 
		     let check_inTm_f = check_inTm contexte f (big_step_eval_inTm type_f [])  (pretty_print_exTm exT [] ^ ";") in
		     let check_inTm_a = check_inTm contexte a (vapp(big_p,VZero)) (pretty_print_exTm exT [] ^ ";") in
		     let steps_iter = "(<= " ^ pretty_print_inTm n []^ "((" ^ pretty_print_inTm type_f [] ^ ") (-> " ^ pretty_print_inTm f []
				     ^ ")(" ^ pretty_print_inTm (value_to_inTm 0 (vapp(big_p,VZero))) [] ^ ")(-> " 
				     ^ pretty_print_inTm a [] ^ ")))" in 
		     if res_debug(check_inTm_n)
		     then 
		       begin 
			 if res_debug(check_inTm_p)
			 then 
			   begin 
			     if res_debug(check_inTm_f)
			     then
			       begin 
				 if res_debug(check_inTm_a)
				 then create_retSynth (create_report true (contexte_to_string contexte) steps_iter "NO") (vapp(big_p,big_n)) 
				 else create_retSynth (create_report false (contexte_to_string contexte) steps "Iter : a is not of type (P 0)") VStar
			       end
			     else create_retSynth (create_report false (contexte_to_string contexte) steps "Iter : f is not of type (pi n N (-> (P n) (P (succ n))))") VStar
			   end 
			 else create_retSynth (create_report false (contexte_to_string contexte) steps "Iter : p is not of type (-> N *)") VStar
		       end 
		     else create_retSynth (create_report false (contexte_to_string contexte) steps "Iter : n is not of type VNat") VStar     
  | Ifte(p,c,tHen,eLse) -> 
     let big_p = big_step_eval_inTm p [] in
     let big_c = big_step_eval_inTm c [] in 
     let check_inTm_p = check_inTm contexte p (big_step_eval_inTm (read "(-> B *)") []) (pretty_print_exTm exT [] ^ ";") in    
     let check_inTm_c = check_inTm contexte c (big_step_eval_inTm (read "B") []) (pretty_print_exTm exT [] ^ ";") in
     let check_inTm_tHen = check_inTm contexte tHen (vapp(big_p,VTrue)) (pretty_print_exTm exT [] ^ ";") in
     let check_inTm_eLse = check_inTm contexte eLse (vapp(big_p,VFalse)) (pretty_print_exTm exT [] ^ ";") in
     if res_debug(check_inTm_p)
     then
       begin 
	 if res_debug(check_inTm_c)
	 then 
	   begin
	     if res_debug(check_inTm_tHen)
	     then 
	       begin 
		 if res_debug(check_inTm_eLse) 
		 then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (vapp(big_p,big_c)) 
		 else create_retSynth (create_report false (contexte_to_string contexte) steps "Ifte : eLse is not of type (P VFalse)") VStar
	       end 
	     else create_retSynth (create_report false (contexte_to_string contexte) steps "Ifte : tHen is not of type (P VTrue)") VStar     
	   end 
	 else create_retSynth (create_report false (contexte_to_string contexte) steps "Ifte : c is not of type VBool") VStar     
       end  
     else create_retSynth (create_report false (contexte_to_string contexte) steps "Ifte : p is not of type (-> B *)") VStar
     (* le check_inTm de f est nul parceque j'utilise pas les boundvar qui sont binde par les premier pi, A CHANGER *)
  | DFold(alpha,p,n,xs,f,a) -> let check_inTm_alpha = check_inTm contexte alpha VStar (pretty_print_exTm exT [] ^ ";") in
			       let type_p = (Pi("n",(Nat,(Pi("xs",(Vec(alpha,Inv(Var (Bound 0))),Star)))))) in 
			       let check_inTm_p = check_inTm contexte p (big_step_eval_inTm type_p []) (pretty_print_exTm exT [] ^ ";") in
			       let check_inTm_n = check_inTm contexte n VNat (pretty_print_exTm exT [] ^ ";") in			       
 			       let check_inTm_xs = check_inTm contexte xs (big_step_eval_inTm (Vec(alpha,n)) [])  (pretty_print_exTm exT [] ^ ";") in 
  			       let check_inTm_f = check_inTm contexte f 
						   (big_step_eval_inTm 
						      (Pi("n",(Nat,
							  Pi("xs",(Vec(alpha,Inv(Var(Bound 0))),
							     Pi("a",(alpha,
								Pi("NO",(Inv(Appl(Appl(Ann(p,type_p),n),xs)),
								   Inv(Appl(Appl(Ann(p,type_p),Succ(n)),DCons(a,xs)))))))))))) [])
						   (pretty_print_exTm exT [] ^ ";") in 
			       let check_inTm_a = check_inTm contexte a (big_step_eval_inTm (Inv(Appl(Appl(Ann(p,type_p),Zero),DNil(alpha)))) [])
						   (pretty_print_exTm exT [] ^ ";") in 
			       if res_debug check_inTm_alpha 
			       then 
				 begin 
				   if res_debug check_inTm_p
				   then 
				     begin 
				       if res_debug check_inTm_n 
				       then 
					 begin 
					   if res_debug check_inTm_xs 
					   then
					     begin 
					       if res_debug check_inTm_f 
					       then 
						 begin 
						   if res_debug check_inTm_a 
						   then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (big_step_eval_inTm (Inv(Appl(Appl(Ann(p,type_p),n),xs))) [])
						   else create_retSynth (create_report false (contexte_to_string contexte) steps "DFold a must be of type alpha") VStar
						 end 						   
					       else create_retSynth (create_report false (contexte_to_string contexte) steps "DFold f must be of type ...") VStar
					     end 
					   else create_retSynth (create_report false (contexte_to_string contexte) steps "DFold xs must be of type Vec alpha n") VStar
					 end
				       else create_retSynth (create_report false (contexte_to_string contexte) steps "DFold n not a Nat") VStar
				     end 
				   else create_retSynth (create_report false (contexte_to_string contexte) steps "DFold P must be of type") VStar
				 end 				   
			       else create_retSynth (create_report false (contexte_to_string contexte) steps "DFold alpha must be of type star") VStar 
			 
  | Transp(gA,p,a,b,q,x) -> let check_inTm_gA = check_inTm contexte gA VStar (pretty_print_exTm exT [] ^ ";") in
			   let check_inTm_a = check_inTm contexte a (big_step_eval_inTm gA []) (pretty_print_exTm exT [] ^ ";") in
			   let check_inTm_b = check_inTm contexte b (big_step_eval_inTm gA []) (pretty_print_exTm exT [] ^ ";") in
			   let check_inTm_q = check_inTm contexte q (big_step_eval_inTm (Id(gA,a,b)) [])(pretty_print_exTm exT [] ^ ";") in
			   let type_p = Pi("a",(gA,Pi("b",(gA,Pi("NO",(Id(gA,Inv(Var(Bound 1)),Inv(Var(Bound 0))),Star)))))) in 
			   let check_inTm_p = check_inTm contexte p (big_step_eval_inTm type_p []) (pretty_print_exTm exT [] ^ ";") in
			   let check_inTm_x = check_inTm contexte x (big_step_eval_inTm (Inv(Appl(Appl(Appl(Ann(p,type_p),a),b),q))) []) (pretty_print_exTm exT [] ^ ";") in
			   if res_debug check_inTm_gA 
			   then
			     begin 
			       if res_debug check_inTm_a 
			       then 
				 begin 
				   if res_debug check_inTm_b 
				   then 
				     begin 
				       if res_debug check_inTm_q 
				       then
					 begin 
					   if res_debug check_inTm_p
					   then 
					     begin 
					       if res_debug check_inTm_x
					       then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (big_step_eval_inTm (Inv(Appl(Appl(Appl(Ann(p,type_p),a),b),q))) [])
					       else create_retSynth (create_report false (contexte_to_string contexte) steps "Trans: x wrong type") VStar 
					     end 
					   else create_retSynth (create_report false (contexte_to_string contexte) steps "Trans: p wrong type") VStar 
					 end 
				       else create_retSynth (create_report false (contexte_to_string contexte) steps "Trans: q wrong type") VStar 
				     end 
				   else create_retSynth (create_report false (contexte_to_string contexte) steps "Trans: b must be of type gA") VStar 
				 end
			       else create_retSynth (create_report false (contexte_to_string contexte) steps "Trans: a must be of type gA") VStar 
			     end
			   else create_retSynth (create_report false (contexte_to_string contexte) steps "Trans: gA must be of type Star") VStar     			      
  | Fold(p,alpha,xs,f,a) -> 
     let check_inTm_alpha = check_inTm contexte alpha VStar (pretty_print_exTm exT [] ^ ";") in 
     let () = Printf.printf "Check_InTm alpha = %s \n" (string_of_bool(res_debug check_inTm_alpha)) in
     let type_p = Pi("xs",(Liste(alpha),Star)) in 
     let check_inTm_p = check_inTm contexte p (big_step_eval_inTm type_p []) (pretty_print_exTm exT [] ^ ";") in 
     let () = Printf.printf "Check_InTm p = %s \n" (string_of_bool(res_debug check_inTm_p)) in
     let check_inTm_xs = check_inTm contexte xs (big_step_eval_inTm (Liste(alpha)) []) (pretty_print_exTm exT [] ^ ";") in 
     let type_f = (Pi("a",(alpha,
		      Pi("xs",(Liste(alpha),			 
			 Pi("NO",(Inv(Appl(Ann(p,type_p),Liste(alpha))),
			    Inv(Appl(Ann(p,type_p),Cons(Inv(Var(Bound 2)),Inv(Var(Bound 1)))))))))))) in		    
     let check_inTm_f = check_inTm contexte f (big_step_eval_inTm (type_f) []) (pretty_print_exTm exT [] ^ ";") in 
     let () = Printf.printf "Check_InTm f = %s \n" (string_of_bool(res_debug check_inTm_f)) in
     let check_inTm_a = check_inTm contexte a (big_step_eval_inTm (Inv(Appl(Ann(p,type_p),Nil))) []) (pretty_print_exTm exT [] ^ ";") in 
     let () = Printf.printf "Check_InTm a = %s \n" (string_of_bool(res_debug check_inTm_a)) in
     if res_debug check_inTm_alpha 
     then
       begin 
	 if res_debug check_inTm_p
	 then
	   begin 
	     if res_debug check_inTm_xs 
	     then
	       begin
		 if res_debug check_inTm_f
		 then
		   begin 
		     if res_debug check_inTm_a 
		     then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (big_step_eval_inTm (Inv(Appl(Ann(p,type_p),xs))) [])
		     else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: a must be of type alpha") VStar
		   end
		 else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: f has the wrong type") VStar
	       end
	     else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: xs must be of type Liste(alpha)") VStar
	   end
	 else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: P has the wrong type") VStar
       end 
     else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: alpha must be of type Star") VStar

(* Fonction pour le debug qui permet de supprimer le surplut d'annotations *)

let rec remove_useless_anotation_inTm terme = 
  match terme with 
  | Abs(n,x) -> Abs(n,remove_useless_anotation_inTm x)
  | Pi(x,(y,z)) -> Pi(x,(remove_useless_anotation_inTm y, remove_useless_anotation_inTm z))
  | Inv(Ann(t,typ)) -> remove_useless_anotation_inTm t
  | Inv(x) -> Inv(remove_useless_anotation_exTm x)
  | Star -> Star
  | Zero -> Zero
  | Succ(x) -> Succ(remove_useless_anotation_inTm x)
  | Nat -> Nat 
  | Liste (x) -> Liste(remove_useless_anotation_inTm x)
  | Nil -> Nil 
  | Cons(x,y) -> Cons(remove_useless_anotation_inTm x,remove_useless_anotation_inTm y)
  | Vec(x,y) -> Vec(remove_useless_anotation_inTm x,remove_useless_anotation_inTm y)
  | DNil x -> DNil(remove_useless_anotation_inTm x)
  | DCons(x,y) -> DCons(remove_useless_anotation_inTm x, remove_useless_anotation_inTm y) 
  | Id(x,y,z) -> Id(remove_useless_anotation_inTm x, remove_useless_anotation_inTm y, remove_useless_anotation_inTm z)
  | Refl   -> Refl
  | Bool -> Bool
  | True -> True
  | False -> False
  | Pair(x,y) -> Pair(remove_useless_anotation_inTm x,remove_useless_anotation_inTm y)
  | Sig(x,(y,z)) -> Sig(x,(remove_useless_anotation_inTm y, remove_useless_anotation_inTm z))
and remove_useless_anotation_exTm terme = 
  match terme with 
  | Ann(x,y) -> Ann(remove_useless_anotation_inTm x,remove_useless_anotation_inTm y)
  | Var x -> Var x
  | Appl(x,y) -> Appl(remove_useless_anotation_exTm x,remove_useless_anotation_inTm y)
  | Iter(a,b,c,d) -> Iter(remove_useless_anotation_inTm a,remove_useless_anotation_inTm b,remove_useless_anotation_inTm c,remove_useless_anotation_inTm d)
  | Transp(a,b,c,d,e,f) -> Transp(remove_useless_anotation_inTm a,remove_useless_anotation_inTm b,remove_useless_anotation_inTm c,remove_useless_anotation_inTm d,remove_useless_anotation_inTm e,remove_useless_anotation_inTm f)
  | P0(x) -> P0(remove_useless_anotation_exTm x)
  | P1 x -> P1(remove_useless_anotation_exTm x)
  | DFold(a,b,c,d,e,f) -> DFold(remove_useless_anotation_inTm a,remove_useless_anotation_inTm b,remove_useless_anotation_inTm c,remove_useless_anotation_inTm d,remove_useless_anotation_inTm e,remove_useless_anotation_inTm f) 
  | Fold(a,b,c,d,e) -> Fold(remove_useless_anotation_inTm a,remove_useless_anotation_inTm b,remove_useless_anotation_inTm c,remove_useless_anotation_inTm d,remove_useless_anotation_inTm e)
  | Ifte(a,b,c,d) -> Ifte(remove_useless_anotation_inTm a,remove_useless_anotation_inTm b,remove_useless_anotation_inTm c,remove_useless_anotation_inTm d)
 



(* let () = Printf.printf "%s" (print_report (check_inTm [] (read "(lamba x x)") (big_step_eval_inTm (read "(-> * *)") []) "")) *)
