open Sexplib


(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #require "sexplib";;
  #require "oUnit";;
  #use "lambda.ml";;
*)
(* Je n'ai pas encore fait ce qui suit mais il faut le faire c'est important : j'ai mis un neutral pour les projections je pense que c'est normale vu que si l'on tente de réduire une projection appliquée à une
variable il faut pouvoir la mettre en 'attente' *)

type name =
  | Global of string 
  | Bound of int 
  | Quote of int

(*=inTm_head *) 
type inTm =
  (*=End *)
  | Hole_inTm of int
  (*=inTm *)
  | Abs of name * inTm
  | Inv of exTm
  | Pi of name * inTm * inTm 
  | Star
(*=End *)
(*=terme_nat *)
  | Zero
  | Succ of inTm
  | Nat
(*=End *)
  | Pair of inTm * inTm 
  | Liste of inTm 
  | Nil of inTm 
  | Cons of inTm * inTm 
(*=terme_vector *)
  | Vec of inTm * inTm
  | DNil of inTm
  | DCons of inTm * inTm 
  (*=End *)
  (*=what *)      
  | What of string
  (*=End *)
  | Id of inTm * inTm * inTm
  | Refl (* TODO: remove *) of inTm 
(*=exTm_head *) 
(*=terme_bool *)				 
  | Bool
  | True 
  | False	
(*=End *)
  | Sig of name * inTm * inTm 		 
and exTm = 
(*=End *)
  | Hole_exTm of int 
(*=exTm *) 
  | Ann of inTm * inTm 
  | BVar of int 
  | FVar of name 
  | Appl of exTm * inTm
(*=End *)
(*=terme_iter *)
  | Iter of inTm * inTm * inTm * inTm  
(*=End *)
  | Trans of inTm * inTm * inTm * inTm * inTm * inTm 
  | P0 of exTm
  | P1 of exTm 
(*=terme_dfold *)
  | DFold of inTm * inTm * inTm * inTm * inTm * inTm 
(*=End *)
  | Fold of inTm * inTm * inTm * inTm * inTm 
(*=terme_ifte *)
  | Ifte of inTm * inTm * inTm * inTm 
(*=End *)
 
(*=value_head *)
type value = 
(*=End *)
  | VLam of (value -> value)
  | VNeutral of neutral 
(*=value_pi_star *)
  | VStar 
  | VPi of value * (value -> value)
  | VSig of value * (value -> value)
  | VPair of value * value
(*=End *)
(*=Value_Nat *)
  | VNat
  | VZero
  | VSucc of value
(*=End*)
(*=Value_Bool *)
  | VBool
  | VTrue
  | VFalse
(*=End*)
(*=Value_Vector *)
  | VVec of value * value 
  | VDNil of value
  | VDCons of value * value 
(*=End *)
(*=Value_liste *)
  | VListe of value 
  | VNil of value 
  | VCons of value * value 
(*=End *)
  | VId of value * value * value 
  | VRefl of value 
and neutral = 
  | NFree of name 
  | NApp of neutral * value 
  | NIter of value * value * value * value
  | NIfte of value * value * value * value
(*=neutral_fold *)
  | NDFold of value * value * value * value * value * value 
  | NP0 of value
  | NP1 of value
  | NFold of value * value * value * value * value
(*=End *)
  | NTrans of value * value * value * value * value * value  

(*=debug *) 
type debug = 
  | Report of debug * debug * debug * debug
  | Success of bool
  | Contexte of string
  | Steps of string
  | Error of string
and debug_synth = 
  | RetSynth of debug * value
(*=End *)
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
      | Sexp.List [Sexp.Atom"_"; Sexp.Atom num] ->
	 Hole_inTm (int_of_string num)	 
      | Sexp.List [Sexp.Atom "?";Sexp.Atom a] -> What a
      | Sexp.List [Sexp.Atom "succ"; n] -> 
	 Succ(parse_term env n)
      | Sexp.List [Sexp.Atom "id";gA;a;b] -> 
	 Id((parse_term env gA),(parse_term env a),(parse_term env b))
      | Sexp.List[Sexp.Atom "refl";a] -> 
	 Refl(parse_term env a)
      | Sexp.List [Sexp.Atom "lambda"; Sexp.Atom var; body] -> 
	 Abs(Global(var),(parse_term (Global(var)::env) body))
      | Sexp.List [Sexp.Atom "lambda"; Sexp.List vars ; body] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser: Lambdainvalid variable") vars
	 in 
	 List.fold_right 
           (fun var b -> Abs(var,b))
           (List.map (fun x -> Global(x)) vars)
           (parse_term (List.append (List.rev ((List.map (fun x -> Global(x)) vars))) env) body)      
      | Sexp.List [Sexp.Atom "->"; s ; t ] -> 
	 Pi(Global("NO"),(parse_term env s),(parse_term (Global("NO") :: env) t))
      | Sexp.List [Sexp.Atom "pi"; Sexp.Atom var ; s ; t] -> 
	 Pi(Global(var),(parse_term env s),(parse_term (Global(var)::env) t))        
      | Sexp.List [Sexp.Atom "pi";Sexp.List vars; s; t] -> 
	 let vars = List.map (function 
			       | Sexp.Atom v -> v
			       | _ -> failwith "Parser pi invalide variable") vars 
	 in 
	 List.fold_right
	   (fun var b -> Pi(var,(parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env) s),b))
	   (List.map (fun x -> Global(x)) vars)
	   (parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env) t)
      | Sexp.List [Sexp.Atom "sig"; Sexp.Atom var ;a;b] ->
	 Sig(Global(var),(parse_term env a),(parse_term (Global(var)::env) b))
      | Sexp.List [Sexp.Atom "sig"; Sexp.List vars;a;b] ->
	 let vars = List.map (function 
			       | Sexp.Atom v -> v 
			       | _ -> failwith "Parser sig invalide variable") vars
	 in 
	 List.fold_right 
	   (fun var b -> Sig(var,(parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env) a),b))
	   (List.map (fun x -> Global(x)) vars)
	   (parse_term (List.append (List.rev (List.map (fun x -> Global(x)) vars)) env ) t)
      | Sexp.List [a;Sexp.Atom ",";b] -> 
	 Pair((parse_term env a),(parse_term env b))
      | Sexp.List [Sexp.Atom "liste";alpha] -> 
	 Liste(parse_term env alpha)
      | Sexp.List [Sexp.Atom "nil";alpha] -> 
	 Nil(parse_term env alpha)
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
    | [] -> FVar v
    | w :: env when v = w -> BVar n
    | _ :: env -> lookup_var env (n+1) v 
  in
  match t with 
  | Sexp.List [Sexp.Atom"_"; Sexp.Atom num] ->
     Hole_exTm (int_of_string num)
  | Sexp.List [Sexp.Atom "p0";x] ->
     P0(parse_exTm env x)
  | Sexp.List [Sexp.Atom "p1";x] ->
     P1(parse_exTm env x)
  | Sexp.List [Sexp.Atom "iter"; p ; n ; f ; z] ->
     Iter((parse_term env p),(parse_term env n),(parse_term env f),(parse_term env z))
  | Sexp.List [Sexp.Atom ":" ;x; t] -> 
     Ann((parse_term env x),(parse_term env t))
  | Sexp.List [Sexp.Atom "dfold";alpha;p;n;xs;f;a] -> 
     DFold((parse_term env alpha),(parse_term env p),(parse_term env n),(parse_term env xs),(parse_term env f),(parse_term env a))
  | Sexp.List [Sexp.Atom "trans"; gA;p;a;b;q;x] ->
     Trans((parse_term env gA),(parse_term env p),(parse_term env a),(parse_term env b),(parse_term env q),(parse_term env x))
  | Sexp.Atom v -> lookup_var env 0 (Global(v))
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

(* Fonction de remplacement des holes dans les termes *)
let rec replace_hole_inTm terme tsub num = 
  match terme with 
  | Hole_inTm(x) -> if x = num then tsub else Hole_inTm(x)
  | Inv x -> Inv(replace_hole_exTm x tsub num)
  | Abs(x,y) -> Abs(x,(replace_hole_inTm y tsub (num)))
  | Star -> Star
  | Pi(v,x,y) -> Pi(v,(replace_hole_inTm x tsub num),(replace_hole_inTm y tsub (num)))
  (*=End *)
  | Sig(x,a,b) -> Sig(x,(replace_hole_inTm a tsub num),(replace_hole_inTm b tsub (num)))
  | Zero -> Zero 
  | Succ n -> Succ(replace_hole_inTm n tsub num)
  | Nat -> Nat
  | Bool -> Bool
  | True -> True 
  | False -> False 
  | Pair(x,y) -> Pair((replace_hole_inTm x tsub num),(replace_hole_inTm y tsub num))
  | Liste(alpha) -> Liste(replace_hole_inTm alpha tsub num)
  | Nil(alpha) -> Nil(replace_hole_inTm alpha tsub num)
  | Cons(a,xs) -> Cons((replace_hole_inTm a tsub num),(replace_hole_inTm xs tsub num))
  | Vec(alpha,n) -> Vec((replace_hole_inTm alpha tsub num),(replace_hole_inTm n tsub num))
  | DNil(alpha) -> DNil(replace_hole_inTm alpha tsub num)
  | DCons(a,xs) -> DCons((replace_hole_inTm a tsub num),(replace_hole_inTm a tsub num))
  | What(a) -> What(a)
  | Id(gA,a,b) -> Id((replace_hole_inTm gA tsub num),(replace_hole_inTm a tsub num),(replace_hole_inTm b tsub num))
  | Refl(a) -> Refl(replace_hole_inTm a tsub num)
(*=replace_hole_exTm *)
and replace_hole_exTm  terme tsub num = 
  match terme with 
    (* Attention c'est pas bon du tout de mettre cette annotation, c'est une solution temporaire *)
  | Hole_exTm(x) -> if x = num then Ann(tsub,Star) else Hole_exTm(x)
  | FVar x -> FVar x
  | BVar x -> BVar x
  | Appl(x,y) -> Appl((replace_hole_exTm x tsub num),(replace_hole_inTm y tsub num))
  | Ann(x,y) -> Ann((replace_hole_inTm x tsub num),(replace_hole_inTm y tsub num))
  (*=End *)
  | Iter(p,n,f,a) -> Iter((replace_hole_inTm p tsub num),(replace_hole_inTm n tsub num),(replace_hole_inTm f tsub num),(replace_hole_inTm a tsub num))
  | Ifte(p,c,tHen,eLse) -> Ifte((replace_hole_inTm p tsub num),(replace_hole_inTm c tsub num),(replace_hole_inTm tHen tsub num),(replace_hole_inTm eLse tsub num))
  | P0(x) -> P0(replace_hole_exTm x tsub num)
  | P1(x) -> P1(replace_hole_exTm x tsub num)
  | DFold(alpha,p,n,xs,f,a) -> DFold((replace_hole_inTm alpha tsub num),(replace_hole_inTm p tsub num),(replace_hole_inTm n tsub num),
				     (replace_hole_inTm xs tsub num),(replace_hole_inTm f tsub num),(replace_hole_inTm a tsub num))
  | Trans(gA,p,a,b,q,x) -> Trans((replace_hole_inTm gA tsub num),(replace_hole_inTm p tsub num),(replace_hole_inTm a tsub num),
				 (replace_hole_inTm b tsub num),(replace_hole_inTm q tsub num),(replace_hole_inTm x tsub num))
  | Fold(gA,alpha,xs,f,a) -> Fold((replace_hole_inTm gA tsub num),(replace_hole_inTm alpha tsub num),(replace_hole_inTm xs tsub num),(replace_hole_inTm f tsub num),
			    (replace_hole_inTm a tsub num))

(*Fonction pour vérifier si il n'y a plus de holes dans le terme, renvoie true si pas de trou *)
let rec check_if_no_hole_inTm terme = 
  match terme with 
  | Hole_inTm(x) -> false
  | Inv x -> check_if_no_hole_exTm x 
  | Abs(x,y) -> check_if_no_hole_inTm y 
  | Star -> true 
  | Pi(v,x,y) -> check_if_no_hole_inTm x && check_if_no_hole_inTm y 
  (*=End *)
  | Sig(x,a,b) -> check_if_no_hole_inTm a && check_if_no_hole_inTm b 
  | Zero -> true 
  | Succ n -> check_if_no_hole_inTm n 
  | Nat -> true
  | Bool -> true
  | True -> true 
  | False -> true
  | Pair(x,y) -> check_if_no_hole_inTm x && check_if_no_hole_inTm y 
  | Liste(alpha) -> check_if_no_hole_inTm alpha 
  | Nil(alpha) -> check_if_no_hole_inTm alpha 
  | Cons(a,xs) -> check_if_no_hole_inTm a && check_if_no_hole_inTm xs 
  | Vec(alpha,n) -> check_if_no_hole_inTm alpha && check_if_no_hole_inTm n 
  | DNil(alpha) -> check_if_no_hole_inTm alpha 
  | DCons(a,xs) -> check_if_no_hole_inTm a && check_if_no_hole_inTm a 
  | What(a) -> true 
  | Id(gA,a,b) -> check_if_no_hole_inTm gA && check_if_no_hole_inTm a && check_if_no_hole_inTm b 
  | Refl(a) -> check_if_no_hole_inTm a 
and check_if_no_hole_exTm terme = 
  match terme with 
  | Hole_exTm(x) -> false
  | FVar x -> true
  | BVar x -> true
  | Appl(x,y) -> check_if_no_hole_exTm x && check_if_no_hole_inTm y 
  | Ann(x,y) -> check_if_no_hole_inTm x && check_if_no_hole_inTm y 
  (*=End *)
  | Iter(p,n,f,a) -> check_if_no_hole_inTm p && check_if_no_hole_inTm n && check_if_no_hole_inTm f && check_if_no_hole_inTm a 
  | Ifte(p,c,tHen,eLse) -> check_if_no_hole_inTm p && check_if_no_hole_inTm c  && check_if_no_hole_inTm tHen && check_if_no_hole_inTm eLse 
  | P0(x) -> check_if_no_hole_exTm x 
  | P1(x) -> check_if_no_hole_exTm x 
  | DFold(alpha,p,n,xs,f,a) -> check_if_no_hole_inTm alpha && check_if_no_hole_inTm p && check_if_no_hole_inTm n &&
				 check_if_no_hole_inTm xs && check_if_no_hole_inTm f && check_if_no_hole_inTm a 
  | Trans(gA,p,a,b,q,x) -> check_if_no_hole_inTm gA && check_if_no_hole_inTm p && check_if_no_hole_inTm a && 
				 check_if_no_hole_inTm b && check_if_no_hole_inTm q && check_if_no_hole_inTm x 
  | Fold(gA,alpha,xs,f,a) -> check_if_no_hole_inTm gA && check_if_no_hole_inTm alpha && check_if_no_hole_inTm xs && 
				  check_if_no_hole_inTm f && check_if_no_hole_inTm a 
				 


 
let rec pretty_print_inTm t l = 
  match t with 
  | Hole_inTm(x) -> "(_ " ^ string_of_int x ^ ")"
  | Abs(Global(str),x) -> "(lambda " ^ str ^ " " ^ pretty_print_inTm x (str :: l) ^ ")"
  | Abs(_,x) -> failwith "Pretty print Abs first arg must be a global"
  | Inv (x) ->  pretty_print_exTm x l
  | Pi (Global(str),s,t) -> "(pi " ^ str ^ " " ^ pretty_print_inTm s l ^ " " ^ pretty_print_inTm t (str :: l) ^ ")"
  | Pi (_,s,t) -> failwith "Pretty print Pi first arg must be a global"
  | Sig(Global(str),a,b) -> "(sig " ^ str ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm b (str :: l) ^ ")"
  | Sig(_,a,b) -> failwith "Pretty print Sig first arg must be a global"
  | Star -> "*"
  | Succ n -> "(succ " ^ pretty_print_inTm n l ^ ")"
  | Zero -> "zero"
  | Nat -> "N" 
  | Bool -> "B"
  | True -> "true"
  | False -> "false"
  | Pair(a,b) -> "(" ^ pretty_print_inTm a l ^ " , " ^ pretty_print_inTm b l ^ ")"
  | Liste(alpha) -> "(liste " ^ pretty_print_inTm alpha l ^ ")"
  | Nil(alpha) -> "(nil " ^ pretty_print_inTm alpha l ^ ")"
  | Cons(a,xs) -> "(cons " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
  | Vec(alpha,n) -> "(vec " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm n l ^ ")"
  | DNil(alpha) -> "(dnil " ^ pretty_print_inTm alpha l ^ ")"
  | DCons(a,xs) -> "(dcons " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm xs l ^ ")"
  | What(s)-> "(? " ^ s ^ ")"
  | Id(bA,a,b) -> "(id " ^ pretty_print_inTm bA l ^ " " ^ pretty_print_inTm a l ^ " " ^ pretty_print_inTm b l ^ ")"
  | Refl(a) -> "(refl " ^ pretty_print_inTm a l ^ ")"
and pretty_print_exTm t l =
  match t with 
  | Hole_exTm(x) -> "(_ " ^ string_of_int x ^ ")"
  | Ann(x,y) ->  "(: " ^ pretty_print_inTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | BVar(x) -> begin 
      try List.nth l x with 
	| Failure("nth") ->  failwith ("Pretty_print_exTm BVar: something goes wrong list is to short BVar de " ^ string_of_int x) 
	| _ -> List.nth l x
    end
  | FVar (Global x) ->  x
  | FVar (Quote x) -> string_of_int x 
  | FVar (Bound x) -> string_of_int x
  | Appl(x,y) -> "(" ^ pretty_print_exTm x l ^ " " ^ pretty_print_inTm y l ^ ")"
  | Iter(p,n,f,z) -> "(iter " ^ pretty_print_inTm p l ^ " " ^ pretty_print_inTm n l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm z l ^ ")"
  | Ifte(p,c,tHen,eLse) -> "(ifte " ^ pretty_print_inTm p l ^ " " ^ pretty_print_inTm c l ^ " " ^ pretty_print_inTm tHen l ^ " " ^ pretty_print_inTm eLse l ^ ")"
  | P0(x) -> "(p0 " ^ pretty_print_exTm x l ^ ")"
  | P1(x) -> "(p1 " ^ pretty_print_exTm x l ^ ")"
  |  DFold(alpha,p,n,xs,f,a) -> "(dfold " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm p l ^ " " ^pretty_print_inTm n l ^ 
				 " " ^ pretty_print_inTm xs l ^ " " ^ pretty_print_inTm f l ^ " " ^ pretty_print_inTm a l ^ ")"
  | Trans(bA,p,a,b,q,x) -> "(trans " ^ pretty_print_inTm bA l ^ " " ^pretty_print_inTm p l ^ " " ^pretty_print_inTm a l ^ " " ^
			     pretty_print_inTm b l ^ " " ^pretty_print_inTm q l ^ " " ^pretty_print_inTm x l ^ ")"
  | Fold(bA,alpha,xs,f,a) -> "(fold " ^ pretty_print_inTm bA l ^ " " ^ pretty_print_inTm alpha l ^ " " ^ pretty_print_inTm xs l ^ "  " ^ pretty_print_inTm f l ^ " " ^
			 pretty_print_inTm a l ^ ")"
(*=substitution_inTm *)
let rec substitution_inTm t tsub var = 
  match t with 
  | Hole_inTm(x) -> Hole_inTm x
  | Inv x -> Inv(substitution_exTm x tsub var)
  | Abs(x,y) -> Abs(x,(substitution_inTm y tsub (var+1)))
  | Star -> Star
  | Pi(v,x,y) -> Pi(v,(substitution_inTm x tsub var),(substitution_inTm y tsub (var+1)))
  (*=End *)
  | Sig(x,a,b) -> Sig(x,(substitution_inTm a tsub var),(substitution_inTm b tsub (var+1)))
  | Zero -> Zero 
  | Succ n -> Succ(substitution_inTm n tsub var)
  | Nat -> Nat
  | Bool -> Bool
  | True -> True 
  | False -> False 
  | Pair(x,y) -> Pair((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  | Liste(alpha) -> Liste(substitution_inTm alpha tsub var)
  | Nil(alpha) -> Nil(substitution_inTm alpha tsub var)
  | Cons(a,xs) -> Cons((substitution_inTm a tsub var),(substitution_inTm xs tsub var))
  | Vec(alpha,n) -> Vec((substitution_inTm alpha tsub var),(substitution_inTm n tsub var))
  | DNil(alpha) -> DNil(substitution_inTm alpha tsub var)
  | DCons(a,xs) -> DCons((substitution_inTm a tsub var),(substitution_inTm a tsub var))
  | What(a) -> What(a)
  | Id(gA,a,b) -> Id((substitution_inTm gA tsub var),(substitution_inTm a tsub var),(substitution_inTm b tsub var))
  | Refl(a) -> Refl(substitution_inTm a tsub var)
(*=substitution_exTm *)
and substitution_exTm  t tsub var = 
  match t with 
  | Hole_exTm(x) -> Hole_exTm x
  | FVar x -> FVar x
  | BVar x when x = var -> tsub
  | BVar x -> BVar x
  | Appl(x,y) -> Appl((substitution_exTm x tsub var),(substitution_inTm y tsub var))
  | Ann(x,y) -> Ann((substitution_inTm x tsub var),(substitution_inTm y tsub var))
  (*=End *)
  | Iter(p,n,f,a) -> Iter((substitution_inTm p tsub var),(substitution_inTm n tsub var),(substitution_inTm f tsub var),(substitution_inTm a tsub var))
  | Ifte(p,c,tHen,eLse) -> Ifte((substitution_inTm p tsub var),(substitution_inTm c tsub var),(substitution_inTm tHen tsub var),(substitution_inTm eLse tsub var))
  | P0(x) -> P0(substitution_exTm x tsub var)
  | P1(x) -> P1(substitution_exTm x tsub var)
  | DFold(alpha,p,n,xs,f,a) -> DFold((substitution_inTm alpha tsub var),(substitution_inTm p tsub var),(substitution_inTm n tsub var),
				     (substitution_inTm xs tsub var),(substitution_inTm f tsub var),(substitution_inTm a tsub var))
  | Trans(gA,p,a,b,q,x) -> Trans((substitution_inTm gA tsub var),(substitution_inTm p tsub var),(substitution_inTm a tsub var),
				 (substitution_inTm b tsub var),(substitution_inTm q tsub var),(substitution_inTm x tsub var))
  | Fold(gA,alpha,xs,f,a) -> Fold((substitution_inTm gA tsub var),(substitution_inTm alpha tsub var),(substitution_inTm xs tsub var),(substitution_inTm f tsub var),
			    (substitution_inTm a tsub var))



let vfree n = VNeutral(NFree n)
  
(*=big_step_head *)
let rec big_step_eval_inTm t envi = 
(*=End *)
  match t with 
  | Hole_inTm x -> failwith "You can't eval a Hole" 
(*=big_step_inv *)
  | Inv(i) -> big_step_eval_exTm i envi
(*=End *)
  | Abs(x,y) -> VLam(function arg -> (big_step_eval_inTm y (arg::envi)))
(*=big_step_new *)
  | Star -> VStar
  | Pi (v,x,y) -> 
     VPi ((big_step_eval_inTm x envi),
	  (function arg -> (big_step_eval_inTm y (arg :: envi))))
(*=End *)
  | Sig (x,a,b) -> 
     VSig ((big_step_eval_inTm a envi),
	   (function arg -> (big_step_eval_inTm b (arg :: envi))))
(*=big_step_nat *) 
  | Nat -> VNat
  | Zero -> VZero
  | Succ(n) -> VSucc(big_step_eval_inTm n envi)
(*=End *)
(*=big_step_bool *) 
  | Bool -> VBool
  | True -> VTrue 
  | False -> VFalse 
(*=End *)
(*=big_step_vec *) 
  | Vec(alpha,n) -> VVec((big_step_eval_inTm alpha envi),(big_step_eval_inTm n envi))
  | DNil(alpha) -> VDNil(big_step_eval_inTm alpha envi)
  | DCons(a,xs) -> VDCons((big_step_eval_inTm a envi),(big_step_eval_inTm xs envi))
(*=End *)
  | Id(gA,a,b) -> VId((big_step_eval_inTm gA envi),(big_step_eval_inTm a envi),(big_step_eval_inTm b envi))
  | Refl(a) -> VRefl(big_step_eval_inTm a envi)
  | Pair(x,y) -> VPair((big_step_eval_inTm x envi),(big_step_eval_inTm y envi))
  | Liste(a) -> VListe(big_step_eval_inTm a envi)
  | Nil(a) -> VNil(big_step_eval_inTm a envi)
  | Cons(xs,a) -> VCons((big_step_eval_inTm xs envi),(big_step_eval_inTm a envi))
  | What(a) -> failwith "do not put a hole in a type, it make no sense"  
and vapp v = 
  match v with 
  | ((VLam f),v) -> f v
  | ((VNeutral n),v) -> VNeutral(NApp(n,v))
  | _ -> failwith "must not append"   
(*=vitter *)
and vitter (p,n,f,a) =
  match n,f with
  | (VZero,VLam fu) -> a
  | (VSucc(x),VLam fu) -> vapp(fu n,(vitter (p,x,f,a)))
  | _ -> VNeutral(NIter(p,n,f,a))
(*=End *)
(*=vfold *) 
and vdfold(alpha,p,n,xs,f,a) = 
  match xs,f,n with
  | (VDNil(alphi),VLam fu,VZero) -> a
  | (VDCons(elem,y),VLam fu,VSucc(ni)) -> vapp(vapp(vapp(fu n,xs),elem),vdfold(alpha,p,ni,y,f,a))
  | _ -> VNeutral(NDFold(alpha,p,n,xs,f,a))
(*=End *)
and vifte(p,c,tHen,eLse) = 
  match c with 
  | VTrue -> tHen 
  | VFalse -> eLse 
  | _ -> VNeutral(NIfte(p,c,tHen,eLse))
and vfold(p,alpha,xs,f,a) = 
  match xs,f with 
  | (VNil(alphi),VLam fu) -> a 
  | (VCons(elem,suite),VLam fu) -> vapp(vapp((fu elem),xs),vfold(p,alpha,suite,f,a))
  | _ -> VNeutral(NFold(p,alpha,xs,f,a))
and big_step_eval_exTm t envi = 
  match t with
  | Hole_exTm x -> failwith "you can't eval a hole"
  | Ann(x,_) -> big_step_eval_inTm x envi 
  | FVar(v) -> vfree v 
  | BVar(v) -> List.nth envi v 
  | Appl(x,y) -> vapp((big_step_eval_exTm x envi),(big_step_eval_inTm y envi))    
(*=big_step_iter *)
  | Iter(p,n,f,a) -> vitter ((big_step_eval_inTm p envi),
			     (big_step_eval_inTm n envi),
			     (big_step_eval_inTm f envi),
			     (big_step_eval_inTm a envi))
(*=End *)
(*=big_step_bool *)
  | Ifte(p,c,tHen,eLse) -> vifte((big_step_eval_inTm p envi),
				 (big_step_eval_inTm c envi),
				 (big_step_eval_inTm tHen envi),
				 (big_step_eval_inTm eLse envi))
  (*=End *)
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
  | Quote k -> BVar (i - k - 1)
  | x -> FVar x

let gensym =
  let c = ref 0 in
  fun () -> incr c; "x" ^ string_of_int !c
(*=value_to_inTm_head *)
let rec value_to_inTm i v =
  match v with 
(*=End *)
  | VLam f -> value_to_inTm (i+1) (f (vfree(Quote i)))
  | VNeutral n -> Inv(neutral_to_exTm i n)
(*=value_to_inTm_new *)		     
  | VPi(x,f) -> let var = gensym () in 
		begin
		  Pi(Global(var),
		     (value_to_inTm i x),
		     (value_to_inTm (i+1) (f(vfree(Quote i)))))
		end
(*=End *)
  | VSig(x,f) -> let var = gensym () in 
		 begin 
		   Sig(Global(var),
		       (value_to_inTm i x),
		       (value_to_inTm (i+1) (f(vfree(Quote i)))))
		 end 
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
  | VRefl(a) -> Refl(value_to_inTm i a) 
  | VListe(a) -> Liste(value_to_inTm i a)
  | VNil(a) -> Nil(value_to_inTm i a)
  | VCons(a,xs) -> Cons((value_to_inTm i a),(value_to_inTm i xs)) 
and neutral_to_exTm i v = 
  match v with 
  | NFree x -> boundfree i x
  | NApp(n,x) -> Appl((neutral_to_exTm i n),(value_to_inTm i x))
  | NDFold(alpha,p,n,xs,f,a) -> DFold((value_to_inTm i alpha),(value_to_inTm i p),(value_to_inTm i n),
				      (value_to_inTm i xs),(value_to_inTm i f),(value_to_inTm i a))
  | NIter(p,n,f,a) -> Iter((value_to_inTm i p),(value_to_inTm i n),(value_to_inTm i f),(value_to_inTm i a))
  | NIfte(p,c,tHen,eLse) -> Ifte((value_to_inTm i p),(value_to_inTm i c),(value_to_inTm i tHen),(value_to_inTm i eLse))
  | NTrans(gA,p,a,b,q,x) -> Trans((value_to_inTm i gA),(value_to_inTm i p),(value_to_inTm i a),
				  (value_to_inTm i b),(value_to_inTm i q),(value_to_inTm i x))
  (* ça me plait pas du tout mais je suis un peu dans le flou la, cette annotation qui ne sert a rien *)
  | NP0(x) -> P0(Ann((value_to_inTm i x),Star))
  | NP1(x) -> P1(Ann((value_to_inTm i x),Star))
  | NFold(p,alpha,xs,f,a) -> Fold((value_to_inTm i p),(value_to_inTm i alpha),(value_to_inTm i xs),(value_to_inTm i f),(value_to_inTm i a))



let rec equal_inTm t1 t2 = 
  match (t1,t2) with 
  | (Abs(_,x1),Abs(_,x2)) -> equal_inTm x1 x2
  | (Pi(_,x1,y1),Pi(_,x2,y2)) -> if equal_inTm x1 x2 then equal_inTm y1 y2 else false
  | (Sig(_,x1,y1),Sig(_,x2,y2)) -> if equal_inTm x1 x2 then equal_inTm y1 y2 else false
  | (Star,Star) -> true 
  | (Zero,Zero) -> true 
  | (Succ(n1),Succ(n2)) -> equal_inTm n1 n2
  | (Nat,Nat) -> true
  | (Bool,Bool) -> true 
  | (True,True) -> true 
  | (False,False) -> true 
  | (Inv(x1),Inv(x2)) -> equal_exTm x1 x2
  | (Pair(x1,y1),Pair(x2,y2)) -> if equal_inTm x1 x2 then equal_inTm y1 y2 else false
  | (What(a),What(b)) -> true
  | (Vec(x1,y1),Vec(x2,y2)) -> if equal_inTm x1 x2 then equal_inTm y1 y2 else false
  | (DNil x1,DNil x2) -> equal_inTm x1 x2 
  | (DCons(x1,y1),DCons(x2,y2)) -> if equal_inTm x1 x2 then equal_inTm y1 y2 else false
  | (Id(x1,y1,z1),Id(x2,y2,z2)) -> equal_inTm x1 x2 && equal_inTm y1 y2 && equal_inTm z1 z2
  | (Refl(a),Refl(b)) -> equal_inTm a b 
  | (Liste(a),Liste(b))-> equal_inTm a b
  | (Nil(a),Nil(b)) -> equal_inTm a b 
  | (Cons(y1,z1),Cons(y2,z2)) -> equal_inTm y1 y2 && equal_inTm z1 z2				  
  | _ -> false 
and equal_exTm t1 t2 = 
  match (t1,t2) with 
  | (Ann(x1,y1),Ann(x2,y2)) -> if equal_inTm x1 x2 then equal_inTm y1 y2 else false
  | (BVar(x1),BVar(x2)) -> x1 = x2 
  | (FVar(x1),FVar(x2)) -> x1 = x2
  | (Appl(x1,y1),Appl(x2,y2)) -> if equal_exTm x1 x2 then equal_inTm y1 y2 else false
  | (Iter(w1,x1,y1,z1),Iter(w2,x2,y2,z2)) -> 
     if equal_inTm w1 w2 then (if equal_inTm x1 x2 then (if equal_inTm y1 y2 then equal_inTm z1 z2 else false) else false) else false
  | (Ifte(w1,x1,y1,z1),Ifte(w2,x2,y2,z2)) -> 
     if equal_inTm w1 w2 then (if equal_inTm x1 x2 then (if equal_inTm y1 y2 then equal_inTm z1 z2 else false) else false) else false
  | (P0(x1),P0(x2)) -> equal_exTm x1 x2
  | (P1(x1),P1(x2)) -> equal_exTm x1 x2
  | (DFold(alpha1,p1,n1,xs1,f1,a1),DFold(alpha2,p2,n2,xs2,f2,a2)) -> if equal_inTm alpha1 alpha2 then (if equal_inTm p1 p2 
								     then (if equal_inTm p1 p2 then (if equal_inTm n1 n2 
								     then (if equal_inTm xs1 xs2 then (if equal_inTm f1 f2 
												       then equal_inTm a1 a2 else false)
													else false) 
												     else false) else false) 
												       else false) else false
  | (Fold(p1,alpha1,xs1,f1,a1),Fold(p2,alpha2,xs2,f2,a2)) -> 
     equal_inTm p1 p2 && equal_inTm alpha1 alpha2 && equal_inTm xs1 xs2 && 
       equal_inTm f1 f2 && equal_inTm a1 a2  
  | _ -> false
							 
															      
(*=check_head *)      
let rec lcheck contexte ty inT =
  match inT with
  (*=End *)
    (*=check_abs *)      
  | Abs(x,y) ->
     begin
       match ty with
       | VPi(s,t) -> let freshVar = gensym() in
		     lcheck (((Global freshVar),s)::contexte)
		       (t (vfree (Global freshVar)))
		       (substitution_inTm y (FVar(Global(freshVar))) 0)
       | _ -> false
     end
  (*=End *)
  (*=check_inv *)
  | Inv(x) -> 
     let ret = lsynth contexte x in
	 if equal_inTm (value_to_inTm 0 (ty)) (value_to_inTm 0 ret)
	 then true
	 else false
	   
(*=End *)
(*=check_star *)
  | Star -> 
     begin 
      match ty with 
	| VStar -> true 
	| _ -> false 
     end
(*=End *)
(*=check_pi *)
  | Pi (v,s,t) -> 
     begin 
       match ty with 
       | VStar -> let freshVar = gensym () in 
		  lcheck contexte VStar s 
		  && lcheck (((Global freshVar),
			      (big_step_eval_inTm s []))::contexte)
			    VStar
			    (substitution_inTm t (FVar(Global(freshVar))) 0)
       | _ -> false
     end 
  | Sig (x,a,b) -> 
     begin
       match ty with 
       | VStar -> let freshVar = gensym () in 
		  lcheck contexte VStar a 
		  && lcheck (((Global freshVar),
			      (big_step_eval_inTm a []))::contexte)
			    VStar
			    (substitution_inTm b (FVar(Global(freshVar))) 0)
       | _ -> false
     end
  (*=End *)
  | Pair(x,y) -> 
     begin 
       match ty with 
       | VSig(a,b) -> lcheck contexte a x &&
			  lcheck contexte (b (big_step_eval_inTm x [])) y 
       | _ -> false
     end 
  (*=check_nat *)
  | Nat -> ty = VStar
  | Zero -> ty = VNat
  | Succ(x) -> 
     begin 
       match ty with 
	 | VNat -> lcheck contexte VNat x 
	 | _ -> false
     end
  (*=End *)
  | Bool -> ty = VStar
  | True -> ty = VBool
  | False -> ty = VBool
(*=check_vec *)
  | Vec(alpha,n) -> ty = VStar && 
		      lcheck contexte VStar alpha  &&
	  		lcheck contexte VNat n   			       
(*=End *)
(*=check_dnil *)
  | DNil(alpha) -> 
     begin
       match ty with
       | VVec(alpha_vec,VZero) ->
	  equal_inTm (value_to_inTm 0
			(big_step_eval_inTm alpha [])) 
	    (value_to_inTm 0 alpha_vec)								
       | _ -> false
     end 
(*=End *)
(*=check_dcons *)
  | DCons(a,xs) -> 
     begin 
       match ty with 
       | VVec(alpha,VSucc(n)) ->
	  lcheck contexte (VVec(alpha,n)) xs  && 				 
	    lcheck contexte alpha a  				 
       | _ -> false
     end 
(*=End *)
  | What(a) -> false 
(*=check_id *)
  | Id(gA,a,b) ->
     let eval_gA = big_step_eval_inTm gA [] in
     ty = VStar &&
     lcheck contexte VStar gA  &&
       lcheck contexte eval_gA a  &&
       lcheck contexte eval_gA b 
(*=End *)
(*=check_refl *)
  | Refl(a) ->
     begin
       match ty with 
       | VId(gA,ta,ba) -> 
	  if equal_inTm a (value_to_inTm 0 ta) &&
	    equal_inTm a (value_to_inTm 0 ba)
	  then lcheck contexte gA a
	  else false
       | _ -> false
     end
(*=End *)
  | _ -> failwith "HEHEHEHEHE"
(*=synth_head *)     
and lsynth ctxt exT =
  match exT with
  (*=End *)
  (*=synth_var *)
  | BVar x -> failwith "Impossible to check a BoundVar"
  | FVar x -> List.assoc x ctxt
  (*=End *)
(*=End *)
(*=synth_ann *) 
  | Ann(x,t) -> let eval_t = big_step_eval_inTm t [] in
		if lcheck ctxt VStar t 
		  && lcheck ctxt (big_step_eval_inTm t []) x 
		then eval_t 		    		   
		else failwith "fail synth Ann"  
(*=End *)
(*=synth_app *) 
  | Appl(f,s) -> 
     let synth_f = lsynth ctxt f in
     begin
       match synth_f with
       | VPi(s_pi,fu) -> if lcheck ctxt s_pi s 
		     then (fu (big_step_eval_inTm s [])) 
		     else failwith "fail synth Appl"
       | _ -> failwith "fail synth Appl"
     end
  (*=End *)
  (*=synth_iter *)
  | Iter(p,n,f,a) ->
     let big_p = big_step_eval_inTm p [] in
     let big_n = big_step_eval_inTm n [] in 
     if lcheck ctxt (big_step_eval_inTm (read "(-> N *)") []) p &&
       lcheck ctxt (big_step_eval_inTm (read "N") []) n &&
       lcheck ctxt (big_step_eval_inTm
			  (Pi(Global("n"),Nat,
			      Pi(Global("NO"),(Inv(Appl(Ann(p,Pi(Global"NO",Nat,Star)),n))),
				 (Inv(Appl(Ann(p,Pi(Global"NO",Nat,Star)),Succ(n))))))) [])
       f &&
       lcheck ctxt (vapp(big_p,VZero)) a 
     then (vapp(big_p,big_n))
     else failwith "Iter synth fail"
  (*=End *)
  | Ifte(p,c,tHen,eLse) -> 
     let big_p = big_step_eval_inTm p [] in 
     let big_c = big_step_eval_inTm c [] in 
     if lcheck ctxt (big_step_eval_inTm (read "(-> B *)") []) p &&
	  lcheck ctxt (big_step_eval_inTm (read "B") []) c &&
	    lcheck ctxt (vapp(big_p,VTrue)) tHen && 
	      lcheck ctxt (vapp(big_p,VFalse)) eLse 
     then (vapp(big_p,big_c))
     else failwith "Ifte synth fail" 
  (*=synth_dfold *)
  | DFold(alpha,p,n,xs,f,a) ->
     let type_p = (Pi(Global"n",Nat,(Pi(Global"xs",Vec(alpha,Inv(BVar 0)),Star)))) in 
     if lcheck ctxt VStar alpha &&
       lcheck ctxt (big_step_eval_inTm type_p []) p &&
       lcheck ctxt VNat n &&
       lcheck ctxt (big_step_eval_inTm (Vec(alpha,n)) []) xs &&
       lcheck ctxt
       (big_step_eval_inTm 
	  (Pi(Global"n",Nat,
	      Pi(Global"xs",Vec(alpha,Inv(BVar 0)),
		 Pi(Global"a",alpha,
		    Pi(Global"NO",Inv(Appl(Appl(Ann(p,type_p),n),xs)),
		       Inv(Appl(Appl(Ann(p,type_p),Succ(n)),DCons(a,xs)))))))) []) f &&
       lcheck ctxt (big_step_eval_inTm (Inv(Appl(Appl(Ann(p,type_p),Zero),DNil(alpha)))) []) a				 
     then (big_step_eval_inTm (Inv(Appl(Appl(Ann(p,type_p),n),xs))) [])
     else failwith "DFOld synth something goes wrong"
  (*=End *)
  (*=synth_trans *)
  | Trans(gA,p,a,b,q,x) ->
     let type_p = Pi(Global"a",gA,Pi(Global"b",gA,Pi(Global"NO",Id(gA,Inv(BVar 1),Inv(BVar 0)),Star))) in 
     if lcheck ctxt VStar gA &&
       lcheck ctxt (big_step_eval_inTm gA []) a &&
       lcheck ctxt (big_step_eval_inTm gA []) b &&
       lcheck ctxt  (big_step_eval_inTm (Id(gA,a,b)) []) q &&  
       lcheck ctxt (big_step_eval_inTm type_p []) p && 
       lcheck ctxt (big_step_eval_inTm (Inv(Appl(Appl(Appl(Ann(p,type_p),a),b),q))) []) x
     then (big_step_eval_inTm (Inv(Appl(Appl(Appl(Ann(p,type_p),a),b),q))) [])
     else failwith "Trans synth fail"           			       
  (*=End *)
  | _ -> failwith "HAHAHAHAHAHAHA"
    




     
let rec contexte_to_string contexte = 
  match contexte with 
  | [] -> "|" 	    
  | (Global s,w) :: tail -> "(" ^ s ^ "," ^ pretty_print_inTm (value_to_inTm 0 w) [] ^ ");" ^ contexte_to_string tail  
  | _ -> failwith "Must not append"




     
let rec check contexte inT ty steps = 
  match inT with
  | Hole_inTm x -> create_report false (contexte_to_string contexte) steps "IT'S A HOLE!!!!"
  | Abs(x,y) -> 
     begin  
       match ty with 
       | VPi(s,t) -> let freshVar = gensym () in 
		     check (((Global freshVar),s)::contexte) (substitution_inTm y (FVar(Global(freshVar))) 0) (t (vfree (Global freshVar))) (pretty_print_inTm inT [] ^ ";"^ steps) 
       | _ -> create_report false (contexte_to_string contexte) steps "Abs type must be a Pi"
     end 
  | Inv(x) -> 
     let ret = synth contexte x (pretty_print_inTm inT [] ^ ";" ^ steps) in 
     if res_debug_synth ret
     then 
       begin 
	 if equal_inTm (value_to_inTm 0 (ty)) (value_to_inTm 0 (ret_debug_synth ret)) (* elle est ici l'erreur il faut que je 
test le retour de la synthèse *) 
	 then create_report true (contexte_to_string contexte) steps "NO"
	 else create_report false (contexte_to_string contexte) steps "Inv: ret and ty are not equal"
       end
     else create_report false (contexte_to_string contexte) steps ("Inv: Synth of x goes wrong \n ----Rapport du Inv---\n" ^ print_report_synth ret ^ "\n------Fin Rapport Inv---\n")
  | Star -> 
     begin 
      match ty with 
	| VStar -> create_report true (contexte_to_string contexte) steps "No"
	| _ -> create_report false (contexte_to_string contexte) steps "Star : ty must be of type Star"
     end
  | Pi (v,s,t) -> 
     begin 
       match ty with 
       | VStar -> let freshVar = gensym () in 
		  if res_debug(check contexte s VStar (pretty_print_inTm inT [] ^ ";"^ steps))
		  then check (((Global freshVar),(big_step_eval_inTm s []))::contexte) (substitution_inTm t (FVar(Global(freshVar))) 0) VStar (pretty_print_inTm inT [] ^ ";"^ steps)
		  else create_report false (contexte_to_string contexte) steps "Pi : S is not of type Star"
       | _ -> create_report false (contexte_to_string contexte) steps "Pi : ty must be of type Star"
     end 
  |Sig(v,s,t) -> 
    begin 
      match ty with 
      | VStar -> let freshVar = gensym () in 
		 if res_debug(check contexte s VStar (pretty_print_inTm inT [] ^ ";"^ steps))
		 then check (((Global freshVar),(big_step_eval_inTm s []))::contexte) (substitution_inTm t (FVar(Global(freshVar))) 0) VStar (pretty_print_inTm inT [] ^ ";"^ steps)
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
	 | VNat -> check contexte x VNat (pretty_print_inTm inT [] ^ ";"^ steps)
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
       | VSig(a,b) -> 
	  let check_x = check contexte x a (pretty_print_inTm inT [] ^ ";"^ steps) in
	  let check_y = check (*pas sur a 100% de ne rien mettre dans le contexte ici à réfléchir*)
			  contexte y (b (big_step_eval_inTm x [])) (pretty_print_inTm inT [] ^ ";"^ steps) in 
	  if res_debug(check_x) 
	  then
	    begin 
	      if res_debug(check_y) 
	      then create_report true (contexte_to_string contexte) steps "No"
	      else create_report false (contexte_to_string contexte) steps "Pair: element y of the pair as the wrong type"
	    end 
	  else create_report false (contexte_to_string contexte) steps "Pair: element x of the pair as the wrong type"
	  
       | _ -> create_report false (contexte_to_string contexte) steps "Pair: ty must VSig"
     end 
  | Vec(alpha,n) -> 
     begin        
       match ty with 
       | VStar -> let check_alpha = check contexte alpha VStar (pretty_print_inTm inT [] ^ ";"^ steps) in
		  if res_debug(check_alpha) 
		  then check contexte n VNat (pretty_print_inTm inT [] ^ ";"^ steps)
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
       | VVec(alpha,VSucc(n)) -> let check_xs = check contexte xs (VVec(alpha,n)) (pretty_print_inTm inT [] ^ ";"^ steps) in 
				 if res_debug(check_xs)
				 then check contexte a alpha (pretty_print_inTm inT [] ^ ";"^ steps)
				 else create_report false (contexte_to_string contexte) steps "DCons : xs must be of type (VVec alpha n)"
       | _ -> create_report false (contexte_to_string contexte) steps "DCons : ty must be a VVec"
     end
  (*=check_what *)
  | What(a) -> create_report true (contexte_to_string contexte) steps ("(contexte " ^ (contexte_to_string contexte) ^ ")(type " ^ (pretty_print_inTm inT []) ^ ")")
  (*=End *)
  | Id(gA,a,b) -> let check_gA = check contexte gA VStar (pretty_print_inTm inT [] ^ ";"^ steps) in 		  
		  let eval_gA = big_step_eval_inTm gA [] in 
		  let check_a = check contexte a eval_gA (pretty_print_inTm inT [] ^ ";"^ steps) in 
		  let check_b = check contexte b eval_gA (pretty_print_inTm inT [] ^ ";"^ steps) in 
		  if res_debug(check_gA) 
		  then 
		    begin 
		      if res_debug(check_a) 
		      then 
			begin 
			  if res_debug(check_b) 
			  then create_report true (contexte_to_string contexte) steps "NO"
			  else create_report false (contexte_to_string contexte) steps "Id : b must be of type gA"
			end 
		      else create_report false (contexte_to_string contexte) steps "Id : a must be of type gA"
		    end  
		  else create_report false (contexte_to_string contexte) steps "Id : gA must be of type Star"
  | Refl(a) -> 
     begin
       match ty with 
       | VId(gA,ta,ba) -> let quote_ta = value_to_inTm 0 ta in 
			  let quote_ba = value_to_inTm 0 ba in
			  if equal_inTm a quote_ta && equal_inTm a quote_ba
			  then
			    begin 
			      check contexte a gA (pretty_print_inTm inT [] ^ ";"^ steps)
			    end 
			  else create_report false (contexte_to_string contexte) steps "Refl : a and ta must be equal"	       
       | _ -> create_report false (contexte_to_string contexte) steps "Refl : ty must be of type Id"
     end
  | Liste(alpha) -> 
     begin 
       match ty with 
       | VStar -> let check_alpha = check contexte alpha VStar (pretty_print_inTm inT [] ^ ";"^ steps) in
		  if res_debug(check_alpha) 
		  then create_report true (contexte_to_string contexte) steps "NO"
		  else create_report false (contexte_to_string contexte) steps "Liste : alpha seems to not be of type Star"
       | _ -> create_report false (contexte_to_string contexte) steps "Liste : ty must be VStar" 
     end
  | Nil(alpha) -> 
     begin 
       match ty with 
       | VListe(alpha_liste) -> if equal_inTm (value_to_inTm 0 (big_step_eval_inTm alpha [])) 
					    (value_to_inTm 0 alpha_liste)
				then create_report true (contexte_to_string contexte) steps "NO"
				else create_report false (contexte_to_string contexte) steps "Nil : the 2 alpha seems to not be the same"
       | _ -> create_report false (contexte_to_string contexte) steps "Nil : ty must be VListe"       
     end
  | Cons(a,xs) -> 
     begin 
       match ty with 
       | VListe(alpha_liste) -> let check_a = check contexte a alpha_liste (pretty_print_inTm inT [] ^ ";"^ steps) in
				let check_xs = check contexte xs (VListe(alpha_liste)) (pretty_print_inTm inT [] ^ ";"^ steps) in
				if res_debug(check_a) 
				then 
				  begin 
				    if res_debug(check_xs)
				    then create_report true (contexte_to_string contexte) steps "NO"
				    else create_report false (contexte_to_string contexte) steps "Cons : xs is not of type Liste(alpha)"
				  end
				else create_report false (contexte_to_string contexte) steps "Cons : a is not of type alpha"
       | _ -> create_report false (contexte_to_string contexte) steps "Cons : ty must be VListe(alpha)"
     end 
(*=synth_var *) 
and synth contexte exT steps =
  match exT with 
  | Hole_exTm x -> create_retSynth (create_report false (contexte_to_string contexte) steps "IT'S A HOLE") VStar
  | BVar x -> create_retSynth (create_report false (contexte_to_string contexte) steps "BVar : not possible during type checking") VStar
  | FVar x -> create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (List.assoc x contexte)
(*=End *)
  | P0(x) -> let synth_x = synth contexte x (pretty_print_exTm exT [] ^ ";" ^ steps) in 
	     if res_debug_synth synth_x
	     then
	       begin
		 match ret_debug_synth synth_x with 
		 | VSig(a,b) -> create_retSynth (create_report true (contexte_to_string contexte) steps "NO") a
		 | _ -> create_retSynth (create_report false (contexte_to_string contexte) steps "P0 : has to be applied to a pair") VStar
	       end 
	     else create_retSynth (create_report false (contexte_to_string contexte) steps "P0 : synth of elem don't work") VStar
  | P1(x) -> let synth_x = synth contexte x (pretty_print_exTm exT [] ^ ";" ^ steps) in 
	     if res_debug_synth synth_x
	     then
	       begin
		 match ret_debug_synth synth_x with 
		 | VSig(a,b) -> create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (b (big_step_eval_exTm (P0(x)) []))
		 | _ -> create_retSynth (create_report false (contexte_to_string contexte) steps "P0 : has to be applied to a pair") VStar
	       end 
	     else create_retSynth (create_report false (contexte_to_string contexte) steps "P0 : synth of elem don't work") VStar
  (*=synth_ann *) 
  | Ann(x,t) -> let ret = check contexte t VStar (pretty_print_exTm exT [] ^ ";"^ steps) in 
		let eval_t = big_step_eval_inTm t [] in
		if res_debug(ret)
		then 
		  begin 
		    if res_debug(check contexte x eval_t (pretty_print_exTm exT [] ^ ";"))
		    then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") eval_t
		    else create_retSynth (create_report false (contexte_to_string contexte) steps "Ann : x is not of type t") VStar
		  end
		else create_retSynth (create_report false (contexte_to_string contexte) steps "Ann : t is not of type VStar") VStar
(*=End *)
(*=synth_app *) 
  | Appl(f,s) -> 
     let synth_f = synth contexte f (pretty_print_exTm exT [] ^ ";"^ steps) in 
     if res_debug_synth synth_f 
     then
     begin
       match ret_debug_synth synth_f with 
       | VPi(s_pi,fu) -> if res_debug(check contexte s s_pi (pretty_print_exTm exT [] ^ ";"))
		     then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (fu (big_step_eval_inTm s [])) 
		     else create_retSynth (create_report false (contexte_to_string contexte) steps "Appl : s is not of type S") VStar
       | _ -> create_retSynth (create_report false (contexte_to_string contexte) steps "Appl : f is not of type Pi") VStar
     end
     else create_retSynth (create_report false (contexte_to_string contexte) steps "Appl : synth of f goes wrong") VStar
(*=End *) 
  | Iter(p,n,f,a) -> let big_p = big_step_eval_inTm p [] in
		     let big_n = big_step_eval_inTm n [] in 
 		     let check_p = check contexte p (big_step_eval_inTm (read "(-> N *)") []) (pretty_print_exTm exT [] ^ ";") in    
		     let check_n = check contexte n (big_step_eval_inTm (read "N") []) (pretty_print_exTm exT [] ^ ";") in
		     let check_f = check contexte f (big_step_eval_inTm (Pi(Global("n"),Nat,Pi(Global("NO"),(Inv(Appl(Ann(p,Pi(Global"NO",Nat,Star)),n))),(Inv(Appl(Ann(p,Pi(Global"NO",Nat,Star)),Succ(n))))))) [])  (pretty_print_exTm exT [] ^ ";") in
		     let check_a = check contexte a (vapp(big_p,VZero)) (pretty_print_exTm exT [] ^ ";") in
		     if res_debug(check_n)
		     then 
		       begin 
			 if res_debug(check_p)
			 then 
			   begin 
			     if res_debug(check_f)
			     then
			       begin 
				 if res_debug(check_a)
				 then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (vapp(big_p,big_n)) 
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
     let check_p = check contexte p (big_step_eval_inTm (read "(-> B *)") []) (pretty_print_exTm exT [] ^ ";") in    
     let check_c = check contexte c (big_step_eval_inTm (read "B") []) (pretty_print_exTm exT [] ^ ";") in
     let check_tHen = check contexte tHen (vapp(big_p,VTrue)) (pretty_print_exTm exT [] ^ ";") in
     let check_eLse = check contexte eLse (vapp(big_p,VFalse)) (pretty_print_exTm exT [] ^ ";") in
     if res_debug(check_p)
     then
       begin 
	 if res_debug(check_c)
	 then 
	   begin
	     if res_debug(check_tHen)
	     then 
	       begin 
		 if res_debug(check_eLse) 
		 then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (vapp(big_p,big_c)) 
		 else create_retSynth (create_report false (contexte_to_string contexte) steps "Ifte : eLse is not of type (P VFalse)") VStar
	       end 
	     else create_retSynth (create_report false (contexte_to_string contexte) steps "Ifte : tHen is not of type (P VTrue)") VStar     
	   end 
	 else create_retSynth (create_report false (contexte_to_string contexte) steps "Ifte : c is not of type VBool") VStar     
       end  
     else create_retSynth (create_report false (contexte_to_string contexte) steps "Ifte : p is not of type (-> B *)") VStar
     (* le check de f est nul parceque j'utilise pas les boundvar qui sont binde par les premier pi, A CHANGER *)
  | DFold(alpha,p,n,xs,f,a) -> let check_alpha = check contexte alpha VStar (pretty_print_exTm exT [] ^ ";") in
			       let type_p = (Pi(Global"n",Nat,(Pi(Global"xs",Vec(alpha,Inv(BVar 0)),Star)))) in 
			       let check_p = check contexte p (big_step_eval_inTm type_p []) (pretty_print_exTm exT [] ^ ";") in
			       let check_n = check contexte n VNat (pretty_print_exTm exT [] ^ ";") in			       
 			       let check_xs = check contexte xs (big_step_eval_inTm (Vec(alpha,n)) [])  (pretty_print_exTm exT [] ^ ";") in 
  			       let check_f = check contexte f 
						   (big_step_eval_inTm 
						      (Pi(Global"n",Nat,
							  Pi(Global"xs",Vec(alpha,Inv(BVar 0)),
							     Pi(Global"a",alpha,
								Pi(Global"NO",Inv(Appl(Appl(Ann(p,type_p),n),xs)),
								   Inv(Appl(Appl(Ann(p,type_p),Succ(n)),DCons(a,xs)))))))) []) 
						   (pretty_print_exTm exT [] ^ ";") in 
			       let check_a = check contexte a (big_step_eval_inTm (Inv(Appl(Appl(Ann(p,type_p),Zero),DNil(alpha)))) [])
						   (pretty_print_exTm exT [] ^ ";") in 
			       if res_debug check_alpha 
			       then 
				 begin 
				   if res_debug check_p
				   then 
				     begin 
				       if res_debug check_n 
				       then 
					 begin 
					   if res_debug check_xs 
					   then
					     begin 
					       if res_debug check_f 
					       then 
						 begin 
						   if res_debug check_a 
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
			 
  | Trans(gA,p,a,b,q,x) -> let check_gA = check contexte gA VStar (pretty_print_exTm exT [] ^ ";") in
			   let check_a = check contexte a (big_step_eval_inTm gA []) (pretty_print_exTm exT [] ^ ";") in
			   let check_b = check contexte b (big_step_eval_inTm gA []) (pretty_print_exTm exT [] ^ ";") in
			   let check_q = check contexte q (big_step_eval_inTm (Id(gA,a,b)) [])(pretty_print_exTm exT [] ^ ";") in
			   let type_p = Pi(Global"a",gA,Pi(Global"b",gA,Pi(Global"NO",Id(gA,Inv(BVar 1),Inv(BVar 0)),Star))) in 
			   let check_p = check contexte p (big_step_eval_inTm type_p []) (pretty_print_exTm exT [] ^ ";") in
			   let check_x = check contexte x (big_step_eval_inTm (Inv(Appl(Appl(Appl(Ann(p,type_p),a),b),q))) []) (pretty_print_exTm exT [] ^ ";") in
			   if res_debug check_gA 
			   then
			     begin 
			       if res_debug check_a 
			       then 
				 begin 
				   if res_debug check_b 
				   then 
				     begin 
				       if res_debug check_q 
				       then
					 begin 
					   if res_debug check_p
					   then 
					     begin 
					       if res_debug check_x
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
     let check_alpha = check contexte alpha VStar (pretty_print_exTm exT [] ^ ";") in 
     let type_p = (Pi(Global"a",Star,(Pi(Global"xs",Liste(Inv(BVar 0)),Star)))) in 
     let check_p = check contexte p (big_step_eval_inTm type_p []) (pretty_print_exTm exT [] ^ ";") in 
     let check_xs = check contexte xs (big_step_eval_inTm (Liste(alpha)) []) (pretty_print_exTm exT [] ^ ";") in 
     let type_f = (Pi(Global"a",alpha,
		      Pi(Global"xs",Liste(alpha),			 
			 Pi(Global"NO",Inv(Appl(Appl(Ann(p,type_p),alpha),Inv(BVar 0))),
			    Inv(Appl(Appl(Ann(p,type_p),alpha),Cons(Inv(BVar 2),Inv(BVar 1)))))))) in		    
     let check_f = check contexte f (big_step_eval_inTm (type_f) []) (pretty_print_exTm exT [] ^ ";") in 
     let check_a = check contexte a (big_step_eval_inTm alpha []) (pretty_print_exTm exT [] ^ ";") in 
     if res_debug check_alpha 
     then
       begin 
	 if res_debug check_p
	 then
	   begin 
	     if res_debug check_xs 
	     then
	       begin
		 if res_debug check_f
		 then
		   begin 
		     if res_debug check_a 
		     then create_retSynth (create_report true (contexte_to_string contexte) steps "NO") (big_step_eval_inTm (Inv(Appl(Appl(Ann(p,type_p),alpha),xs))) [])
		     else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: a must be of type alpha") VStar
		   end
		 else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: f has the wrong type") VStar
	       end
	     else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: xs must be of type Liste(alpha)") VStar
	   end
	 else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: P has the wrong type") VStar
       end 
     else create_retSynth (create_report false (contexte_to_string contexte) steps "Fold: alpha must be of type Star") VStar


(* let () = Printf.printf "%s" (print_report (check [] (read "(lamba x x)") (big_step_eval_inTm (read "(-> * *)") []) "")) *)

