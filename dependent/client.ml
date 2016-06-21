open Lambda 
open Sexplib
open ArbreZip


(*
  To load in the OCaml toplevel:
  #use "topfind";;
  #use "client.ml";;
*)

(* fichier client 2.0 *)



let init_view = {goal = "()"; preuve = "()"; hypo = "()"; validate = false }
let init_view_arg g p h v = {goal = g; preuve = p; hypo = h; validate = v }



let pretty_print_view g = 
  g.hypo ^ "\n==============\n" ^ g.goal ^ " |- " ^ g.preuve


(* fonctions permettant la communication avec le serveur *)

let create_request g tact var = 
  "((goal " ^ g.goal ^ ") (env (" ^ g.hypo ^ ")) " ^ g.preuve ^ " " ^ tact ^ " " ^ var ^ ")"

let send_to_serv str = 
  Serveur.main str



