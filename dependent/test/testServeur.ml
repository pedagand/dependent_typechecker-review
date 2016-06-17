open OUnit2
open Serveur
open Lambda
open Tactics
open Sexplib

let compare_term a b = 
  Sexp.of_string a = Sexp.of_string b

let inputs_read = 
[
  ("((goal (-> N N)) (env ((a , N) (b , B))) (lambda x x) intro lol)",(Request(R_goal(Goal(Pi(Global"NO",Nat,Nat))),R_environment(Env([Couple("a",Nat);Couple("b",Bool)])),R_terme(Abs(Global"x",Inv(BVar 0))),R_tactic("intro"),R_var("lol")))) 
]

let inputs_print = 
[
  ((Request(R_goal(Goal(Pi(Global"NO",Nat,Nat))),R_environment(Env([Couple("a",Nat);Couple("b",Bool)])),R_terme(Abs(Global"x",Inv(BVar 0))),R_tactic("intro"),R_var("lol"))),"((goal (pi NO N N)) (env ((a , N) (b , B))) (lambda x x) intro lol)") 
]

let tests_read_request  
  = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal ~printer:(fun a -> pretty_print_global a ) (read_request term) res) inputs_read

let tests_print_request
= List.map (fun (term, res) -> "test" >:: fun ctxt -> assert_equal (compare_term (pretty_print_global term) res) true) inputs_print


