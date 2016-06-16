open OUnit2
open Serveur
open Lambda
open Tactics

(* let () = Printf.printf "%s\n" (pretty_print_global (read_request "((goal (-> N N)) (env ((a , N) (b , B))) (lambda x x))")) 
let () = Printf.printf "%s\n" (pretty_print_global (read_request "((goal (-> * (-> * *))) (env ((a , N) (b , B))) (lambda x (lambda y x)))"))
*)
let inputs = 
[
  ("((goal (-> N N)) (env ((a , N) (b , B))) (lambda x x))",(Request(R_goal(Goal(Pi(Global"NO",Nat,Nat))),R_environment(Env([Couple("a",Nat);Couple("b",Bool)])),R_terme(Abs(Global"x",Inv(BVar 0))))))
]



let tests_read_request  
  = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal ~printer:(fun a -> pretty_print_global a ) (read_request term) res) inputs  


