open OUnit2
open Sexplib
open Lambda


(* ------------------------- test substitution  --------------------------- *)

			       (*  
let test_sub_inTm4 test_ctxt = assert_equal
				 (substitution_inTm  (Inv(Ifte(True,BVar 0,BVar 0))) (FVar "x") 0 )
				 (Inv(Ifte(True,FVar "x",FVar "x")))
 *)
			       

let inputs = 
  [("(lambda x (x 0))",(Var (Global "y")),"(y 0)");
   ("(pi x * (pi y x *))",(Var (Global "x1")),"(pi y x1 *)");
   ("(sig x * (sig y x *))",(Var (Global "x1")),"(sig y x1 *)");
   ("(lambda x (succ x))",(Var (Global "x1")),"(succ x1)");
   ("(pi P (-> A *) (-> (P a) (P b)))",(Var (Global "x1")),
    "(-> (x1 a) (x1 b))"); 
   ("(lambda A (lambda a (lambda b (pi P (-> A *) (-> (P a) (P b))))))",
    (Var (Global "x1")),"(lambda a (lambda b (pi P (-> x1 *) (-> (P a) (P b)))))");
   ("(lambda a (lambda b (pi P (-> A *) (-> (P a) (P b)))))",
    (Var (Global "x1")),"(lambda b (pi P (-> A *) (-> (P x1) (P b))))");
   ("(lambda b (pi P (-> A *) (-> (P a) (P b))))",
    (Var (Global "x1")),"(pi P (-> A *) (-> (P a) (P x1)))");   
   ("(lambda x (: (p0 (x , b)) (N X N)))",
    (Var (Global "x1")),"(: (p0(x1 , b)) (N X N))");
   ("(lambda x (: (p1 (x , b)) (N X N)))",
    (Var (Global "x1")),"(: (p1(x1 , b)) (N X N))");
   ("(pi x * (x X N))",(Var (Global "x1")),"(x1 X N)");
   ("(lambda x (pi x x *))",(Var (Global "x1")),"(pi x x1 *)");      

  ]


(* il va me falloir une technique pour les noms je pense le faire avec gensym *)

let tests = List.map (fun (term,sub,res) -> "testsub" >:: fun ctxt -> assert_equal (equal (subst_inTm (read term) sub) (read res)) (true)) inputs

