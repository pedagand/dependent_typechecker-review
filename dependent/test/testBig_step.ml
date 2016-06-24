open OUnit2
open Sexplib
open Lambda



let inputs = 
[
  ("((: (lambda x x) (-> N N)) y)","y");
  ("(iter (lambda x N) zero (lambda n (lambda x (succ x))) zero)","zero");
  ("(iter (lambda x N) (succ (succ (succ zero))) (lambda n (lambda x (succ x))) zero)","(succ (succ (succ zero)))"); 
  ("(iter (lambda x N) (succ zero) (lambda n (lambda x (+ (succ (succ zero)) x))) zero)","(succ (succ zero))");
  ("(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x (+ (succ (succ zero)) x))) zero)","(succ (succ (succ (succ zero))))");
  ("(iter (lambda x N) (succ (succ (succ zero))) (lambda n (lambda x (+ (succ (succ zero)) x))) zero)","(succ (succ (succ (succ (succ (succ zero))))))");
  ("(+ (succ (succ zero)) (succ zero))","(succ (succ (succ zero)))");
  ("(mult (succ (succ zero)) (succ zero))","(succ (succ zero))");
  ("(mult (succ (succ zero)) (succ (succ zero)))","(succ (succ (succ (succ zero))))");
  ("(mult (succ (succ (succ zero))) (succ (succ zero)))","(succ (succ (succ (succ (succ (succ zero))))))");



  ("(dfold N (lambda n (lambda xs N)) (succ (succ zero)) (dcons (succ zero) (dcons (succ (succ zero)) (dnil N))) (lambda n (lambda xs (lambda a (lambda x (+ a x))))) zero)","(succ (succ (succ zero)))");
  ("(ifte (lambda x B) true true false)","true");
  ("(ifte (lambda x B) false true false)","false");
  ("(fold (lambda x (lambda y N)) N (cons (succ zero) (cons (succ zero) (nil N))) (lambda a (lambda xs (lambda no (+ a no)))) zero)",
   "(succ (succ zero))");
]


let tests = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal (value_to_inTm 0 (big_step_eval_inTm (read term) [])) (read res)) inputs 
