open OUnit2
open Sexplib
open Lambda

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a A (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let testcheck3x = "(pi A * (pi B (pi x A *) *))"    

let testcheck4x = "(pi F (-> * *) (pi X * (-> (F X) *)))"   

let eq = "(lambda A (lambda a (lambda b (pi P (-> A *) (-> (P a) (P b))))))"


let inputs =   
  [    
    (* tests vérification lambda *)
    ("(lambda x x)","(-> * *)",true);  
    ("(lambda x x)","(-> * N)",false);
    ("(lambda x x)","(-> N N)",true);
    ("(lambda x x)","(-> N *)",false);
    ("(lambda x (lambda y (x y)))","(-> (-> N N) (-> N N))",true);
    ("(lambda x (lambda y (x y)))","(-> (-> N N) (-> N N))",true);
    ("(lambda x (lambda y (y x)))","(-> (-> N N) (-> N N))",false);
    ("(lambda x x)","(-> (-> * *) *)",false); 
    ("(lambda x (x y))","(-> * *)",false);
    ("(lambda x (lambda y y))","(-> * (-> * *))",true);    
    ("(lambda x (lambda y (y x)))","(-> * (-> (-> * *) *))",true);
    ("(lambda x (lambda y (x y)))","(-> * (-> (-> * *) *))",false);
    ("(lambda x (lambda y x))","(-> * (-> (-> * *) *))",true); 
    ("(lambda x zero)","(-> * N)",true);
    ("(lambda x N)","(-> N *)",true);
    ("(lambda x (lambda y (succ y)))","(-> N (-> N N))",true);



    (* tests vérification Pi *)
    ("(pi x * *)","*",true);
    ("(pi x * *)","N",false); 
    ("(-> * *)","*",true);
    ("(pi y N N)","*",true);
    ("(pi x * x)","*",true);
    ("(pi x (lambda y y) *)","*",false);
    ("(pi x N (pi y N N))","*",true); 
    ("(pi x N (pi y N x))","*",false); 
    ("(pi A * (pi B (pi x A *) *))","*",true); 

    (* tests de vérification Sig *)
    ("(sig x * *)","*",true);
    ("(sig x * *)","N",false); 
    ("(sig y N N)","*",true);
    ("(sig x * x)","*",true);
    ("(sig x (lambda y y) *)","*",false);
    ("(sig x N (pi y N N))","*",true); 
    ("(sig x N (pi y N x))","*",false); 
    ("(sig A * (pi B (pi x A *) *))","*",true); 
    
    (* tests de vérification des Paires *)
    ("((succ zero),(dcons zero (dnil N)))","(sig n N (vec N (succ zero)))",true);
    ("((succ zero),(dcons true (dnil B)))","(sig n N (vec B (succ zero)))",true);
    ("((succ zero),(dcons zero (dnil N)))","(sig n N (vec N n))",true);
    ("(true , false)","(sig a B B)",true);  (* be carefull with spaces because of the lisp syntaxe *)


    ("(true , zero)","(sig a B B)",false);
    ("((succ zero),(dcons true (dnil N)))","(sig n N (vec B (succ zero)))",false);
    ("((succ zero),(dcons true (dnil B)))","(sig n N (vec B (succ (succ (zero)))))",false);
    ("((succ (succ zero)),(dcons zero (dnil N)))","(sig n N (vec N n))",false);
    ("((succ zero),(dcons zero (dnil N)))","(sig n N (vec N zero))",false);

    (* tests de synthèse sur les projections *)
    ("(p0 (: (true , false) (sig n B B)))","B",true);
    ("(p1 (: (true , zero) (sig n B N)))","N",true);
    ("(p0 (: ((succ zero),(dcons zero (dnil N))) (sig n N (vec N (succ zero)))))","N",true);
    ("(p1 (: ((succ zero),(dcons zero (dnil N))) (sig n N (vec N (succ zero)))))","(vec N (succ zero))",true);
    ("(p1 (: ((succ zero),(dcons zero (dnil N))) (sig n N (vec N n))))","(vec N (succ zero))",true);

    ("(p0 (: (true , zero) (sig n B N)))","N",false);
    ("(p0 (: (zero , false) (sig n N B)))","B",false);
    ("(p0 (: (true , false) (sig n B B)))","N",false);
    ("(p1 (: ((succ zero),(dcons zero (dnil N))) (sig n N (vec N n))))","(vec N zero)",false);


    (* tests synthèse Ann *)
    ("(: (lambda x x) (-> N N))","(-> N N)",true);
    ("(: (lambda x x) (-> N *))","(-> N *)",false);
    ("(: (lambda x x) (-> * *))","(-> N N)",false); 
    ("(lambda x (: x N))","(-> N N)",true);
    ("(lambda x (: x *))","(-> N N)",false);
    ("(lambda x (: x N))","(-> * *)",false);
    ("(lambda x (: x N))","(-> * N)",false);
    ("(: (true , false) (sig n B B))","(sig n B B)",true);
    ("(: (true , false) (sig n N B))","(sig n B B)",false);
    ("(: (true , false) (sig n B B))","(sig n N B)",false);
    
    
    (* tests synthèse application *)
    ("(((: (lambda x (lambda y (y x))) (-> * (-> (-> * *) *))) N) (lambda z z))","*",true);
    ("(: (lambda x (lambda y y)) (-> * (-> * *)))","(-> * (-> * *))",true);
    ("((: (lambda x x) (-> (-> * (-> * *)) (-> * (-> * *)))) (lambda (x y) x))","(-> * (-> * *))",true); 
    ("(:(lambda x (succ x)) (-> N N))","(-> N N)",true);
    ("((: (lambda x (succ x)) (-> N N)) zero)","N",true); 
    ("((: (lambda x (succ x)) (-> * *)) zero)","N",false);  
    ("((: (lambda x N) (-> N *)) zero)","*",true);  
    ("((: (lambda x x) (-> * *)) zero)","N",false);  
    ("((: (lambda x zero) (-> * N)) N)","N",true);
    ("((: (lambda x (lambda y (x y))) (-> (-> N N) (-> N N))) (lambda x (succ x)) zero)","N",true);
    ("((: (lambda x (lambda y (x y))) (-> (-> N N) (-> N N))) (lambda x x) N)","N",false);
    
    (* tests des entiers *)
    ("zero","N",true);
    ("(succ zero)","N",true);
    ("(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x (succ x))) zero)","N",true); 
    ("(succ (succ zero))","N",true);
    ("(iter (lambda x N) (succ zero) (lambda n (lambda x (+ (succ (succ zero)) x))) zero)","N",true);
    ("(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x (mult (succ zero) x))) (succ zero))","N",true);
    ("(+ (succ (succ zero)) (succ zero))","N",true);
    ("(mult (succ (succ zero)) (succ zero))","N",true);
    ("(pow (succ (succ zero)) (succ zero))","N",true);
    ("(lambda m (lambda n (iter (lambda x N) m (lambda x (lambda y (succ y))) n)))","(pi m N (pi n N N))",true);
    ("(lambda m (iter (lambda x (pi n N N)) m (lambda x (lambda y (lambda n (succ (y n))))) (lambda n n)))",
     "(pi m N (pi n N N))",true); 


    ("(succ N)","N",false);
    ("(succ (succ zero))","N",true);
    ("(succ (succ zero))","*",false);
    ("(mult (succ (succ zero)) true)","N",false);
    ("(+ (succ (succ zero)) true)","N",false);
    ("(pow (succ (succ zero)) true)","N",false);
    ("(iter (lambda x N) (succ (succ N)) (lambda n (lambda x (succ x))) zero)","N",false); 

    
    (* tests des booléens *)
    ("B","*",true);
    ("true","B",true);
    ("false","B",true);
    ("true","N",false);
    ("false","N",false);
    ("(ifte (lambda x B) true false true)","B",true);
    ("(ifte (lambda x N) true zero (succ zero))","N",true);

    ("(ifte (lambda x B) true false true)","N",false);
    ("(ifte (lambda x B) zero false true)","B",false);
    ("(ifte (lambda x zero) true false true)","B",false);
    ("(ifte (lambda x B) true false zero)","B",false);
    ("(ifte (lambda x B) true zero false)","B",false);


    (* tests sur les listes *)
    ("(liste N)","*",true);
    ("(liste B)","*",true);
    ("(liste (-> * *))","*",true);
    ("nil","(liste N)",true);
    ("(cons zero nil)","(liste N)",true);
    ("(cons true nil)","(liste B)",true);
    ("(cons zero (cons (succ zero) nil))","(liste N)",true);
    ("(cons zero (cons zero nil))","(liste N)",true);    
    ("(cons (succ zero) (cons (succ zero) nil))","(liste N)",true);
    ("(fold (lambda y N) N nil (lambda a (lambda xs (lambda no zero))) zero)","N",true);
    ("(fold (lambda y N) N (cons (succ zero) (cons (succ zero) nil)) (lambda a (lambda xs (lambda no (+ a no)))) zero)","N",true);
    ("(fold (lambda y N) N (cons zero (cons zero (cons zero nil))) (lambda a (lambda xs (lambda no (+ (succ zero) no)))) zero)", 
     "N",true); 


    ("(liste zero)","*",false);
    ("(liste N)","N",false);
    ("(cons true nil)","(liste N)",false);
    ("(cons zero nil)","(liste B)",false);
    ("(cons zero N)","(liste N)",false);
    ("(cons zero (cons true nil))","(liste N)",false);    
    ("(fold (lambda y B) N (cons (succ zero) (cons (succ zero) nil)) (lambda a (lambda xs (lambda no (+ a no)))) zero)","N",false);
    ("(fold (lambda y N) B (cons (succ zero) (cons (succ zero) nil)) (lambda a (lambda xs (lambda no (+ a no)))) zero)","N",false);
    ("(fold (lambda y N) N (cons (succ zero) (cons (succ zero) nil)) (lambda a (lambda xs (lambda no (+ a no)))) true)","N",false);
    ("(fold (lambda y N) N (cons (succ zero) (cons (succ zero) nil)) (lambda a (lambda xs (lambda no (+ a no)))) true)","N",false);  
    
    

    


    (test1y,"*",true);
    (testcheck4x,"*",true); 

    (eq, "(pi A * (-> A (-> A *)))",true); 

    ("(vec N (succ (succ zero)))","*",true);
    ("(dnil N)","(vec N zero)",true);			      
    ("(dnil zero)","(vec N zero)",false);
    ("(dnil N)","(vec N (succ zero))",false);
    ("(dcons zero (dnil N))","(vec N (succ zero))",true);	  
    ("(dcons zero (dcons zero (dnil N)))","(vec N (succ (succ zero)))",true);
    ("(dcons zero (dcons zero (dnil N)))","(vec N (succ zero))",false);
    ("(dcons zero (dcons zero (dcons zero (dnil N))))","(vec B (succ (succ (succ zero))))",false);
    ("(dcons zero (dnil N))","(vec N (succ (succ zero)))",false);
    ("(dcons zero (dcons zero (dcons zero (dnil N))))","(vec N (succ (succ zero)))",false);
    ("(lambda x (? lol))","(-> * *)",true);
    ("(lambda x (lambda y (? lol)))","(-> * (-> * *))",true);
    ("(lambda x (lambda y (? lol)))","(-> * *)",false);
    
    ("(id N zero (succ zero))","*",true);
   ("(refl zero)","(id N zero zero)",true);				
   ("(+ (succ (succ zero)) (succ (succ zero)))","N",true);
   ("(dfold N (lambda n (lambda xs N)) (succ zero) (dcons zero (dnil N)) (lambda n (lambda xs (lambda a (lambda x (succ a))))) zero)","N",true); 
   ("(dfold N (lambda n (lambda xs N)) (succ zero) (dcons zero (dnil N)) (lambda n (lambda xs (lambda a (lambda x (+ a x))))) zero)","N",true);			   ("(dfold N (lambda n (lambda xs N)) (succ (succ zero)) (dcons (succ zero) (dcons (succ (succ zero)) (dnil N))) (lambda n (lambda xs (lambda a (lambda x (+ a x))))) zero)","N",true);										
   ("(dfold N (lambda n (lambda xs N)) (succ (succ zero)) (dcons zero (dnil N)) (lambda n (lambda xs (lambda a (lambda x (+ a x))))) zero)","N",false);
   ("(refl (succ (succ (succ (succ zero)))))","(id N (+ (succ (succ zero)) (succ (succ zero))) (succ (succ (succ (succ zero)))))",true);
   ("(refl (succ (succ (succ zero))))","(id N (+ (succ (succ zero)) (succ (succ zero))) (succ (succ (succ zero))))",false);
   (* ("(lambda (A a b q) (trans A (lambda (a b q) (id A b a)) a b q (lambda a (refl a))))", "(pi A * (pi a A (pi b A (-> (id A a b) (id A b a)))))", true); *)
(* 
    ("(list N)","*",true);
    ("(nil N)","(list N)",true);
    ("(cons N zero (nil N))","(list N)",true);
    ("(cons N zero (nil *))","(list N)",false);
    ("(cons * zero (nil N))","(list N)",false); *)  
  ]

(* let () = Printf.printf "%s" (print_report (check [] (read "(dfold N (lambda n (lambda xs N)) (dcons zero (dnil N)) 
	    (lambda n (lambda xs (lambda a a))) zero)") VNat "")) *)
    
let tests = List.map (fun (term,chek, res) -> term >:: fun ctxt -> assert_equal (res_debug(check [] (read term) (big_step_eval_inTm (read chek) []) "")) res) inputs 

(* let ltests = List.map (fun (term,chek,res) -> term >:: fun ctxt -> assert_equal (lcheck [] (big_step_eval_inTm (read chek) []) (read term)) res) inputs *)
