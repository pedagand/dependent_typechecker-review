open OUnit2
open Lambda


(* let test1x = (Pi("A",(Star,(Pi "B",(Pi "x", (Inv(Var(Bound 0)),Star)),Pi("C",(Pi ("x", (Inv(Var(Bound 1)),Star)), (Pi "1",(Pi "2", (Pi("a",(Star,Pi("b",(Inv(Appl(Var(Bound 2) ,Inv(Var(Bound 1))))),Inv(Appl(Var(Bound 2), Inv(Var(Bound 1))))))),(Pi ("a",(Inv(Var(Bound 3)),Inv(Appl(Var(Bound 3),Inv(Var(Bound 0)))))))),(Pi ("a",(Inv(Var(Bound 3)),Inv(Appl(Var(Bound 2),Inv(Var(Bound 0))))))))))))))) *)

let test1y = "(pi A * (pi B (pi x A *) (pi C (pi x A *) (pi 1 (pi 2 (pi a * (pi b (B a) (C a))) (pi a A (B a))) (pi a A (C a))))))"

let inputs
    = [("(lambda x x)", Abs("x",Inv(Var(Bound 0))));
       ("(lambda x y)", Abs("x",Inv(Var(Global("y")))));
       ("(x y z)", 
	Inv(Appl(Appl(Var(Global"x"), Inv(Var (Global "y"))), Inv(Var (Global "z")))));
       ("(lambda (x y z) (x (y z)))", Abs("x",(Abs("y",(Abs("z",(Inv(Appl(Var(Bound 2), Inv(Appl(Var(Bound 1), Inv(Var(Bound 0)))))))))))));
       ("(lambda (x y z) (x y z))", Abs("x",Abs("y",Abs("z",Inv(Appl (Appl (Var(Bound 2), Inv(Var(Bound 1))), Inv(Var(Bound 0))))))));
       ("(: (lambda x x) (-> N N))",Inv(Ann(Abs("x",Inv(Var(Bound 0))),Pi("NO",(Nat,Nat)))));
       ("((: (lambda x x) *) y)", Inv(Appl(Ann(Abs("x",Inv(Var(Bound 0))),Star),Inv(Var (Global "y")))));
       ("((: (lambda x x) (-> N N)) y)",Inv(Appl(Ann(Abs("x",Inv(Var(Bound 0))),Pi("NO",(Nat,Nat))),Inv(Var (Global "y")))));
       ("(pi x * *)",Pi("x",(Star,Star)));
       ("(pi x (pi y * *) *)", Pi("x",(Pi("y",(Star,Star)),Star)));
       ("(pi (x y z) * (lambda w w))",Pi("x",(Star,Pi("y",(Star,Pi("z",(Star,Abs("w",Inv(Var(Bound 0))))))))));
       ("(pi A * (pi B (pi x A *) *))",Pi("A",(Star,Pi("B",(Pi ("x" ,(Inv(Var(Bound 0)), Star)),Star)))));
       ("(pi x * (pi y N (vec x (succ zero))))",Pi("x",(Star,Pi("y",(Nat,Vec(Inv(Var(Bound 1)),Succ(Zero)))))));
       ("(pi x * (pi y N (vec x y)))",Pi("x",(Star,Pi("y",(Nat,Vec(Inv(Var(Bound 1)),Inv(Var(Bound 0))))))));
       ("(-> * *)",Pi("NO",(Star,Star)));
       ("(succ (succ zero))",Succ(Succ(Zero)));
       ("(: (succ zero) N)",Inv(Ann(Succ(Zero),Nat)));
       ("(iter N N N N)",Inv(Iter(Nat,Nat,Nat,Nat)));
       ("(iter (lambda x N) (succ (succ zero)) (lambda n (lambda x (succ x))) zero)",Inv(Iter(Abs("x",Nat),Succ(Succ Zero),Abs("n",Abs("x",Succ (Inv (Var(Bound 0))))),Zero)));
       ("(pi P (-> A *) (-> (P a) (P b)))", 
	Pi("P",((Pi("NO",(Inv(Var(Global "A")),Star))),Pi("NO",(Inv(Appl(Var(Bound 0),Inv(Var (Global"a")))),Inv(Appl(Var(Bound 1),Inv(Var (Global"b")))))))));
       ("(sig x N N)",Sig("x",(Nat,Nat)));
       ("(sig x N x)",Sig("x",(Nat,Inv(Var(Bound 0)))));
       ("(p0 (: (true , false) (sig n B B)))",Inv(P0(Ann(Pair(True,False),Sig("n",(Bool,Bool))))));
       ("(lambda A (lambda a (lambda b (pi P (-> A *) (-> (P a) (P b))))))",
	Abs("A",Abs("a",Abs("b",(Pi("P",((Pi("NO",(Inv(Var(Bound 2)),Star))),Pi("NO",(Inv(Appl(Var(Bound 0),Inv(Var(Bound 2)))),Inv(Appl(Var(Bound 1),Inv(Var(Bound 2)))))))))))));
       ("(a , b)",Pair(Inv(Var (Global "a")),Inv(Var (Global"b"))));
       ("((p1 x2) , (succ (p1 x2)))",Pair(Inv(P1(Var(Global"x2"))),Succ(Inv(P1(Var(Global"x2"))))));
       ("(iter (lambda x x) zero (lambda x (succ x)) zero)",
	Inv(Iter(Abs("x",Inv(Var(Bound 0))),Zero,Abs("x",Succ(Inv(Var(Bound 0)))),Zero)));
       ("B",Bool);
       ("true",True);
       ("false",False);
       ("(ifte (lambda x B) true true false)",Inv(Ifte(Abs("x",Bool),True,True,False))); 
       ("(liste N)",Liste(Nat));
       ("nil", Nil);
       ("(cons zero nil)",(Cons(Zero,Nil)));
       ("(vec N (succ zero))",Vec(Nat,Succ(Zero)));
       ("(dnil N)",DNil(Nat));
       ("(dcons zero (dnil N))",DCons(Zero,DNil(Nat)));
       ("(dfold alpha P m xs f a)",Inv(DFold(Inv(Var(Global "alpha")),Inv(Var(Global "P")),Inv(Var(Global "m")),Inv(Var(Global "xs")),Inv(Var(Global "f")),Inv(Var(Global "a")))));
       ("(id N zero (succ zero))", Id(Nat,Zero,Succ(Zero)));
       ("refl",Refl);
       ("(trans N N N N N N)",Inv(Transp(Nat,Nat,Nat,Nat,Nat,Nat)));
(*        ("(pi A * (pi a A (pi b A (-> (id A a b) (id A b a)))))", Nat);
       ("(lambda (A a b q) (trans A (lambda (a b q) (id A b a)) a b q (lambda a (refl a))))", Nat); *)
       ("(+ (succ (succ zero)) (succ (succ zero)))", Inv(Appl(Appl(Ann((read "(lambda n_plus (lambda a_plus (iter (lambda x_plus N) n_plus (lambda ni_plus (lambda x_plus (succ x_plus))) a_plus)))"),(read "(-> N (-> N N))")),(Succ(Succ Zero))),(Succ(Succ Zero)))));
       ("(mult (succ (succ zero)) (succ (succ zero)))", Inv(Appl(Appl(Ann((read "(lambda n_plus (lambda a_plus (iter (lambda x_plus N) n_plus (lambda ni_plus (lambda x_plus (+ a_plus x_plus))) zero)))"),(read "(-> N (-> N N))")),(Succ(Succ Zero))),(Succ(Succ Zero)))));
       ("(pow (succ (succ zero)) (succ (succ zero)))", Inv(Appl(Appl(Ann((read "(lambda n_plus (lambda a_plus (iter (lambda x_plus N) a_plus (lambda ni_plus (lambda x_plus (mult n_plus x_plus))) (succ zero))))"),(read "(-> N (-> N N))")),(Succ(Succ Zero))),(Succ(Succ Zero)))));
       ("(number 5)",(Succ(Succ(Succ(Succ(Succ(Zero)))))));
       ("(number 0)",Zero);
       ("(number 7)",(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero)))))))));
       ("(lambda x (lambda y (lambda x x)))",(Abs("x",Abs("y",Abs("x",Inv(Var(Bound 0)))))))
      (* ( (pretty_print_inTm test1x []),(test1x)); *)
      (* (test1y),(test1x) ;*)]
	



let tests
    = List.map (fun (term, res) -> term >:: fun ctxt -> assert_equal ~printer:(fun a -> pretty_print_inTm a []) (read term) res) inputs

