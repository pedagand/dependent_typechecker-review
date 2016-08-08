open OUnit2
open Sexplib
open Lambda
 

(* We compare pretty-printed strings based on the tokens (ignoring spacing) *)
let compare_term a b = 
  Sexp.of_string a = Sexp.of_string b


let inputs = 
  [ ((Abs("x",Inv(Var(Bound 0)))),"(lambda x x)");
    ((Abs("x",Abs("y",Abs("z",Inv(Appl(Var(Bound 2), Inv(Appl(Var(Bound 1), Inv(Var(Bound 0)))))))))),"(lambda x (lambda y (lambda z (x (y z)))))");
    ((Inv(Ann(Abs("x",Inv(Var(Bound 0))),Pi("x",(Star,Star))))),"(: (lambda x x) (pi x * *))");
    ((Pi("x",(Star,Pi("y",(Star,Pi("z",(Star,Star))))))),
     "(pi x * (pi y * (pi z * *)))");
    ((Succ(Succ(Zero))),"(succ (succ zero))");
    ((Inv(Iter(Nat,Nat,Nat,Nat))),"(iter N N N N)");
    ((Pair(Inv(Var (Global "x")),Inv(Var (Global "y")))),"(x , y)");
    ((Pair(Inv(P1(Var(Global"x2"))),Succ(Inv(P1(Var(Global"x2")))))),"((p1 x2) , (succ (p1 x2)))");
    (Sig("x",(Nat,Nat)),"(sig x N N)");
    (Sig("x",(Nat,Inv(Var(Bound 0)))),"(sig x N x)");
    (Cons(Zero,Nil),"(cons zero nil)");
    (Liste(Nat),"(liste N)");
    (Nil,"nil");
    (Inv(DFold(Inv(Var(Global "alpha")),Inv(Var(Global "P")),Inv(Var(Global "m")),Inv(Var(Global "xs")),Inv(Var(Global "f")),Inv(Var(Global "a")))),"(dfold alpha P m xs f a)");
    (DCons(Zero,DNil(Nat)),"(dcons zero (dnil N))");
    (DNil(Nat),"(dnil N)");
    (Inv(DFold(Nat,Nat,Nat,Nat,Nat,Nat)),"(dfold N N N N N N)");
    (Vec(Nat,Succ(Zero)),"(vec N (succ zero))");
    (Id(Nat,Zero,Succ(Zero)),"(id N zero (succ zero))");
    (Refl,"refl");
    (Inv(Transp(Nat,Nat,Nat,Nat,Nat,Nat)),"(trans N N N N N N)");
    (Bool,"B");
    (True,"true");
    (False,"false");
    (Inv(Ifte(Abs("x",Bool),True,True,False)),"(ifte (lambda x B) true true false)"); 
  ]

let tests = List.map (fun (term, res) -> "test" >:: fun ctxt -> assert_equal (compare_term (pretty_print_inTm term []) res) true) inputs
