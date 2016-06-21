open OUnit2
open Sexplib
open Lambda
 

(* We compare pretty-printed strings based on the tokens (ignoring spacing) *)
let compare_term a b = 
  Sexp.of_string a = Sexp.of_string b


let inputs = 
  [ ((Abs(Global"x",Inv(BVar 0))),"(lambda x x)");
    ((Abs(Global "x",Abs(Global "y",Abs(Global "z",Inv(Appl(BVar 2, Inv(Appl(BVar 1, Inv(BVar 0))))))))),"(lambda x (lambda y (lambda z (x (y z)))))");
    ((Inv(Ann(Abs(Global "x",Inv(BVar 0)),Pi(Global "x",Star,Star)))),"(: (lambda x x) (pi x * *))");
    ((Pi(Global "x",Star,Pi(Global "y",Star,Pi(Global "z",Star,Star)))),
     "(pi x * (pi y * (pi z * *)))");
    ((Succ(Succ(Zero))),"(succ (succ zero))");
    ((Inv(Iter(Nat,Nat,Nat,Nat))),"(iter N N N N)");
    ((Pair(Inv(FVar (Global "x")),Inv(FVar (Global "y")))),"(x , y)");
    (Sig(Global "x",Nat,Nat),"(sig x N N)");
    (Sig(Global "x",Nat,Inv(BVar 0)),"(sig x N x)");
    (Cons(Zero,Nil(Nat)),"(cons zero (nil N))");
    (Liste(Nat),"(liste N)");
    (Nil(Nat),"(nil N)");
    (Inv(DFold(Inv(FVar(Global "alpha")),Inv(FVar(Global "P")),Inv(FVar(Global "m")),Inv(FVar(Global "xs")),Inv(FVar(Global "f")),Inv(FVar(Global "a")))),"(dfold alpha P m xs f a)");
    (DCons(Zero,DNil(Nat)),"(dcons zero (dnil N))");
    (DNil(Nat),"(dnil N)");
    (Inv(DFold(Nat,Nat,Nat,Nat,Nat,Nat)),"(dfold N N N N N N)");
    (Vec(Nat,Succ(Zero)),"(vec N (succ zero))");
    (What("lol"),"(? lol)");
    (Abs(Global"x",What("lol")),"(lambda x (? lol))");
    (Id(Nat,Zero,Succ(Zero)),"(id N zero (succ zero))");
    (Refl(Zero),"(refl zero)");
    (Inv(Trans(Nat,Nat,Nat,Nat,Nat,Nat)),"(trans N N N N N N)");
    (Bool,"B");
    (True,"true");
    (False,"false");
    (Inv(Ifte(Abs(Global"x",Bool),True,True,False)),"(ifte (lambda x B) true true false)"); 
  ]

let tests = List.map (fun (term, res) -> "test" >:: fun ctxt -> assert_equal (compare_term (pretty_print_inTm term []) res) true) inputs
