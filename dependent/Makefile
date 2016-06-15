all : lambda_calcul

lambda_calcul: lambda.ml
	ocamlbuild -use-ocamlfind lambda.native

nat: nat.ml
	ocamlbuild -use-ocamlfind nat.native

test.native: test.ml
	ocamlbuild -use-ocamlfind test.native

interface.native: interface.ml
	ocamlbuild -use-ocamlfind interface.native

clean: 
	ocamlbuild -clean
