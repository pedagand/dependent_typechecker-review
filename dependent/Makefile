all : lambda_calcul

lambda_calcul: lambda.ml
	ocamlbuild -use-ocamlfind lambda.native

nat: nat.ml
	ocamlbuild -use-ocamlfind nat.native

test.native: test.ml
	ocamlbuild -use-ocamlfind test.native

interface.native: interface.ml
	ocamlbuild -use-ocamlfind interface.native

tactics.native: tactics.ml
	ocamlbuild -use-ocamlfind tactics.native

serveur.native: serveur.ml
	ocamlbuild -use-ocamlfind serveur.native
clean: 
	ocamlbuild -clean
