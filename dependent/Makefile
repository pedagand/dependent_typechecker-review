all : lambda_calcul

lambda_calcul: lambda.ml
	ocamlbuild -use-ocamlfind lambda.native

nat: nat.ml
	ocamlbuild -use-ocamlfind nat.native

test.native: test.ml
	ocamlbuild -use-ocamlfind test.native

interface.native: interface.ml
	ocamlbuild -use-ocamlfind interface.native
	touch reponse_serv.txt 
	echo test > reponse_serv.txt
	chmod 755 reponse_serv.txt

tactics.native: tactics.ml
	ocamlbuild -use-ocamlfind tactics.native

serveur.native: serveur.ml
	ocamlbuild -use-ocamlfind serveur.native

client.native: client.ml
	ocamlbuild -use-ocamlfind client.native
clean: 
	ocamlbuild -clean
	rm reponse_serv.txt 
