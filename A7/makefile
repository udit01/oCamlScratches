all:
	ocamlc -c syntax.ml
	ocamlc -c unify.ml
	# ocamlc -c solve.ml
	ocamlc -c parser.mli
	ocamlyacc parser.mly
	ocamlc -c parser.ml
	ocamllex lexer.mll
	ocamlc -c lexer.ml
	# ocamlc -c prolog.ml
	# ocamlc -o prolog prolog.cmo  lexer.cmo parser.cmo solve.cmo 
	cp ../prolog prolog
clean:
	rm *.cmo *.cmi *.mli lexer.ml parser.ml
