#!/bin/sh
ocamllex lexer.mll && \
ocamlyacc parser.mly && \
ocamlc -c syntax.ml && \
ocamlc -c parser.mli && \
ocamlc -c parser.ml && \
ocamlc -c lexer.ml && \
ocamlc -c main.ml && \
ocamlmktop -o prolog.top syntax.cmo parser.cmo lexer.cmo main.cmo