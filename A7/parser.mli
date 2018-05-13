type token =
  | VAR of (string)
  | CONST of (string)
  | IF
  | COMMA
  | TRUE
  | FAIL
  | CUT
  | PERIOD
  | LPAREN
  | RPAREN
  | GOAL
  | EOF

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.toplevel_cmd list
val expr :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.toplevel_cmd
