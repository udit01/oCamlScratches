type token =
  | LP
  | RP
  | EOL
  | IFF
  | COMMA
  | EOF
  | BOOL of (bool)
  | VAR of (string)
  | ID of (string)

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.clause
