{
  open Parser
  open Lexing

  let incr_lines lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}

let const = ['a'-'z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9']*
let var = ['A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9']*


rule token = parse
    '#' [^'\n']* '\n' { incr_lines lexbuf; token lexbuf }
  | '\n'            { incr_lines lexbuf; token lexbuf }
  | [' ' '\t']      { token lexbuf }
  | "?-"            { GOAL }
  | ":-"            { IF }
  | "true"          { TRUE }
  | "fail"          { FAIL }
  | '!'             { CUT }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ','             { COMMA }
  | '.'             { PERIOD }
  | const           { CONST (lexeme lexbuf) }
  | var             { VAR (lexeme lexbuf) }
  | eof             { EOF }

{
}
