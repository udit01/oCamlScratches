%{
  open Syntax
%}

%token <string>VAR
%token <string>CONST
%token IF
%token COMMA
%token TRUE
%token FAIL
%token CUT
%token PERIOD
%token LPAREN RPAREN
%token GOAL
%token EOF

%start file
%start expr
%type <Syntax.toplevel_cmd list> file
%type <Syntax.toplevel_cmd> expr

%%

file:
  | EOF                      { [] }
  | expr file                { $1 :: $2 }

expr:
  | goal      { $1 }
  | assertion { $1 }

goal:
  | GOAL clause PERIOD        { Goal $2 }

assertion:
  | atom PERIOD               { Assert ($1, []) }
  | atom IF clause PERIOD     { Assert ($1, $3) }

atom:
  | FAIL                      { Fail }
  | CUT                       { Cut }
  | CONST                     { Atom ($1, []) }
  | CONST LPAREN args RPAREN  { Atom ($1, $3) }

clause:
  | TRUE                      { [] }
  | atom                      { [$1] }
  | atom COMMA clause         { $1 :: $3 }

args:
  | literal            { [$1] }
  | literal COMMA args { $1 :: $3 }

literal:
  | CONST                    { Const $1 }
  | VAR                      { Var ($1, 0) }
  | CONST LPAREN args RPAREN { App ($1, $3) }


%%
