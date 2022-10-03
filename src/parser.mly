%{
%}

(* Infix operations a la OCaml *)
%token <Name.ident Location.located> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4

(* Names *)
%token <Name.ident> NAME
%token UNDERSCORE

(* Parentheses & punctuations *)
%token LPAREN RPAREN PERIOD
%token COLONEQ
%token COMMA COLON DARROW ARROW

(* Expressions *)
%token TYPE
%token PROD
%token LAMBDA

%token NAT
%token ZERO
%token SUCC
%token <int> NUMERAL
%token IND
%token EMPTY
%token IND_EMPTY
%token IDENTITY
%token EQUALS
%token REFL
%token IND_ID

(* Toplevel commands *)

%token <string> QUOTED_STRING
%token LOAD
%token DEFINITION
%token CHECK
%token EVAL
%token AXIOM

(* End of input token *)
%token EOF

(* Precedence and fixity of infix operators *)
%left     INFIXOP0
%right    INFIXOP1
%left     INFIXOP2
%left     INFIXOP3
%right    INFIXOP4

%start <Input.toplevel list> file
%start <Input.toplevel> commandline

%%

(* Toplevel syntax *)

file:
  | f=filecontents EOF            { f }

filecontents:
  |                                   { [] }
  | d=topcomp PERIOD ds=filecontents  { d :: ds }

commandline:
  | topcomp PERIOD EOF       { $1 }
  | top_level_term           { $1 }

top_level_term: mark_location(plain_level_top_term) { $1 }
plain_level_top_term: e=term EOF { Input.TopEval e }

(* Things that can be defined on toplevel. *)
topcomp: mark_location(plain_topcomp) { $1 }
plain_topcomp:
  | LOAD fn=QUOTED_STRING                { Input.TopLoad fn }
  | DEFINITION x=var_name COLONEQ e=term { Input.TopDefinition (x, e) }
  | CHECK e=term                         { Input.TopCheck e }
  | EVAL e=term                          { Input.TopEval e }
  | AXIOM x=var_name COLON e=term        { Input.TopAxiom (x, e) }

(* Main syntax tree *)
term : mark_location(plain_term) { $1 }
plain_term:
  | e=plain_equals_term                             { e }
  | PROD a=prod_abstraction COMMA e=term           { Input.Prod (a, e) }
  | e1=equals_term ARROW e2=term                   { Input.Arrow (e1, e2) }
  | LAMBDA a=lambda_abstraction DARROW e=term      { Input.Lambda (a, e) }
  | e=equals_term COLON t=term                     { Input.Ascribe (e, t) }
  | IDENTITY LPAREN e1=term COMMA e2=term RPAREN   { Input.Identity (e1, e2) }

equals_term: mark_location(plain_equals_term) { $1 }
plain_equals_term:
    | e=plain_infix_term { e }
    | e1=infix_term EQUALS e2=infix_term       { Input.Identity (e1, e2) }

infix_term: mark_location(plain_infix_term) { $1 }
plain_infix_term:
  | e=plain_app_term { e }
  | e2=infix_term oploc=infix e3=infix_term
    { let {Location.data=op; loc} = oploc in
      let op = Location.locate ~loc (Input.Var op) in
      let e1 = Location.locate ~loc (Input.Apply (op, e2)) in
      Input.Apply (e1, e3)
    }

app_term: mark_location(plain_app_term) { $1 }
plain_app_term:
  | e=plain_prefix_term          { e }
  | SUCC e=prefix_term           { Input.Succ e }
  | REFL e=prefix_term           { Input.Refl e }
  | IND_EMPTY LPAREN e1=term COMMA e2=term RPAREN   { Input.IndEmpty (e1, e2) }
  | IND LPAREN e1=term COMMA e2=term COMMA e3=term COMMA e4=term RPAREN
     { Input.IndNat (e1, e2, e3, e4) }
  | IND_ID LPAREN e1=term COMMA e2=term COMMA e3=term RPAREN
     { Input.IndId (e1, e2, e3) }
  | e1=app_term e2=prefix_term   { Input.Apply (e1, e2) }

prefix_term: mark_location(plain_prefix_term) { $1 }
plain_prefix_term:
  | e=plain_simple_term                       { e }
  | oploc=prefix e2=prefix_term
    { let {Location.data=op; loc} = oploc in
      let op = Location.locate ~loc (Input.Var op) in
      Input.Apply (op, e2)
    }

(* simple_term : mark_location(plain_simple_term) { $1 } *)
plain_simple_term:
  | LPAREN e=plain_term RPAREN         { e }
  | TYPE                               { Input.Type }
  | NAT                                { Input.Nat }
  | ZERO                               { Input.Zero }
  | EMPTY                              { Input.Empty }
  | NUMERAL                            { Input.Numeral $1 }
  | x=var_name                         { Input.Var x }

var_name:
  | NAME                     { $1 }
  | LPAREN op=infix RPAREN   { op.Location.data }
  | LPAREN op=prefix RPAREN  { op.Location.data }
  | UNDERSCORE               { Name.anonymous () }

%inline infix:
  | op=INFIXOP0    { op }
  | op=INFIXOP1    { op }
  | op=INFIXOP2    { op }
  | op=INFIXOP3    { op }
  | op=INFIXOP4    { op }

%inline prefix:
  | op=PREFIXOP { op }

lambda_abstraction:
  | xs=nonempty_list(var_name) COLON t=term  { [(xs, Some t)] }
  | xs=nonempty_list(var_name)               { [(xs, None)] }
  | lst=nonempty_list(typed_binder)          { List.map (fun (xs, t) -> (xs, Some t)) lst }

prod_abstraction:
  | xs=nonempty_list(var_name) COLON t=term  { [(xs, t)] }
  | lst=nonempty_list(typed_binder)          { lst }

typed_binder:
  | LPAREN xs=nonempty_list(var_name) COLON t=term RPAREN { (xs, t) }

mark_location(X):
  x=X
  { Location.locate ~loc:(Location.make $startpos $endpos) x }
%%
