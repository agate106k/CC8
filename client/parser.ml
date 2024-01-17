type token =
  | NUM of (int)
  | STR of (string)
  | ID of (string)
  | INT
  | IF
  | WHILE
  | SPRINT
  | IPRINT
  | SCAN
  | EQ
  | NEQ
  | GT
  | LT
  | GE
  | LE
  | ELSE
  | RETURN
  | NEW
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | LB
  | RB
  | LS
  | RS
  | LP
  | RP
  | ASSIGN
  | SEMI
  | COMMA
  | TYPE
  | VOID
  | ERROR

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"

open Printf
open Ast

# 45 "parser.ml"
let yytransl_const = [|
  260 (* INT *);
  261 (* IF *);
  262 (* WHILE *);
  263 (* SPRINT *);
  264 (* IPRINT *);
  265 (* SCAN *);
  266 (* EQ *);
  267 (* NEQ *);
  268 (* GT *);
  269 (* LT *);
  270 (* GE *);
  271 (* LE *);
  272 (* ELSE *);
  273 (* RETURN *);
  274 (* NEW *);
  275 (* PLUS *);
  276 (* MINUS *);
  277 (* TIMES *);
  278 (* DIV *);
  279 (* LB *);
  280 (* RB *);
  281 (* LS *);
  282 (* RS *);
  283 (* LP *);
  284 (* RP *);
  285 (* ASSIGN *);
  286 (* SEMI *);
  287 (* COMMA *);
  288 (* TYPE *);
  289 (* VOID *);
  290 (* ERROR *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* STR *);
  259 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\003\000\004\000\004\000\005\000\005\000\
\005\000\005\000\006\000\006\000\007\000\007\000\009\000\009\000\
\010\000\010\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\013\000\013\000\014\000\014\000\008\000\011\000\011\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\012\000\
\012\000\012\000\012\000\012\000\012\000\000\000"

let yylen = "\002\000\
\001\000\001\000\004\000\001\000\002\000\000\000\003\000\005\000\
\006\000\006\000\003\000\001\000\000\000\001\000\004\000\002\000\
\002\000\001\000\004\000\007\000\002\000\005\000\007\000\005\000\
\005\000\005\000\005\000\005\000\005\000\003\000\001\000\001\000\
\000\000\001\000\003\000\001\000\004\000\001\000\001\000\004\000\
\004\000\003\000\003\000\003\000\003\000\002\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\006\000\032\000\054\000\001\000\031\000\
\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\038\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\046\000\000\000\000\000\
\000\000\000\000\000\000\030\000\000\000\000\000\000\000\000\000\
\000\000\018\000\000\000\005\000\000\000\000\000\000\000\000\000\
\019\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\047\000\000\000\
\000\000\044\000\045\000\000\000\000\000\000\000\000\000\000\000\
\000\000\037\000\017\000\000\000\029\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\024\000\025\000\026\000\
\027\000\041\000\040\000\028\000\000\000\000\000\000\000\000\000\
\007\000\000\000\000\000\000\000\003\000\004\000\000\000\000\000\
\000\000\000\000\000\000\011\000\020\000\023\000\008\000\016\000\
\000\000\000\000\000\000\010\000\000\000\009\000\015\000"

let yydgoto = "\002\000\
\014\000\015\000\120\000\032\000\060\000\089\000\121\000\016\000\
\122\000\061\000\034\000\039\000\035\000\036\000"

let yysindex = "\004\000\
\102\255\000\000\241\254\048\255\248\254\011\255\031\255\041\255\
\047\255\032\255\060\255\000\000\000\000\000\000\000\000\000\000\
\000\000\032\255\032\255\032\255\032\255\032\255\026\255\032\255\
\058\255\000\000\014\255\032\255\032\255\050\255\098\255\004\255\
\070\255\034\255\090\255\108\255\093\255\182\255\096\255\112\255\
\113\255\029\255\115\255\032\255\032\255\000\000\190\255\032\255\
\032\255\032\255\032\255\000\000\117\255\048\255\129\255\152\255\
\153\255\000\000\156\255\000\000\076\255\136\255\146\255\032\255\
\000\000\032\255\032\255\032\255\032\255\032\255\032\255\102\255\
\102\255\147\255\148\255\151\255\141\255\154\255\000\000\082\255\
\082\255\000\000\000\000\155\255\183\255\158\255\162\255\171\255\
\086\255\000\000\000\000\032\255\000\000\034\255\034\255\034\255\
\034\255\034\255\034\255\034\255\167\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\173\255\118\255\118\255\118\255\
\000\000\197\255\186\255\102\255\000\000\000\000\184\255\210\255\
\187\255\188\255\189\255\000\000\000\000\000\000\000\000\000\000\
\198\255\118\255\198\255\000\000\217\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\194\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\116\255\000\000\000\000\000\000\000\000\000\000\
\000\000\251\254\000\000\195\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\194\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\221\255\000\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\138\255\
\160\255\000\000\000\000\000\000\000\000\000\000\000\000\103\255\
\000\000\000\000\000\000\000\000\000\000\001\255\199\255\200\255\
\201\255\202\255\203\255\204\255\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\205\255\205\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\206\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\226\255\224\255\000\000\000\000\000\000\113\000\222\255\
\000\000\000\000\252\255\204\000\190\000\000\000"

let yytablesize = 287
let yytable = "\059\000\
\022\000\058\000\002\000\003\000\001\000\030\000\054\000\055\000\
\005\000\006\000\007\000\008\000\009\000\033\000\017\000\037\000\
\038\000\038\000\021\000\042\000\010\000\011\000\036\000\046\000\
\047\000\036\000\012\000\041\000\035\000\002\000\091\000\035\000\
\026\000\013\000\027\000\056\000\057\000\022\000\044\000\077\000\
\045\000\101\000\102\000\080\000\081\000\082\000\083\000\048\000\
\049\000\050\000\051\000\028\000\048\000\049\000\050\000\051\000\
\075\000\023\000\029\000\094\000\043\000\095\000\096\000\097\000\
\098\000\099\000\100\000\024\000\048\000\049\000\050\000\051\000\
\018\000\025\000\019\000\003\000\020\000\119\000\004\000\052\000\
\005\000\006\000\007\000\008\000\009\000\126\000\031\000\115\000\
\048\000\049\000\050\000\051\000\010\000\011\000\132\000\062\000\
\134\000\133\000\012\000\090\000\053\000\003\000\050\000\051\000\
\004\000\013\000\005\000\006\000\007\000\008\000\009\000\048\000\
\049\000\050\000\051\000\113\000\114\000\063\000\010\000\011\000\
\118\000\055\000\065\000\072\000\012\000\039\000\039\000\039\000\
\039\000\039\000\039\000\013\000\012\000\012\000\039\000\039\000\
\039\000\039\000\064\000\073\000\074\000\039\000\076\000\039\000\
\084\000\039\000\039\000\042\000\042\000\042\000\042\000\042\000\
\042\000\085\000\086\000\087\000\042\000\042\000\088\000\048\000\
\049\000\050\000\051\000\042\000\092\000\042\000\106\000\042\000\
\042\000\043\000\043\000\043\000\043\000\043\000\043\000\093\000\
\103\000\104\000\043\000\043\000\105\000\107\000\116\000\109\000\
\108\000\043\000\110\000\043\000\111\000\043\000\043\000\066\000\
\067\000\068\000\069\000\070\000\071\000\112\000\117\000\124\000\
\048\000\049\000\050\000\051\000\048\000\049\000\050\000\051\000\
\048\000\049\000\050\000\051\000\128\000\127\000\129\000\125\000\
\131\000\079\000\130\000\135\000\012\000\033\000\034\000\004\000\
\123\000\040\000\048\000\049\000\050\000\051\000\052\000\053\000\
\013\000\014\000\078\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\022\000\000\000\000\000\022\000\000\000\022\000\022\000\022\000\
\022\000\022\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\022\000\022\000\000\000\000\000\000\000\000\000\022\000\
\022\000\000\000\000\000\000\000\000\000\000\000\022\000"

let yycheck = "\032\000\
\000\000\032\000\003\001\000\001\001\000\010\000\003\001\004\001\
\005\001\006\001\007\001\008\001\009\001\018\000\030\001\020\000\
\021\000\022\000\027\001\024\000\017\001\018\001\028\001\028\000\
\029\000\031\001\023\001\002\001\028\001\030\001\061\000\031\001\
\001\001\030\001\003\001\032\001\033\001\027\001\025\001\044\000\
\027\001\072\000\073\000\048\000\049\000\050\000\051\000\019\001\
\020\001\021\001\022\001\020\001\019\001\020\001\021\001\022\001\
\028\001\027\001\027\001\064\000\003\001\066\000\067\000\068\000\
\069\000\070\000\071\000\027\001\019\001\020\001\021\001\022\001\
\025\001\027\001\027\001\000\001\029\001\110\000\003\001\030\001\
\005\001\006\001\007\001\008\001\009\001\116\000\027\001\092\000\
\019\001\020\001\021\001\022\001\017\001\018\001\129\000\026\001\
\131\000\130\000\023\001\024\001\003\001\000\001\021\001\022\001\
\003\001\030\001\005\001\006\001\007\001\008\001\009\001\019\001\
\020\001\021\001\022\001\030\001\031\001\028\001\017\001\018\001\
\003\001\004\001\030\001\028\001\023\001\010\001\011\001\012\001\
\013\001\014\001\015\001\030\001\030\001\031\001\019\001\020\001\
\021\001\022\001\031\001\028\001\028\001\026\001\028\001\028\001\
\028\001\030\001\031\001\010\001\011\001\012\001\013\001\014\001\
\015\001\025\001\003\001\003\001\019\001\020\001\003\001\019\001\
\020\001\021\001\022\001\026\001\029\001\028\001\026\001\030\001\
\031\001\010\001\011\001\012\001\013\001\014\001\015\001\030\001\
\030\001\030\001\019\001\020\001\030\001\028\001\016\001\001\001\
\030\001\026\001\029\001\028\001\027\001\030\001\031\001\010\001\
\011\001\012\001\013\001\014\001\015\001\027\001\026\001\003\001\
\019\001\020\001\021\001\022\001\019\001\020\001\021\001\022\001\
\019\001\020\001\021\001\022\001\003\001\030\001\028\001\030\001\
\028\001\028\001\031\001\003\001\023\001\028\001\028\001\003\001\
\112\000\022\000\028\001\028\001\028\001\028\001\028\001\028\001\
\028\001\028\001\045\000\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\000\001\255\255\255\255\003\001\255\255\005\001\006\001\007\001\
\008\001\009\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\017\001\018\001\255\255\255\255\255\255\255\255\023\001\
\024\001\255\255\255\255\255\255\255\255\255\255\030\001"

let yynames_const = "\
  INT\000\
  IF\000\
  WHILE\000\
  SPRINT\000\
  IPRINT\000\
  SCAN\000\
  EQ\000\
  NEQ\000\
  GT\000\
  LT\000\
  GE\000\
  LE\000\
  ELSE\000\
  RETURN\000\
  NEW\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  LB\000\
  RB\000\
  LS\000\
  RS\000\
  LP\000\
  RP\000\
  ASSIGN\000\
  SEMI\000\
  COMMA\000\
  TYPE\000\
  VOID\000\
  ERROR\000\
  "

let yynames_block = "\
  NUM\000\
  STR\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 27 "parser.mly"
             (  _1  )
# 293 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 30 "parser.mly"
           ( IntTyp )
# 299 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 31 "parser.mly"
                     ( ArrayTyp (_3, IntTyp) )
# 306 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 32 "parser.mly"
               ( NameTyp _1 )
# 313 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 35 "parser.mly"
                ( _1@_2 )
# 321 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 36 "parser.mly"
                ( [] )
# 327 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ids) in
    Obj.repr(
# 39 "parser.mly"
                     ( List.map (fun x -> VarDec (_1,x)) _2 )
# 335 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 40 "parser.mly"
                              ( [TypeDec (_2,_4)] )
# 343 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 41 "parser.mly"
                                    ( [FuncDec(_2, _4, _1, _6)] )
# 353 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 42 "parser.mly"
                                      ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 362 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 45 "parser.mly"
                       ( _1@[_3] )
# 370 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                       ( [_1]  )
# 377 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 49 "parser.mly"
                        ( [] )
# 383 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 50 "parser.mly"
                        ( _1 )
# 390 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 53 "parser.mly"
                             ( _1@[(_3,_4)] )
# 399 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
                             ( [(_1,_2)] )
# 407 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 57 "parser.mly"
                   ( _1@[_2] )
# 415 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 58 "parser.mly"
                   ( [_1] )
# 422 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 61 "parser.mly"
                              ( Assign (Var _1, _3) )
# 430 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                                       ( Assign (IndexedVar (Var _1, _3), _6) )
# 439 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 63 "parser.mly"
                  ( print_endline "Syntax error"; Parsing.yyparse () )
# 445 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 64 "parser.mly"
                              ( If (_3, _5, None) )
# 453 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 66 "parser.mly"
                              ( If (_3, _5, Some _7) )
# 462 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 67 "parser.mly"
                              ( While (_3, _5) )
# 470 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 68 "parser.mly"
                              ( CallProc ("sprint", [StrExp _3]) )
# 477 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 69 "parser.mly"
                              ( CallProc ("iprint", [_3]) )
# 484 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 70 "parser.mly"
                           ( CallProc ("scan", [VarExp (Var _3)]) )
# 491 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 71 "parser.mly"
                           ( CallProc ("new", [ VarExp (Var _3)]) )
# 498 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 72 "parser.mly"
                                ( CallProc (_1, _3) )
# 506 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 73 "parser.mly"
                           ( CallProc ("return", [_2]) )
# 513 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 74 "parser.mly"
             ( _1 )
# 520 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
            ( NilStmt )
# 526 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
                           ( [] )
# 532 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 79 "parser.mly"
                           ( _1 )
# 539 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 82 "parser.mly"
                          ( _1@[_3] )
# 547 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                           ( [_1] )
# 554 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 86 "parser.mly"
                         ( Block (_2, _3) )
# 562 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 89 "parser.mly"
           ( IntExp _1  )
# 569 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 90 "parser.mly"
          ( VarExp (Var _1) )
# 576 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 91 "parser.mly"
                          ( CallFunc (_1, _3) )
# 584 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 92 "parser.mly"
                      ( VarExp (IndexedVar (Var _1, _3)) )
# 592 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                      ( CallFunc ("+", [_1; _3]) )
# 600 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                       ( CallFunc ("-", [_1; _3]) )
# 608 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                       ( CallFunc ("*", [_1; _3]) )
# 616 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                     ( CallFunc ("/", [_1; _3]) )
# 624 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                               ( CallFunc("!", [_2]) )
# 631 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                   ( _2 )
# 638 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 101 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 646 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 102 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 654 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 103 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 662 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 104 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 670 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 678 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 686 "parser.ml"
               : 'cond))
(* Entry prog *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.stmt)
;;
