type token =
  | NUM of (int)
  | STR of (string)
  | ID of (string)
  | INT
  | IF
  | WHILE
  | DO
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
  | PERCENT
  | POW
  | INCREMENT
  | PLUS_ASSIGN

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"

open Printf
open Ast

# 49 "parser.ml"
let yytransl_const = [|
  260 (* INT *);
  261 (* IF *);
  262 (* WHILE *);
  263 (* DO *);
  264 (* SPRINT *);
  265 (* IPRINT *);
  266 (* SCAN *);
  267 (* EQ *);
  268 (* NEQ *);
  269 (* GT *);
  270 (* LT *);
  271 (* GE *);
  272 (* LE *);
  273 (* ELSE *);
  274 (* RETURN *);
  275 (* NEW *);
  276 (* PLUS *);
  277 (* MINUS *);
  278 (* TIMES *);
  279 (* DIV *);
  280 (* LB *);
  281 (* RB *);
  282 (* LS *);
  283 (* RS *);
  284 (* LP *);
  285 (* RP *);
  286 (* ASSIGN *);
  287 (* SEMI *);
  288 (* COMMA *);
  289 (* TYPE *);
  290 (* VOID *);
  291 (* PERCENT *);
  292 (* POW *);
  293 (* INCREMENT *);
  294 (* PLUS_ASSIGN *);
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
\002\000\013\000\013\000\014\000\014\000\008\000\011\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\011\000\011\000\012\000\012\000\012\000\012\000\012\000\
\012\000\000\000"

let yylen = "\002\000\
\001\000\001\000\004\000\001\000\002\000\000\000\003\000\005\000\
\006\000\006\000\003\000\001\000\000\000\001\000\004\000\002\000\
\002\000\001\000\004\000\004\000\007\000\005\000\007\000\007\000\
\005\000\005\000\005\000\005\000\005\000\005\000\003\000\001\000\
\001\000\000\000\001\000\003\000\001\000\004\000\001\000\001\000\
\004\000\004\000\003\000\003\000\003\000\003\000\003\000\003\000\
\002\000\002\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\006\000\033\000\058\000\001\000\032\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\039\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\049\000\000\000\000\000\000\000\000\000\000\000\000\000\031\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\018\000\
\000\000\005\000\000\000\000\000\000\000\000\000\019\000\020\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\051\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\038\000\017\000\000\000\030\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\025\000\
\000\000\026\000\027\000\028\000\042\000\041\000\029\000\000\000\
\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\
\003\000\004\000\000\000\000\000\000\000\000\000\000\000\011\000\
\021\000\023\000\024\000\008\000\016\000\000\000\000\000\000\000\
\010\000\000\000\009\000\015\000"

let yydgoto = "\002\000\
\014\000\015\000\132\000\033\000\066\000\099\000\133\000\016\000\
\134\000\067\000\040\000\041\000\036\000\037\000"

let yysindex = "\003\000\
\100\255\000\000\027\255\237\254\254\254\100\255\024\255\026\255\
\032\255\099\255\034\255\000\000\000\000\000\000\000\000\000\000\
\099\255\099\255\099\255\099\255\099\255\099\255\066\255\075\255\
\099\255\072\255\000\000\244\254\099\255\099\255\094\255\090\255\
\025\255\221\255\134\000\065\255\064\255\065\000\071\000\147\255\
\070\255\082\255\085\255\093\255\088\000\097\255\099\255\099\255\
\000\000\002\255\092\000\099\255\099\255\099\255\099\255\000\000\
\099\255\099\255\109\255\027\255\102\255\098\255\120\255\000\000\
\136\255\000\000\073\255\110\255\114\255\099\255\000\000\000\000\
\099\255\099\255\099\255\099\255\099\255\099\255\100\255\100\255\
\099\255\115\255\116\255\118\255\109\000\122\255\000\000\240\254\
\240\254\002\255\002\255\134\000\134\000\123\255\154\255\134\255\
\137\255\138\255\053\255\000\000\000\000\099\255\000\000\134\000\
\134\000\134\000\134\000\134\000\134\000\134\000\155\255\000\000\
\142\255\000\000\000\000\000\000\000\000\000\000\000\000\146\255\
\083\255\083\255\083\255\000\000\171\255\117\000\100\255\150\255\
\000\000\000\000\157\255\187\255\160\255\162\255\163\255\000\000\
\000\000\000\000\000\000\000\000\000\000\179\255\083\255\179\255\
\000\000\201\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\176\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\121\255\000\000\000\000\000\000\000\000\
\000\000\000\000\248\254\000\000\181\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\176\255\
\000\000\164\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\209\255\005\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\002\000\
\024\000\186\255\208\255\046\000\052\000\000\000\000\000\000\000\
\000\000\057\255\000\000\000\000\000\000\000\000\000\000\010\255\
\182\255\185\255\196\255\197\255\198\255\203\255\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\204\255\204\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\205\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\250\255\225\255\000\000\000\000\000\000\093\000\129\255\
\000\000\000\000\249\255\239\255\188\000\000\000"

let yytablesize = 426
let yytable = "\023\000\
\022\000\065\000\031\000\001\000\042\000\054\000\055\000\002\000\
\021\000\034\000\035\000\038\000\039\000\047\000\145\000\048\000\
\147\000\045\000\057\000\058\000\037\000\050\000\051\000\037\000\
\049\000\022\000\064\000\060\000\061\000\004\000\005\000\006\000\
\007\000\008\000\009\000\002\000\057\000\058\000\036\000\085\000\
\035\000\036\000\010\000\011\000\088\000\089\000\090\000\091\000\
\012\000\092\000\093\000\024\000\017\000\025\000\018\000\013\000\
\019\000\062\000\063\000\026\000\101\000\032\000\104\000\113\000\
\020\000\105\000\106\000\107\000\108\000\109\000\110\000\043\000\
\111\000\112\000\046\000\003\000\044\000\004\000\005\000\006\000\
\007\000\008\000\009\000\124\000\125\000\130\000\061\000\012\000\
\012\000\131\000\010\000\011\000\059\000\069\000\126\000\070\000\
\012\000\100\000\079\000\027\000\096\000\028\000\003\000\013\000\
\004\000\005\000\006\000\007\000\008\000\009\000\080\000\146\000\
\081\000\052\000\053\000\054\000\055\000\010\000\011\000\029\000\
\138\000\082\000\097\000\012\000\056\000\084\000\030\000\095\000\
\057\000\058\000\013\000\040\000\040\000\040\000\040\000\040\000\
\040\000\094\000\098\000\102\000\040\000\040\000\040\000\040\000\
\103\000\114\000\115\000\040\000\116\000\040\000\118\000\040\000\
\040\000\119\000\120\000\040\000\040\000\073\000\074\000\075\000\
\076\000\077\000\078\000\121\000\122\000\123\000\052\000\053\000\
\054\000\055\000\128\000\127\000\129\000\136\000\050\000\050\000\
\050\000\050\000\050\000\050\000\139\000\057\000\058\000\050\000\
\050\000\050\000\050\000\140\000\142\000\141\000\050\000\144\000\
\050\000\143\000\050\000\050\000\045\000\045\000\045\000\045\000\
\045\000\045\000\012\000\148\000\034\000\045\000\045\000\045\000\
\045\000\035\000\052\000\004\000\045\000\053\000\045\000\135\000\
\045\000\045\000\046\000\046\000\046\000\046\000\046\000\046\000\
\054\000\055\000\056\000\046\000\046\000\046\000\046\000\057\000\
\013\000\014\000\046\000\086\000\046\000\000\000\046\000\046\000\
\052\000\053\000\054\000\055\000\000\000\000\000\000\000\068\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\057\000\
\058\000\000\000\000\000\022\000\000\000\022\000\022\000\022\000\
\022\000\022\000\022\000\000\000\043\000\043\000\043\000\043\000\
\043\000\043\000\022\000\022\000\000\000\043\000\043\000\000\000\
\022\000\022\000\000\000\000\000\043\000\000\000\043\000\022\000\
\043\000\043\000\044\000\044\000\044\000\044\000\044\000\044\000\
\000\000\000\000\000\000\044\000\044\000\000\000\000\000\000\000\
\000\000\000\000\044\000\000\000\044\000\000\000\044\000\044\000\
\047\000\047\000\047\000\047\000\047\000\047\000\048\000\048\000\
\048\000\048\000\048\000\048\000\000\000\000\000\000\000\000\000\
\047\000\000\000\047\000\000\000\047\000\047\000\048\000\000\000\
\048\000\000\000\048\000\048\000\052\000\053\000\054\000\055\000\
\000\000\000\000\052\000\053\000\054\000\055\000\000\000\071\000\
\000\000\000\000\000\000\057\000\058\000\072\000\000\000\000\000\
\000\000\057\000\058\000\052\000\053\000\054\000\055\000\052\000\
\053\000\054\000\055\000\000\000\083\000\000\000\000\000\000\000\
\087\000\000\000\057\000\058\000\000\000\000\000\057\000\058\000\
\052\000\053\000\054\000\055\000\000\000\000\000\000\000\117\000\
\052\000\053\000\054\000\055\000\000\000\000\000\000\000\057\000\
\058\000\000\000\000\000\137\000\000\000\000\000\000\000\057\000\
\058\000\052\000\053\000\054\000\055\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\057\000\058\000"

let yycheck = "\006\000\
\000\000\033\000\010\000\001\000\022\000\022\001\023\001\003\001\
\028\001\017\000\018\000\019\000\020\000\026\001\142\000\028\001\
\144\000\025\000\035\001\036\001\029\001\029\000\030\000\032\001\
\037\001\028\001\033\000\003\001\004\001\005\001\006\001\007\001\
\008\001\009\001\010\001\031\001\035\001\036\001\029\001\047\000\
\048\000\032\001\018\001\019\001\052\000\053\000\054\000\055\000\
\024\001\057\000\058\000\028\001\026\001\028\001\028\001\031\001\
\030\001\033\001\034\001\028\001\067\000\028\001\070\000\081\000\
\038\001\073\000\074\000\075\000\076\000\077\000\078\000\006\001\
\079\000\080\000\003\001\003\001\002\001\005\001\006\001\007\001\
\008\001\009\001\010\001\031\001\032\001\003\001\004\001\031\001\
\032\001\121\000\018\001\019\001\003\001\029\001\102\000\032\001\
\024\001\025\001\029\001\001\001\003\001\003\001\003\001\031\001\
\005\001\006\001\007\001\008\001\009\001\010\001\029\001\143\000\
\028\001\020\001\021\001\022\001\023\001\018\001\019\001\021\001\
\127\000\029\001\003\001\024\001\031\001\029\001\028\001\026\001\
\035\001\036\001\031\001\011\001\012\001\013\001\014\001\015\001\
\016\001\029\001\003\001\030\001\020\001\021\001\022\001\023\001\
\031\001\031\001\031\001\027\001\031\001\029\001\029\001\031\001\
\032\001\031\001\001\001\035\001\036\001\011\001\012\001\013\001\
\014\001\015\001\016\001\030\001\028\001\028\001\020\001\021\001\
\022\001\023\001\029\001\017\001\027\001\003\001\011\001\012\001\
\013\001\014\001\015\001\016\001\031\001\035\001\036\001\020\001\
\021\001\022\001\023\001\031\001\029\001\003\001\027\001\029\001\
\029\001\032\001\031\001\032\001\011\001\012\001\013\001\014\001\
\015\001\016\001\024\001\003\001\029\001\020\001\021\001\022\001\
\023\001\029\001\029\001\003\001\027\001\029\001\029\001\123\000\
\031\001\032\001\011\001\012\001\013\001\014\001\015\001\016\001\
\029\001\029\001\029\001\020\001\021\001\022\001\023\001\029\001\
\029\001\029\001\027\001\048\000\029\001\255\255\031\001\032\001\
\020\001\021\001\022\001\023\001\255\255\255\255\255\255\027\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\035\001\
\036\001\255\255\255\255\003\001\255\255\005\001\006\001\007\001\
\008\001\009\001\010\001\255\255\011\001\012\001\013\001\014\001\
\015\001\016\001\018\001\019\001\255\255\020\001\021\001\255\255\
\024\001\025\001\255\255\255\255\027\001\255\255\029\001\031\001\
\031\001\032\001\011\001\012\001\013\001\014\001\015\001\016\001\
\255\255\255\255\255\255\020\001\021\001\255\255\255\255\255\255\
\255\255\255\255\027\001\255\255\029\001\255\255\031\001\032\001\
\011\001\012\001\013\001\014\001\015\001\016\001\011\001\012\001\
\013\001\014\001\015\001\016\001\255\255\255\255\255\255\255\255\
\027\001\255\255\029\001\255\255\031\001\032\001\027\001\255\255\
\029\001\255\255\031\001\032\001\020\001\021\001\022\001\023\001\
\255\255\255\255\020\001\021\001\022\001\023\001\255\255\031\001\
\255\255\255\255\255\255\035\001\036\001\031\001\255\255\255\255\
\255\255\035\001\036\001\020\001\021\001\022\001\023\001\020\001\
\021\001\022\001\023\001\255\255\029\001\255\255\255\255\255\255\
\029\001\255\255\035\001\036\001\255\255\255\255\035\001\036\001\
\020\001\021\001\022\001\023\001\255\255\255\255\255\255\027\001\
\020\001\021\001\022\001\023\001\255\255\255\255\255\255\035\001\
\036\001\255\255\255\255\031\001\255\255\255\255\255\255\035\001\
\036\001\020\001\021\001\022\001\023\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\035\001\036\001"

let yynames_const = "\
  INT\000\
  IF\000\
  WHILE\000\
  DO\000\
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
  PERCENT\000\
  POW\000\
  INCREMENT\000\
  PLUS_ASSIGN\000\
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
# 349 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 30 "parser.mly"
           ( IntTyp )
# 355 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 31 "parser.mly"
                     ( ArrayTyp (_3, IntTyp) )
# 362 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 32 "parser.mly"
               ( NameTyp _1 )
# 369 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 35 "parser.mly"
                ( _1@_2 )
# 377 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 36 "parser.mly"
                ( [] )
# 383 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ids) in
    Obj.repr(
# 39 "parser.mly"
                     ( List.map (fun x -> VarDec (_1,x)) _2 )
# 391 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 40 "parser.mly"
                              ( [TypeDec (_2,_4)] )
# 399 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 41 "parser.mly"
                                    ( [FuncDec(_2, _4, _1, _6)] )
# 409 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 42 "parser.mly"
                                      ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 418 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 45 "parser.mly"
                       ( _1@[_3] )
# 426 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                       ( [_1]  )
# 433 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 49 "parser.mly"
                        ( [] )
# 439 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 50 "parser.mly"
                        ( _1 )
# 446 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 53 "parser.mly"
                             ( _1@[(_3,_4)] )
# 455 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
                             ( [(_1,_2)] )
# 463 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 57 "parser.mly"
                   ( _1@[_2] )
# 471 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 58 "parser.mly"
                   ( [_1] )
# 478 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 61 "parser.mly"
                              ( Assign (Var _1, _3) )
# 486 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                                 ( Assign (Var _1, CallFunc ("+", [VarExp (Var _1); _3])) )
# 494 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 63 "parser.mly"
                                       ( Assign (IndexedVar (Var _1, _3), _6) )
# 503 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 64 "parser.mly"
                              ( If (_3, _5, None) )
# 511 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 66 "parser.mly"
                              ( If (_3, _5, Some _7) )
# 520 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'stmt) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    Obj.repr(
# 67 "parser.mly"
                                     ( DoWhile (_2, _5) )
# 528 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 68 "parser.mly"
                              ( While (_3, _5) )
# 536 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 69 "parser.mly"
                              ( CallProc ("sprint", [StrExp _3]) )
# 543 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                              ( CallProc ("iprint", [_3]) )
# 550 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 71 "parser.mly"
                           ( CallProc ("scan", [VarExp (Var _3)]) )
# 557 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 72 "parser.mly"
                           ( CallProc ("new", [ VarExp (Var _3)]) )
# 564 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 73 "parser.mly"
                                ( CallProc (_1, _3) )
# 572 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 74 "parser.mly"
                           ( CallProc ("return", [_2]) )
# 579 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 75 "parser.mly"
             ( _1 )
# 586 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
            ( NilStmt )
# 592 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "parser.mly"
                           ( [] )
# 598 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 80 "parser.mly"
                           ( _1 )
# 605 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                          ( _1@[_3] )
# 613 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 84 "parser.mly"
                           ( [_1] )
# 620 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 87 "parser.mly"
                         ( Block (_2, _3) )
# 628 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 90 "parser.mly"
           ( IntExp _1  )
# 635 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 91 "parser.mly"
         ( VarExp (Var _1) )
# 642 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 92 "parser.mly"
                         ( CallFunc (_1, _3) )
# 650 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                     ( VarExp (IndexedVar (Var _1, _3)) )
# 658 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                     ( CallFunc ("+", [_1; _3]) )
# 666 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                      ( CallFunc ("-", [_1; _3]) )
# 674 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                      ( CallFunc ("*", [_1; _3]) )
# 682 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                    ( CallFunc ("/", [_1; _3]) )
# 690 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                        ( CallFunc ("%", [_1; _3]) )
# 698 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parser.mly"
                    ( CallFunc ("^", [_1; _3]) )
# 706 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 100 "parser.mly"
                   ( CallFunc ("++", [VarExp (Var _1)]) )
# 713 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 101 "parser.mly"
                              ( CallFunc("!", [_2]) )
# 720 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 102 "parser.mly"
                  ( _2 )
# 727 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 735 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 743 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 751 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 108 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 759 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 767 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 110 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 775 "parser.ml"
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
