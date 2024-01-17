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
  | PERCENT
  | POW
  | INCREMENT
  | PLUS_ASSIGN

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"

open Printf
open Ast

# 48 "parser.ml"
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
  290 (* PERCENT *);
  291 (* POW *);
  292 (* INCREMENT *);
  293 (* PLUS_ASSIGN *);
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
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\011\000\012\000\012\000\012\000\012\000\012\000\012\000\
\000\000"

let yylen = "\002\000\
\001\000\001\000\004\000\001\000\002\000\000\000\003\000\005\000\
\006\000\006\000\003\000\001\000\000\000\001\000\004\000\002\000\
\002\000\001\000\004\000\004\000\007\000\005\000\007\000\005\000\
\005\000\005\000\005\000\005\000\005\000\003\000\001\000\001\000\
\000\000\001\000\003\000\001\000\004\000\001\000\001\000\004\000\
\004\000\003\000\003\000\003\000\003\000\003\000\003\000\002\000\
\002\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\006\000\032\000\057\000\001\000\031\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\038\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\048\000\000\000\000\000\
\000\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\018\000\000\000\005\000\000\000\
\000\000\000\000\000\000\019\000\020\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\050\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\037\000\
\017\000\000\000\029\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\024\000\025\000\026\000\027\000\041\000\
\040\000\028\000\000\000\000\000\000\000\000\000\007\000\000\000\
\000\000\000\000\003\000\004\000\000\000\000\000\000\000\000\000\
\000\000\011\000\021\000\023\000\008\000\016\000\000\000\000\000\
\000\000\010\000\000\000\009\000\015\000"

let yydgoto = "\002\000\
\013\000\014\000\126\000\031\000\063\000\095\000\127\000\015\000\
\128\000\064\000\033\000\039\000\034\000\035\000"

let yysindex = "\009\000\
\148\255\000\000\033\255\245\254\253\254\005\255\007\255\013\255\
\006\255\018\255\000\000\000\000\000\000\000\000\000\000\006\255\
\006\255\006\255\006\255\006\255\006\255\053\255\006\255\056\255\
\000\000\237\254\006\255\006\255\128\255\058\255\103\255\249\254\
\131\000\035\255\037\255\237\255\085\000\162\255\043\255\067\255\
\069\255\089\000\073\255\006\255\006\255\000\000\009\255\106\000\
\006\255\006\255\006\255\006\255\000\000\006\255\006\255\076\255\
\033\255\059\255\083\255\110\255\000\000\111\255\000\000\122\255\
\086\255\087\255\006\255\000\000\000\000\006\255\006\255\006\255\
\006\255\006\255\006\255\148\255\148\255\088\255\089\255\092\255\
\110\000\095\255\000\000\015\255\015\255\009\255\009\255\131\000\
\131\000\094\255\115\255\105\255\114\255\116\255\034\255\000\000\
\000\000\006\255\000\000\131\000\131\000\131\000\131\000\131\000\
\131\000\131\000\121\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\106\255\063\255\063\255\063\255\000\000\135\255\
\127\000\148\255\000\000\000\000\112\255\141\255\131\255\129\255\
\133\255\000\000\000\000\000\000\000\000\000\000\144\255\063\255\
\144\255\000\000\161\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\140\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\068\255\000\000\000\000\000\000\000\000\000\000\000\000\
\010\255\000\000\142\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\140\255\000\000\179\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\166\255\001\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\022\000\044\000\201\255\223\255\066\000\
\072\000\000\000\000\000\000\000\000\000\061\255\000\000\000\000\
\000\000\000\000\000\000\011\255\151\255\152\255\157\255\158\255\
\159\255\160\255\001\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\167\255\167\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\174\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\227\255\225\255\000\000\000\000\000\000\086\000\124\255\
\000\000\000\000\002\000\182\000\161\000\000\000"

let yytablesize = 422
let yytable = "\062\000\
\022\000\061\000\138\000\002\000\140\000\044\000\025\000\045\000\
\026\000\001\000\029\000\049\000\050\000\051\000\052\000\020\000\
\046\000\032\000\065\000\036\000\037\000\038\000\038\000\021\000\
\042\000\027\000\054\000\055\000\047\000\048\000\002\000\022\000\
\028\000\023\000\097\000\051\000\052\000\036\000\035\000\024\000\
\036\000\035\000\054\000\055\000\030\000\081\000\107\000\108\000\
\054\000\055\000\084\000\085\000\086\000\087\000\041\000\088\000\
\089\000\016\000\043\000\017\000\056\000\018\000\066\000\119\000\
\120\000\124\000\058\000\067\000\100\000\019\000\076\000\101\000\
\102\000\103\000\104\000\105\000\106\000\039\000\039\000\039\000\
\039\000\039\000\039\000\091\000\125\000\092\000\039\000\039\000\
\039\000\039\000\012\000\012\000\132\000\039\000\077\000\039\000\
\078\000\039\000\039\000\121\000\080\000\039\000\039\000\090\000\
\139\000\057\000\058\000\004\000\005\000\006\000\007\000\008\000\
\093\000\094\000\098\000\115\000\099\000\109\000\110\000\009\000\
\010\000\111\000\113\000\114\000\003\000\011\000\004\000\005\000\
\006\000\007\000\008\000\123\000\012\000\116\000\059\000\060\000\
\122\000\130\000\009\000\010\000\117\000\133\000\118\000\134\000\
\011\000\096\000\049\000\050\000\051\000\052\000\003\000\012\000\
\004\000\005\000\006\000\007\000\008\000\053\000\135\000\136\000\
\137\000\054\000\055\000\141\000\009\000\010\000\011\000\033\000\
\004\000\034\000\011\000\070\000\071\000\072\000\073\000\074\000\
\075\000\012\000\051\000\052\000\049\000\050\000\051\000\052\000\
\053\000\054\000\055\000\056\000\049\000\049\000\049\000\049\000\
\049\000\049\000\013\000\054\000\055\000\049\000\049\000\049\000\
\049\000\014\000\040\000\129\000\049\000\082\000\049\000\000\000\
\049\000\049\000\044\000\044\000\044\000\044\000\044\000\044\000\
\000\000\000\000\000\000\044\000\044\000\044\000\044\000\000\000\
\000\000\000\000\044\000\000\000\044\000\000\000\044\000\044\000\
\045\000\045\000\045\000\045\000\045\000\045\000\000\000\000\000\
\000\000\045\000\045\000\045\000\045\000\000\000\000\000\000\000\
\045\000\000\000\045\000\000\000\045\000\045\000\000\000\049\000\
\050\000\051\000\052\000\022\000\000\000\022\000\022\000\022\000\
\022\000\022\000\068\000\000\000\000\000\000\000\054\000\055\000\
\000\000\022\000\022\000\000\000\000\000\000\000\000\000\022\000\
\022\000\000\000\000\000\000\000\000\000\000\000\022\000\042\000\
\042\000\042\000\042\000\042\000\042\000\000\000\000\000\000\000\
\042\000\042\000\000\000\000\000\000\000\000\000\000\000\042\000\
\000\000\042\000\000\000\042\000\042\000\043\000\043\000\043\000\
\043\000\043\000\043\000\000\000\000\000\000\000\043\000\043\000\
\000\000\000\000\000\000\000\000\000\000\043\000\000\000\043\000\
\000\000\043\000\043\000\046\000\046\000\046\000\046\000\046\000\
\046\000\047\000\047\000\047\000\047\000\047\000\047\000\000\000\
\000\000\000\000\000\000\046\000\000\000\046\000\000\000\046\000\
\046\000\047\000\000\000\047\000\000\000\047\000\047\000\049\000\
\050\000\051\000\052\000\049\000\050\000\051\000\052\000\000\000\
\000\000\000\000\069\000\000\000\079\000\000\000\054\000\055\000\
\000\000\000\000\054\000\055\000\049\000\050\000\051\000\052\000\
\049\000\050\000\051\000\052\000\000\000\083\000\000\000\112\000\
\000\000\000\000\000\000\054\000\055\000\000\000\000\000\054\000\
\055\000\049\000\050\000\051\000\052\000\049\000\050\000\051\000\
\052\000\000\000\000\000\000\000\131\000\000\000\000\000\000\000\
\054\000\055\000\000\000\000\000\054\000\055\000"

let yycheck = "\031\000\
\000\000\031\000\135\000\003\001\137\000\025\001\001\001\027\001\
\003\001\001\000\009\000\019\001\020\001\021\001\022\001\027\001\
\036\001\016\000\026\001\018\000\019\000\020\000\021\000\027\001\
\023\000\020\001\034\001\035\001\027\000\028\000\030\001\027\001\
\027\001\027\001\064\000\021\001\022\001\028\001\028\001\027\001\
\031\001\031\001\034\001\035\001\027\001\044\000\076\000\077\000\
\034\001\035\001\049\000\050\000\051\000\052\000\002\001\054\000\
\055\000\025\001\003\001\027\001\003\001\029\001\028\001\030\001\
\031\001\003\001\004\001\031\001\067\000\037\001\028\001\070\000\
\071\000\072\000\073\000\074\000\075\000\010\001\011\001\012\001\
\013\001\014\001\015\001\025\001\116\000\003\001\019\001\020\001\
\021\001\022\001\030\001\031\001\122\000\026\001\028\001\028\001\
\028\001\030\001\031\001\098\000\028\001\034\001\035\001\028\001\
\136\000\003\001\004\001\005\001\006\001\007\001\008\001\009\001\
\003\001\003\001\029\001\001\001\030\001\030\001\030\001\017\001\
\018\001\030\001\028\001\030\001\003\001\023\001\005\001\006\001\
\007\001\008\001\009\001\026\001\030\001\029\001\032\001\033\001\
\016\001\003\001\017\001\018\001\027\001\030\001\027\001\003\001\
\023\001\024\001\019\001\020\001\021\001\022\001\003\001\030\001\
\005\001\006\001\007\001\008\001\009\001\030\001\028\001\031\001\
\028\001\034\001\035\001\003\001\017\001\018\001\023\001\028\001\
\003\001\028\001\023\001\010\001\011\001\012\001\013\001\014\001\
\015\001\030\001\028\001\028\001\019\001\020\001\021\001\022\001\
\028\001\028\001\028\001\028\001\010\001\011\001\012\001\013\001\
\014\001\015\001\028\001\034\001\035\001\019\001\020\001\021\001\
\022\001\028\001\021\000\118\000\026\001\045\000\028\001\255\255\
\030\001\031\001\010\001\011\001\012\001\013\001\014\001\015\001\
\255\255\255\255\255\255\019\001\020\001\021\001\022\001\255\255\
\255\255\255\255\026\001\255\255\028\001\255\255\030\001\031\001\
\010\001\011\001\012\001\013\001\014\001\015\001\255\255\255\255\
\255\255\019\001\020\001\021\001\022\001\255\255\255\255\255\255\
\026\001\255\255\028\001\255\255\030\001\031\001\255\255\019\001\
\020\001\021\001\022\001\003\001\255\255\005\001\006\001\007\001\
\008\001\009\001\030\001\255\255\255\255\255\255\034\001\035\001\
\255\255\017\001\018\001\255\255\255\255\255\255\255\255\023\001\
\024\001\255\255\255\255\255\255\255\255\255\255\030\001\010\001\
\011\001\012\001\013\001\014\001\015\001\255\255\255\255\255\255\
\019\001\020\001\255\255\255\255\255\255\255\255\255\255\026\001\
\255\255\028\001\255\255\030\001\031\001\010\001\011\001\012\001\
\013\001\014\001\015\001\255\255\255\255\255\255\019\001\020\001\
\255\255\255\255\255\255\255\255\255\255\026\001\255\255\028\001\
\255\255\030\001\031\001\010\001\011\001\012\001\013\001\014\001\
\015\001\010\001\011\001\012\001\013\001\014\001\015\001\255\255\
\255\255\255\255\255\255\026\001\255\255\028\001\255\255\030\001\
\031\001\026\001\255\255\028\001\255\255\030\001\031\001\019\001\
\020\001\021\001\022\001\019\001\020\001\021\001\022\001\255\255\
\255\255\255\255\030\001\255\255\028\001\255\255\034\001\035\001\
\255\255\255\255\034\001\035\001\019\001\020\001\021\001\022\001\
\019\001\020\001\021\001\022\001\255\255\028\001\255\255\026\001\
\255\255\255\255\255\255\034\001\035\001\255\255\255\255\034\001\
\035\001\019\001\020\001\021\001\022\001\019\001\020\001\021\001\
\022\001\255\255\255\255\255\255\030\001\255\255\255\255\255\255\
\034\001\035\001\255\255\255\255\034\001\035\001"

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
# 341 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 30 "parser.mly"
           ( IntTyp )
# 347 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 31 "parser.mly"
                     ( ArrayTyp (_3, IntTyp) )
# 354 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 32 "parser.mly"
               ( NameTyp _1 )
# 361 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 35 "parser.mly"
                ( _1@_2 )
# 369 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 36 "parser.mly"
                ( [] )
# 375 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ids) in
    Obj.repr(
# 39 "parser.mly"
                     ( List.map (fun x -> VarDec (_1,x)) _2 )
# 383 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 40 "parser.mly"
                              ( [TypeDec (_2,_4)] )
# 391 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 41 "parser.mly"
                                    ( [FuncDec(_2, _4, _1, _6)] )
# 401 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 42 "parser.mly"
                                      ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 410 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 45 "parser.mly"
                       ( _1@[_3] )
# 418 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                       ( [_1]  )
# 425 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 49 "parser.mly"
                        ( [] )
# 431 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 50 "parser.mly"
                        ( _1 )
# 438 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 53 "parser.mly"
                             ( _1@[(_3,_4)] )
# 447 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
                             ( [(_1,_2)] )
# 455 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 57 "parser.mly"
                   ( _1@[_2] )
# 463 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 58 "parser.mly"
                   ( [_1] )
# 470 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 61 "parser.mly"
                              ( Assign (Var _1, _3) )
# 478 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                                 ( Assign (Var _1, CallFunc ("+", [VarExp (Var _1); _3])) )
# 486 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 63 "parser.mly"
                                       ( Assign (IndexedVar (Var _1, _3), _6) )
# 495 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 64 "parser.mly"
                              ( If (_3, _5, None) )
# 503 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 66 "parser.mly"
                              ( If (_3, _5, Some _7) )
# 512 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 67 "parser.mly"
                              ( While (_3, _5) )
# 520 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 68 "parser.mly"
                              ( CallProc ("sprint", [StrExp _3]) )
# 527 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 69 "parser.mly"
                              ( CallProc ("iprint", [_3]) )
# 534 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 70 "parser.mly"
                           ( CallProc ("scan", [VarExp (Var _3)]) )
# 541 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 71 "parser.mly"
                           ( CallProc ("new", [ VarExp (Var _3)]) )
# 548 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 72 "parser.mly"
                                ( CallProc (_1, _3) )
# 556 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 73 "parser.mly"
                           ( CallProc ("return", [_2]) )
# 563 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 74 "parser.mly"
             ( _1 )
# 570 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
            ( NilStmt )
# 576 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
                           ( [] )
# 582 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 79 "parser.mly"
                           ( _1 )
# 589 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 82 "parser.mly"
                          ( _1@[_3] )
# 597 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                           ( [_1] )
# 604 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 86 "parser.mly"
                         ( Block (_2, _3) )
# 612 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 89 "parser.mly"
           ( IntExp _1  )
# 619 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 90 "parser.mly"
         ( VarExp (Var _1) )
# 626 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 91 "parser.mly"
                         ( CallFunc (_1, _3) )
# 634 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 92 "parser.mly"
                     ( VarExp (IndexedVar (Var _1, _3)) )
# 642 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                     ( CallFunc ("+", [_1; _3]) )
# 650 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                      ( CallFunc ("-", [_1; _3]) )
# 658 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                      ( CallFunc ("*", [_1; _3]) )
# 666 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                    ( CallFunc ("/", [_1; _3]) )
# 674 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                        ( CallFunc ("%", [_1; _3]) )
# 682 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                    ( CallFunc ("^", [_1; _3]) )
# 690 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 99 "parser.mly"
                   ( CallFunc ("++", [VarExp (Var _1)]) )
# 697 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 100 "parser.mly"
                              ( CallFunc("!", [_2]) )
# 704 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 101 "parser.mly"
                  ( _2 )
# 711 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 104 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 719 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 727 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 735 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 743 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 108 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 751 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 759 "parser.ml"
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
