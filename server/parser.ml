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
\005\000\005\000\005\000\006\000\006\000\008\000\008\000\010\000\
\010\000\011\000\011\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\013\000\013\000\014\000\014\000\009\000\007\000\007\000\
\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
\007\000\007\000\007\000\012\000\012\000\012\000\012\000\012\000\
\012\000\000\000"

let yylen = "\002\000\
\001\000\001\000\004\000\001\000\002\000\000\000\003\000\005\000\
\005\000\006\000\006\000\003\000\001\000\000\000\001\000\004\000\
\002\000\002\000\001\000\004\000\004\000\007\000\005\000\007\000\
\005\000\005\000\005\000\005\000\005\000\005\000\003\000\001\000\
\001\000\000\000\001\000\003\000\001\000\004\000\001\000\001\000\
\004\000\004\000\003\000\003\000\003\000\003\000\003\000\003\000\
\002\000\002\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\006\000\033\000\058\000\001\000\032\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\039\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\049\000\000\000\000\000\
\000\000\000\000\000\000\000\000\031\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\019\000\000\000\005\000\000\000\
\000\000\000\000\000\000\020\000\021\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\051\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\038\000\
\018\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\025\000\026\000\027\000\028\000\042\000\
\041\000\029\000\000\000\000\000\000\000\000\000\000\000\007\000\
\000\000\000\000\000\000\003\000\004\000\000\000\000\000\000\000\
\000\000\000\000\000\000\012\000\022\000\024\000\008\000\017\000\
\000\000\000\000\000\000\009\000\011\000\000\000\010\000\016\000"

let yydgoto = "\002\000\
\013\000\014\000\127\000\031\000\063\000\095\000\033\000\128\000\
\015\000\129\000\064\000\039\000\034\000\035\000"

let yysindex = "\004\000\
\095\255\000\000\022\000\005\255\010\255\025\255\041\255\044\255\
\066\255\050\255\000\000\000\000\000\000\000\000\000\000\066\255\
\066\255\066\255\066\255\066\255\066\255\013\255\066\255\053\255\
\000\000\237\254\066\255\066\255\220\255\076\255\021\255\043\000\
\133\000\055\255\057\255\051\000\068\000\135\255\064\255\068\255\
\071\255\072\000\079\255\066\255\066\255\000\000\244\254\089\000\
\066\255\066\255\066\255\066\255\000\000\066\255\066\255\080\255\
\022\000\069\255\108\255\111\255\000\000\112\255\000\000\067\255\
\087\255\096\255\066\255\000\000\000\000\066\255\066\255\066\255\
\066\255\066\255\066\255\095\255\095\255\097\255\102\255\103\255\
\093\000\089\255\000\000\255\254\255\254\244\254\244\254\133\000\
\133\000\104\255\137\255\107\255\114\255\028\255\029\255\000\000\
\000\000\066\255\000\000\133\000\133\000\133\000\133\000\133\000\
\133\000\133\000\126\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\125\255\078\255\078\255\078\255\066\255\000\000\
\149\255\110\000\095\255\000\000\000\000\123\255\155\255\131\255\
\129\255\133\255\116\000\000\000\000\000\000\000\000\000\000\000\
\145\255\078\255\145\255\000\000\000\000\172\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\148\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\109\255\000\000\000\000\000\000\000\000\000\000\000\000\
\241\254\000\000\151\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\148\255\000\000\152\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\178\255\001\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\218\255\002\000\174\255\196\255\024\000\
\030\000\000\000\000\000\000\000\000\000\075\255\000\000\000\000\
\000\000\000\000\000\000\019\255\162\255\163\255\164\255\169\255\
\170\255\171\255\001\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\173\255\173\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\175\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\228\255\227\255\000\000\000\000\000\000\247\255\059\000\
\197\255\000\000\000\000\191\000\168\000\000\000"

let yytablesize = 424
let yytable = "\029\000\
\023\000\062\000\061\000\002\000\001\000\044\000\032\000\045\000\
\036\000\037\000\038\000\038\000\037\000\042\000\041\000\037\000\
\046\000\047\000\048\000\051\000\052\000\054\000\055\000\057\000\
\058\000\004\000\005\000\006\000\007\000\008\000\002\000\020\000\
\054\000\055\000\081\000\097\000\021\000\009\000\010\000\084\000\
\085\000\086\000\087\000\011\000\088\000\089\000\036\000\107\000\
\108\000\036\000\012\000\022\000\059\000\060\000\118\000\043\000\
\119\000\100\000\120\000\121\000\101\000\102\000\103\000\104\000\
\105\000\106\000\025\000\023\000\026\000\003\000\024\000\004\000\
\005\000\006\000\007\000\008\000\030\000\141\000\056\000\143\000\
\125\000\058\000\066\000\009\000\010\000\027\000\126\000\067\000\
\122\000\011\000\096\000\076\000\028\000\091\000\134\000\077\000\
\012\000\003\000\078\000\004\000\005\000\006\000\007\000\008\000\
\013\000\013\000\080\000\090\000\142\000\131\000\092\000\009\000\
\010\000\093\000\094\000\098\000\113\000\011\000\040\000\040\000\
\040\000\040\000\040\000\040\000\012\000\099\000\109\000\040\000\
\040\000\040\000\040\000\110\000\111\000\114\000\040\000\116\000\
\040\000\115\000\040\000\040\000\117\000\123\000\040\000\040\000\
\070\000\071\000\072\000\073\000\074\000\075\000\124\000\132\000\
\135\000\049\000\050\000\051\000\052\000\136\000\137\000\138\000\
\139\000\050\000\050\000\050\000\050\000\050\000\050\000\011\000\
\054\000\055\000\050\000\050\000\050\000\050\000\144\000\034\000\
\130\000\050\000\035\000\050\000\004\000\050\000\050\000\045\000\
\045\000\045\000\045\000\045\000\045\000\052\000\053\000\054\000\
\045\000\045\000\045\000\045\000\055\000\056\000\057\000\045\000\
\014\000\045\000\015\000\045\000\045\000\046\000\046\000\046\000\
\046\000\046\000\046\000\040\000\082\000\000\000\046\000\046\000\
\046\000\046\000\000\000\000\000\000\000\046\000\000\000\046\000\
\000\000\046\000\046\000\043\000\043\000\043\000\043\000\043\000\
\043\000\000\000\000\000\000\000\043\000\043\000\049\000\050\000\
\051\000\052\000\000\000\043\000\000\000\043\000\000\000\043\000\
\043\000\053\000\000\000\000\000\000\000\054\000\055\000\000\000\
\000\000\000\000\000\000\023\000\000\000\023\000\023\000\023\000\
\023\000\023\000\000\000\044\000\044\000\044\000\044\000\044\000\
\044\000\023\000\023\000\000\000\044\000\044\000\000\000\023\000\
\023\000\000\000\000\000\044\000\000\000\044\000\023\000\044\000\
\044\000\047\000\047\000\047\000\047\000\047\000\047\000\048\000\
\048\000\048\000\048\000\048\000\048\000\000\000\016\000\000\000\
\017\000\047\000\018\000\047\000\000\000\047\000\047\000\048\000\
\000\000\048\000\019\000\048\000\048\000\049\000\050\000\051\000\
\052\000\000\000\000\000\000\000\065\000\049\000\050\000\051\000\
\052\000\000\000\000\000\000\000\054\000\055\000\000\000\000\000\
\068\000\000\000\000\000\000\000\054\000\055\000\049\000\050\000\
\051\000\052\000\049\000\050\000\051\000\052\000\000\000\000\000\
\000\000\069\000\000\000\079\000\000\000\054\000\055\000\000\000\
\000\000\054\000\055\000\049\000\050\000\051\000\052\000\049\000\
\050\000\051\000\052\000\000\000\083\000\000\000\112\000\000\000\
\000\000\000\000\054\000\055\000\000\000\000\000\054\000\055\000\
\049\000\050\000\051\000\052\000\000\000\000\000\049\000\050\000\
\051\000\052\000\000\000\133\000\000\000\000\000\000\000\054\000\
\055\000\140\000\000\000\000\000\000\000\054\000\055\000\049\000\
\050\000\051\000\052\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\054\000\055\000"

let yycheck = "\009\000\
\000\000\031\000\031\000\003\001\001\000\025\001\016\000\027\001\
\018\000\019\000\020\000\021\000\028\001\023\000\002\001\031\001\
\036\001\027\000\028\000\021\001\022\001\034\001\035\001\003\001\
\004\001\005\001\006\001\007\001\008\001\009\001\030\001\027\001\
\034\001\035\001\044\000\064\000\027\001\017\001\018\001\049\000\
\050\000\051\000\052\000\023\001\054\000\055\000\028\001\076\000\
\077\000\031\001\030\001\027\001\032\001\033\001\027\001\003\001\
\029\001\067\000\030\001\031\001\070\000\071\000\072\000\073\000\
\074\000\075\000\001\001\027\001\003\001\003\001\027\001\005\001\
\006\001\007\001\008\001\009\001\027\001\137\000\003\001\139\000\
\003\001\004\001\028\001\017\001\018\001\020\001\116\000\031\001\
\098\000\023\001\024\001\028\001\027\001\025\001\123\000\028\001\
\030\001\003\001\028\001\005\001\006\001\007\001\008\001\009\001\
\030\001\031\001\028\001\028\001\138\000\119\000\003\001\017\001\
\018\001\003\001\003\001\029\001\028\001\023\001\010\001\011\001\
\012\001\013\001\014\001\015\001\030\001\030\001\030\001\019\001\
\020\001\021\001\022\001\030\001\030\001\030\001\026\001\029\001\
\028\001\001\001\030\001\031\001\027\001\016\001\034\001\035\001\
\010\001\011\001\012\001\013\001\014\001\015\001\026\001\003\001\
\030\001\019\001\020\001\021\001\022\001\003\001\028\001\031\001\
\028\001\010\001\011\001\012\001\013\001\014\001\015\001\023\001\
\034\001\035\001\019\001\020\001\021\001\022\001\003\001\028\001\
\118\000\026\001\028\001\028\001\003\001\030\001\031\001\010\001\
\011\001\012\001\013\001\014\001\015\001\028\001\028\001\028\001\
\019\001\020\001\021\001\022\001\028\001\028\001\028\001\026\001\
\028\001\028\001\028\001\030\001\031\001\010\001\011\001\012\001\
\013\001\014\001\015\001\021\000\045\000\255\255\019\001\020\001\
\021\001\022\001\255\255\255\255\255\255\026\001\255\255\028\001\
\255\255\030\001\031\001\010\001\011\001\012\001\013\001\014\001\
\015\001\255\255\255\255\255\255\019\001\020\001\019\001\020\001\
\021\001\022\001\255\255\026\001\255\255\028\001\255\255\030\001\
\031\001\030\001\255\255\255\255\255\255\034\001\035\001\255\255\
\255\255\255\255\255\255\003\001\255\255\005\001\006\001\007\001\
\008\001\009\001\255\255\010\001\011\001\012\001\013\001\014\001\
\015\001\017\001\018\001\255\255\019\001\020\001\255\255\023\001\
\024\001\255\255\255\255\026\001\255\255\028\001\030\001\030\001\
\031\001\010\001\011\001\012\001\013\001\014\001\015\001\010\001\
\011\001\012\001\013\001\014\001\015\001\255\255\025\001\255\255\
\027\001\026\001\029\001\028\001\255\255\030\001\031\001\026\001\
\255\255\028\001\037\001\030\001\031\001\019\001\020\001\021\001\
\022\001\255\255\255\255\255\255\026\001\019\001\020\001\021\001\
\022\001\255\255\255\255\255\255\034\001\035\001\255\255\255\255\
\030\001\255\255\255\255\255\255\034\001\035\001\019\001\020\001\
\021\001\022\001\019\001\020\001\021\001\022\001\255\255\255\255\
\255\255\030\001\255\255\028\001\255\255\034\001\035\001\255\255\
\255\255\034\001\035\001\019\001\020\001\021\001\022\001\019\001\
\020\001\021\001\022\001\255\255\028\001\255\255\026\001\255\255\
\255\255\255\255\034\001\035\001\255\255\255\255\034\001\035\001\
\019\001\020\001\021\001\022\001\255\255\255\255\019\001\020\001\
\021\001\022\001\255\255\030\001\255\255\255\255\255\255\034\001\
\035\001\030\001\255\255\255\255\255\255\034\001\035\001\019\001\
\020\001\021\001\022\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\034\001\035\001"

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
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 41 "parser.mly"
                                ( [VarDecInit (_1, _2, _4)] )
# 400 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 42 "parser.mly"
                                    ( [FuncDec(_2, _4, _1, _6)] )
# 410 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 43 "parser.mly"
                                      ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 419 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                       ( _1@[_3] )
# 427 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 47 "parser.mly"
                       ( [_1]  )
# 434 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
                        ( [] )
# 440 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 51 "parser.mly"
                        ( _1 )
# 447 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
                             ( _1@[(_3,_4)] )
# 456 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 55 "parser.mly"
                             ( [(_1,_2)] )
# 464 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 58 "parser.mly"
                   ( _1@[_2] )
# 472 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 59 "parser.mly"
                   ( [_1] )
# 479 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                              ( Assign (Var _1, _3) )
# 487 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 63 "parser.mly"
                                 ( Assign (Var _1, CallFunc ("+", [VarExp (Var _1); _3])) )
# 495 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 64 "parser.mly"
                                       ( Assign (IndexedVar (Var _1, _3), _6) )
# 504 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 65 "parser.mly"
                              ( If (_3, _5, None) )
# 512 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 67 "parser.mly"
                              ( If (_3, _5, Some _7) )
# 521 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 68 "parser.mly"
                              ( While (_3, _5) )
# 529 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 69 "parser.mly"
                              ( CallProc ("sprint", [StrExp _3]) )
# 536 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                              ( CallProc ("iprint", [_3]) )
# 543 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 71 "parser.mly"
                           ( CallProc ("scan", [VarExp (Var _3)]) )
# 550 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 72 "parser.mly"
                           ( CallProc ("new", [ VarExp (Var _3)]) )
# 557 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 73 "parser.mly"
                                ( CallProc (_1, _3) )
# 565 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 74 "parser.mly"
                           ( CallProc ("return", [_2]) )
# 572 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 75 "parser.mly"
             ( _1 )
# 579 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
            ( NilStmt )
# 585 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "parser.mly"
                           ( [] )
# 591 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 80 "parser.mly"
                           ( _1 )
# 598 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                          ( _1@[_3] )
# 606 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 84 "parser.mly"
                           ( [_1] )
# 613 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 87 "parser.mly"
                         ( Block (_2, _3) )
# 621 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 90 "parser.mly"
           ( IntExp _1  )
# 628 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 91 "parser.mly"
         ( VarExp (Var _1) )
# 635 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 92 "parser.mly"
                         ( CallFunc (_1, _3) )
# 643 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                     ( VarExp (IndexedVar (Var _1, _3)) )
# 651 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                     ( CallFunc ("+", [_1; _3]) )
# 659 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                      ( CallFunc ("-", [_1; _3]) )
# 667 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                      ( CallFunc ("*", [_1; _3]) )
# 675 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                    ( CallFunc ("/", [_1; _3]) )
# 683 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                        ( CallFunc ("%", [_1; _3]) )
# 691 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parser.mly"
                    ( CallFunc ("^", [_1; _3]) )
# 699 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 100 "parser.mly"
                   ( CallFunc ("++", [VarExp (Var _1)]) )
# 706 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 101 "parser.mly"
                              ( CallFunc("!", [_2]) )
# 713 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 102 "parser.mly"
                  ( _2 )
# 720 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 728 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 736 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 744 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 108 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 752 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 760 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 110 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 768 "parser.ml"
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
