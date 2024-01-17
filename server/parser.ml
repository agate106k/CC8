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
  | FOR
  | DOTDOT

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"

open Printf
open Ast

# 50 "parser.ml"
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
  294 (* FOR *);
  295 (* DOTDOT *);
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
\002\000\001\000\004\000\004\000\007\000\005\000\007\000\005\000\
\009\000\005\000\005\000\005\000\005\000\005\000\003\000\001\000\
\001\000\000\000\001\000\003\000\001\000\004\000\001\000\001\000\
\004\000\004\000\003\000\003\000\003\000\003\000\003\000\003\000\
\002\000\002\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\006\000\033\000\000\000\058\000\001\000\032\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\039\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\049\000\
\000\000\000\000\000\000\000\000\000\000\000\000\031\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\018\000\000\000\
\005\000\000\000\000\000\000\000\000\000\000\000\019\000\020\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\051\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\038\000\017\000\000\000\000\000\030\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\024\000\
\026\000\027\000\028\000\042\000\041\000\029\000\000\000\000\000\
\000\000\000\000\007\000\000\000\000\000\000\000\000\000\003\000\
\004\000\000\000\000\000\000\000\000\000\000\000\011\000\000\000\
\021\000\023\000\008\000\016\000\000\000\000\000\000\000\000\000\
\010\000\000\000\009\000\000\000\015\000\025\000"

let yydgoto = "\002\000\
\014\000\015\000\131\000\032\000\065\000\098\000\132\000\016\000\
\133\000\066\000\035\000\041\000\036\000\037\000"

let yysindex = "\013\000\
\140\255\000\000\254\254\005\255\007\255\055\255\057\255\060\255\
\006\255\063\255\000\000\000\000\068\255\000\000\000\000\000\000\
\006\255\006\255\006\255\006\255\006\255\006\255\044\255\006\255\
\025\255\000\000\075\255\006\255\006\255\051\255\048\255\071\255\
\080\255\090\000\015\000\070\255\065\255\120\255\107\000\086\000\
\077\255\078\255\079\255\111\000\082\255\006\255\006\255\000\000\
\227\254\128\000\006\255\006\255\006\255\006\255\000\000\006\255\
\006\255\084\255\254\254\074\255\105\255\111\255\000\000\112\255\
\000\000\114\255\087\255\095\255\096\255\006\255\000\000\000\000\
\006\255\006\255\006\255\006\255\006\255\006\255\140\255\140\255\
\098\255\099\255\100\255\132\000\097\255\000\000\251\254\251\254\
\227\254\227\254\015\000\015\000\103\255\133\255\106\255\109\255\
\124\255\026\255\000\000\000\000\006\255\006\255\000\000\015\000\
\015\000\015\000\015\000\015\000\015\000\015\000\143\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\127\255\056\255\
\056\255\056\255\000\000\153\255\019\255\149\000\140\255\000\000\
\000\000\130\255\158\255\134\255\141\255\149\255\000\000\006\255\
\000\000\000\000\000\000\000\000\148\255\056\255\148\255\153\000\
\000\000\176\255\000\000\140\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\155\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\154\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\246\254\000\000\159\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\155\255\000\000\
\184\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\178\255\001\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\002\000\032\000\
\206\255\228\255\054\000\064\000\000\000\000\000\000\000\000\000\
\032\255\000\000\000\000\000\000\000\000\000\000\000\000\024\255\
\162\255\163\255\164\255\172\255\173\255\174\255\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\179\255\179\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\180\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\226\255\227\255\000\000\000\000\000\000\087\000\137\255\
\000\000\000\000\247\255\164\000\166\000\000\000"

let yytablesize = 444
let yytable = "\030\000\
\022\000\063\000\064\000\002\000\056\000\057\000\026\000\034\000\
\027\000\038\000\039\000\040\000\040\000\001\000\044\000\053\000\
\054\000\037\000\049\000\050\000\037\000\145\000\017\000\147\000\
\018\000\028\000\019\000\045\000\056\000\057\000\002\000\021\000\
\029\000\022\000\020\000\100\000\084\000\051\000\052\000\053\000\
\054\000\087\000\088\000\089\000\090\000\043\000\091\000\092\000\
\111\000\112\000\058\000\036\000\056\000\057\000\036\000\123\000\
\124\000\136\000\129\000\060\000\104\000\012\000\012\000\105\000\
\106\000\107\000\108\000\109\000\110\000\051\000\052\000\053\000\
\054\000\059\000\060\000\004\000\005\000\006\000\007\000\008\000\
\055\000\023\000\067\000\024\000\056\000\057\000\025\000\009\000\
\010\000\031\000\130\000\125\000\126\000\011\000\033\000\070\000\
\138\000\069\000\094\000\046\000\012\000\047\000\061\000\062\000\
\079\000\080\000\081\000\095\000\013\000\083\000\048\000\093\000\
\146\000\096\000\097\000\101\000\003\000\150\000\004\000\005\000\
\006\000\007\000\008\000\102\000\117\000\103\000\144\000\113\000\
\114\000\115\000\009\000\010\000\118\000\119\000\120\000\121\000\
\011\000\099\000\051\000\052\000\053\000\054\000\003\000\012\000\
\004\000\005\000\006\000\007\000\008\000\071\000\122\000\013\000\
\128\000\056\000\057\000\135\000\009\000\010\000\127\000\139\000\
\140\000\141\000\011\000\040\000\040\000\040\000\040\000\040\000\
\040\000\012\000\011\000\142\000\040\000\040\000\040\000\040\000\
\143\000\013\000\149\000\040\000\004\000\040\000\034\000\040\000\
\040\000\042\000\035\000\040\000\040\000\052\000\053\000\054\000\
\040\000\050\000\050\000\050\000\050\000\050\000\050\000\055\000\
\056\000\057\000\050\000\050\000\050\000\050\000\013\000\014\000\
\134\000\050\000\000\000\050\000\085\000\050\000\050\000\045\000\
\045\000\045\000\045\000\045\000\045\000\000\000\050\000\000\000\
\045\000\045\000\045\000\045\000\000\000\000\000\000\000\045\000\
\000\000\045\000\000\000\045\000\045\000\046\000\046\000\046\000\
\046\000\046\000\046\000\000\000\045\000\000\000\046\000\046\000\
\046\000\046\000\000\000\000\000\000\000\046\000\000\000\046\000\
\000\000\046\000\046\000\022\000\000\000\022\000\022\000\022\000\
\022\000\022\000\046\000\043\000\043\000\043\000\043\000\043\000\
\043\000\022\000\022\000\000\000\043\000\043\000\000\000\022\000\
\022\000\000\000\000\000\043\000\000\000\043\000\022\000\043\000\
\043\000\051\000\052\000\053\000\054\000\000\000\022\000\000\000\
\043\000\044\000\044\000\044\000\044\000\044\000\044\000\000\000\
\056\000\057\000\044\000\044\000\000\000\000\000\000\000\000\000\
\000\000\044\000\000\000\044\000\000\000\044\000\044\000\047\000\
\047\000\047\000\047\000\047\000\047\000\000\000\044\000\000\000\
\000\000\048\000\048\000\048\000\048\000\048\000\048\000\047\000\
\000\000\047\000\000\000\047\000\047\000\000\000\000\000\000\000\
\000\000\048\000\000\000\048\000\047\000\048\000\048\000\073\000\
\074\000\075\000\076\000\077\000\078\000\000\000\048\000\000\000\
\051\000\052\000\053\000\054\000\051\000\052\000\053\000\054\000\
\000\000\000\000\000\000\068\000\000\000\000\000\000\000\056\000\
\057\000\000\000\000\000\056\000\057\000\051\000\052\000\053\000\
\054\000\051\000\052\000\053\000\054\000\000\000\000\000\000\000\
\072\000\000\000\082\000\000\000\056\000\057\000\000\000\000\000\
\056\000\057\000\051\000\052\000\053\000\054\000\051\000\052\000\
\053\000\054\000\000\000\086\000\000\000\116\000\000\000\000\000\
\000\000\056\000\057\000\000\000\000\000\056\000\057\000\051\000\
\052\000\053\000\054\000\051\000\052\000\053\000\054\000\000\000\
\000\000\000\000\137\000\000\000\148\000\000\000\056\000\057\000\
\000\000\000\000\056\000\057\000"

let yycheck = "\009\000\
\000\000\032\000\032\000\003\001\034\001\035\001\001\001\017\000\
\003\001\019\000\020\000\021\000\022\000\001\000\024\000\021\001\
\022\001\028\001\028\000\029\000\031\001\141\000\025\001\143\000\
\027\001\020\001\029\001\003\001\034\001\035\001\030\001\027\001\
\027\001\027\001\037\001\066\000\046\000\019\001\020\001\021\001\
\022\001\051\000\052\000\053\000\054\000\002\001\056\000\057\000\
\079\000\080\000\003\001\028\001\034\001\035\001\031\001\030\001\
\031\001\039\001\003\001\004\001\070\000\030\001\031\001\073\000\
\074\000\075\000\076\000\077\000\078\000\019\001\020\001\021\001\
\022\001\003\001\004\001\005\001\006\001\007\001\008\001\009\001\
\030\001\027\001\003\001\027\001\034\001\035\001\027\001\017\001\
\018\001\027\001\120\000\101\000\102\000\023\001\027\001\031\001\
\127\000\028\001\025\001\025\001\030\001\027\001\032\001\033\001\
\028\001\028\001\028\001\003\001\038\001\028\001\036\001\028\001\
\142\000\003\001\003\001\029\001\003\001\148\000\005\001\006\001\
\007\001\008\001\009\001\029\001\028\001\030\001\136\000\030\001\
\030\001\030\001\017\001\018\001\030\001\001\001\029\001\027\001\
\023\001\024\001\019\001\020\001\021\001\022\001\003\001\030\001\
\005\001\006\001\007\001\008\001\009\001\030\001\027\001\038\001\
\026\001\034\001\035\001\003\001\017\001\018\001\016\001\030\001\
\003\001\028\001\023\001\010\001\011\001\012\001\013\001\014\001\
\015\001\030\001\023\001\031\001\019\001\020\001\021\001\022\001\
\028\001\038\001\003\001\026\001\003\001\028\001\028\001\030\001\
\031\001\022\000\028\001\034\001\035\001\028\001\028\001\028\001\
\039\001\010\001\011\001\012\001\013\001\014\001\015\001\028\001\
\028\001\028\001\019\001\020\001\021\001\022\001\028\001\028\001\
\122\000\026\001\255\255\028\001\047\000\030\001\031\001\010\001\
\011\001\012\001\013\001\014\001\015\001\255\255\039\001\255\255\
\019\001\020\001\021\001\022\001\255\255\255\255\255\255\026\001\
\255\255\028\001\255\255\030\001\031\001\010\001\011\001\012\001\
\013\001\014\001\015\001\255\255\039\001\255\255\019\001\020\001\
\021\001\022\001\255\255\255\255\255\255\026\001\255\255\028\001\
\255\255\030\001\031\001\003\001\255\255\005\001\006\001\007\001\
\008\001\009\001\039\001\010\001\011\001\012\001\013\001\014\001\
\015\001\017\001\018\001\255\255\019\001\020\001\255\255\023\001\
\024\001\255\255\255\255\026\001\255\255\028\001\030\001\030\001\
\031\001\019\001\020\001\021\001\022\001\255\255\038\001\255\255\
\039\001\010\001\011\001\012\001\013\001\014\001\015\001\255\255\
\034\001\035\001\019\001\020\001\255\255\255\255\255\255\255\255\
\255\255\026\001\255\255\028\001\255\255\030\001\031\001\010\001\
\011\001\012\001\013\001\014\001\015\001\255\255\039\001\255\255\
\255\255\010\001\011\001\012\001\013\001\014\001\015\001\026\001\
\255\255\028\001\255\255\030\001\031\001\255\255\255\255\255\255\
\255\255\026\001\255\255\028\001\039\001\030\001\031\001\010\001\
\011\001\012\001\013\001\014\001\015\001\255\255\039\001\255\255\
\019\001\020\001\021\001\022\001\019\001\020\001\021\001\022\001\
\255\255\255\255\255\255\026\001\255\255\255\255\255\255\034\001\
\035\001\255\255\255\255\034\001\035\001\019\001\020\001\021\001\
\022\001\019\001\020\001\021\001\022\001\255\255\255\255\255\255\
\030\001\255\255\028\001\255\255\034\001\035\001\255\255\255\255\
\034\001\035\001\019\001\020\001\021\001\022\001\019\001\020\001\
\021\001\022\001\255\255\028\001\255\255\026\001\255\255\255\255\
\255\255\034\001\035\001\255\255\255\255\034\001\035\001\019\001\
\020\001\021\001\022\001\019\001\020\001\021\001\022\001\255\255\
\255\255\255\255\030\001\255\255\028\001\255\255\034\001\035\001\
\255\255\255\255\034\001\035\001"

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
  FOR\000\
  DOTDOT\000\
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
# 28 "parser.mly"
             (  _1  )
# 356 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 31 "parser.mly"
           ( IntTyp )
# 362 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 32 "parser.mly"
                     ( ArrayTyp (_3, IntTyp) )
# 369 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 33 "parser.mly"
               ( NameTyp _1 )
# 376 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 36 "parser.mly"
                ( _1@_2 )
# 384 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 37 "parser.mly"
                ( [] )
# 390 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ids) in
    Obj.repr(
# 40 "parser.mly"
                     ( List.map (fun x -> VarDec (_1,x)) _2 )
# 398 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 41 "parser.mly"
                              ( [TypeDec (_2,_4)] )
# 406 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 42 "parser.mly"
                                    ( [FuncDec(_2, _4, _1, _6)] )
# 416 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 43 "parser.mly"
                                      ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 425 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 46 "parser.mly"
                       ( _1@[_3] )
# 433 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 47 "parser.mly"
                       ( [_1]  )
# 440 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
                        ( [] )
# 446 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 51 "parser.mly"
                        ( _1 )
# 453 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 54 "parser.mly"
                             ( _1@[(_3,_4)] )
# 462 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 55 "parser.mly"
                             ( [(_1,_2)] )
# 470 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 58 "parser.mly"
                   ( _1@[_2] )
# 478 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 59 "parser.mly"
                   ( [_1] )
# 485 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                              ( Assign (Var _1, _3) )
# 493 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 63 "parser.mly"
                                 ( Assign (Var _1, CallFunc ("+", [VarExp (Var _1); _3])) )
# 501 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 64 "parser.mly"
                                       ( Assign (IndexedVar (Var _1, _3), _6) )
# 510 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 65 "parser.mly"
                              ( If (_3, _5, None) )
# 518 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 67 "parser.mly"
                              ( If (_3, _5, Some _7) )
# 527 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 68 "parser.mly"
                              ( While (_3, _5) )
# 535 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 69 "parser.mly"
                                                 ( For (_3, _5, _7, _9) )
# 545 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 70 "parser.mly"
                              ( CallProc ("sprint", [StrExp _3]) )
# 552 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 71 "parser.mly"
                              ( CallProc ("iprint", [_3]) )
# 559 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 72 "parser.mly"
                           ( CallProc ("scan", [VarExp (Var _3)]) )
# 566 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 73 "parser.mly"
                           ( CallProc ("new", [ VarExp (Var _3)]) )
# 573 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 74 "parser.mly"
                                ( CallProc (_1, _3) )
# 581 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 75 "parser.mly"
                           ( CallProc ("return", [_2]) )
# 588 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 76 "parser.mly"
             ( _1 )
# 595 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "parser.mly"
            ( NilStmt )
# 601 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 80 "parser.mly"
                           ( [] )
# 607 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 81 "parser.mly"
                           ( _1 )
# 614 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 84 "parser.mly"
                          ( _1@[_3] )
# 622 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 85 "parser.mly"
                           ( [_1] )
# 629 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 88 "parser.mly"
                         ( Block (_2, _3) )
# 637 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 91 "parser.mly"
           ( IntExp _1  )
# 644 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 92 "parser.mly"
         ( VarExp (Var _1) )
# 651 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 93 "parser.mly"
                         ( CallFunc (_1, _3) )
# 659 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                     ( VarExp (IndexedVar (Var _1, _3)) )
# 667 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                     ( CallFunc ("+", [_1; _3]) )
# 675 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                      ( CallFunc ("-", [_1; _3]) )
# 683 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 97 "parser.mly"
                      ( CallFunc ("*", [_1; _3]) )
# 691 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                    ( CallFunc ("/", [_1; _3]) )
# 699 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parser.mly"
                        ( CallFunc ("%", [_1; _3]) )
# 707 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 100 "parser.mly"
                    ( CallFunc ("^", [_1; _3]) )
# 715 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 101 "parser.mly"
                   ( CallFunc ("++", [VarExp (Var _1)]) )
# 722 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 102 "parser.mly"
                              ( CallFunc("!", [_2]) )
# 729 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 103 "parser.mly"
                  ( _2 )
# 736 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 744 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 752 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 108 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 760 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 768 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 110 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 776 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 111 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 784 "parser.ml"
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
