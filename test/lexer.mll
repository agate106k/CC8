(* File lexer.mll *)
{
 open Parser  
 exception No_such_symbol
 open ErrorFlag
 let line = ref 1
}

let digit = ['0'-'9']
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9']*

rule lexer = parse
| digit+ as num  { NUM (int_of_string num) }
| "if"                    { IF }
| "else"                  { ELSE }
| "while"                 { WHILE }
| "scan"                  { SCAN }
| "sprint"                { SPRINT }
| "iprint"                { IPRINT }
| "int"                   { INT }
| "return"                { RETURN }
| "type"                  { TYPE }
| "void"                  { VOID }
| id as text              { ID text }
| '\"'[^'\"']*'\"' as str { STR str }
| '='                     { ASSIGN }
| "=="                    { EQ }
| "!="                    { NEQ }
| '>'                     { GT }
| '<'                     { LT }
| ">="                    { GE }
| "<="                    { LE }
| '+'                     { PLUS }
| '-'                     { MINUS }
| '*'                     { TIMES }
| '/'                     { DIV }
| '{'                     { LB  }
| '}'                     { RB  }
| '['                     { LS }
| ']'                     { RS }
| '('                     { LP  }
| ')'                     { RP  }
| ','                     { COMMA }
| ';'                     { SEMI }
| "//"                    { comment lexbuf }
| ['\n']                  { incr line; Lexing.new_line lexbuf; lexer lexbuf }
| [' ' '\t']              { lexer lexbuf }
| eof                     { raise End_of_file }

| _ {
    ErrorFlag.set_error (); (* エラーを記録 *)
    ERROR (* ERRORトークンを返す *)
  }
and comment = parse
  | '\n' { incr line; Lexing.new_line lexbuf; lexer lexbuf }
  | _    { comment lexbuf }
  | eof { raise End_of_file }
