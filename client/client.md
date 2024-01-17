これを足すとコメントできる
| "//"                    { comment lexbuf }
and comment = parse
| '\n'                    { lexer lexbuf }
| _                       { comment lexbuf }