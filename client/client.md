これを足すとコメントできる
| "//"                    { comment lexbuf }
and comment = parse
| '\n'                    { lexer lexbuf }
| _                       { comment lexbuf }





これを足すと

https://github.com/agate106k/CC8/pull/1

