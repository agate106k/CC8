```parser.mly
%token PERCENT POW INCREMENT

    | expr PERCENT expr { CallFunc ("%", [$1; $3]) }  /* %追加 */
    | expr POW expr { CallFunc ("^", [$1; $3]) }
    | ID INCREMENT { CallFunc ("++", [VarExp (Var $1)]) }
```
```semant.ml
          | CallFunc ("%", [left; right]) -> 
               (check_int (type_exp left env); check_int(type_exp right env); INT)
          | CallFunc ("^", [base; exponent]) -> 
               (check_int (type_exp base env); check_int(type_exp exponent env); INT)
          | CallFunc ("++", [VarExp v]) -> 
               (check_int (type_exp (VarExp v) env); INT)
```

```emitter.ml
                 | CallFunc ("%", [left; right]) ->
                                          trans_exp left nest env
                                          ^ trans_exp right nest env
                                          ^ "\tpopq %rbx\n"
                                          ^ "\tpopq %rax\n"
                                          ^ "\tcqto\n"
                                          ^ "\tidivq %rbx\n"
                                          ^ "\tmovq %rdx, %rax\n"
                                          ^ "\tpushq %rax\n"
```



                  (* ^のコード *)
                  | CallFunc ("^", [left; right]) ->
                      trans_exp left nest env
                    ^ trans_exp right nest env
                    ^ "\tpopq %rax\n"
                    ^ "\tpopq %rbx\n"
                    ^ "\tmovq $1, %rcx\n"
                    ^ "\tcmpq $0, %rbx\n"
                    ^ "\tje L_end\n"
                    ^ "L_loop:\n"
                    ^ "\timulq %rax, %rcx\n"
                    ^ "\tdecq %rbx\n"
                    ^ "\tcmpq $0, %rbx\n"
                    ^ "\tjne L_loop\n"
                    ^ "L_end:\n"
                    ^ "\tpushq %rcx\n"
                  (* ++のコード *)
                  | CallFunc ("++", [VarExp v]) ->
                      trans_var v nest env
                    ^ "\tmovq (%rax), %rbx\n"
                    ^ "\tincq %rbx\n"
                    ^ "\tmovq %rbx, (%rax)\n"
                    ^ "\tpushq %rbx\n"