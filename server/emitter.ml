open Ast
open Printf
open Types
open Table
open Semant

let label = ref 0
let incLabel() = (label := !label+1; !label)

(* str を n 回コピーする *)
let rec nCopyStr n str =
    if n > 0 then str ^ (nCopyStr (pred n) str) else ""

(* 呼出し時にcalleeに渡す静的リンク *)
let passLink src dst = 
  if src >= dst then 
    let deltaLevel = src-dst+1 in
      "\tmovq %rbp, %rax\n"
     ^ nCopyStr deltaLevel "\tmovq 16(%rax), %rax\n"
     ^ "\tpushq %rax\n"
  else
    "\tpushq %rbp\n"   

let output = ref ""

(* printfやscanfで使う文字列 *)
let io =  "IO:\n\t.string \"%lld\"\n"
            ^ "\t.text\n"
(* main関数の頭 *)
let header =  "\t.globl main\n"
            ^ "main:\n"
            ^ "\tpushq %rbp\n"        (* フレームポインタの保存 *)
            ^ "\tmovq %rsp, %rbp\n"   (* フレームポインタをスタックポインタの位置に *)
(* プロローグとエピローグ *)
let prologue = "\tpushq %rbp\n"       (* フレームポインタの保存 *)
             ^ "\tmovq %rsp, %rbp\n"  (* フレームポインタのスタックポインタ位置への移動 *)
let epilogue = "\tleaveq\n"            (* -> movq %ebp, %esp; popl %ebp *)
             ^ "\tretq\n"              (* 呼出し位置の次のアドレスへ戻る *)

(* 宣言部の処理：変数宣言->記号表への格納，関数定義->局所宣言の処理とコード生成 *)
let rec trans_dec ast nest tenv env = match ast with
  (* 関数定義の処理 *)
  | FuncDec (s, l, _, block) -> 
      (* 仮引数の記号表への登録 *)
      let env' = type_param_dec l (nest + 1) tenv env in 
      (* 関数本体（ブロック）の処理 *)
      let code = trans_stmt block (nest + 1) tenv env' in
      (* 関数コードの合成 *)
      output := !output ^
                s ^ ":\n"               (* 関数ラベル *)
                ^ prologue              (* プロローグ *)
                ^ code                  (* 本体コード *)
                ^ epilogue;             (* エピローグ *)
      ""
  (* 初期化付き変数宣言の処理 *)
  | InitVarDec (t, s, e) ->
      let var_code = trans_var (Var s) nest env in
      let exp_code = trans_exp e nest env in
      exp_code ^ var_code ^ "\tpopq (%rax)\n"
  (* 変数宣言の処理 *)
  | VarDec (t, s) -> ""
  (* 型宣言の処理 *)
  | TypeDec (s, t) -> 
      let entry = tenv s in
      match entry with
          (NAME (_, ty_opt)) -> ty_opt := Some (create_ty t tenv);
          ""
        | _ -> raise (Err s)
(* 文の処理 *)
and trans_stmt ast nest tenv env = 
                 type_stmt ast env;
                 match ast with
                  (* 代入のコード：代入先フレームをsetVarで求める．*)
                     Assign (v, e) -> trans_exp e nest env
                                    ^ trans_var v nest env
                                    ^ "\tpopq (%rax)\n"
                  
                   (* iprintのコード *)
                   | CallProc ("iprint", [arg]) -> 
                           (trans_exp arg nest env
                        ^  "\tpopq  %rsi\n"
                        ^  "\tleaq IO(%rip), %rdi\n"
                        ^  "\tmovq $0, %rax\n"
                        ^  "\tcallq printf\n")
                   (* sprintのコード *)
                   | CallProc ("sprint", [StrExp s]) -> 
                       (let l = incLabel() in
                              ("\t.data\n"
                            ^ sprintf "L%d:\t.string %s\n" l s
                            ^ "\t.text\n"
                            ^ sprintf "\tleaq L%d(%%rip), %%rdi\n" l 
                            ^  "\tmovq $0, %rax\n"     
                            ^ "\tcallq printf\n"))
                   (* scanのコード *)
                   | CallProc ("scan", [VarExp v]) ->
                               (trans_var v nest env
                             ^ "\tmovq %rax, %rsi\n"
                             ^ "\tleaq IO(%rip), %rdi\n"
                             ^ "\tmovq $0, %rax\n"
                             ^ "\tcallq scanf\n")
                  (* returnのコード *)
                  | CallProc ("return", [arg]) ->
                              trans_exp arg nest env
                            ^ "\tpopq %rax\n"
                  | CallProc ("new", [VarExp v]) ->
                        let size = calc_size (type_var v env) in
                      sprintf "\tmovq $%d, %%rdi\n" size
                            ^ "\tcallq malloc\n"
                            ^ "\tpushq %rax\n"
                            ^  trans_var v nest env
                            ^  "\tpopq (%rax)\n"
                  (* 手続き呼出しのコード *)
                  | CallProc (s, el) -> 
                      let entry = env s in 
                         (match entry with
                             (FunEntry {formals=_; result=_; level=level}) -> 
                                 (* 実引数のコード *)
                                 (* 16バイト境界に調整 *)
                                 (if (List.length el) mod 2 = 1 then "" else "\tpushq $0\n")
                               ^ List.fold_right  (fun  ast code -> code ^ (trans_exp ast nest env)) el "" 
                                 (* 静的リンクを渡すコード *)
                               ^  passLink nest level
                                 (* 関数の呼出しコード *)
                               ^  "\tcallq " ^ s ^ "\n"
                                 (* 積んだ引数+静的リンクを降ろす *)
                               ^  sprintf "\taddq $%d, %%rsp\n" ((List.length el + 1 + 1) / 2 * 2 * 8) 
                            | _ -> raise (No_such_symbol s)) 
                  (* ブロックのコード：文を表すブロックは，関数定義を無視する．*)
                  | Block (dl, sl) -> 
                      let (tenv', env', addr') = type_decs dl nest tenv env in
                      let decs_code = List.fold_left (fun code dec -> code ^ trans_dec dec nest tenv' env') "" dl in
                      let ex_frame = sprintf "\tsubq $%d, %%rsp\n" ((-addr' + 16) / 16 * 16) in
                      let stmts_code = List.fold_left (fun code stmt -> code ^ trans_stmt stmt nest tenv' env') "" sl in
                      decs_code ^ ex_frame ^ stmts_code
                                (* elseなしif文のコード *)
                  | If (e,s,None) -> let (condCode,l) = trans_cond e nest env in
                                                  condCode
                                                ^ trans_stmt s nest tenv env
                                                ^ sprintf "L%d:\n" l
                  (* elseありif文のコード *)
                  | If (e,s1,Some s2) -> let (condCode,l1) = trans_cond e nest env in
                                            let l2 = incLabel() in 
                                                  condCode
                                                ^ trans_stmt s1 nest tenv env
                                                ^ sprintf "\tjmp L%d\n" l2
                                                ^ sprintf "L%d:\n" l1
                                                ^ trans_stmt s2 nest tenv env 
                                                ^ sprintf "L%d:\n" l2

                  (* do-while文のコード *)
                  | DoWhile (s,e) -> let (condCode, l1) = trans_cond e nest env in
                                      let l2 = incLabel() in
                                          sprintf "L%d:\n" l2
                                        ^ trans_stmt s nest tenv env
                                        ^ condCode
                                        ^ sprintf "\tjmp L%d\n" l2
                                        ^ sprintf "L%d:\n" l1
                  (* while文のコード *)
                  | While (e,s) -> let (condCode, l1) = trans_cond e nest env in
                                     let l2 = incLabel() in
                                         sprintf "L%d:\n" l2 
                                       ^ condCode
                                       ^ trans_stmt s nest tenv env
                                       ^ sprintf "\tjmp L%d\n" l2
                                       ^ sprintf "L%d:\n" l1
                  | For (v, e1, e2, s) ->
                                       trans_stmt (Assign(Var v, e1)) nest tenv env
                                       ^ let (condCode, l1) = trans_cond (CallFunc ("<", [(VarExp (Var v)); e2])) nest env in
                                       let l2 = incLabel() in sprintf "L%d:\n" l2  (* コロンを追加 *)
                                       ^ condCode
                                       ^ trans_stmt s nest tenv env
                                       ^ trans_exp (IncExp(Var v)) nest env
                                       ^ sprintf "\tjmp L%d\n" l2
                                       ^ sprintf "L%d:\n" l1
                  (* 空文 *)
                  | NilStmt -> ""
(* 参照アドレスの処理 *)
and trans_var ast nest env = match ast with
                   Var s -> let entry = env s in 
                        (match entry with
                            VarEntry {offset=offset; level=level; ty=_} -> 
                                  "\tmovq %rbp, %rax\n" 
                                ^ nCopyStr (nest-level) "\tmovq 16(%rax), %rax\n"
                                ^ sprintf "\tleaq %d(%%rax), %%rax\n" offset
                           | _ -> raise (No_such_symbol s))
                 | IndexedVar (v, size) -> 
                            trans_exp (CallFunc("*", [IntExp 8; size])) nest env
                          ^ trans_var v nest env
                          ^ "\tmovq (%rax), %rax\n"
                          ^ "\tpopq %rbx\n"
                          ^ "\tleaq (%rax,%rbx), %rax\n"
(* 式の処理 *)
and trans_exp ast nest env = match ast with
                  (* 整数定数のコード *)
                    IntExp i -> (sprintf "\tpushq $%d\n" i)
                  (* 変数参照のコード：reVarで参照フレームを求める *)
                  | VarExp v -> 
                             trans_var v nest env
                           ^ "\tmovq (%rax), %rax\n"
                           ^ "\tpushq %rax\n"
                  | IncExp v ->
                           trans_var v nest env
                           ^ "\tmovq (%rax), %rbx\n"  (* 値を一時的なレジスタに保存 *)
                           ^ "\taddq $1, %rbx\n"  (* 値を増加させる *)
                           ^ "\tmovq %rbx, (%rax)\n"  (* 値を元の位置に保存 *)
                           ^ "\tsubq $1, %rbx\n"  (* 元の値を復元 *)
                           ^ "\tpushq %rbx\n"  (* 元の値をスタックにプッシュ *)
                  (* +のコード *)
                  | CallFunc ("+", [left; right]) -> 
                                             trans_exp left nest env
                                           ^ trans_exp right nest env
                                           ^ "\tpopq %rax\n"
                                           ^ "\taddq %rax, (%rsp)\n"
                  (* -のコード *)
                  | CallFunc ("-", [left; right]) ->
                                             trans_exp left nest env
                                           ^ trans_exp right nest env
                                           ^ "\tpopq %rax\n"
                                           ^ "\tsubq %rax, (%rsp)\n"
                  (* *のコード *)
                  | CallFunc ("*", [left; right]) ->
                                             trans_exp left nest env
                                           ^ trans_exp right nest env
                                           ^ "\tpopq %rax\n"
                                           ^ "\timulq (%rsp), %rax\n"
                                           ^ "\tmovq %rax, (%rsp)\n"
                  (* ^のコード *)
| CallFunc ("^", [base; exp]) ->
    let base_code = trans_exp base nest env in
    let exp_code = trans_exp exp nest env in
    let loop_label = incLabel() in
    let end_label = incLabel() in
    base_code
  ^ exp_code
  ^ "\tpopq %rbx\n"  (* 指数を %rbx に格納 *)
  ^ "\tpopq %rax\n"  (* 基数を %rax に格納 *)
  ^ "\tmovq $1, %rcx\n"  (* 結果の初期値を 1 に設定 *)
  ^ sprintf "L%d:\n" loop_label
  ^ "\ttestq %rbx, %rbx\n"  (* 指数が 0 かどうかテスト *)
  ^ sprintf "\tje L%d\n" end_label  (* 0 なら終了ラベルへジャンプ *)
  ^ "\timulq %rax, %rcx\n"  (* 結果に基数を掛ける *)
  ^ "\tdecq %rbx\n"  (* 指数をデクリメント *)
  ^ sprintf "\tjmp L%d\n" loop_label  (* ループラベルへジャンプ *)
  ^ sprintf "L%d:\n" end_label
  ^ "\tpushq %rcx\n"  (* 結果をスタックにプッシュ *)
                  (* /のコード *)
                  
                  | CallFunc ("/", [left; right]) ->
                                             trans_exp left nest env
                                           ^ trans_exp right nest env
                                           ^ "\tpopq %rbx\n"
                                           ^ "\tpopq %rax\n"
                                           ^ "\tcqto\n"
                                           ^ "\tidivq %rbx\n"
                                           ^ "\tpushq %rax\n"
                  (* %のコード *)
                  | CallFunc ("%", [left; right]) ->
                                          trans_exp left nest env
                                          ^ trans_exp right nest env
                                          ^ "\tpopq %rbx\n"
                                          ^ "\tpopq %rax\n"
                                          ^ "\tcqto\n"
                                          ^ "\tidivq %rbx\n"
                                          ^ "\tmovq %rdx, %rax\n"
                                          ^ "\tpushq %rax\n"
                  (* 反転のコード *)
                  | CallFunc("!",  arg::_) -> 
                                             trans_exp arg nest env
                                           ^ "\tnegq (%rsp)\n"
                  (* 関数呼出しのコード *)
                  | CallFunc (s, el) -> 
                                 trans_stmt (CallProc(s, el)) nest initTable env 
                                 (* 返戻値は%raxに入れて返す *)
                               ^ "\tpushq %rax\n"
                  | _ -> raise (Err "internal error")
(* 関係演算の処理 *)
and trans_cond ast nest env = match ast with
                  | CallFunc (op, left::right::_) -> 
                      (let code = 
                       (* オペランドのコード *)
                          trans_exp left nest env
                        ^ trans_exp right nest env
                       (* オペランドの値を %rax，%rbxへ *)
                        ^ "\tpopq %rax\n"
                        ^ "\tpopq %rbx\n"
                       (* cmp命令 *)                       
                        ^ "\tcmpq %rax, %rbx\n" in
                          let l = incLabel () in
                             match op with
                               (* 条件と分岐の関係は，逆 *)
                                "==" -> (code ^ sprintf "\tjne L%d\n" l, l)
                              | "!=" -> (code ^ sprintf "\tje L%d\n"l, l)
                              | ">"  -> (code ^ sprintf "\tjle L%d\n" l, l)
                              | "<"  -> (code ^ sprintf "\tjge L%d\n" l, l)
                              | ">=" -> (code ^ sprintf "\tjl L%d\n" l, l)
                              | "<=" -> (code ^ sprintf "\tjg L%d\n" l, l)
                              | _ -> ("",0))
                 | _ -> raise (Err "internal error")
(* プログラム全体の生成 *)
let trans_prog ast = let code = trans_stmt ast 0 initTable initTable in
                                io ^ header ^ code ^ epilogue ^ (!output)
