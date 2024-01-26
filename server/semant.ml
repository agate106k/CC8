open Ast
open Types
open Table

exception Err of string
exception TypeErr of string

let rec calc_size ty = match ty with
                   ARRAY (n, t, _) -> n * (calc_size t)
                 | INT -> 8
                 | _ -> raise (Err "internal error")

let actual_ty ty =
   let rec travTy t l = 
      match t with 
         NAME (s, tyref) -> 
             (match !tyref with 
                Some actty -> if List.mem actty l then raise (TypeErr "cyclic type definition")
                              else travTy (actty) (actty::l)
              | None -> raise (TypeErr "no actual type"))
       | _ -> t
   in travTy ty [ty]

let check_int ty = if ty != INT then raise (TypeErr "type error 1")

let check_array ty = 
          match ty with
             ARRAY _ -> ()
           | _ -> raise (TypeErr "type error 2")

exception SymErr of string
let rec check_redecl decs tl vl = 
     match decs with
         [] -> ()
       | FuncDec (s,_,_,_)::rest -> if List.mem s vl then raise (SymErr s)
                                    else check_redecl rest tl (s::vl) 
       | VarDec (_,s)::rest -> if List.mem s vl then raise (SymErr s)
                               else check_redecl rest tl (s::vl) 
       | TypeDec (s,_)::rest -> if List.mem s tl then raise (SymErr s)
                                else check_redecl rest (s::tl) vl 
(* 型式の生成 *)
let rec create_ty ast tenv =
    match ast with
        NameTyp id -> tenv id
      | ArrayTyp (size, typ) -> ARRAY (size, create_ty typ tenv, ref ())
      | IntTyp -> INT 
      | VoidTyp -> UNIT

(* 実引数は，%rbp から +24 のところにある．*)
let savedARG = 24 (* return address,  static link, old %rbp *)

(* 関数のシグネチャを保持するための環境を定義する *)
let function_env = ref []

(* 関数のシグネチャを環境に追加する *)
let enter_function name ret_type arg_types =
  function_env := (name, ret_type, arg_types) :: !function_env

(* 現在の関数の返戻値の型を取得する *)
let current_function_return_type () =
  match !function_env with
  | (name, ret_type, arg_types) :: _ -> ret_type
  | [] -> raise (Failure "No function currently being processed")


let rec type_dec ast (nest, addr) tenv env =
   match ast with
      (* 関数定義の処理 *)
      FuncDec (s, l, rlt, Block (dl,sl)) -> 
      (* 関数名の記号表への登録 *)
      check_redecl ((List.map (fun (t,s) -> VarDec (t,s)) l) @ dl) [] [];
      let formals = List.map (fun (typ,_) -> create_ty typ tenv) l in
      let result = create_ty rlt tenv in
      let env' = update s (FunEntry {formals=formals; result=result; level=nest+1}) env in
      (* 関数のシグネチャを環境に追加 *)
      enter_function s result formals;
      (* 関数本体のステートメントリストに対する型チェックを追加 *)
      let has_return = List.exists (function CallProc ("return", _) -> true | _ -> false) sl in
      if actual_ty result != UNIT && not has_return then
          raise (TypeErr "function must have a return statement");
      (tenv, env', addr)
    (* 変数宣言の処理 *)
    | VarDec (t,s) -> (tenv, 
              update s (VarEntry {ty= create_ty t tenv; offset=addr-8; level=nest}) env, addr-8)
    (* 型宣言の処理 *)
    | TypeDec (s,t) -> let tenv' = update s (NAME (s,ref None)) tenv in (tenv', env, addr)
    | _ -> raise (Err "internal error")
and type_decs dl nest tenv env =
         List.fold_left 
                (fun (tenv,env,addr) d ->  type_dec d (nest,addr) tenv env) (tenv,env,0) dl
and type_param_dec args nest tenv env =
         let (env',_) = List.fold_left (fun (env,addr) (t,s) -> 
           (update s (VarEntry {offset=addr; 
                       level=nest; ty=create_ty t tenv}) env, addr+8)) 
                                                      (env,savedARG) args in env'
and type_stmt ast env = 
       match ast with
            CallProc ("scan", [arg]) ->
                    if (type_exp arg env) != INT then 
                          raise (TypeErr "type error 3")
          | CallProc ("iprint", [arg]) -> 
                    if (type_exp arg env) != INT then
                          raise (TypeErr "iprint requires int value")
                    (* return 文の型チェックを行う *)
          | CallProc ("return", []) ->
                     let current_fun_type = current_function_return_type () in
                     if current_fun_type != UNIT then
                          raise (TypeErr "non-void function must return a value")
          (* return 文の型チェックを行う *)
          | CallProc ("return", args) ->
          let current_fun_type = current_function_return_type () in
          (match args, current_fun_type with
               | [], UNIT -> ()  (* void関数のreturn文のチェック *)
               | [arg], _ ->  (* 値を返すreturn文のチェック *)
               let arg_type = type_exp arg env in
               if actual_ty arg_type != actual_ty current_fun_type then
                    raise (TypeErr "return expression type does not match function return type")
               | [], _ ->  (* non-void関数が値を返さない場合のチェック *)
               raise (TypeErr "non-void function must return a value")
               | _ -> raise (Err "invalid return statement"))

          | CallProc ("sprint", _) -> ()
          | CallProc ("new", [VarExp (Var s)]) -> let entry = env s in 
                    (match entry with
                          VarEntry {ty=ty; _} -> check_array (actual_ty ty)
                        | _ -> raise (No_such_symbol s))
          | CallProc (s, el) -> 
                    let _ = type_exp (CallFunc (s, el)) env in ()
          | Block (dl, _) -> check_redecl dl [] []
          | Assign (v, e) -> 
               if (type_var v env) != (type_exp e env) then raise (TypeErr "type error 4")
          | If (e,_,_) -> type_cond e env
          | DoWhile (s, e) ->
               (* (check_int (type_exp e env); type_stmt s env) *)
               type_cond e env
          | While (e,_) -> type_cond e env
          | NilStmt -> ()
and type_var ast env =
       match ast with
            Var s -> let entry = env s in 
                    (match entry with
                          VarEntry {ty=ty; _ } -> (actual_ty ty)
                        | _ -> raise (No_such_symbol s))
          | IndexedVar (v, size) -> 
                    (check_int (type_exp size env);
                     match type_var v env with
                             ARRAY (_,ty,_) -> (actual_ty ty)
                        |  _ -> raise (TypeErr "type error 5"))
and type_exp ast env = 
        match ast with
            VarExp s -> type_var s env
          | IntExp i -> INT
          | IncExp v -> (check_int (type_exp (VarExp v) env); INT)
          | CallFunc ("+", [left; right]) -> 
               (check_int (type_exp left env); check_int(type_exp right env); INT)
          | CallFunc ("-", [left; right]) -> 
               (check_int (type_exp left env); check_int(type_exp right env); INT)
          | CallFunc ("*", [left; right]) -> 
               (check_int (type_exp left env); check_int(type_exp right env); INT)
          | CallFunc ("/", [left; right]) -> 
               (check_int (type_exp left env); check_int(type_exp right env); INT)
          | CallFunc ("%", [left; right]) -> 
               (check_int (type_exp left env); check_int(type_exp right env); INT)
          | CallFunc ("^", [base; exponent]) -> 
               (check_int (type_exp base env); check_int(type_exp exponent env); INT)
          | CallFunc ("!", [arg]) -> 
               (check_int (type_exp arg env); INT)
          | CallFunc (s, el) -> 
               let entry = env s in 
                  (match entry with
                     (FunEntry {formals=fpTyl; result=rltTy; level=_}) -> 
                         if List.length fpTyl == List.length el then 
                             let fpTyl' = List.map actual_ty fpTyl 
                             and apTyl = List.map (fun e -> type_exp e env) el in
                                let l = List.combine fpTyl' apTyl in 
                                    if List.for_all (fun (f,a) -> f == a) l then actual_ty rltTy
                                    else raise (TypeErr "type error 6")
                        else raise (TypeErr "type error 7")
                   | _ -> raise (No_such_symbol s))
          | _ -> raise (Err "internal error")
and type_cond ast env =  
       match ast with
            CallFunc (_, [left; right]) -> 
               (check_int (type_exp left env); check_int(type_exp right env))
          | _ -> raise (Err "internal error")
