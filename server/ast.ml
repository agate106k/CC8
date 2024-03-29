

(* The definition of the abstract syntax tree *)
type id = string
type var = Var of id | IndexedVar of var * exp
and stmt = Assign of var * exp        
        | CallProc of id * (exp list)
        | Block of (dec list) * (stmt list)
        | If of exp * stmt * (stmt option)
        | DoWhile of stmt * exp
        | While of exp * stmt
        | For of id * exp * exp * stmt
        | NilStmt
and exp = VarExp of var | StrExp of string | IntExp of int 
        | CallFunc of id * (exp list)
        | IncExp of var
and dec = FuncDec of id * ((typ*id) list) * typ * stmt
        | TypeDec of id * typ
        | VarDec of typ * id
        | InitVarDec of typ * id * exp
and typ = NameTyp of string
        | ArrayTyp of int * typ
        | IntTyp
        | VoidTyp

