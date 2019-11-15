type exp = Int of int | Add of exp * exp | Sub of exp * exp
         | Bool of bool | And of exp * exp | Or of exp * exp
         | Eq of exp * exp | If of exp * exp * exp

type cmd = Assign of ident * exp | Seq of cmd * cmd | Skip
         | IfC of exp * cmd * cmd | While of exp * cmd
         | Call of ident * ident * exp list | Return of exp

type typ = Tint | Tbool


let rec type_of (e : exp) : typ option = 
      match e with 
          | Int n -> Some(Tint)
          | Add (e1,e2) -> (match type_of e1, type_of e2 with
                            | Some (Tint), Some (Tint) -> Some (Tint)
                            | _, _ -> None)
          | Sub (e1,e2) -> (match type_of e1, type_of e2 with
                            | Some (Tint), Some (Tint) -> Some (Tint)
                            | _, _ -> None)
          | Bool b -> Some (Tbool)
          | And (e1,e2) -> (match type_of e1, type_of e2 with
                            | Some (Tbool), Some (Tbool) -> Some (Tbool)
                            | _, _ -> None)
          | Or (e1,e2) -> (match type_of e1, type_of e2 with
                            | Some (Tbool), Some (Tbool) -> Some (Tbool)
                            | _, _ -> None)
          | Eq (e1,e2) ->  (match type_of e1, type_of e2 with
                             | Some (Tbool), Some (Tbool) -> Some (Tbool)
                             | Some (Tint), Some (Tint) -> Some (Tbool) 
                             | _, _ -> None)
          | If (e, e1, e2) -> match type_of e with 
                                | Some (Tbool) -> (match type_of e1, type_of e2 with
                                      | Some (Tbool), Some (Tbool) -> Some (Tbool)
                                      | Some (Tint), Some (Tint) -> Some (Tint) 
                                      | _, _ -> None)
                                | _ ->None
