type ident = string 

type exp = Var of ident | Int of int | Add of exp * exp 
         | Sub of exp * exp| Mult of exp * exp 
         | Bool of bool | Not of exp | And of exp * exp | Or of exp * exp
         | Eq of exp * exp | If of exp * exp * exp

let next = ref 0
type tident = int
let fresh_tident (u : unit) : tident = next := !next + 1; !next

type typ = Tint | Tbool
type constraints = (typ * typ) list
type context = ident -> typ option


let rec get_constraints (gamma : context) (e : exp) : (typ * constraints) option =
 ( match e with
  | Var x -> (match gamma x with Some t -> Some (t, []) | None -> None)
  | Int i -> Some (Tint, [])
  | Bool b -> Some (Tbool, [])
  | Eq (e1, e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                     | Some (t1, c1), Some (t2, c2) ->  Some (Tbool, (t1, t2) :: c1 @ c2)
                     | _, _ -> None)
  | And( e1, e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                    | Some (t1, c1), Some (t2, c2) ->  Some (Tbool, (t1, t2) :: c1 @ c2)
                    | _, _ -> None)
  | Or( e1, e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                    | Some (t1, c1), Some (t2, c2) ->  Some (Tbool, (t1, t2) :: c1 @ c2)
                    | _, _ -> None)
  | If (e', e1, e2) -> (match get_constraints gamma e', get_constraints gamma e1, get_constraints gamma e2 with
                     | Some (t, c), Some (t1, c1), Some (t2, c2) -> Some (t1, (t, Tbool) :: (t1, t2) :: c @ c1 @ c2)
                     | _, _, _ -> None)
  | Not e' -> (match get_constraints gamma e' with
					 | Some (t, c) -> Some (Tbool, (t, Tbool) :: c)
					 | _ -> None)
  | Sub( e1, e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                    | Some (t1, c1), Some (t2, c2) ->  Some (Tint, (t1, t2) :: c1 @ c2)
                    | _, _ -> None)
  | Add( e1, e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                    | Some (t1, c1), Some (t2, c2) ->  Some (Tint, (t1, t2) :: c1 @ c2)
                    | _, _ -> None)
  | Mult( e1, e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                    | Some (t1, c1), Some (t2, c2) ->  Some (Tint, (t1, t2) :: c1 @ c2)
                    | _, _ -> None)

  )