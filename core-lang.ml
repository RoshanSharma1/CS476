type ident = string 

type exp = Var of ident | Int of int | Add of exp * exp 
         | Sub of exp * exp| Mult of exp * exp 
         | Bool of bool | Not of exp | And of exp * exp | Or of exp * exp
         | Eq of exp * exp | If of exp * exp * exp | Array of ident * exp
         | Tuple of exp * exp | Fst of exp | Snd of exp

let next = ref 0
type tident = int
let fresh_tident (u : unit) : tident = next := !next + 1; !next

type typ = Tint | Tbool | TArray of typ | Tvar of tident | Ttuple of typ * typ
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
  | Array (x, e') -> (match gamma x, get_constraints gamma e' with 
                    | Some t1, Some (t2, c) -> 
                                    let t = fresh_tident () in
                                    Some (Tvar t,(t1, (TArray (Tvar t))) :: (t2, Tint) :: c)
                    | _, _ -> None)
  | Tuple (e1, e2) ->
     (match get_constraints gamma e1, get_constraints gamma e2 with
      | Some (t1, c1), Some (t2, c2) ->
         Some (Ttuple (t1, t2), c1 @ c2)
      | _, _ -> None)
  | Fst e ->
     (match get_constraints gamma e with
      | Some (t, c) ->
         let t1 = fresh_tident () in
         let t2 = fresh_tident () in
         Some (Tvar t1, (t, Ttuple (Tvar t1, Tvar t2)) :: c)
      | None -> None)
  | Snd e ->
     (match get_constraints gamma e with
      | Some (t, c) ->
         let t1 = fresh_tident () in
         let t2 = fresh_tident () in
         Some (Tvar t2, (t, Ttuple (Tvar t1, Tvar t2)) :: c)
      | None -> None)

  )