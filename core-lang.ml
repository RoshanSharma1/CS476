open List

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

type substitution = tident -> typ option
let empty_subst : substitution = fun _ -> None
let empty_context : context = fun _ -> None
let update g x t = fun y -> if y = x then Some t else g y
let single_subst x t : substitution = update empty_subst x t
                                        
let rec apply_subst (s : substitution) (t : typ) : typ =
  match t with
  | Tint -> Tint
  | Tbool -> Tbool
  | Ttuple (t1, t2) -> Ttuple (apply_subst s t1, apply_subst s t2)
  | TArray t1 -> TArray (apply_subst s t1)
  | Tvar x -> (match s x with Some t -> t | None -> Tvar x)

let compose_subst s1 s2 = fun x ->
  match s2 x with
  | Some t -> Some (apply_subst s1 t)
  | None -> s1 x

let apply_subst_c (s : substitution) (c : constraints) : constraints =
  map (fun (t1, t2) -> (apply_subst s t1, apply_subst s t2)) c

let rec fv (t : typ) =
  match t with
  | Tvar x -> [x]
  | TArray t1 -> fv t1
  | Ttuple (t1, t2) -> fv t1 @ fv t2
  | _ -> []
  
  let rec unify (c : constraints) : substitution option =
   match c with
   | [] -> Some empty_subst
   | (s, t) :: rest ->
      if s = t then unify rest else
        match s, t with
        | Tvar x, _ -> if exists (fun y -> y = x) (fv t) then None else
                         let s1 = single_subst x t in
                         (match unify (apply_subst_c s1 rest) with
                          | Some s' -> Some (compose_subst s' s1)
                          | None -> None)
        | _, Tvar x -> if exists (fun y -> y = x) (fv s) then None else
                         let s1 = single_subst x s in
                         (match unify (apply_subst_c s1 rest) with
                          | Some s' -> Some (compose_subst s' s1)
                          | None -> None)
        | TArray s1, TArray t1 -> unify ((s1, t1) :: rest)
        | Ttuple (s1, s2), Ttuple (t1, t2) -> unify ((s1, t1) :: (s2, t2) :: rest)
        | _, _ -> None

let infer_type (e : exp) =
         match get_constraints empty_context e with
         | Some (t, c) ->
            (match unify c with
             | Some s -> Some (apply_subst s t)
             | None -> None)
         | None -> None