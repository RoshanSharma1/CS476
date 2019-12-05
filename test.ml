(* Test Cases *)

let test1 : exp = (GetField ((Struct [("Shape", Int 1); ("Side", Bool false)]), "Side"))
let res1 = infer_type test1
(* res1 = Some Tbool *)

let test2 : exp = Fst (Tuple (Add (Int 6, Int 8), Or (Bool true, Bool false)))
let res2 = infer_type test2
(* res2 = Some Tint *)

let test3 : exp = If (Not (Bool true), test1, Bool true)
let res3 = infer_type test3
(* res3 = Some Tbool *)

let test4 : exp = If (Not (Bool true), test1, Int 8)
let res4 = infer_type test4
(* res3 = None *)

let s1 : exp = Struct [("Shape", Int 1); ("Side", Bool false); ("id", Int 87)]
let test5 : cmd = SetField (s1, "id", Mult (GetField (s1, "Shape"), Int 5))
let res5 = infer_type_c empty_context test5
(* bool = true *)

let test6 : cmd = SetField (s1, "Side", And (GetField (s1, "Side"), Bool true))
let res6 = infer_type_c empty_context test6
(* bool = true *)

let test7 : cmd = Seq (IfC (test3, test5, Skip),
                        While (test1, test6))
let res7 = infer_type_c empty_context test7
(* bool = true *)

let test8 : cmd = Seq (IfC (test2, test5, Skip),
                        While (test1, test6))
let res8 = infer_type_c empty_context test8
(* bool = false *)

let test9 : cmd = Seq ((Assign ("x", Int 5)), Assign ("y", Add ( Var "x", Int 6)))
let res9 = infer_type_c empty_context test9
(* bool = true *)

let c1 : cmd = Seq (Seq ((Assign ( "x", Add (Var "a", Fst (Var "c")))), Assign("y", And (Var "b", Snd (Var "c")))),
                   Return (Int 0))
let test10 : func = (Tint, [(Tint, "a"); (Tbool, "b"); (Ttuple (Tint, Tbool), "c")], c1)
let res10 = update_func_gamma empty_context test10
(* Context = {a = Tint, b = Tbool, c = Ttuple(Tint, Tbool)} *)
let res10_5 = infer_type_func test10
(* bool = true *)

let test11 : cmd = Call ("x", "test10", [Int 3; Bool true; Tuple ((Int 6, Bool false))])
let res11 = infer_type_c (update empty_context "test10" (make_func_type test10)) test11
(* bool = true *)

let p : prog = ([test10], test11)


