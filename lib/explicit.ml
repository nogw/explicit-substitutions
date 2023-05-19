(* Explicit substitutions *)
(* http://pauillac.inria.fr/~levy/pubs/90popljfp.pdf *)

type subst = 
  | Id 
  | Shift 
  | Cons of pretype * subst 
  | Comp of subst * subst
[@@deriving show, eq]

and pretype =
  | Variable of int
  | Forall of pretype
  | Arrow of pretype * pretype
  | Closure of pretype * subst
[@@deriving show, eq]

let rec weak_form_variable index subst =
  match subst with
  | Id -> (Variable index, Id)
  | Shift -> (Variable (succ index), Id)
  | Cons (Closure (t, s), _) when index = 0 -> weak_form t s
  | Cons (_, _) when index = 0 -> failwith "closure expected"
  | Cons (_, s) -> weak_form_variable (pred index) s
  | Comp (a, b) -> weak_form_closure (Variable index) a b

and weak_form_closure t s subst =
  match t with
  | Variable index -> (
      match s with
      | Id -> weak_form_variable index subst
      | Shift -> weak_form_variable (succ index) subst
      | Cons (t, _) when index = 0 -> weak_form t subst
      | Cons (_, s) -> weak_form_closure (Variable (pred index)) s subst
      | Comp (a, b) -> weak_form_closure t a (Comp (b, subst)))
  | _ -> weak_form t (Comp (s, subst))

and weak_form pretype subst =
  match pretype with
  | Variable index -> weak_form_variable index subst
  | Closure (t, s) -> weak_form_closure t s subst
  | _ -> (pretype, subst)

let rec normal_form pretype subst =
  let pretype, sub = weak_form pretype subst in
  match pretype with
  | Variable _ -> pretype
  | Forall all -> Forall (normal_form all (Cons (Closure (Variable 0, Id), Comp (sub, Shift))))
  | Arrow (l, r) -> Arrow (normal_form l sub, normal_form r sub)
  | _ -> failwith "unexpect closure"

module TestNF = struct
  type test_obj = { name: string; received: pretype; expected: pretype }

  let test_subst ~name ~received ~expected = { name; received; expected }

  let test_1 = test_subst 
    ~name:"Variable 0, Id"
    ~received: (normal_form (Variable 0) Id)
    ~expected: (Variable 0)

  let test_2 = test_subst 
    ~name:"Variable 5, Id"
    ~received: (normal_form (Variable 5) Id)
    ~expected: (Variable 5)

  let test_3 = test_subst 
    ~name:"Variable 0, Shift" 
    ~received: (normal_form (Variable 0) Shift)
    ~expected: (Variable 1)

  let test_4 = test_subst 
    ~name:"Variable 5, Shift" 
    ~received: (normal_form (Variable 5) Shift)
    ~expected: (Variable 6)

  let test_5 = test_subst
    ~name: "Variable 0, Comp (Id, Id)"
    ~received: (normal_form (Variable 0) (Comp (Id, Id))) 
    ~expected: (Variable 0)

  let test_6 = test_subst
    ~name: "Variable 0, Comp (Id, Shift)"
    ~received: (normal_form (Variable 0) (Comp (Id, Shift))) 
    ~expected: (Variable 1)
  
  let test_7 = test_subst
    ~name: "Variable 0, Comp (Shift, Id)"
    ~received: (normal_form (Variable 0) (Comp (Shift, Id))) 
    ~expected: (Variable 1)
  
  let test_8 = test_subst
    ~name: "Variable 0, Comp (Shift, Shift)"
    ~received: (normal_form (Variable 0) (Comp (Shift, Shift))) 
    ~expected: (Variable 2)

  let test_9 = test_subst 
    ~name:"Variable 0, Cons ((Closure 0, Id), Shift)"
    ~received: (normal_form (Variable 0) (Cons ((Closure ((Variable 0), Id)), Shift)))
    ~expected: (Variable 0)

  let test_10 = test_subst 
    ~name:"Variable 0, Cons ((Closure 5, Id), Shift)"
    ~received: (normal_form (Variable 0) (Cons ((Closure ((Variable 5), Id)), Shift)))
    ~expected: (Variable 5)

  let test_11 = test_subst 
    ~name:"Variable 1, Cons ((Closure 5, Id), Shift)"
    ~received: (normal_form (Variable 1) (Cons ((Closure ((Variable 5), Id)), Shift)))
    ~expected: (Variable 1)

  let test_12 = test_subst 
    ~name:"Variable 1, Cons ((Closure 5, Id), Id)"
    ~received: (normal_form (Variable 1) (Cons ((Closure ((Variable 5), Id)), Id)))
    ~expected: (Variable 0)

  let test_13 = test_subst
    ~name: "Arrow (Variable 0, Variable 0), Id"
    ~received: (normal_form (Arrow (Variable 0, Variable 0)) Id)
    ~expected: (Arrow (Variable 0, Variable 0))
    
  let test_14 = test_subst
    ~name: "Arrow (Variable 0, Variable 0), Shift"
    ~received: (normal_form (Arrow (Variable 0, Variable 0)) Shift)
    ~expected: (Arrow (Variable 1, Variable 1))

  let test_15 = test_subst 
    ~name:"Forall (Variable 0)), Id"
    ~received: (normal_form (Forall (Variable 0)) Id)
    ~expected: (Forall (Variable 0))
    
  let test_16 = test_subst 
    ~name:"Forall (Variable 0)), Shift"
    ~received: (normal_form (Forall (Variable 0)) Shift)
    ~expected: (Forall (Variable 0))
    
  let test_17 = test_subst 
    ~name:"Forall (Variable 1)), Shift"
    ~received: (normal_form (Forall (Variable 5)) Shift)
    ~expected: (Forall (Variable 6))
    
  let test_18 = test_subst 
    ~name:"Forall (Variable 0)), (Cons (Closure (Variable 5, Id), Id)"
    ~received: (normal_form (Forall (Variable 0)) (Cons (Closure (Variable 5, Id), Id)))
    ~expected: (Forall (Variable 0))
    
  let test_19 = test_subst 
    ~name:"Forall (Variable 1)), (Cons (Closure (Variable 5, Id), Id)"
    ~received: (normal_form (Forall (Variable 1)) (Cons (Closure (Variable 5, Id), Id)))
    ~expected: (Forall (Variable 6))

  let test_20 = test_subst 
    ~name:"Forall (Forall (Variable 2))), (Cons (Closure (Variable 0, Id), Shift)"
    ~received: (normal_form (Forall (Forall (Variable 2))) (Cons (Closure (Variable 0, Id), Shift)))
    ~expected: (Forall (Forall (Variable 2)))

  let test_21 = test_subst 
    ~name:"Forall (Forall (Variable 2))), (Cons (Closure (Variable 0, Id), Id)"
    ~received: (normal_form (Forall (Forall (Variable 2))) (Cons (Closure (Variable 0, Id), Id)))
    ~expected: (Forall (Forall (Variable 2)))

  let tests = [
    test_1;
    test_2;
    test_3;
    test_4;
    test_5;
    test_6;
    test_7;
    test_8;
    test_9;
    test_10;
    test_11;
    test_12;
    test_13;
    test_14;
    test_15;
    test_16;
    test_17;
    test_18;
    test_19;
    test_20;
    test_21;
  ]

  let test { name; expected; received } =
    Alcotest.test_case name `Quick (fun () -> 
      let pretype_eq = Alcotest.testable pp_pretype equal_pretype in
      Alcotest.((check' pretype_eq) ~msg:"same pretype" ~expected ~actual:received))

  let tests = ("tests normal-form", List.map test tests) 
end

module TestWF = struct
  type testable = (pretype * subst) [@@deriving show, eq]
  type test_obj = { name: string; received: testable; expected: testable }

  let test_subst ~name ~received ~expected = { name; received; expected }

  let test_1 = test_subst
    ~name: "Variable 0, (Comp (Comp (Cons (Closure (Variable 0, Id), Shift), Shift), Shift))"
    ~received: (weak_form (Variable 0) (Comp (Comp (Cons (Closure (Variable 0, Id), Shift), Shift), Shift)))
    ~expected: (Variable 2, Id)

  let test_2 = test_subst
    ~name: "Variable 1, (Comp (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Shift)), Shift))"
    ~received: (weak_form (Variable 1) (Comp (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Shift)), Shift)))
    ~expected: (Variable 2, Id)

  let test_3 = test_subst
    ~name: "Variable 2, (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Shift)), Shift)))"
    ~received: (weak_form (Variable 2) (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Shift)), Shift))))
    ~expected: (Variable 2, Id)

  let test_4 = test_subst
    ~name: "Variable 0, (Comp (Cons (Closure (Variable 1, Id), Shift), Comp (Cons (Closure (Variable 2, Id), Shift), Shift)))"
    ~received: (weak_form (Variable 0) (Comp (Cons (Closure (Variable 1, Id), Shift), Comp (Cons (Closure (Variable 2, Id), Shift), Shift))))
    ~expected: ((Variable 2), Id)

  let test_5 = test_subst
    ~name: "Forall (Forall (Variable 2)), (Cons (Closure (Variable 0, Id), Shift)"
    ~received: (weak_form (Forall (Forall (Variable 2))) (Cons (Closure (Variable 0, Id), Shift)))
    ~expected: (Forall (Forall (Variable 2)), Cons (Closure (Variable 0, Id), Shift))

  let test_6 = test_subst
    ~name: "Forall (Variable 2), (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Shift))"
    ~received: (weak_form (Forall (Variable 2)) (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Shift))))
    ~expected: (Forall (Variable 2), Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Shift)))

  let test_7 = test_subst
    ~name: "Forall (Variable 0), (Id)"
    ~received: (weak_form (Forall (Variable 0)) Id)
    ~expected: (Forall (Variable 0), Id)
  
  let test_8 = test_subst
    ~name: "Forall (Variable 1), (Cons (Closure (Variable 0, Id), Shift))"
    ~received: (weak_form (Forall (Variable 1)) (Cons (Closure (Variable 0, Id), Shift)))
    ~expected: (Forall (Variable 1), Cons (Closure (Variable 0, Id), Shift))
  
  let test_9 = test_subst
    ~name: "Forall (Variable 1), (Comp (Cons (Closure (Variable 0, Id), Shift), Shift))"
    ~received: (weak_form (Forall (Variable 1)) (Comp (Cons (Closure (Variable 0, Id), Shift), Shift)))
    ~expected: (Forall (Variable 1), Comp (Cons (Closure (Variable 0, Id), Shift), Shift))
  
  let test_10 = test_subst
    ~name: "Forall (Forall (Forall (Variable 2))), (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Comp (Cons (Closure (Variable 0, Id), Shift), Shift))))"
    ~received: (weak_form (Forall (Forall (Forall (Variable 2)))) (Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Comp (Cons (Closure (Variable 0, Id), Shift), Shift)))))
    ~expected: (Forall (Forall (Forall (Variable 2))), Cons (Closure (Variable 0, Id), Comp (Cons (Closure (Variable 0, Id), Shift), Comp (Cons (Closure (Variable 0, Id), Shift), Shift))))

  let test_11 = test_subst
    ~name: "Forall (Variable 0), (Cons (Closure (Variable 1, Id), Shift))"
    ~received: (weak_form (Forall (Variable 0)) (Cons (Closure (Variable 1, Id), Shift)))
    ~expected: (Forall (Variable 0), Cons (Closure (Variable 1, Id), Shift))
  
  let test_12 = test_subst
    ~name: "Forall (Variable 2), (Comp (Comp (Cons (Closure (Variable 0, Id), Shift), Shift), Shift))"
    ~received: (weak_form (Forall (Variable 2)) (Comp (Comp (Cons (Closure (Variable 0, Id), Shift), Shift), Shift)))
    ~expected: (Forall (Variable 2), Comp (Comp (Cons (Closure (Variable 0, Id), Shift), Shift), Shift))

  let tests = [
    test_1;
    test_2;
    test_3;
    test_4;
    test_5;
    test_6;
    test_7;
    test_8;
    test_9;
    test_10;
    test_11;
    test_12;
  ]

  let test { name; expected; received } =
    Alcotest.test_case name `Quick (fun () -> 
      let pretype_eq = Alcotest.testable pp_testable equal_testable in
      Alcotest.((check' pretype_eq) ~msg:"same pretype" ~expected ~actual:received))

  let tests = ("tests weak-form", List.map test tests)
end

let test () = Alcotest.run "Subst" [ TestNF.tests; TestWF.tests ]
