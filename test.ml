open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Graph
open Assembly

let alloc_strat = Naive

let t ?(alloc = alloc_strat) name program input expected =
  name >:: test_run ~args:[] ~std_input:input alloc program name expected
;;

let te name program expected_err = name >:: test_err Naive program name expected_err

let t_error name error thunk = name >:: fun _ -> assert_raises error thunk

let ta name program input expected =
  name >:: test_run_anf ~args:[] ~std_input:input program name expected
;;

let tgc ?(alloc = alloc_strat) name heap_size program input expected =
  name >:: test_run ~args:[string_of_int heap_size] ~std_input:input alloc program name expected
;;

let tvg ?(alloc = alloc_strat) name program input expected =
  name >:: test_run_valgrind ~args:[] ~std_input:input alloc program name expected
;;

let tvgc ?(alloc = alloc_strat) name heap_size program input expected =
  name
  >:: test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input alloc program name expected
;;

let terr ?(alloc = alloc_strat) name program input expected =
  name >:: test_err ~args:[] ~std_input:input alloc program name expected
;;

let tgcerr ?(alloc = alloc_strat) name heap_size program input expected =
  name >:: test_err ~args:[string_of_int heap_size] ~std_input:input alloc program name expected
;;

let tanf name program expected =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

let t_asm name value expected = name >:: fun _ -> assert_equal expected value ~printer:to_asm

let tparse name program expected =
  name
  >:: fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program
;;

let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

let tfvs name program expected =
  name
  >:: fun _ ->
  let ast = parse_string name program in
  let anfed = anf (tag ast) in
  match anfed with
  | AProgram (body, _) ->
      let vars = StringSet.elements (free_vars body) in
      let c = Stdlib.compare in
      let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
      assert_equal (List.sort c expected) (List.sort c vars) ~printer:str_list_print
;;

(* Test helper for free_vars_cache *)
let tfvsc name program expected =
  name
  >:: fun _ ->
  let ast = desugar (parse_string name program) in
  let anfed = anf (tag ast) in
  let actual = fvs_to_list (free_vars_cache (atag anfed)) in
  (* let c = Stdlib.compare in *)
  let print_tags (fvs, tag) =
    " (["
    ^ List.fold_left (fun fv prev_string -> fv ^ " " ^ prev_string) "" fvs
    ^ "]" ^ sprintf ", %d" tag ^ ")"
  in
  (* let print_aprog p = string_of_aprogram p in *)
  let print_aprog p = string_of_aprogram_with 100 print_tags p in
  assert_equal expected actual ~printer:print_aprog
;;

let t_any name value expected = name >:: fun _ -> assert_equal expected value ~printer:ExtLib.dump

(* A small helper to wrap strings in quotes for printing purposes *)
let quoted_str (s : string) : string = Printf.sprintf "\"%s\"" s

let t_string name value expected = name >:: fun _ -> assert_equal expected value ~printer:quoted_str

let graph_from_assoc_list ls =
  let nodes, neighbors = List.split ls in
  let neighbors_sets = List.map StringSet.of_list neighbors in
  let new_ls = List.combine nodes neighbors_sets in
  List.fold_left (fun m (k, v) -> Graph.add k v m) Graph.empty new_ls
;;

let t_graph name value expected =
  name
  >:: fun _ ->
  assert_equal
    (string_of_graph (graph_from_assoc_list expected))
    (string_of_graph value) ~printer:quoted_str
;;

let t_viz_graph name value expected =
  name
  >:: fun _ ->
  assert_equal
    (graph_to_viz (graph_from_assoc_list expected))
    (graph_to_viz value) ~printer:quoted_str
;;

let tinterfere name program expected =
  let (AProgram (body, _)) =
    free_vars_cache (atag (anf (rename_and_tag (tag (desugar (parse_string name program))))))
  in
  t_string name
    (graph_to_viz (interfere body StringSet.empty StringSet.empty))
    (graph_to_viz (graph_from_assoc_list expected))
;;

let tcgraph ?(delete = StringSet.empty) name program expected =
  let ast = rename_and_tag (tag (desugar (Runner.parse_string name program))) in
  let actual =
    match free_vars_cache (atag (anf ast)) with
    | AProgram (body, _) -> body
  in
  let c = Stdlib.compare in
  t_any name
    (List.sort c (color_graph (interfere actual StringSet.empty delete) []))
    (List.sort c expected)
;;

let talloc ?(no_builtins = true) name program expected =
  let parsed_prog = parse_string name program in
  let prog_builtins = if no_builtins then parsed_prog else add_native_lambdas parsed_prog in
  t_any name
    (snd
       (naive_stack_allocation
          (free_vars_cache (atag (anf (rename_and_tag (tag (desugar prog_builtins)))))) ) )
    expected
;;

let tregalloc name program expected =
  let c = Stdlib.compare in
  t_any name
    (List.sort c
       (snd
          (register_allocation
             (free_vars_cache
                (atag (anf (rename_and_tag (tag (desugar (parse_string name program)))))) ) ) ) )
    expected
;;

let builtins_size =
  4 (* arity + 0 vars + codeptr + padding *) * List.length Compile.native_fun_bindings
;;

let free_vars_suite =
  "free_vars_suite"
  >::: [ tfvs "id" "x" ["x"];
         tfvs "num" "3" [];
         tfvs "bool" "true" [];
         tfvs "bool_and_x" "true && x" ["x"];
         tfvs "sub1_x" "sub1(x)" ["x"];
         tfvs "sub1_x_bound" "let x = a in sub1(x)" ["a"];
         tfvs "num_let" "let x = 1 in 3" [];
         tfvs "identity" "(lambda (x): x)" [];
         tfvs "identity_free" "(lambda (x): y)" ["y"];
         tfvs "prim1" "add1(x)" ["x"];
         tfvs "print1_nest" "sub1((x + y))" ["x"; "y"];
         tfvs "no_frees_1" "add1(100)" [];
         tfvs "prim2" "x + y" ["x"; "y"];
         tfvs "prim2_nest" "(a + b) - (c + d)" ["a"; "b"; "c"; "d"];
         tfvs "no_frees_2" "1 + 2" [];
         tfvs "if" "if a: b else: c" ["a"; "b"; "c"];
         tfvs "if2" "if a: a else: c" ["a"; "c"];
         tfvs "if_lambda" "(lambda (a, c): if a: a else: c)" [];
         tfvs "if_nested_lambda" "(lambda (a): (lambda (c): if a: a else: c))" [];
         tfvs "if_nested_lambda2" "(lambda (a): c + (lambda (c): if a: a else: c))" ["c"];
         tfvs "if_nested_lambda3" "(lambda (a): (lambda (c): if b: a else: c))" ["b"];
         tfvs "if_nested_lambda4" "(lambda (a): (lambda (b, c, d): if b: a else: c))" [];
         tfvs "if_nested_lambda5" "(lambda (a): (lambda (b, c, d): if b: a else: e))" ["e"];
         tfvs "if_let" "let c = true in if a: b else: c" ["a"; "b"];
         tfvs "nested_let" "let a = 1, c = true in a" [];
         tfvs "nested_let2" "let a = 1 in let c = true in a" [];
         tfvs "letrec" "let rec a = b, b = a, c = d in e" ["d"; "e"];
         tfvs "tuple" "let rec a = b, b = a, c = 1 in (a, b, c, d, e)" ["d"; "e"];
         tfvs "tuple_nest" "(x, y, (z))" ["x"; "y"; "z"];
         tfvs "tuple_no_frees" "(1, 2, 3)" [];
         tfvs "seq" "let rec a = b, b = a, c = 1 in a; b; d; c" ["d"];
         tfvs "app" "let b = 2 in add(a, b, c)" ["a"; "c"; "add"];
         tfvs "get_tuple" "let x = (1, 2, z) in d[y]" ["z"; "d"; "y"];
         tfvs "get_tuple_nest" "((1, 2, foo)[a])[b]" ["foo"; "a"; "b"];
         tfvs "get_tuple_no_frees" "(1, 2, 3)[2]" [];
         tfvs "set_tuple" "let x = (1, 2, eight) in q[3] := z" ["eight"; "q"; "z"];
         tfvs "set_tuple_nest" "((1, 2, eight)[q])[n] := (56 * x - (r + y))"
           ["eight"; "q"; "n"; "x"; "r"; "y"];
         tfvs "lam" "(lambda (x, y): x + y + k)" ["k"];
         tfvs "lam_all_frees" "(lambda: x + y)" ["x"; "y"];
         tfvs "lam_nest" "(lambda (x, y) : (a, b) && false)(t)" ["a"; "b"; "t"];
         tfvs "lam_none" "(lambda (x, y): x + y)" [];
         tfvs "let_no_frees" "let x = 1, y = 2 in x + y" [];
         tfvs "let_free_vars" "let x = y, z = 34 in a * x * y * z" ["y"; "a"];
         tfvs "let_and_lam" "let x = 10, y = (lambda (z): x + z) in y(100)" [];
         tfvs "letrec_and_lam"
           "(lambda (x, y): let rec k = (lambda (x2): x2 + p + k(3)) in k(y + g))" ["p"; "g"];
         tfvs "fun_all" "func(x, y)" ["func"; "x"; "y"];
         tfvs "fun_nest" "fun((x + y), z)" ["fun"; "x"; "y"; "z"];
         tfvs "fun_only_name" "fun(1, 2, 3)" ["fun"];
         tfvs "letrec_self_recurse" "let rec f = (lambda : f()) in f()" [];
         tfvs "letrec_self_recurse_if" "let rec f = (lambda : if 1 < 2: 1 else: f()) in f()" [];
         tfvs "fact" "let rec fact = (lambda (n): if n <= 1: 1 else: n * fact(sub1(n))) in fact" []
       ]
;;

let fvc_suite =
  "fvc_suite"
  >::: [ tfvsc "num" "1" (AProgram (ACExpr (CImmExpr (ImmNum (1L, ([], 1)))), ([], 0)));
         tfvsc "bool" "false" (AProgram (ACExpr (CImmExpr (ImmBool (false, ([], 1)))), ([], 0)));
         tfvsc "id" "x" (AProgram (ACExpr (CImmExpr (ImmId ("x", (["x"], 1)))), (["x"], 0)));
         tfvsc "capp_closed" "fun(1, 2, 3)"
           (AProgram
              ( ACExpr
                  (CApp
                     ( ImmId ("fun", (["fun"], 5)),
                       [ImmNum (1L, ([], 2)); ImmNum (2L, ([], 3)); ImmNum (3L, ([], 4))],
                       Unknown,
                       (["fun"], 1) ) ),
                (["fun"], 0) ) );
         tfvsc "capp_frees" "fun((x + y), z)"
           (AProgram
              ( ALet
                  ( "binop_3",
                    CPrim2 (Plus, ImmId ("x", (["x"], 8)), ImmId ("y", (["y"], 7)), (["x"; "y"], 6)),
                    ACExpr
                      (CApp
                         ( ImmId ("fun", (["fun"], 5)),
                           [ImmId ("binop_3", (["binop_3"], 3)); ImmId ("z", (["z"], 4))],
                           Unknown,
                           (["binop_3"; "fun"; "z"], 2) ) ),
                    (["fun"; "x"; "y"; "z"], 1) ),
                (["fun"; "x"; "y"; "z"], 0) ) );
         tfvsc "if_closed" "if true: 100 else: 200"
           (AProgram
              ( ACExpr
                  (CIf
                     ( ImmBool (true, ([], 4)),
                       ACExpr (CImmExpr (ImmNum (100L, ([], 3)))),
                       ACExpr (CImmExpr (ImmNum (200L, ([], 2)))),
                       ([], 1) ) ),
                ([], 0) ) );
         tfvsc "if_frees" "if a: b else: c"
           (AProgram
              ( ACExpr
                  (CIf
                     ( ImmId ("a", (["a"], 4)),
                       ACExpr (CImmExpr (ImmId ("b", (["b"], 3)))),
                       ACExpr (CImmExpr (ImmId ("c", (["c"], 2)))),
                       (["c"], 1) ) ),
                (["a"; "b"; "c"], 0) ) );
         tfvsc "prim1_closed" "add1(100)"
           (AProgram (ACExpr (CPrim1 (Add1, ImmNum (100L, ([], 2)), ([], 1))), ([], 0)));
         tfvsc "prim1_free" "add1(x)"
           (AProgram (ACExpr (CPrim1 (Add1, ImmId ("x", (["x"], 2)), (["x"], 1))), (["x"], 0)));
         tfvsc "prim2_nest" "(a + b) * (c + d)"
           (AProgram
              ( ALet
                  ( "binop_3",
                    CPrim2
                      (Plus, ImmId ("a", (["a"], 11)), ImmId ("b", (["b"], 10)), (["a"; "b"], 9)),
                    ALet
                      ( "binop_6",
                        CPrim2
                          (Plus, ImmId ("c", (["c"], 8)), ImmId ("d", (["d"], 7)), (["c"; "d"], 6)),
                        ACExpr
                          (CPrim2
                             ( Times,
                               ImmId ("binop_3", (["binop_3"], 5)),
                               ImmId ("binop_6", (["binop_6"], 4)),
                               (["binop_3"; "binop_6"], 3) ) ),
                        (["binop_3"; "c"; "d"], 2) ),
                    (["a"; "b"; "c"; "d"], 1) ),
                (["a"; "b"; "c"; "d"], 0) ) );
         tfvsc "lam_closed" "(lambda (x, y): x + y)"
           (AProgram
              ( ACExpr
                  (CLambda
                     ( ["x"; "y"],
                       ACExpr
                         (CPrim2
                            (Plus, ImmId ("x", (["x"], 4)), ImmId ("y", (["y"], 3)), (["x"; "y"], 2))
                         ),
                       ([], 1) ) ),
                ([], 0) ) );
         tfvsc "lam_one_free" "(lambda (x, y): x + y + z)"
           (AProgram
              ( ACExpr
                  (CLambda
                     ( ["x"; "y"],
                       ALet
                         ( "binop_6",
                           CPrim2
                             ( Plus,
                               ImmId ("x", (["x"], 8)),
                               ImmId ("y", (["y"], 7)),
                               (["x"; "y"], 6) ),
                           ACExpr
                             (CPrim2
                                ( Plus,
                                  ImmId ("binop_6", (["binop_6"], 5)),
                                  ImmId ("z", (["z"], 4)),
                                  (["binop_6"; "z"], 3) ) ),
                           (["x"; "y"; "z"], 2) ),
                       (["z"], 1) ) ),
                (["z"], 0) ) );
         tfvsc "lam_all_free" "(lambda: a + b)"
           (AProgram
              ( ACExpr
                  (CLambda
                     ( [],
                       ACExpr
                         (CPrim2
                            (Plus, ImmId ("a", (["a"], 4)), ImmId ("b", (["b"], 3)), (["a"; "b"], 2))
                         ),
                       (["a"; "b"], 1) ) ),
                (["a"; "b"], 0) ) );
         tfvsc "tuple_frees" "(x, y, (z), 1, 2)"
           (AProgram
              ( ACExpr
                  (CTuple
                     ( [ ImmId ("x", (["x"], 2));
                         ImmId ("y", (["y"], 3));
                         ImmId ("z", (["z"], 4));
                         ImmNum (1L, ([], 5));
                         ImmNum (2L, ([], 6)) ],
                       (["x"; "y"; "z"], 1) ) ),
                (["x"; "y"; "z"], 0) ) );
         tfvsc "let_closed" "let x = 1, y = 2 in x + y"
           (AProgram
              ( ALet
                  ( "x",
                    CImmExpr (ImmNum (1L, ([], 7))),
                    ALet
                      ( "y",
                        CImmExpr (ImmNum (2L, ([], 6))),
                        ACExpr
                          (CPrim2
                             ( Plus,
                               ImmId ("x", (["x"], 5)),
                               ImmId ("y", (["y"], 4)),
                               (["x"; "y"], 3) ) ),
                        (["x"], 2) ),
                    ([], 1) ),
                ([], 0) ) );
         tfvsc "let_free" "let x = y, z = 10 in x + y + z + q"
           (AProgram
              ( ALet
                  ( "x",
                    CImmExpr (ImmId ("y", (["y"], 15))),
                    ALet
                      ( "z",
                        CImmExpr (ImmNum (10L, ([], 14))),
                        ALet
                          ( "binop_12",
                            CPrim2
                              ( Plus,
                                ImmId ("x", (["x"], 13)),
                                ImmId ("y", (["y"], 12)),
                                (["x"; "y"], 11) ),
                            ALet
                              ( "binop_11",
                                CPrim2
                                  ( Plus,
                                    ImmId ("binop_12", (["binop_12"], 10)),
                                    ImmId ("z", (["z"], 9)),
                                    (["binop_12"; "z"], 8) ),
                                ACExpr
                                  (CPrim2
                                     ( Plus,
                                       ImmId ("binop_11", (["binop_11"], 7)),
                                       ImmId ("q", (["q"], 6)),
                                       (["binop_11"; "q"], 5) ) ),
                                (["binop_12"; "q"; "z"], 4) ),
                            (["q"; "x"; "y"; "z"], 3) ),
                        (["q"; "x"; "y"], 2) ),
                    (["q"; "y"], 1) ),
                (["q"; "y"], 0) ) );
         tfvsc "lets_lams" "let x = 10, foo = (lambda (y): x + y) in foo(100)"
           (AProgram
              ( ALet
                  ( "x",
                    CImmExpr (ImmNum (10L, ([], 10))),
                    ALet
                      ( "foo",
                        CLambda
                          ( ["y"],
                            ACExpr
                              (CPrim2
                                 ( Plus,
                                   ImmId ("x", (["x"], 9)),
                                   ImmId ("y", (["y"], 8)),
                                   (["x"; "y"], 7) ) ),
                            (["x"], 6) ),
                        ACExpr
                          (CApp
                             ( ImmId ("foo", (["foo"], 5)),
                               [ImmNum (100L, ([], 4))],
                               Unknown,
                               (["foo"], 3) ) ),
                        (["x"], 2) ),
                    ([], 1) ),
                ([], 0) ) );
         tfvsc "seq_frees" "let x = y in x; y + z"
           (AProgram
              ( ALet
                  ( "x",
                    CImmExpr (ImmId ("y", (["y"], 7))),
                    ASeq
                      ( CImmExpr (ImmId ("x", (["x"], 6))),
                        ACExpr
                          (CPrim2
                             ( Plus,
                               ImmId ("y", (["y"], 5)),
                               ImmId ("z", (["z"], 4)),
                               (["y"; "z"], 3) ) ),
                        (["x"; "y"; "z"], 2) ),
                    (["y"; "z"], 1) ),
                (["y"; "z"], 0) ) ) ]
;;

let naive_alloc_suite =
  "naive_alloc_suite"
  >::: [ talloc "num" "5" [(0, [])];
         talloc "bool" "true" [(0, [])];
         talloc "or" "true || false"
           [ ( 0,
               [ ("unary_4", RegOffset (-8, RBP));
                 ("unary_3", RegOffset (-16, RBP));
                 ("unary_8", RegOffset (-24, RBP)) ] ) ];
         talloc "simple_let" "let x = 5 in x" [(0, [("x_4", RegOffset (~-8, RBP))])];
         talloc "simple_let_unused" "let x = 5 in 1" [(0, [("x_4", RegOffset (~-8, RBP))])];
         talloc "nested_let" "let x = 5 in let y = 6 in x + y"
           [(0, [("x_4", RegOffset (~-8, RBP)); ("y_8", RegOffset (~-16, RBP))])];
         talloc "let_in_bind" "let x = (let y = 6 in x) in 1"
           [(0, [("y_7", RegOffset (~-8, RBP)); ("x_4", RegOffset (~-16, RBP))])];
         talloc "identity" "(lambda (x): x)" [(0, []); (1, [("x_5", RegOffset (24, RBP))])];
         talloc "free_var" "(lambda: x)" [(0, []); (1, [("x", RegOffset (~-8, RBP))])];
         talloc "closed_over_var" "let y = 20 in (lambda (x): x + y)"
           [ (0, [("y_4", RegOffset (~-8, RBP))]);
             (2, [("x_11", RegOffset (24, RBP)); ("y_4", RegOffset (~-8, RBP))]) ];
         talloc "two_lams" "(lambda (x): x); (lambda (x): x)"
           [(0, []); (2, [("x_12", RegOffset (24, RBP))]); (4, [("x_8", RegOffset (24, RBP))])];
         talloc "letrec1" "let rec id = (lambda (x): x) in id(1)"
           [(0, [("id_4", RegOffset (~-8, RBP))]); (5, [("x_8", RegOffset (24, RBP))])];
         talloc "letrec2"
           "let rec id = (lambda (x): x), k = (lambda (x): (lambda (y): x + z + w)) in id(1) + \
            k(2)(3)"
           [ ( 0,
               [ ("k_10", RegOffset (-16, RBP));
                 ("id_4", RegOffset (-8, RBP));
                 ("app_23", RegOffset (-24, RBP));
                 ("app_28", RegOffset (-32, RBP));
                 ("app_26", RegOffset (-40, RBP)) ] );
             (17, [("x_8", RegOffset (24, RBP))]);
             ( 19,
               [ ("x_21", RegOffset (24, RBP));
                 ("z", RegOffset (-16, RBP));
                 ("w", RegOffset (-8, RBP)) ] );
             ( 20,
               [ ("y_20", RegOffset (24, RBP));
                 ("z", RegOffset (-24, RBP));
                 ("x_21", RegOffset (-16, RBP));
                 ("w", RegOffset (-8, RBP));
                 ("binop_16", RegOffset (-32, RBP)) ] ) ];
         talloc "final_boss"
           "def foo(x): let bar = (x, (x + 1)), baz = t[0], fuzz = t[1] in baz + fuz\nfoo(4)"
           [ (0, [("foo_4", RegOffset (-8, RBP))]);
             ( 5,
               [ ("x_29", RegOffset (24, RBP));
                 ("t", RegOffset (-16, RBP));
                 ("fuz", RegOffset (-8, RBP));
                 ("binop_11", RegOffset (-24, RBP));
                 ("bar_8", RegOffset (-32, RBP));
                 ("baz_16", RegOffset (-40, RBP));
                 ("fuzz_22", RegOffset (-48, RBP)) ] ) ] ]
;;

let reg_alloc_suite =
  "reg_alloc_suite"
  >::: [ tregalloc "num" "3" [(0, [])];
         tregalloc "prim1" "sub1(6)" [(0, [])];
         (* TODO there's a let, there should be a reg *)
         tregalloc "let" "let x = 1 in x" [(0, [("x_4", Reg R10)])];
         tregalloc "two_prim1s" "add1(sub1(6))" [(0, [("unary_3", Reg R10)])];
         (* TODO let free adder programs should use <=1 register *)
         tregalloc "three_prim1s" "add1(add1(sub1(6)))"
           [(0, [("unary_3", Reg R12); ("unary_4", Reg R10)])];
         tregalloc "four_prim1s" "sub1(add1(add1(sub1(6))))"
           [(0, [("unary_3", Reg R13); ("unary_4", Reg R12); ("unary_5", Reg R10)])];
         tregalloc "plus" "3 + 4" [(0, [])];
         tregalloc "plus3" "3 + 4 + 5" [(0, [("binop_3", Reg R10)])];
         tregalloc "plus4" "3 + 4 + 5 + 6" [(0, [("binop_3", Reg R12); ("binop_4", Reg R10)])];
         tregalloc "plus_times" "(3 + 4) * (5 + 6)"
           [(0, [("binop_3", Reg R12); ("binop_6", Reg R10)])];
         tregalloc "nested_let_both_bottom" "let x = 1, y = 2 in (x, y)"
           [(0, [("x_4", Reg R12); ("y_8", Reg R10)])];
         tregalloc "nested_let_neither_bottom" "let x = 1, y = 2 in 3"
           [(0, [("x_4", Reg R12); ("y_8", Reg R10)])];
         tregalloc "nested_let_first_bottom" "let x = 1, y = 2 in x"
           [(0, [("x_4", Reg R12); ("y_8", Reg R10)])];
         tregalloc "nested_let_chain" "let x = 1, y = x in y"
           [(0, [("x_4", Reg R12); ("y_8", Reg R10)])];
         tregalloc "disjoint_interference"
           "let x = 1 in let y = (let w = 3 in w) in let z = 3 in (x, y, z)"
           [(0, [("w_11", Reg R14); ("x_4", Reg R13); ("y_8", Reg R12); ("z_16", Reg R10)])];
         tregalloc "def_simple" "def f(x): x\n\nf(49)"
           [(0, [("f_4", Reg R10)]); (5, [("x_7", RegOffset (24, RBP))])];
         tregalloc "def_simple2" "def f(x, y): x + y\n\nf(3, 46)"
           [ (0, [("f_4", Reg R10)]);
             (6, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         tregalloc "def_let_complex" "def f(x, y): x + y\ndef g(x, y, z): let a = 4 in a\n\na()"
           [ (0, [("f_4", Reg R12); ("g_13", Reg R10)]);
             ( 5,
               [ ("a_17", Reg R10);
                 ("x_20", RegOffset (24, RBP));
                 ("y_21", RegOffset (32, RBP));
                 ("z_22", RegOffset (40, RBP)) ] );
             (9, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         tregalloc "let_def_boss"
           "def f(x, y): x + y\ndef g(x, y, z): let h = 355 in h\n\nlet x = 5 in f(x, x)"
           [ (0, [("f_4", Reg R13); ("g_13", Reg R12); ("x_25", Reg R10)]);
             ( 9,
               [ ("h_17", Reg R10);
                 ("x_20", RegOffset (24, RBP));
                 ("y_21", RegOffset (32, RBP));
                 ("z_22", RegOffset (40, RBP)) ] );
             (13, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         tregalloc "def_and_if"
           "def f(x, y): if x: (let g = 12 in g) else: (let h = 35 in h)\n\nf(false, 44)"
           [ (0, [("f_4", Reg R10)]);
             ( 6,
               [ ("g_10", Reg R10);
                 ("h_15", Reg R10);
                 ("x_18", RegOffset (24, RBP));
                 ("y_19", RegOffset (32, RBP)) ] ) ];
         tregalloc "big_boy"
           "def foo(x, y): if x: (let g = 12 in g) else: (let h = 6 in h)\n\
            def bar(x, y): if x: (let g = 44 in g) else: (let h = 89 in h)\n\n\
            let x = 343, y = 23 in foo(x, y) + bar(x, y)"
           [ ( 0,
               [ ("app_47", Reg RSI);
                 ("app_51", Reg RBX);
                 ("bar_22", Reg R14);
                 ("foo_4", Reg R13);
                 ("x_40", Reg R12);
                 ("y_44", Reg R10) ] );
             ( 20,
               [ ("g_28", Reg R10);
                 ("h_33", Reg R10);
                 ("x_36", RegOffset (24, RBP));
                 ("y_37", RegOffset (32, RBP)) ] );
             ( 29,
               [ ("g_10", Reg R10);
                 ("h_15", Reg R10);
                 ("x_18", RegOffset (24, RBP));
                 ("y_19", RegOffset (32, RBP)) ] ) ];
         tregalloc "tuple_simple" "let t = (1, 2, 3) in t" [(0, [("t_4", Reg R10)])];
         tregalloc "two_3tuples" "let t = (1, 2, 3), y = (3, 4, 5) in y"
           [(0, [("t_4", Reg R12); ("y_11", Reg R10)])];
         tregalloc "tup_gets" "let t = (1, 2, 3), x = t[0], y = t[1], z = t[2] in z"
           [(0, [("t_4", Reg R14); ("x_11", Reg R13); ("y_17", Reg R12); ("z_23", Reg R10)])];
         tregalloc "def_tup_get"
           "def f(x): let t = ((x + 6), (x - 14)), b = t[0], c = t[1] in b + c\n\n\
            let t = (1, 16), x = t[0], y = t[1] in f(x + y)"
           [ ( 0,
               [ ("binop_51", Reg RBX);
                 ("f_4", Reg R14);
                 ("t_34", Reg R13);
                 ("x_40", Reg R12);
                 ("y_46", Reg R10) ] );
             ( 21,
               [ ("b_18", Reg RBX);
                 ("binop_10", Reg R14);
                 ("binop_13", Reg R13);
                 ("c_24", Reg R12);
                 ("t_8", Reg R10);
                 ("x_31", RegOffset (24, RBP)) ] ) ];
         tregalloc "seq_and_lets"
           "let x = 4, y = 5, z = 10 in x + y + z; let a = 1, b = 2, c = 3 in a + b + c"
           [ ( 0,
               [ ("a_24", Reg RCX);
                 ("b_28", Reg RDI);
                 ("binop_18", Reg RSI);
                 ("binop_35", Reg RBX);
                 ("c_32", Reg R14);
                 ("x_4", Reg R13);
                 ("y_8", Reg R12);
                 ("z_12", Reg R10) ] ) ];
         tregalloc "identity" "(lambda (x): x)" [(0, []); (1, [("x_5", RegOffset (24, RBP))])];
         tregalloc "lam_fv" "let y = 12 in (lambda (x): x + y)"
           [(0, [("y_4", Reg R10)]); (2, [("y_4", Reg R10); ("x_11", RegOffset (24, RBP))])];
         tregalloc "lam_none" "(lambda: 1)" [(0, []); (1, [])];
         tregalloc "lam_complex"
           "let f = (lambda (x): x * 4), g = (lambda (x): x + 23) in f(4) + g(2)"
           [ (0, [("app_21", Reg R14); ("app_24", Reg R13); ("f_4", Reg R12); ("g_13", Reg R10)]);
             (14, [("x_19", RegOffset (24, RBP))]);
             (18, [("x_10", RegOffset (24, RBP))]) ];
         tregalloc "nesting_lams" "(lambda (x): (lambda (y): x + y)(2))(3)"
           [ (0, [("lam_4", Reg R10)]);
             (5, [("lam_8", Reg R10); ("x_14", RegOffset (24, RBP))]);
             (10, [("x_14", Reg R10); ("y_13", RegOffset (24, RBP))]) ];
         tregalloc "letrec"
           "let rec f = (lambda (n): let rec g = (lambda (x): if n <= 1: x else: f(x - 1) ) in \
            g(n)) in f(7)"
           [ (0, [("f_4", Reg R10)]);
             (5, [("f_4", Reg R12); ("g_9", Reg R10); ("n_26", RegOffset (24, RBP))]);
             ( 10,
               [ ("binop_13", Reg R14);
                 ("binop_18", Reg R13);
                 ("f_4", Reg R12);
                 ("n_26", Reg R10);
                 ("x_22", RegOffset (24, RBP)) ] ) ] ]
;;

let interfere_suite =
  "interfere_suite"
  >::: [ tinterfere "num" "3" [];
         tinterfere "prim1" "sub1(6)" [];
         tinterfere "let" "let x = 1 in x" [("x_4", [])];
         tinterfere "two_prim1s" "add1(sub1(6))" [("unary_3", [])];
         tinterfere "three_prim1s" "add1(add1(sub1(6)))"
           [("unary_3", ["unary_4"]); ("unary_4", ["unary_3"])];
         tinterfere "nested_let" "let x = 1 in let y = 2 in (x, y)"
           [("x_4", ["y_8"]); ("y_8", ["x_4"])];
         tinterfere "nested_let_not_in_bottom" "let x = 1 in let y = x in y"
           [("x_4", ["y_8"]); ("y_8", ["x_4"])];
         tinterfere "three_nested_let"
           "let x = 1 in let y = 2 in let z = 3 in let xy = x + y in xy + z"
           [ ("x_4", ["z_12"; "y_8"; "xy_16"]);
             ("xy_16", ["z_12"; "y_8"; "x_4"]);
             ("y_8", ["z_12"; "x_4"; "xy_16"]);
             ("z_12", ["y_8"; "xy_16"; "x_4"]) ];
         tinterfere "disjoint_interference"
           "let x = 1 in let y = (let w = 3 in w) in let z = 3 in (x, y, z)"
           [ ("w_11", ["x_4"; "y_8"; "z_16"]);
             ("x_4", ["z_16"; "y_8"; "w_11"]);
             ("y_8", ["z_16"; "x_4"; "w_11"]);
             ("z_16", ["y_8"; "x_4"; "w_11"]) ];
         tinterfere "if_simple" "if true: 1 else: 2" [];
         tinterfere "if_in_let" "let x = true in if x: 1 else: 2" [("x_4", [])];
         tinterfere "lets_in_if" "if true: (let x = 1 in x) else: (let y = 2 in y)"
           [("x_6", []); ("y_11", [])];
         tinterfere "lets_in_and_out_if"
           "let z = true in if z: (let x = 1 in x) else: (let y = 2 in y)"
           [("x_10", ["z_4"]); ("y_15", ["z_4"]); ("z_4", ["y_15"; "x_10"])];
         tinterfere "lets_in_and_out_if_interfere"
           "let z = true in if z: (let x = 1 in x) else: (let y = 2 in y + z)"
           [("x_10", ["z_4"]); ("y_15", ["z_4"]); ("z_4", ["y_15"; "x_10"])];
         tinterfere "simple_seq" "print(5); 6" [];
         tinterfere "let_in_seq" "let x = 1 in x; let y = 2 in y"
           [("x_4", ["y_12"]); ("y_12", ["x_4"])];
         tinterfere "let_over_seq" "let z = 3 in (let x = 1 in x; let y = 2 in y)"
           [("x_8", ["z_4"; "y_16"]); ("y_16", ["z_4"; "x_8"]); ("z_4", ["y_16"; "x_8"])];
         tinterfere "let_over_seq_interfere" "let z = 3 in (let x = 1 in x + z; let y = 2 in y)"
           [("x_8", ["z_4"; "y_18"]); ("y_18", ["z_4"; "x_8"]); ("z_4", ["x_8"; "y_18"])];
         tinterfere "let_over_seq_interfere_both"
           "let z = 3 in (let x = 1 in x + z; let y = 2 in y + z)"
           [("x_8", ["z_4"; "y_18"]); ("y_18", ["z_4"; "x_8"]); ("z_4", ["y_18"; "x_8"])];
         tinterfere "letrec_single" "let rec x = 1 in x" [("x_4", [])];
         tinterfere "letrec_double" "let rec x = 1, y = 2 in 3" [("x_4", ["y_7"]); ("y_7", ["x_4"])];
         tinterfere "letrec_triple" "let rec x = 1, y = 2, z = 3 in x + y + z"
           [ ("x_4", ["y_7"; "z_10"; "binop_13"]);
             ("y_7", ["x_4"; "z_10"; "binop_13"]);
             ("z_10", ["x_4"; "y_7"; "binop_13"]);
             ("binop_13", ["x_4"; "y_7"; "z_10"]) ];
         tinterfere "letrec_single_with_free" "let rec x = y in 1" [("x_4", ["y"]); ("y", ["x_4"])];
         tinterfere "letrec_double_one_free" "let rec x = 1, y = z in 2"
           [("x_4", ["y_7"; "z"]); ("y_7", ["x_4"; "z"]); ("z", ["x_4"; "y_7"])];
         tinterfere "letrec_id" "let rec foo = (lambda (x): x) in foo(3)" [("foo_4", [])];
         tinterfere "letrec_recursive"
           "let rec foo = (lambda (x): x), bar = (lambda (y): foo(y)) in bar(1) + foo(3)"
           [ ("foo_4", ["bar_10"; "app_21"; "app_18"]);
             ("bar_10", ["foo_4"; "app_21"; "app_18"]);
             ("app_18", ["foo_4"; "bar_10"; "app_21"]);
             ("app_21", ["foo_4"; "bar_10"; "app_18"]) ];
         tinterfere "letrec_simple_body"
           "let rec foo = (lambda (x): x), bar = (lambda (y): foo(y)) in 1"
           [("foo_4", ["bar_10"]); ("bar_10", ["foo_4"])];
         tinterfere "letrec_recursive_nest"
           "let rec foo = (lambda (x): x) in let rec bar = (lambda (y): foo(y)) in bar(1) + foo(3)"
           [ ("foo_4", ["app_19"; "app_22"; "bar_11"]);
             ("bar_11", ["app_19"; "app_22"; "foo_4"]);
             ("app_22", ["app_19"; "bar_11"; "foo_4"]);
             ("app_19", ["foo_4"; "bar_11"; "app_22"]) ];
         tinterfere "letrec_and_ifs"
           "let rec foo = (lambda (x): x) in if (4 > 3): let rec bar = (lambda (x): x) in 1 else: \
            let rec baz = (lambda (x): x) in 4"
           [ ("foo_4", ["bar_15"; "baz_23"; "binop_10"]);
             ("bar_15", ["foo_4"; "binop_10"]);
             ("baz_23", ["foo_4"; "binop_10"]);
             ("binop_10", ["foo_4"; "baz_23"; "bar_15"]) ] ]
;;

let remove_node =
  [ t_graph "r1"
      (remove_node
         (graph_from_assoc_list [("x", ["y"; "z"]); ("z", ["x"; "y"]); ("y", ["x"; "z"])])
         "z" )
      [("x", ["y"]); ("y", ["x"])] ]
;;

let graph_suite = "graph_suite" >::: remove_node

let color_graph_suite =
  "color_graph_suite"
  >::: [ t_any "color1" (color_graph (graph_from_assoc_list [("x", [])]) []) [("x", Reg R10)];
         t_any "color2_non_interfering"
           (color_graph (graph_from_assoc_list [("x", []); ("y", [])]) [])
           [("x", Reg R10); ("y", Reg R10)];
         t_any "color2_interfering"
           (color_graph (graph_from_assoc_list [("x", ["y"]); ("y", ["x"])]) [])
           [("x", Reg R12); ("y", Reg R10)];
         t_any "color3_all_interfere"
           (color_graph
              (graph_from_assoc_list [("x", ["y"; "z"]); ("z", ["x"; "y"]); ("y", ["x"; "z"])])
              [] )
           [("x", Reg R13); ("y", Reg R12); ("z", Reg R10)];
         t_any "color3_2_interfere"
           (color_graph (graph_from_assoc_list [("x", []); ("z", ["y"]); ("y", ["z"])]) [])
           [("x", Reg R10); ("y", Reg R12); ("z", Reg R10)];
         t_any "color3_indirect_interfere"
           (color_graph (graph_from_assoc_list [("x", ["y"]); ("z", ["y"]); ("y", ["x"; "z"])]) [])
           [("x", Reg R10); ("y", Reg R12); ("z", Reg R10)];
         t_any "color_12_non_interfering"
           (color_graph
              (graph_from_assoc_list
                 [ ("a", []);
                   ("b", []);
                   ("c", []);
                   ("d", []);
                   ("e", []);
                   ("f", []);
                   ("g", []);
                   ("h", []);
                   ("i", []);
                   ("j", []);
                   ("k", []);
                   ("l", []) ] )
              [] )
           [ ("a", Reg R10);
             ("b", Reg R10);
             ("c", Reg R10);
             ("d", Reg R10);
             ("e", Reg R10);
             ("f", Reg R10);
             ("g", Reg R10);
             ("h", Reg R10);
             ("i", Reg R10);
             ("j", Reg R10);
             ("k", Reg R10);
             ("l", Reg R10) ];
         t_any "color_12_non_interfering"
           (color_graph
              (graph_from_assoc_list
                 [ ("z", ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"]);
                   ("a", ["z"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"]);
                   ("b", ["z"; "a"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"]);
                   ("c", ["z"; "a"; "b"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"]);
                   ("d", ["z"; "a"; "b"; "c"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"]);
                   ("e", ["z"; "a"; "b"; "c"; "d"; "f"; "g"; "h"; "i"; "j"; "k"; "l"]);
                   ("f", ["z"; "a"; "b"; "c"; "d"; "e"; "g"; "h"; "i"; "j"; "k"; "l"]);
                   ("g", ["z"; "a"; "b"; "c"; "d"; "e"; "f"; "h"; "i"; "j"; "k"; "l"]);
                   ("h", ["z"; "a"; "b"; "c"; "d"; "e"; "f"; "g"; "i"; "j"; "k"; "l"]);
                   ("i", ["z"; "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "j"; "k"; "l"]);
                   ("j", ["z"; "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "k"; "l"]);
                   ("k", ["z"; "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "l"]);
                   ("l", ["z"; "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"]) ] )
              [] )
           [ ("a", RegOffset (~-16, RBP));
             ("b", RegOffset (~-8, RBP));
             ("c", Reg R9);
             ("d", Reg R8);
             ("e", Reg RDX);
             ("f", Reg RCX);
             ("g", Reg RDI);
             ("h", Reg RSI);
             ("i", Reg RBX);
             ("j", Reg R14);
             ("k", Reg R13);
             ("l", Reg R12);
             ("z", Reg R10) ];
         tcgraph "num" "1" [];
         tcgraph "simple_let" "let x = 10 in x" [("x_4", Reg R10)];
         tcgraph "three_let_plus" "let x = 1, y = 2, z = 3 in x + y + z"
           [("binop_15", Reg R14); ("x_4", Reg R13); ("y_8", Reg R12); ("z_12", Reg R10)];
         tcgraph "three_let_use" "let x = 1, y = x + 2, z = y + x + 3 in y"
           [("z_14", Reg R10); ("y_8", Reg R12); ("x_4", Reg R13); ("binop_16", Reg R14)];
         tcgraph "nesting_lets" "let x = (let y = x + 1 in y) in let y = (let z = x in x) in x + y "
           [("z_17", Reg R10); ("y_7", Reg R12); ("y_14", Reg R13); ("x", Reg R10); ("x_4", Reg R14)];
         tcgraph "lets_and_lams" "let x = 1 in (lambda (f, g, h): let y = x + g in 1)"
           [("x_4", Reg R10)];
         tcgraph ~delete:(StringSet.of_list ["a"]) "let_with_delete" "let y = x + a in x"
           [("x", Reg R12); ("y_4", Reg R10)];
         tcgraph
           ~delete:(StringSet.of_list ["a"; "b"; "c"])
           "lets_with_delete" "let y = x + a in let x = b + c in b"
           [("y_4", Reg R10); ("x", Reg R12); ("x_10", Reg R12)];
         tcgraph "letrec_simple" "let rec foo = (lambda (x): x) in foo(3)" [("foo_4", Reg R10)];
         tcgraph "double_letrec"
           "let rec foo = (lambda (x): x) in let rec bar = (lambda (z): foo(z)) in bar(1) + foo(3)"
           [("foo_4", Reg R10); ("bar_11", Reg R12); ("app_22", Reg R13); ("app_19", Reg R14)];
         tcgraph "let rec in ifs"
           "let rec foo = (lambda (x): x) in if (4 > 3): let rec bar = (lambda (x): x) in 1 else: \
            let rec baz = (lambda (x): x) in 4"
           [("foo_4", Reg R10); ("bar_15", Reg R13); ("baz_23", Reg R13); ("binop_10", Reg R12)] ]
;;

let pair_tests =
  [ t "tup1"
      "let t = (4, (5, 6)) in\n\
      \            begin\n\
      \              t[0] := 7;\n\
      \              t\n\
      \            end" "" "(7, (5, 6))";
    t "tup2"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := nil;\n\
      \              t\n\
      \            end" "" "(4, nil)";
    t "tup3"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := t;\n\
      \              t\n\
      \            end" "" "(4, <cyclic tuple 1>)";
    t "tup4" "let t = (4, 6) in\n            (t, t)" "" "((4, 6), (4, 6))" ]
;;

let pipeline_suite = "pipeline_suite" >::: pair_tests

let oom =
  [ tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
    tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
    tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation";
    tgcerr "gc_tuple_but_full" builtins_size "(1, 2)" "" "Out of memory";
    tgcerr "gc_lambda_but_full" (3 + builtins_size) "(lambda (x): x)" "" "Out of memory";
    tgcerr "gc_lambda_in_tup_but_full" (11 + builtins_size)
      "((lambda (x): x), (lambda (y): (lambda (x): x + y)))" "" "Out of memory" ]
;;

let gc =
  [ tgc "gc_let" (4 + builtins_size) "let x = (1, 2), y = (3, 4) in x" "" "(1, 2)";
    tgc "gc_lam1" (4 + builtins_size) "let f = (lambda (x): let y = 5 in x) in f(1)" "" "1";
    tgc "gc_lam2" (8 + builtins_size) "let f = (lambda (x): let y = 5 in x) in f((1, 2))" ""
      "(1, 2)";
    tgc "gc_call_lams" (8 + builtins_size) "let f = (lambda: (1, 2)) in f(); f(); f(); f(); f()" ""
      "(1, 2)";
    tgc "gc_call_identity" (4 + builtins_size)
      "let f = (lambda(x): x) in f(1); f(2); f(3); f(4); f(5)" "" "5";
    tgc "gc_num" builtins_size "5" "" "5";
    tgc "gc_lambdas_in_tuples" (16 + builtins_size)
      "let t = ((lambda (x): x), (lambda (y): (lambda (x): 1 + y))) in t[1](2)(4)" "" "3";
    tgc "gc_lambdas_in_tuples_more_frees" (18 + builtins_size)
      "let t = ((lambda (x): x), (lambda (y, z): (lambda (x): 1 + y + z))) in t[1](2, 6)(4)" "" "9";
    tgc "gc_nested_lambdas" (14 + builtins_size)
      "(lambda (x): (lambda (y, z): (lambda (w): w + x + y + z)))(1)(2, 3)(4)" "" "10";
    tgc "gc_nested_tuples" (16 + builtins_size) "(1, (2, (3, (4, 5, (6, nil, nil, (7,))))))[0]" ""
      "1";
    tgc "gc_cyclic_tuple" (4 + builtins_size) "let t = (1, nil) in t[1] := t; t[1][1][1][1][0]" ""
      "1";
    tgc "gc_cyclic_tuples" (12 + builtins_size)
      "let t1 = (1, nil), t2 = (2, t1), t3 = (3, t2) in t1[1] := t3; t1[1][1][0]" "" "2";
    tgc "gc_lambda_in_cyclic_tuple" (8 + builtins_size)
      "let t = ((lambda (x): x), nil) in t[1] := t; t[1][1][1][0](17)" "" "17";
    tgc "gc_recursive_lambda" (4 + builtins_size)
      "let rec fact = (lambda(n): if n == 0: 1 else: n * fact(sub1(n))) in fact(5)" "" "120";
    tgc "gc_stress" (8 + builtins_size)
      "def churn(n): if n == 0: 0 else: (1, 2); churn(sub1(n))\n churn(100)" "" "0";
    tgc "gc_not_needed" (4 + builtins_size) "let garbage = (1, 2) in 1" "" "1" ]
;;

let gc_suite = "gc_suite" >::: oom @ gc

let input_suite = "input_suite" >::: [t "input1" "let x = input() in x + 2" "123" "125"]

let compile_aexpr_suite =
  "compile_aexpr_suite"
  >::: [ t_error "x_not_found" (InternalCompilerError "Name x not found in tag env 1") (fun _ ->
             compile_aexpr
               (free_vars_A
                  (ALet ("x", CImmExpr (ImmNum (4L, 3)), ACExpr (CImmExpr (ImmNum (2L, 4))), 1)) )
               [] 1 "" );
         t_asm "compile_let_no_use"
           (compile_aexpr
              (free_vars_A
                 (ALet ("x", CImmExpr (ImmNum (4L, 3)), ACExpr (CImmExpr (ImmNum (2L, 4))), 1)) )
              [(1, [("x", RegOffset (-8, RBP))])]
              1 "" )
           [ IMov (Reg RAX, Const 8L);
             IInstrComment (IMov (RegOffset (-8, RBP), Reg RAX), "binding x at tag 1");
             IMov (Reg RAX, Const 4L) ];
         t_asm "compile_simple_let1"
           (compile_aexpr
              (free_vars_A
                 (ALet ("x", CImmExpr (ImmNum (4L, 3)), ACExpr (CImmExpr (ImmId ("x", 4))), 1)) )
              [(1, [("x", RegOffset (-8, RBP))])]
              1 "" )
           [ IMov (Reg RAX, Const 8L);
             IInstrComment (IMov (RegOffset (-8, RBP), Reg RAX), "binding x at tag 1");
             IMov (Reg RAX, RegOffset (-8, RBP)) ];
         t_asm "compile_shadowing_let"
           (compile_aexpr
              (free_vars_A
                 (ALet
                    ( "x#1",
                      CImmExpr (ImmNum (4L, 7)),
                      ALet
                        ( "x#2",
                          CPrim2 (Plus, ImmId ("x#1", 6), ImmNum (2L, 5), 4),
                          ACExpr (CImmExpr (ImmId ("x#2", 3))),
                          2 ),
                      1 ) ) )
              [(1, [("x#1", RegOffset (-8, RBP)); ("x#2", RegOffset (-16, RBP))])]
              1 "" )
           [ IMov (Reg RAX, Const 8L);
             IInstrComment (IMov (RegOffset (-8, RBP), Reg RAX), "binding x#1 at tag 1");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 1L);
             IMov (Reg R11, RegOffset (-8, RBP));
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 4L);
             IAnd (Reg RAX, HexConst 1L);
             IMov (Reg R11, Const 4L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IMov (Reg R11, Const 4L);
             IAdd (Reg RAX, Reg R11);
             IJo (Label "?err_overflow");
             IInstrComment (IMov (RegOffset (-16, RBP), Reg RAX), "binding x#2 at tag 1");
             IMov (Reg RAX, RegOffset (-16, RBP)) ] ]
;;

let compile_cexpr_suite =
  "compile_cexpr_suite"
  >::: [ t_asm "compile_number"
           (compile_cexpr (free_vars_C (CImmExpr (ImmNum (45L, 1)))) [] 1 "")
           [IMov (Reg RAX, Const 90L)];
         t_asm "compile_true"
           (compile_cexpr (free_vars_C (CImmExpr (ImmBool (true, 1)))) [] 1 "")
           [IMov (Reg RAX, HexConst (-1L))];
         t_asm "compile_false"
           (compile_cexpr (free_vars_C (CImmExpr (ImmBool (false, 1)))) [] 1 "")
           [IMov (Reg RAX, HexConst 9223372036854775807L)];
         t_asm "compile_id"
           (compile_cexpr
              (free_vars_C (CImmExpr (ImmId ("x#1", 1))))
              [(1, [("x#1", RegOffset (-8, RBP))])]
              1 "" )
           [IMov (Reg RAX, RegOffset (-8, RBP))];
         t_asm "compile_is_bool"
           (compile_cexpr (free_vars_C (CPrim1 (IsBool, ImmBool (true, 1), 2))) [] 1 "")
           [ IMov (Reg RAX, HexConst (-1L));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             IMov (Reg RAX, HexConst 0xFFFFFFFFFFFFFFFFL);
             IJe (Label "is_bool_2");
             IMov (Reg RAX, HexConst 0x7fffffffffffffffL);
             ILabel "is_bool_2" ];
         t_asm "compile_is_num"
           (compile_cexpr (free_vars_C (CPrim1 (IsNum, ImmNum (2L, 1), 2))) [] 1 "")
           [ IMov (Reg RAX, Const 4L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IMov (Reg RAX, HexConst 0xFFFFFFFFFFFFFFFFL);
             IJe (Label "is_num_2");
             IMov (Reg RAX, HexConst 0x7FFFFFFFFFFFFFFFL);
             ILabel "is_num_2" ];
         t_asm "compile_is_tup"
           (compile_cexpr (free_vars_C (CPrim1 (IsTuple, ImmBool (false, 1), 2))) [] 1 "")
           [ IMov (Reg RAX, HexConst 0x7FFFFFFFFFFFFFFFL);
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IMov (Reg RAX, HexConst 0xFFFFFFFFFFFFFFFFL);
             IJe (Label "is_tup_2");
             IMov (Reg RAX, HexConst 0x7FFFFFFFFFFFFFFFL);
             ILabel "is_tup_2" ];
         t_asm "compile_add1"
           (compile_cexpr (free_vars_C (CPrim1 (Add1, ImmNum (5L, 2), 1))) [] 1 "")
           [ IMov (Reg RAX, Const 10L);
             IAnd (Reg RAX, HexConst 1L);
             IMov (Reg R11, Const 10L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 10L);
             IAdd (Reg RAX, Const 2L);
             IJo (Label "?err_overflow") ];
         t_asm "compile_sub1"
           (compile_cexpr (free_vars_C (CPrim1 (Sub1, ImmNum (5L, 2), 1))) [] 1 "")
           [ IMov (Reg RAX, Const 10L);
             IAnd (Reg RAX, HexConst 1L);
             IMov (Reg R11, Const 10L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 10L);
             IAdd (Reg RAX, Const (-2L));
             IJo (Label "?err_overflow") ];
         t_asm "compile_eq"
           (compile_cexpr
              (free_vars_C (CPrim2 (Eq, ImmNum (3L, 1), ImmBool (false, 2), 3)))
              [] 1 "" )
           [ IMov (Reg RAX, Const 6L);
             IMov (Reg R11, HexConst 0x7FFFFFFFFFFFFFFFL);
             ICmp (Reg RAX, Reg R11);
             IMov (Reg RAX, HexConst (-1L));
             IJe (Label "eq_3");
             IMov (Reg RAX, HexConst 0x7FFFFFFFFFFFFFFFL);
             ILabel "eq_3" ];
         t_asm "compile_ge"
           (compile_cexpr
              (free_vars_C (CPrim2 (GreaterEq, ImmNum (12L, 1), ImmNum (10L, 2), 3)))
              [] 1 "" )
           [ IMov (Reg RAX, Const 24L);
             IAnd (Reg RAX, HexConst 1L);
             IMov (Reg R11, Const 24L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 20L);
             IAnd (Reg RAX, HexConst 1L);
             IMov (Reg R11, Const 20L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 24L);
             IMov (Reg R11, Const 20L);
             ICmp (Reg RAX, Reg R11);
             IMov (Reg RAX, HexConst (-1L));
             IJge (Label "greater_eq_3");
             IMov (Reg RAX, HexConst 0x7FFFFFFFFFFFFFFFL);
             ILabel "greater_eq_3" ];
         t_asm "compile_prim2"
           (compile_cexpr (free_vars_C (CPrim2 (Minus, ImmNum (4L, 3), ImmNum (3L, 8), 4))) [] 1 "")
           [ IMov (Reg RAX, Const 8L);
             IAnd (Reg RAX, HexConst 1L);
             IMov (Reg R11, Const 8L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 6L);
             IAnd (Reg RAX, HexConst 1L);
             IMov (Reg R11, Const 6L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 8L);
             IMov (Reg R11, Const 6L);
             ISub (Reg RAX, Reg R11);
             IJo (Label "?err_overflow") ];
         t_asm "compile_if"
           (compile_cexpr
              (free_vars_C
                 (CIf
                    ( ImmBool (true, 4),
                      ACExpr (CImmExpr (ImmNum (4L, 3))),
                      ACExpr (CImmExpr (ImmNum (5L, 2))),
                      1 ) ) )
              [] 1 "" )
           [ IMov (Reg RAX, HexConst (-1L));
             IAnd (Reg RAX, HexConst 7L);
             IMov (Reg R11, HexConst (-1L));
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_if_not_bool");
             IMov (Reg RAX, HexConst (-1L));
             IMov (Reg R11, HexConst 0x7fffffffffffffffL);
             ICmp (Reg RAX, Reg R11);
             IJe (Label "if_false_1");
             IMov (Reg RAX, Const 8L);
             IJmp (Label "done_1");
             ILabel "if_false_1";
             IMov (Reg RAX, Const 10L);
             ILabel "done_1" ];
         t_asm "compile_if_with_fun"
           (compile_cexpr
              (free_vars_C
                 (CIf
                    ( ImmId ("foo_1", 1),
                      ACExpr (CImmExpr (ImmNum (2L, 2))),
                      ACExpr (CImmExpr (ImmNum (20L, 3))),
                      4 ) ) )
              [(1, [("foo_1", RegOffset (-8, RBP))])]
              1 "" )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             IMov (Reg R11, RegOffset (-8, RBP));
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_if_not_bool");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IMov (Reg R11, HexConst 0x7fffffffffffffffL);
             ICmp (Reg RAX, Reg R11);
             IJe (Label "if_false_4");
             IMov (Reg RAX, Const 4L);
             IJmp (Label "done_4");
             ILabel "if_false_4";
             IMov (Reg RAX, Const 40L);
             ILabel "done_4" ];
         t_error "compile_or" (InternalCompilerError "And and or should've been desugared into ifs.")
           (fun _ ->
             compile_cexpr
               (free_vars_C (CPrim2 (Or, ImmBool (false, 1), ImmBool (false, 2), 3)))
               [] 1 "" );
         t_error "compile_and"
           (InternalCompilerError "And and or should've been desugared into ifs.") (fun _ ->
             compile_cexpr
               (free_vars_C (CPrim2 (And, ImmBool (false, 1), ImmBool (false, 2), 3)))
               [] 1 "" );
         t_asm "compile_fun_non_recursive_one_arg"
           (compile_cexpr
              (free_vars_C (CApp (ImmId ("foo", 2), [ImmNum (5L, 2)], Snake, 1)))
              [(1, [("foo", RegOffset (-8, RBP))])]
              1 "" )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 0x7L);
             IMov (Reg R11, RegOffset (-8, RBP));
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 1L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RSI);
             IPush (Reg RDI);
             IPush (Reg RCX);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, Const 10L);
             IPush (Reg R11);
             IInstrComment (IPush (Sized (QWORD_PTR, RegOffset (-8, RBP))), "push closure to stack");
             ICall (RegOffset (8, RAX));
             IInstrComment (IAdd (Reg RSP, Const 16L), "Popping 2 arguments");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RCX);
             IPop (Reg RDI);
             IPop (Reg RSI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm "compile_fun_non_recursive_many_arg"
           (compile_cexpr
              (free_vars_C
                 (CApp
                    ( ImmId ("bar", 4),
                      [ImmNum (5L, 0); ImmNum (5L, 1); ImmNum (5L, 2); ImmNum (5L, 3)],
                      Snake,
                      1 ) ) )
              [(1, [("bar", RegOffset (-8, RBP))])]
              1 "" )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             IMov (Reg R11, RegOffset (-8, RBP));
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 4L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RSI);
             IPush (Reg RDI);
             IPush (Reg RCX);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, Const 10L);
             IPush (Reg R11);
             IMov (Reg R11, Const 10L);
             IPush (Reg R11);
             IMov (Reg R11, Const 10L);
             IPush (Reg R11);
             IMov (Reg R11, Const 10L);
             IPush (Reg R11);
             IInstrComment (IPush (Sized (QWORD_PTR, RegOffset (-8, RBP))), "push closure to stack");
             ICall (RegOffset (8, RAX));
             IInstrComment (IAdd (Reg RSP, Const 40L), "Popping 5 arguments");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RCX);
             IPop (Reg RDI);
             IPop (Reg RSI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm "compile_native_fun_app"
           (compile_cexpr
              (free_vars_C (CApp (ImmId ("print", 1), [ImmNum (3L, 0)], Native, 1)))
              [] 1 "" )
           [ IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RSI);
             IPush (Reg RDI);
             IPush (Reg RCX);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Sized (QWORD_PTR, Reg RDI), Const 6L);
             ICall (Label "print");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RCX);
             IPop (Reg RDI);
             IPop (Reg RSI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm "compile_native_fun_app_multi_arg"
           (compile_cexpr
              (free_vars_C
                 (CApp (ImmId ("equal", 1), [ImmNum (3L, 0); ImmNum (3L, 0)], Native, 1)) )
              [] 1 "" )
           [ IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg RCX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Const 6L);
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Const 6L);
             IMov (Reg RDI, Reg RAX);
             ICall (Label "equal");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RCX);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI) ];
         t_asm "compile_native_fun_app_eight_arg"
           (compile_cexpr
              (free_vars_C
                 (CApp
                    ( ImmId ("equal", 1),
                      [ ImmNum (3L, 0);
                        ImmNum (4L, 0);
                        ImmNum (5L, 0);
                        ImmNum (6L, 0);
                        ImmNum (7L, 0);
                        ImmNum (8L, 0);
                        ImmNum (9L, 0);
                        ImmNum (10L, 0) ],
                      Native,
                      1 ) ) )
              [] 1 "" )
           [ IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg RCX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Const 20L);
             IPush (Reg RAX);
             IMov (Reg RAX, Const 18L);
             IPush (Reg RAX);
             IMov (Reg RAX, Const 16L);
             IMov (Reg R9, Reg RAX);
             IMov (Reg RAX, Const 14L);
             IMov (Reg R8, Reg RAX);
             IMov (Reg RAX, Const 12L);
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Const 10L);
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Const 8L);
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Const 6L);
             IMov (Reg RDI, Reg RAX);
             ICall (Label "equal");
             IAdd (Reg RSP, Const 16L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RCX);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI) ];
         t_asm "compile_tuple"
           (compile_cexpr
              (free_vars_C (CTuple ([ImmNum (3L, 2); ImmBool (false, 1); ImmNil 3], 0)))
              [] 1 "" )
           [ IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 3L);
             IMov (Reg R11, Const 6L);
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, HexConst 0x7FFFFFFFFFFFFFFFL);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IMov (Reg R11, HexConst 0x0000000000000001L);
             IMov (Sized (QWORD_PTR, RegOffset (24, R15)), Reg R11);
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IAdd (Reg R15, Const 32L) ];
         t_asm "compile_checksize"
           (compile_cexpr
              (free_vars_C (CPrim2 (CheckSize, ImmId ("tup_4", 3), ImmNum (2L, 4), 5)))
              [(1, [("tup_4", RegOffset (-8, RBP))])]
              1 "" )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 4L);
             ISar (Reg R11, Const 1L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJne (Label "?err_tuple_destructure_mismatch");
             IAdd (Reg RAX, Const 1L) ];
         t_asm "snake_fun_call_tuple"
           (compile_cexpr
              (free_vars_C
                 (CApp (ImmId ("foo", 0), [ImmId ("y_6", 6); ImmId ("y_3", 5)], Snake, 3)) )
              [ ( 0,
                  [ ("foo", RegOffset (-8, RBP));
                    ("y_6", RegOffset (-16, RBP));
                    ("y_3", RegOffset (-24, RBP)) ] ) ]
              0 "" )
           [ ILineComment "checking that (foo) with tag 3 is a closure";
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IMov (Reg RDI, RegOffset (-8, RBP));
             IJne (Label "?err_call_not_closure");
             IInstrComment (IMov (Reg RAX, RegOffset (-8, RBP)), "compiled closure: foo");
             IInstrComment (ISub (Reg RAX, HexConst 5L), "strip off tag");
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 2L);
             IMov (Reg RDI, Reg R11);
             IJne (Label "?err_call_arity_err");
             IMov (Reg R11, RegOffset (-24, RBP));
             IPush (Reg R11);
             IMov (Reg R11, RegOffset (-16, RBP));
             IPush (Reg R11);
             IInstrComment (IPush (Sized (QWORD_PTR, RegOffset (-8, RBP))), "push closure to stack");
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 24L) ]
         (*t_asm "compile_nullary_lam"
                       (compile_cexpr
                          (free_vars_C (CLambda ([], ACExpr (CImmExpr (ImmNum (100L, 1))), 2)))
                          [] 0 "" )
                       [ ILineComment "skip over the code for the lambda";
                         IJmp (Label "lam_2_done");
                         ILabel "lam_2";
                         ILineComment "prologue";
                         IPush (Reg RBP);
                         IMov (Reg RBP, Reg RSP);
                         ILineComment "unpack the closure";
                         IInstrComment
                           ( ISub (Reg RSP, Const 0L),
                             "reserve space on the stack for closed-over vars and local vars" );
                         IInstrComment
                           ( IMov (Reg R11, RegOffset (16, RBP)),
                             "\\ load the self argument (assumes self is always first argument)" );
                         IInstrComment (ISub (Reg R11, HexConst 5L), "\t/ and untag it");
                         ILineComment "actual function body";
                         IMov (Reg RAX, Const 200L);
                         ILineComment "epilogue";
                         IMov (Reg RSP, Reg RBP);
                         IPop (Reg RBP);
                         IRet;
                         ILabel "lam_2_done";
                         ILineComment "start filling in the closure information";
                         IInstrComment (IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 0L), "arity");
                         IInstrComment (IMov (Sized (QWORD_PTR, Reg R11), Label "lam_2"), "\t\\ code pointer");
                         IInstrComment (IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11), "/");
                         IInstrComment
                           (IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 0L), "# of free variables");
                         ILineComment "start creating the closure value";
                         IInstrComment (IMov (Reg RAX, Reg R15), "\\ create the closure");
                         IInstrComment (IAdd (Reg RAX, HexConst 5L), "/");
                         IInstrComment
                           (IAdd (Reg R15, Const 32L), "update heap pointer, keeping 16-byte alignment");
                         ILineComment "now RAX contains a proper closure value" ];
                     t_asm "compile_unary_lam"
                       (compile_cexpr
                          (free_vars_C (CLambda (["x_4"], ACExpr (CImmExpr (ImmId ("x_4", 2))), 1)))
                          [(0, [("x_4", RegOffset (24, RBP))])]
                          0 "" )
                       [ ILineComment "skip over the code for the lambda";
                         IJmp (Label "lam_1_done");
                         ILabel "lam_1";
                         ILineComment "prologue";
                         IPush (Reg RBP);
                         IMov (Reg RBP, Reg RSP);
                         ILineComment "unpack the closure";
                         IInstrComment
                           ( ISub (Reg RSP, Const 0L),
                             "reserve space on the stack for closed-over vars and local vars" );
                         IInstrComment
                           ( IMov (Reg R11, RegOffset (16, RBP)),
                             "\\ load the self argument (assumes self is always first argument)" );
                         IInstrComment (ISub (Reg R11, HexConst 5L), "\t/ and untag it");
                         ILineComment "actual function body";
                         IMov (Reg RAX, RegOffset (24, RBP));
                         ILineComment "epilogue";
                         IMov (Reg RSP, Reg RBP);
                         IPop (Reg RBP);
                         IRet;
                         ILabel "lam_1_done";
                         ILineComment "start filling in the closure information";
                         IInstrComment (IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 1L), "arity");
                         IInstrComment (IMov (Sized (QWORD_PTR, Reg R11), Label "lam_1"), "\t\\ code pointer");
                         IInstrComment (IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11), "/");
                         IInstrComment
                           (IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 0L), "# of free variables");
                         ILineComment "start creating the closure value";
                         IInstrComment (IMov (Reg RAX, Reg R15), "\\ create the closure");
                         IInstrComment (IAdd (Reg RAX, HexConst 5L), "/");
                         IInstrComment
                           (IAdd (Reg R15, Const 32L), "update heap pointer, keeping 16-byte alignment");
                         ILineComment "now RAX contains a proper closure value" ];
           t_asm "compile_lam_with_frees"
             (compile_cexpr
                (free_vars_C
                   (CLambda
                      ( ["y_8"],
                        ALet
                          ( "binop_4",
                            CPrim2 (Plus, ImmId ("x", 8), ImmId ("y_8", 7), 6),
                            ACExpr (CPrim2 (Plus, ImmId ("binop_4", 5), ImmId ("z", 4), 3)),
                            2 ),
                        1 ) ) )
                [ ( 0,
                    [ ("y_8", RegOffset (24, RBP));
                      ("binop_4", RegOffset (-24, RBP));
                      ("x", RegOffset (8, RBP));
                      ("z", RegOffset (16, RBP)) ] ) ]
                0 "" )
             [ ILineComment "skip over the code for the lambda";
               IJmp (Label "lam_1_done");
               ILabel "lam_1";
               ILineComment "prologue";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILineComment "unpack the closure";
               IInstrComment
                 ( ISub (Reg RSP, Const 48L),
                   "reserve space on the stack for closed-over vars and local vars" );
               IInstrComment
                 ( IMov (Reg R11, RegOffset (16, RBP)),
                   "\\ load the self argument (assumes self is always first argument)" );
               IInstrComment (ISub (Reg R11, HexConst 5L), "\t/ and untag it");
               IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "\\ load z from closure");
               IInstrComment (IMov (RegOffset (16, RBP), Reg RAX), "/ into its correct stack slot");
               IInstrComment (IMov (Reg RAX, RegOffset (32, R11)), "\\ load x from closure");
               IInstrComment (IMov (RegOffset (8, RBP), Reg RAX), "/ into its correct stack slot");
               ILineComment "actual function body";
               IMov (Reg RAX, RegOffset (8, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IMov (Reg RDI, RegOffset (8, RBP));
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, RegOffset (24, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IMov (Reg RDI, RegOffset (24, RBP));
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, RegOffset (8, RBP));
               IMov (Reg R11, RegOffset (24, RBP));
               IAdd (Reg RAX, Reg R11);
               IJo (Label "?err_overflow");
               IInstrComment (IMov (RegOffset (-24, RBP), Reg RAX), "binding binop_4 at tag 2");
               IMov (Reg RAX, RegOffset (-24, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IMov (Reg RDI, RegOffset (-24, RBP));
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, RegOffset (16, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IMov (Reg RDI, RegOffset (16, RBP));
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, RegOffset (-24, RBP));
               IMov (Reg R11, RegOffset (16, RBP));
               IAdd (Reg RAX, Reg R11);
               IJo (Label "?err_overflow");
               ILineComment "epilogue";
               IMov (Reg RSP, Reg RBP);
               IPop (Reg RBP);
               IRet;
               ILabel "lam_1_done";
               ILineComment "start filling in the closure information";
               IInstrComment (IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 1L), "arity");
               IInstrComment (IMov (Sized (QWORD_PTR, Reg R11), Label "lam_1"), "\t\\ code pointer");
               IInstrComment (IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11), "/");
               IInstrComment
                 (IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 2L), "# of free variables");
               IInstrComment (IMov (Reg RAX, RegOffset (16, RBP)), "copy z from argument");
               IInstrComment (IMov (RegOffset (24, R15), Reg RAX), "into closure");
               IInstrComment (IMov (Reg RAX, RegOffset (8, RBP)), "copy x from argument");
               IInstrComment (IMov (RegOffset (32, R15), Reg RAX), "into closure");
               ILineComment "start creating the closure value";
               IInstrComment (IMov (Reg RAX, Reg R15), "\\ create the closure");
               IInstrComment (IAdd (Reg RAX, HexConst 5L), "/");
               IInstrComment
                 (IAdd (Reg R15, Const 48L), "update heap pointer, keeping 16-byte alignment");
               ILineComment "now RAX contains a proper closure value" ] *) ]
;;

let simple_if = "if true: 5 + 3 else: 6 * 6"

let simple_prim1 = "sub1(80)"

let simple_prim2 = "90 - 30"

let complex_prim2 = "(90 - 30) * 80 + 34 - (30 * -1)"

let id_error = "x"

let let_error = "let x = 4 in y"

let invalid_prog = "3 let y = 4 in 90"

let forty = "let x = 40 in x"

let fals = "let x = false in x"

let tru = "let x = true in x"

let math_tests =
  [ t "forty_one" "41" "" "41";
    t "simple_if" simple_if "" "8";
    t "simple_prim1" simple_prim1 "" "79";
    t "simple_minus_negative" "93 - 98" "" "-5";
    t "simple_plus_negative" "-8 + 3" "" "-5";
    t "negate_a_negative" "3 - -10" "" "13";
    t "simple_times" "3 * 4" "" "12";
    t "simple_prim2" simple_prim2 "" "60";
    t "complex_prim2" complex_prim2 "" "4864";
    t "add_nests" "(1 + 2) + (3 + 4)" "" "10";
    t "sub_nests" "(6 - 5) - (4 - 2)" "" "-1";
    t "zero_subtraction" "(1 - 2) - (3 - 4)" "" "0";
    t "mixed_ops1" "(6 - 4) + (3 - 5)" "" "0";
    t "mixed_ops2" "(2 - 5) + (4 * 5)" "" "17";
    t "nest_mixed_ops" "(1 + (2 + 3)) * ((4 - 5) - (0 * 6))" "" "-6";
    t "add1_even" "add1(6)" "" "7";
    t "add1_odd" "add1(5)" "" "6";
    t "add1_neg" "add1(-4)" "" "-3";
    t "sub1_even" "sub1(6)" "" "5";
    t "sub1_odd" "sub1(5)" "" "4";
    t "sub1_neg" "sub1(-4)" "" "-5" ]
;;

let logic_tests =
  [ t "true" "true" "" "true";
    t "false" "false" "" "false";
    t "not_true" "!(true)" "" "false";
    t "not_false" "!(false)" "" "true";
    t "not_mixture" "!(!(!(!(!(false)))))" "" "true";
    t "t_and_t" "true && true" "" "true";
    t "t_and_f" "true && false" "" "false";
    t "f_and_t" "false && true" "" "false";
    t "f_and_f" "false && false" "" "false";
    t "and_short1" "false && print(4)" "" "false";
    t "and_short2" "false && 4" "" "false";
    t "t_or_t" "true || true" "" "true";
    t "t_or_f" "true || false" "" "true";
    t "f_or_t" "false || true" "" "true";
    t "f_or_f" "false || false" "" "false";
    t "or_short1" "true || print(4)" "" "true";
    t "or_short2" "true || 34343" "" "true";
    t "not_and_or" "!(4 > 5) && (false || (3 >= 2))" "" "true";
    t "logic_with_is" "isnum(3) && (isbool(false) && true) && !(5 > 3)" "" "false";
    t "logic_with_print" "print(false) || print(true)" "" "false\ntrue\ntrue";
    t "logic_with_print_short" "print(true) || print(false)" "" "true\ntrue" ]
;;

let print_tests =
  [ t "print_num" "print(4)" "" "4\n4";
    t "print_bool" "print(false)" "" "false\nfalse";
    t "print_binop1" "print(45 + 3 - 2)" "" "46\n46";
    t "print_binop2" "print(print(45) + print(3) - 2)" "" "45\n3\n46\n46";
    t "print_wrapped1" "isnum(print(45 + 3 - 2))" "" "46\ntrue";
    t "print_wrapped2" "isbool(print(true))" "" "true\ntrue";
    t "print_let_bind" "let q = print(4) in (q + 1)" "" "4\n5";
    t "print_let_body" "let q = 5 in print(q)" "" "5\n5";
    t "print_nested_let1" "let x = print(let x = print(2), y = print(false) in (x == y)) in x" ""
      "2\nfalse\nfalse\nfalse";
    t "print_nested_let2" "let x = print(let x = print(0) + 5 in x) in print(x + 10) + 5" ""
      "0\n5\n15\n20";
    t "print_nested_let3" "let a = 4 in let b = print(a * 5) in print(b - 9)" "" "20\n11\n11" ]
;;

let comparison_tests =
  [ (* --------------- Basic Cases --------------- *)
    t "five_g_three" "5 > 3" "" "true";
    t "zero_g_twelve" "0 > 12" "" "false";
    t "negative_g1" "-10 > -9" "" "false";
    t "negative_g2" "-10 > -11" "" "true";
    t "n_g_n" "90 > 90" "" "false";
    t "five_ge_three" "5 >= 3" "" "true";
    t "zero_ge_twelve" "0 >= 12" "" "false";
    t "negative_ge1" "-10 >= -9" "" "false";
    t "negative_ge2" "-10 >= -11" "" "true";
    t "n_ge_n" "90 >= 90" "" "true";
    t "five_l_three" "5 < 3" "" "false";
    t "zero_l_twelve" "0 < 12" "" "true";
    t "negative_l1" "-10 < -9" "" "true";
    t "negative_l2" "-10 < -11" "" "false";
    t "n_l_n" "90 < 90" "" "false";
    t "five_le_three" "5 <= 3" "" "false";
    t "zero_le_twelve" "0 <= 12" "" "true";
    t "negative_le1" "-10 <= -9" "" "true";
    t "negative_le2" "-10 <= -11" "" "false";
    t "n_le_n" "90 <= 90" "" "true";
    t "eq_num_true" "3 == 3" "" "true";
    t "eq_num_false" "33 == 3" "" "false";
    t "eq_zero" "0 == 0" "" "true";
    t "eq_bool_1" "true == true" "" "true";
    t "eq_bool_2" "false == false" "" "true";
    t "eq_bool_3" "true == false" "" "false";
    t "eq_bool_4" "false == true" "" "false";
    t "eq_mixed_1" "34 == true" "" "false";
    t "eq_mixed_2" "false == 45" "" "false";
    (* --------------- Complex Cases --------------- *)
    t "ge_binop_false" "(5 + 10) >= (6 * 3)" "" "false";
    t "ge_binop_true" "(5 * 3) >= (6 * 2)" "" "true";
    t "g_binop_false" "(8 + 0) > (4 * 2)" "" "false";
    t "g_binop_true" "(6 * 30) > (60 * 2)" "" "true";
    t "l_binop_false" "(2 + 2) < (1 * 0)" "" "false";
    t "l_binop_true" "(2 - 1) < (1 + 2)" "" "true";
    t "le_binop_false" "(55 * 2) <= (8 + 4 - 5)" "" "false";
    t "le_binop_true" "(45 - 3) <= (300 * 4)" "" "true";
    t "complex_comp" "(23 >= 23) && ((1 + 4) < 8) || false || !(45 <= 5)" "" "true" ]
;;

let ifs_and_lets_tests =
  [ t "if_true" "if true: 4 else: 28" "" "4";
    t "if_false" "if false: 4 else: 28" "" "28";
    t "if_with_let_conditional" "if (let x = true in x): 4 else: 180" "" "4";
    t "if_with_let_then" "if true: (let x = 22 in x) else: 2" "" "22";
    t "if_with_let_else" "if false: 22 else: (let x = 2 in x)" "" "2";
    t "binop_with_ifs" "(if false: 23 else: 34) + (if true: 10 else: 21)" "" "44";
    t "ifs_and_lets"
      "(let x = (if true: 5 + 5 else: 6 * 2) in (let y = (if true: x * 3 else: x + 5) in y))" ""
      "30";
    t "nesting_ifs" "if false: (if false: 1 else: 2) else: 3" "" "3";
    t "if_with_isnum_cond1" "if isnum(5): 50 else: 3" "" "50";
    t "if_with_isnum_cond2" "if isnum(false): 50 else: 3" "" "3";
    t "if_with_isbool_cond1" "if isbool(true): 50 else: 3" "" "50";
    t "if_with_isbool_cond2" "if isbool(4): 50 else: 3" "" "3";
    t "if_with_isnum_cond_short" "if isnum(false && 300): 5 else: 54" "" "54";
    t "if_with_isbool_cond_short" "if isbool(false && 12): 5 else: true" "" "5";
    t "if_ge_cond_false" "if (3 >= 5): 2 else: 3" "" "3";
    t "if_l_cond_true" "if (2 < 5): 2 else: 3" "" "2";
    t "if_g_branch_else" "if true: (3 > 4) else: (1 == 1)" "" "false";
    t "if_e_branch_then" "if false: (3 > 4) else: (1 == 1)" "" "true";
    t "if_short_circuit" "if (true || 3435): (false && 59) else: true" "" "false";
    t "if_print_then" "if print(true): print(12) + 45 else: print(5)" "" "true\n12\n57";
    t "if_print_else" "if print(false): print(12) else: print(4) * 2" "" "false\n4\n8";
    t "let_x_in_x" "let x = 90 in x" "" "90";
    t "let_x_in_x_plus_num" "let x = 33 in x + 44" "" "77";
    t "let_x_in_x_plus_x" "let x = 20 in x + x" "" "40";
    t "let_two_binds_plus" "let a = 12, b = 4 in a * b" "" "48";
    t "let_add1_body" "let x = 51 in add1(x)" "" "52";
    t "let_add1_bind" "let x = add1(51) in x" "" "52";
    t "let_sub1_body" "let x = 51 in sub1(x)" "" "50";
    t "let_sub1_bind" "let x = sub1(51) in x" "" "50";
    t "nesting_lets_add" "let q = 7, r = 8 in let s = 4 in q + r + s" "" "19";
    t "nesting_lets_minus" "let q = 9, r = 8 in let s = 7 in q - r - s" "" "-6";
    t "nestings_lets_times" "let q = 4, r = 4 in let s = 4 in q * r * s" "" "64";
    t "lets_with_let_binds" "let x = (let y = 6 + 2 in y) in x * 8" "" "64";
    t "shadowing_let_binds" "let x = (let x = 41 in x) in x" "" "41";
    t "let_with_operation_binds" "let thirty = 30 in let twenty = 20, res = (thirty + 5) in res" ""
      "35";
    t "let_binds_letrec_behavior1" "let x = 88, y = x in y" "" "88";
    t "let_binds_letrec_behavior2" "let x = 88, y = add1(x) in y" "" "89";
    t "let_binds_letrec_behavior3" "let x = 88, y = (x + 12) in y" "" "100";
    t "let_plus_let" "(let x = 1 in x) + (let x = 2 in x)" "" "3";
    t "let_not_eq_num" "(let b = 4 in b) == (let b = 55 in b)" "" "false";
    t "let_not_eq_bool" "(let a = false in a) == (let a = true in a)" "" "false";
    t "let_eq_num" "(let b = 4 in b) == (let b = 4 in b)" "" "true";
    t "let_eq_bool" "(let a = false in a) == (let a = false in a)" "" "true";
    t "let_different_binds_eq_num" "(let b = 4 in b) == (let c = 4 in c)" "" "true";
    t "let_different_binds_eq_bool" "(let b = true in b) == (let c = true in c)" "" "true";
    t "let_compare_false" "let x = 213, y = 44 in x < y" "" "false";
    t "let_compare_true" "let x = add1(239 + 4), y = 244 in x >= y" "" "true";
    t "let_isnum_bind" "let x = isnum(4) in if x: 4 else: false" "" "4";
    t "let_isbool_bind" "let x = isbool(4) in if x: 4 else: false" "" "false";
    t "let_comparison_in_binds"
      "let a = (22 == false), b = (34 + 2), c = true, d = (40 == 20) in a || d || c" "" "true";
    t "let_nesting_comparison"
      "let x = (99 >= 4) in let y = (x || (6 == 2)) in (isnum(x) || isbool(y) && y)" "" "true" ]
;;

let is_tests =
  [ t "isnum_num" "isnum(4)" "" "true";
    t "isnum_bool" "isnum(false)" "" "false";
    t "isbool_num" "isbool(-39)" "" "false";
    t "isbool_bool" "isbool(false)" "" "true" ]
;;

let general_error_tests =
  [ te "id_error" id_error "The identifier x, used at <id_error, 1:0-1:1>, is not in scope";
    te "let_error" let_error "The identifier y, used at <let_error, 1:13-1:14>, is not in scope";
    te "invalid_prog" invalid_prog "Parse error at line 1, col 5: token `let`" ]
;;

let misc_tests =
  [ t "forty" forty "" "40";
    t "fals" fals "" "false";
    t "tru" tru "" "true";
    t "if2" "if false: 4 else: 2" "" "2";
    t "if1" "if true: 4 else: 2" "" "4";
    t "let_if" "let y = -1, x = 2 + y in if false: sub1(x) else: y - 3" "" "-4";
    t "starter_file"
      "let x =\n\
      \        if true:\n\
      \          (if true: add1(2) else: add1(3))\n\
      \        else:\n\
      \          (if false: sub1(4) else: sub1(5))\n\
      \      in x" "" "3" ]
;;

let type_error_tests =
  [ te "if_not_bool" "if 4: 2 else: 4" "if expected a boolean";
    te "not_not_bool" "!(3)" "logic expected a boolean";
    te "or_not_bool_right" "false || 4" "logic expected a boolean";
    te "or_not_bool_left" "5 || true" "logic expected a boolean";
    te "and_not_bool_right" "true && 4" "logic expected a boolean";
    te "and_not_bool_left" "5 && true" "logic expected a boolean";
    te "add1_not_num" "add1(true)" "arithmetic expected a number";
    te "sub1_not_num" "sub1(false)" "arithmetic expected a number";
    te "plus_not_num_right" "4 + true" "arithmetic expected a number";
    te "plus_not_num_left" "false + 3" "arithmetic expected a number";
    te "minus_not_num_right" "23 - true" "arithmetic expected a number";
    te "minus_not_num_left" "false - 33" "arithmetic expected a number";
    te "times_not_num_right" "562 * true" "arithmetic expected a number";
    te "times_not_num_left" "false * 332" "arithmetic expected a number";
    te "le_not_num_left" "false <= 3" "comparison expected a number";
    te "le_not_num_right" "4 <= true" "comparison expected a number";
    te "l_not_num_left" "false < 3" "comparison expected a number";
    te "l_not_num_right" "4 < true" "comparison expected a number";
    te "ge_not_num_left" "false >= 3" "comparison expected a number";
    te "ge_not_num_right" "4 >= true" "comparison expected a number";
    te "g_not_num_left" "false > 3" "comparison expected a number";
    te "g_not_num_right" "4 > true" "comparison expected a number";
    te "get_not_num" "(1, 2, 3)[(1,)]" "get index is not a number";
    te "set_not_num" "(1, 2, 3)[(2,)] := 6" "set index is not a number";
    te "get_not_tup" "5[0]" "get expected tuple";
    te "set_not_tup" "5[0] := 2" "set expected tuple";
    te "get_low_idx" "(1, 2, 3)[-3]" "index too small to get";
    te "set_low_idx" "(1, 2, 3)[-3] := 4" "index too small to set";
    te "get_high_idx" "(1, 2, 3)[5]" "index too large to get";
    te "set_high_idx" "(1, 2, 3)[5] := false" "index too large to set";
    te "nil_deref" "nil[4]" "access component of nil" ]
;;

let overflow_error_tests =
  [ te "add1_overflow" "add1(4611686018427387903)" "overflow";
    te "sub1_overflow" "sub1(-4611686018427387904)" "overflow";
    te "plus_overflow" "4611686018427387900 + 48" "overflow";
    te "plus_overflow2" "48 + 4611686018427387900" "overflow";
    te "minus_overflow" "-4611686018427387900 - 100" "overflow";
    te "minus_overflow2" "-100 - 4611686018427387900" "overflow";
    te "times_overflow" "4611686018427387900 * 2" "overflow";
    te "times_overflow2" "2 * 4611686018427387900" "overflow";
    te "number_overflow" "4611686018427387909" "not supported in this language" ]
;;

let test_prog =
  "let x = if sub1(55) < 54: (if 1 > 0: add1(2) else: add1(3)) else: (if 0 == 0: sub1(4) else: \
   sub1(5)) in x"
;;

let input_tests =
  [ t "input1" "let x = input() in x + 2" "123" "125";
    t "input_echo_false" "input()" "false" "false";
    t "input_echo_3" "input()" "3" "3";
    t "input_echo_-72" "input()" "-72" "-72";
    t "input_multiple_inputs" "(input() + 1, !(input()), 3 * input())" "3\ntrue\n-16"
      "(4, false, -48)";
    t "input_nested_input" "def id(x): x\nid(let x = 12 in (2, input()))" "8" "(2, 8)";
    t "input_input_used_twice" "let x = input() in (x + 1, x + 2)" "3" "(4, 5)";
    t "input_almost_overflow" "input() - 4611686018427387903" "4611686018427387903" "0";
    terr "input_overflow_positive" "input()" "4611686018427387904"
      "overflow, got -4611686018427387904";
    terr "input_overflow_negative" "input()" "-4611686018427387905"
      "overflow, got 4611686018427387903";
    terr "input_tuple" "input()" "(1, 2)"
      "Error 1: Illegal input (only a single number or bool expected)";
    terr "input_string" "input()" "nil"
      "Error 1: Illegal input (only a single number or bool expected)";
    t "input_almost_num1" "input()" "1234S" "1234";
    terr "input_almost_num2" "input()" "S1234"
      "Error 1: Illegal input (only a single number or bool expected)" ]
;;

let integration_test_suite =
  "integration_test_suite"
  >::: general_error_tests @ overflow_error_tests @ type_error_tests @ misc_tests @ math_tests
       @ logic_tests @ ifs_and_lets_tests @ comparison_tests @ is_tests @ print_tests @ pair_tests
       @ input_tests
;;

let () =
  run_test_tt_main
    ( "all_tests"
    >::: [ free_vars_suite;
           fvc_suite;
           pipeline_suite;
           graph_suite;
           interfere_suite;
           reg_alloc_suite;
           naive_alloc_suite;
           compile_aexpr_suite;
           (* compile_cexpr_suite; *)
           integration_test_suite;
           (* gc_suite; *)
           color_graph_suite (* input_file_test_suite () *) ] )
;;

(* let () = run_test_tt_main ("all_tests" >::: [input_file_test_suite ()]) *)
