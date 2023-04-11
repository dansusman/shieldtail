open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Graph

let alloc_strat = Naive

let t ?(alloc = alloc_strat) name program input expected =
  name >:: test_run ~args:[] ~std_input:input alloc program name expected
;;

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

let tanf name program input expected =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

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
           (* gc_suite; *)
           color_graph_suite (* input_file_test_suite () *) ] )
;;

(* let () = run_test_tt_main ("all_tests" >::: [input_file_test_suite ()]) *)
