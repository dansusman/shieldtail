open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Graph

let alloc_strat = Register

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
    ^ List.fold_left (fun fv prev_string -> fv ^ "," ^ prev_string) "" fvs
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

let talloc name program expected =
  t_any name
    (snd
       (naive_stack_allocation
          (free_vars_cache
             (atag
                (anf
                   (rename_and_tag (tag (desugar (add_native_lambdas (parse_string name program))))) ) ) ) ) )
    expected
;;

let tregalloc name program expected =
  t_any name
    (snd
       (register_allocation
          (free_vars_cache
             (atag (anf (rename_and_tag (tag (desugar (parse_string name program)))))) ) ) )
    expected
;;

let builtins_size =
  4 (* arity + 0 vars + codeptr + padding *)
  * 1 (* TODO FIXME (List.length Compile.native_fun_bindings) *)
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

let reg_alloc_suite =
  "reg_alloc_suite"
  >::: [ tregalloc "num" "3" [(0, [])];
         tregalloc "prim1" "sub1(6)" [(0, [])];
         (* TODO there's a let, there should be a reg *)
         tregalloc "let" "let x = 1 in x" [(0, [("x_4", Reg R10)])];
         tregalloc "two_prim1s" "add1(sub1(6))" [(0, [("unary_3", Reg R10)])];
         (* TODO let free adder programs should use <=1 register *)
         tregalloc "three_prim1s" "add1(add1(sub1(6)))"
           [(0, [("unary_3", Reg R10); ("unary_4", Reg R10)])];
         tregalloc "four_prim1s" "sub1(add1(add1(sub1(6))))"
           [(0, [("unary_3", Reg R10); ("unary_4", Reg R10); ("unary_5", Reg R10)])];
         tregalloc "plus" "3 + 4" [(0, [])];
         tregalloc "plus3" "3 + 4 + 5" [(0, [("binop_3", Reg R10)])];
         tregalloc "plus4" "3 + 4 + 5 + 6" [(0, [("binop_3", Reg R10); ("binop_4", Reg R10)])];
         tregalloc "plus_times" "(3 + 4) * (5 + 6)"
           [(0, [("binop_3", Reg R12); ("binop_6", Reg R10)])];
         tregalloc "nested_let_both_bottom" "let x = 1, y = 2 in (x, y)"
           [(0, [("x_4", Reg R12); ("y_8", Reg R10)])];
         tregalloc "nested_let_neither_bottom" "let x = 1, y = 2 in 3"
           [(0, [("x_4", Reg R10); ("y_8", Reg R10)])];
         tregalloc "nested_let_first_bottom" "let x = 1, y = 2 in x"
           [(0, [("x_4", Reg R12); ("y_8", Reg R10)])];
         tregalloc "nested_let_chain" "let x = 1, y = x in y"
           [(0, [("x_4", Reg R10); ("y_8", Reg R10)])];
         tregalloc "disjoint_interference"
           "let x = 1 in let y = (let w = 3 in w) in let z = 3 in (x, y, z)"
           [(0, [("w_11", Reg R10); ("x_4", Reg R13); ("y_8", Reg R12); ("z_16", Reg R10)])] ]
;;

let interfere_suite =
  "interfere_suite"
  >::: [ tinterfere "num" "3" [];
         tinterfere "prim1" "sub1(6)" [];
         tinterfere "let" "let x = 1 in x" [("x_4", [])];
         tinterfere "two_prim1s" "add1(sub1(6))" [("unary_3", [])];
         tinterfere "three_prim1s" "add1(add1(sub1(6)))" [("unary_3", []); ("unary_4", [])];
         tinterfere "nested_let" "let x = 1 in let y = 2 in (x, y)"
           [("x_4", ["y_8"]); ("y_8", ["x_4"])];
         tinterfere "nested_let_not_in_bottom" "let x = 1 in let y = x in y"
           [("x_4", []); ("y_8", [])];
         tinterfere "three_nested_let"
           "let x = 1 in let y = 2 in let z = 3 in let xy = x + y in xy + z"
           [ ("x_4", ["z_12"; "y_8"]);
             ("xy_16", ["z_12"]);
             ("y_8", ["z_12"; "x_4"]);
             ("z_12", ["y_8"; "xy_16"; "x_4"]) ];
         tinterfere "disjoint_interference"
           "let x = 1 in let y = (let w = 3 in w) in let z = 3 in (x, y, z)"
           [ ("w_11", ["x_4"]);
             ("x_4", ["z_16"; "y_8"; "w_11"]);
             ("y_8", ["z_16"; "x_4"]);
             ("z_16", ["y_8"; "x_4"]) ];
         tinterfere "if_simple" "if true: 1 else: 2" [];
         tinterfere "if_in_let" "let x = true in if x: 1 else: 2" [("x_4", [])];
         tinterfere "lets_in_if" "if true: (let x = 1 in x) else: (let y = 2 in y)"
           [("x_6", []); ("y_11", [])];
         tinterfere "lets_in_and_out_if"
           "let z = true in if z: (let x = 1 in x) else: (let y = 2 in y)"
           [("x_10", []); ("y_15", []); ("z_4", [])];
         tinterfere "lets_in_and_out_if_interfere"
           "let z = true in if z: (let x = 1 in x) else: (let y = 2 in y + z)"
           [("x_10", []); ("y_15", ["z_4"]); ("z_4", ["y_15"])];
         tinterfere "simple_seq" "print(5); 6" [];
         tinterfere "let_in_seq" "let x = 1 in x; let y = 2 in y" [("x_4", []); ("y_12", [])];
         tinterfere "let_over_seq" "let z = 3 in (let x = 1 in x; let y = 2 in y)"
           [("x_8", []); ("y_16", []); ("z_4", [])];
         tinterfere "let_over_seq_interfere" "let z = 3 in (let x = 1 in x + z; let y = 2 in y)"
           [("x_8", ["z_4"]); ("y_18", []); ("z_4", ["x_8"])];
         tinterfere "let_over_seq_interfere_both"
           "let z = 3 in (let x = 1 in x + z; let y = 2 in y + z)"
           [("x_8", ["z_4"]); ("y_18", ["z_4"]); ("z_4", ["y_18"; "x_8"])];
         tinterfere "letrec_single" "let rec x = 1 in x" [("x_4", [])];
         tinterfere "letrec_double" "let rec x = 1, y = 2 in 3" [("x_4", ["y_7"]); ("y_7", ["x_4"])];
         tinterfere "letrec_triple" "let rec x = 1, y = 2, z = 3 in 4"
           [("x_4", ["y_7"; "z_10"]); ("y_7", ["x_4"; "z_10"]); ("z_10", ["x_4"; "y_7"])];
         tinterfere "letrec_single_with_free" "let rec x = y in 1" [("x_4", ["y"]); ("y", ["x_4"])];
         tinterfere "letrec_double_one_free" "let rec x = 1, y = z in 2"
           [("x_4", ["y_7"; "z"]); ("y_7", ["x_4"; "z"]); ("z", ["x_4"; "y_7"])];
         tinterfere "letrec_id" "let rec foo = (lambda (x): x) in foo(3)" [("foo_4", [])];
         tinterfere "letrec_recursive"
           "let rec foo = (lambda (x): x), bar = (lambda (y): foo(y)) in bar(1) + foo(3)"
           [("foo_4", ["bar_11"]); ("bar_11", ["foo_4"])];
         tinterfere "letrec_simple_body"
           "let rec foo = (lambda (x): x), bar = (lambda (y): application) in 1"
           [("foo_4", ["bar_11"]); ("bar_11", ["foo_4"])];
         tinterfere "letrec_recursive_nest"
           "let rec foo = (lambda (x): x) in let rec bar = (lambda (y): foo(y)) in bar(1) + foo(3)"
           [("foo_4", [""])] ]
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
             ("z", Reg R10) ] ]
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
    tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
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

let gc_suite =
  "gc_suite"
  >::: [ tgc "gc_lam1" (10 + builtins_size)
           "let f = (lambda: (1, 2)) in\n\
           \       begin\n\
           \         f();\n\
           \         f();\n\
           \         f();\n\
           \         f()\n\
           \       end" "" "(1, 2)" ]
       @ oom @ gc
;;

let input_suite = "input_suite" >::: [t "input1" "let x = input() in x + 2" "123" "125"]

let () =
  run_test_tt_main
    ( "all_tests"
    >::: [ free_vars_suite;
           free_vars_suite;
           gc_suite;
           pipeline_suite;
           graph_suite;
           interfere_suite;
           color_graph_suite ] )
;;
