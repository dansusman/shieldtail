open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Graph

let t name program input expected =
  name >:: test_run ~args:[] ~std_input:input Naive program name expected
;;

let tr name program input expected =
  name >:: test_run ~args:[] ~std_input:input Register program name expected
;;

let ta name program input expected =
  name >:: test_run_anf ~args:[] ~std_input:input program name expected
;;

let tgc name heap_size program input expected =
  name >:: test_run ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
;;

let tvg name program input expected =
  name >:: test_run_valgrind ~args:[] ~std_input:input Naive program name expected
;;

let tvgc name heap_size program input expected =
  name
  >:: test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
;;

let terr name program input expected =
  name >:: test_err ~args:[] ~std_input:input Naive program name expected
;;

let tgcerr name heap_size program input expected =
  name >:: test_err ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
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

(* let tfvs name program expected =
     name
     >:: fun _ ->
     let ast = parse_string name program in
     let anfed = anf (tag ast) in
     let vars = free_vars anfed in
     let c = Stdlib.compare in
     let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
     assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print
   ;; *)

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

let tinterfere name program expected =
  let (AProgram (body, _)) =
    free_vars_cache (atag (anf (rename_and_tag (tag (desugar (parse_string name program))))))
  in
  t_string name
    (string_of_graph (interfere body StringSet.empty))
    (string_of_graph (graph_from_assoc_list expected))
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

let regalloc =
  [ tregalloc "num" "3" [(0, [])];
    tregalloc "prim1" "sub1(6)" [(0, [])];
    tregalloc "two_prim1s" "add1(sub1(6))" [(0, [])];
    tregalloc "three_prim1s" "add1(add1(sub1(6)))" [(0, [])] ]
;;

let interfere =
  [ tinterfere "num" "3" [];
    tinterfere "prim1" "sub1(6)" [];
    tinterfere "let" "let x = 1 in x" [];
    tinterfere "two_prim1s" "add1(sub1(6))" [];
    tinterfere "three_prim1s" "add1(add1(sub1(6)))"
      [("unary_3", ["unary_4"]); ("unary_4", ["unary_3"])];
    tinterfere "nested_let" "let x = 1 in let y = 2 in x" [("x_4", ["y_8"]); ("y_8", ["x_4"])];
    tinterfere "three_nested_let" "let x = 1 in let y = 2 in let z = 3 in x + y + z"
      [ ("binop_15", ["z_12"; "y_8"; "x_4"]);
        ("x_4", ["z_12"; "y_8"; "binop_15"]);
        ("y_8", ["z_12"; "x_4"; "binop_15"]);
        ("z_12", ["y_8"; "x_4"; "binop_15"]) ];
    tinterfere "disjoint_interference"
      "let x = 1 in let y = (let w = 3 in w) in let z = 3 in x + y + z"
      [ ("binop_19", ["z_16"; "y_8"; "x_4"]);
        ("w_11", ["y_8"; "x_4"]);
        ("x_4", ["z_16"; "y_8"; "w_11"; "binop_19"]);
        ("y_8", ["z_16"; "x_4"; "w_11"; "binop_19"]);
        ("z_16", ["y_8"; "x_4"; "binop_19"]) ];
    tinterfere "if_simple" "if true: 1 else: 2" [];
    tinterfere "if_in_let" "let x = true in if x: 1 else: 2" [];
    tinterfere "lets_in_if" "if true: (let x = 1 in x) else: (let y = 2 in y)" [];
    tinterfere "lets_in_and_out_if" "let z = true in if z: (let x = 1 in x) else: (let y = 2 in y)"
      [];
    tinterfere "lets_in_and_out_if_interfere"
      "let z = true in if z: (let x = 1 in x) else: (let y = 2 in y + z)"
      [("y_15", ["z_4"]); ("z_4", ["y_15"])];
    tinterfere "simple_seq" "print(5); 6" [];
    tinterfere "let_in_seq" "let x = 1 in x; let y = 2 in y" [];
    tinterfere "let_over_seq" "let z = 3 in (let x = 1 in x; let y = 2 in y)" [];
    tinterfere "let_over_seq_interfere" "let z = 3 in (let x = 1 in x + z; let y = 2 in y)"
      [("x_8", ["z_4"]); ("z_4", ["x_8"])];
    tinterfere "let_over_seq_interfere_both" "let z = 3 in (let x = 1 in x + z; let y = 2 in y + z)"
      [("x_8", ["z_4"]); ("y_18", ["z_4"]); ("z_4", ["y_18"; "x_8"])] ]
;;

let remove_node =
  [ t_graph "r1"
      (remove_node
         (graph_from_assoc_list [("x", ["y"; "z"]); ("z", ["x"; "y"]); ("y", ["x"; "z"])])
         "z" )
      [("x", ["y"]); ("y", ["x"])] ]
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

let oom =
  [ tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
    tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
    tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation" ]
;;

let gc =
  [ tgc "gc_lam1" (10 + builtins_size)
      "let f = (lambda: (1, 2)) in\n\
      \       begin\n\
      \         f();\n\
      \         f();\n\
      \         f();\n\
      \         f()\n\
      \       end" "" "(1, 2)" ]
;;

let input = [t "input1" "let x = input() in x + 2" "123" "125"]

let suite = "unit_tests" >::: remove_node

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
