open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Graph
module StringSet = Set.Make (String)

type 'a name_envt = (string * 'a) list

type 'a tag_envt = (tag * 'a) list

let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env
;;

let const_true = HexConst 0xFFFFFFFFFFFFFFFFL

let const_false = HexConst 0x7FFFFFFFFFFFFFFFL

let bool_mask = HexConst 0x8000000000000000L

let bool_tag = 0x0000000000000007L

let bool_tag_mask = 0x0000000000000007L

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let closure_tag = 0x0000000000000005L

let closure_tag_mask = 0x0000000000000007L

let tuple_tag = 0x0000000000000001L

let tuple_tag_mask = 0x0000000000000007L

let const_nil = HexConst tuple_tag

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let err_GET_NOT_TUPLE = 6L

let err_GET_LOW_INDEX = 7L

let err_GET_HIGH_INDEX = 8L

let err_NIL_DEREF = 9L

let err_OUT_OF_MEMORY = 10L

let err_SET_NOT_TUPLE = 11L

let err_SET_LOW_INDEX = 12L

let err_SET_HIGH_INDEX = 13L

let err_CALL_NOT_CLOSURE = 14L

let err_CALL_ARITY_ERR = 15L

let err_GET_NOT_NUM = 16L

let err_SET_NOT_NUM = 17L

let err_TUPLE_DESTRUCTURE_MISMATCH = 18L

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let caller_saved_regs : arg list = [Reg RDI; Reg RSI; Reg RDX; Reg RCX; Reg R8; Reg R9; Reg R10]

let callee_saved_regs : arg list = [Reg R12; Reg R14; Reg RBX]

let heap_reg = R15

let scratch_reg = R11

(* you can add any functions or data defined by the runtime here for future use *)
let initial_val_env = []

let prim_bindings = []

let native_fun_bindings = [("equal", 2); ("input", 0)]

let initial_fun_env =
  prim_bindings @ [("equal", (dummy_span, Some 2, Some 2)); ("input", (dummy_span, Some 0, Some 0))]
;;

(* You may find some of these helpers useful *)

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" (ExtLib.dump x)))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

let rec find_with_tag ls t x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found in tag env %d" x t))
  | (tag, named_env) :: rest ->
      if tag = t then
        try find named_env x with InternalCompilerError _ -> find_with_tag [] t x
      else
        find_with_tag rest t x
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq (e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet (_, bind, body, _) -> 1 + max (helpC bind) (helpA body)
    | ALetRec (binds, body, _) ->
        List.length binds
        + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in
  helpA e
;;

let rec replicate x i =
  if i = 0 then
    []
  else
    x :: replicate x (i - 1)
;;

let align_size (n : int) = n + (n mod (word_size * 2))

let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
  | [] -> None
  | (DFun (fname, _, _, _) as d) :: ds_rest ->
      if name = fname then
        Some d
      else
        find_decl ds_rest name
;;

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt
;;

let rec find_dup (l : 'a list) : 'a option =
  match l with
  | [] -> None
  | [x] -> None
  | x :: xs ->
      if find_one xs x then
        Some x
      else
        find_dup xs
;;

let rec find_opt (env : 'a name_envt) (elt : string) : 'a option =
  match env with
  | [] -> None
  | (x, v) :: rst ->
      if x = elt then
        Some v
      else
        find_opt rst elt
;;

(* Prepends a list-like env onto an name_envt *)
let merge_envs list_env1 list_env2 = list_env1 @ list_env2

(* Combines two name_envts into one, preferring the first one *)
let prepend env1 env2 =
  let rec help env1 env2 =
    match env1 with
    | [] -> env2
    | ((k, _) as fst) :: rst ->
        let rst_prepend = help rst env2 in
        if List.mem_assoc k env2 then
          rst_prepend
        else
          fst :: rst_prepend
  in
  help env1 env2
;;

let env_keys e = List.map fst e

(* Scope_info stores the location where something was defined,
   and if it was a function declaration, then its type arity and argument arity *)
type scope_info = sourcespan * int option * int option

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  let rec wf_E e (env : scope_info name_envt) =
    debug_printf "In wf_E: %s\n" (ExtString.String.join ", " (env_keys env));
    match e with
    | ESeq (e1, e2, _) -> wf_E e1 env @ wf_E e2 env
    | ETuple (es, _) -> List.concat (List.map (fun e -> wf_E e env) es)
    | EGetItem (e, idx, pos) -> wf_E e env @ wf_E idx env
    | ESetItem (e, idx, newval, pos) -> wf_E e env @ wf_E idx env @ wf_E newval env
    | ENil _ -> []
    | EBool _ -> []
    | ENumber (n, loc) ->
        if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
          [Overflow (n, loc)]
        else
          []
    | EId (x, loc) ->
        if find_one (List.map fst env) x then
          []
        else
          [UnboundId (x, loc)]
    | EPrim1 (_, e, _) -> wf_E e env
    | EPrim2 (_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf (c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ELet (bindings, body, _) ->
        let rec find_locs x (binds : 'a bind list) : 'a list =
          match binds with
          | [] -> []
          | BBlank _ :: rest -> find_locs x rest
          | BName (y, _, loc) :: rest ->
              if x = y then
                loc :: find_locs x rest
              else
                find_locs x rest
          | BTuple (binds, _) :: rest -> find_locs x binds @ find_locs x rest
        in
        let rec find_dupes (binds : 'a bind list) : exn list =
          match binds with
          | [] -> []
          | BBlank _ :: rest -> find_dupes rest
          | BName (x, _, def) :: rest ->
              List.map (fun use -> DuplicateId (x, use, def)) (find_locs x rest) @ find_dupes rest
          | BTuple (binds, _) :: rest -> find_dupes (binds @ rest)
        in
        let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) bindings) in
        let rec process_binds (rem_binds : 'a bind list) (env : scope_info name_envt) =
          match rem_binds with
          | [] -> (env, [])
          | BBlank _ :: rest -> process_binds rest env
          | BTuple (binds, _) :: rest -> process_binds (binds @ rest) env
          | BName (x, allow_shadow, xloc) :: rest ->
              let shadow =
                if allow_shadow then
                  []
                else
                  match find_opt env x with
                  | None -> []
                  | Some (existing, _, _) -> [ShadowId (x, xloc, existing)]
              in
              let new_env = (x, (xloc, None, None)) :: env in
              let newer_env, errs = process_binds rest new_env in
              (newer_env, shadow @ errs)
        in
        let rec process_bindings bindings (env : scope_info name_envt) =
          match bindings with
          | [] -> (env, [])
          | (b, e, loc) :: rest ->
              let errs_e = wf_E e env in
              let env', errs = process_binds [b] env in
              let env'', errs' = process_bindings rest env' in
              (env'', errs @ errs_e @ errs')
        in
        let env2, errs = process_bindings bindings env in
        dupeIds @ errs @ wf_E body env2
    | EApp (func, args, native, loc) ->
        let rec_errors = List.concat (List.map (fun e -> wf_E e env) (func :: args)) in
        ( match func with
        | EId (funname, _) -> (
          match find_opt env funname with
          | Some (_, _, Some arg_arity) ->
              let actual = List.length args in
              if actual != arg_arity then
                [Arity (arg_arity, actual, loc)]
              else
                []
          | _ -> [] )
        | _ -> [] )
        @ rec_errors
    | ELetRec (binds, body, _) ->
        let nonfuns =
          List.find_all
            (fun b ->
              match b with
              | BName _, ELambda _, _ -> false
              | _ -> true )
            binds
        in
        let nonfun_errs = List.map (fun (b, _, where) -> LetRecNonFunction (b, where)) nonfuns in
        let rec find_locs x (binds : 'a bind list) : 'a list =
          match binds with
          | [] -> []
          | BBlank _ :: rest -> find_locs x rest
          | BName (y, _, loc) :: rest ->
              if x = y then
                loc :: find_locs x rest
              else
                find_locs x rest
          | BTuple (binds, _) :: rest -> find_locs x binds @ find_locs x rest
        in
        let rec find_dupes (binds : 'a bind list) : exn list =
          match binds with
          | [] -> []
          | BBlank _ :: rest -> find_dupes rest
          | BName (x, _, def) :: rest ->
              List.map (fun use -> DuplicateId (x, use, def)) (find_locs x rest)
          | BTuple (binds, _) :: rest -> find_dupes (binds @ rest)
        in
        let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) binds) in
        let rec process_binds (rem_binds : sourcespan bind list) (env : scope_info name_envt) =
          match rem_binds with
          | [] -> (env, [])
          | BBlank _ :: rest -> process_binds rest env
          | BTuple (binds, _) :: rest -> process_binds (binds @ rest) env
          | BName (x, allow_shadow, xloc) :: rest ->
              let shadow =
                if allow_shadow then
                  []
                else
                  match find_opt env x with
                  | None -> []
                  | Some (existing, _, _) ->
                      if xloc = existing then
                        []
                      else
                        [ShadowId (x, xloc, existing)]
              in
              let new_env = (x, (xloc, None, None)) :: env in
              let newer_env, errs = process_binds rest new_env in
              (newer_env, shadow @ errs)
        in
        let env, bind_errs = process_binds (List.map (fun (b, _, _) -> b) binds) env in
        let rec process_bindings bindings env =
          match bindings with
          | [] -> (env, [])
          | (b, e, loc) :: rest ->
              let env, errs = process_binds [b] env in
              let errs_e = wf_E e env in
              let env', errs' = process_bindings rest env in
              (env', errs @ errs_e @ errs')
        in
        let new_env, binding_errs = process_bindings binds env in
        let rhs_problems = List.map (fun (_, rhs, _) -> wf_E rhs new_env) binds in
        let body_problems = wf_E body new_env in
        nonfun_errs @ dupeIds @ bind_errs @ binding_errs @ List.flatten rhs_problems @ body_problems
    | ELambda (binds, body, _) ->
        let rec dupe x args =
          match args with
          | [] -> None
          | BName (y, _, loc) :: _ when x = y -> Some loc
          | BTuple (binds, _) :: rest -> dupe x (binds @ rest)
          | _ :: rest -> dupe x rest
        in
        let rec process_args rem_args =
          match rem_args with
          | [] -> []
          | BBlank _ :: rest -> process_args rest
          | BName (x, _, loc) :: rest ->
              ( match dupe x rest with
              | None -> []
              | Some where -> [DuplicateId (x, where, loc)] )
              @ process_args rest
          | BTuple (binds, loc) :: rest -> process_args (binds @ rest)
        in
        let rec flatten_bind (bind : sourcespan bind) : (string * scope_info) list =
          match bind with
          | BBlank _ -> []
          | BName (x, _, xloc) -> [(x, (xloc, None, None))]
          | BTuple (args, _) -> List.concat (List.map flatten_bind args)
        in
        process_args binds @ wf_E body (merge_envs (List.concat (List.map flatten_bind binds)) env)
  and wf_D d (env : scope_info name_envt) (tyenv : StringSet.t) =
    match d with
    | DFun (_, args, body, _) ->
        let rec dupe x args =
          match args with
          | [] -> None
          | BName (y, _, loc) :: _ when x = y -> Some loc
          | BTuple (binds, _) :: rest -> dupe x (binds @ rest)
          | _ :: rest -> dupe x rest
        in
        let rec process_args rem_args =
          match rem_args with
          | [] -> []
          | BBlank _ :: rest -> process_args rest
          | BName (x, _, loc) :: rest ->
              ( match dupe x rest with
              | None -> []
              | Some where -> [DuplicateId (x, where, loc)] )
              @ process_args rest
          | BTuple (binds, loc) :: rest -> process_args (binds @ rest)
        in
        let rec arg_env args (env : scope_info name_envt) =
          match args with
          | [] -> env
          | BBlank _ :: rest -> arg_env rest env
          | BName (name, _, loc) :: rest -> (name, (loc, None, None)) :: arg_env rest env
          | BTuple (binds, _) :: rest -> arg_env (binds @ rest) env
        in
        process_args args @ wf_E body (arg_env args env)
  and wf_G (g : sourcespan decl list) (env : scope_info name_envt) (tyenv : StringSet.t) =
    let add_funbind (env : scope_info name_envt) d =
      match d with
      | DFun (name, args, _, loc) ->
          (name, (loc, Some (List.length args), Some (List.length args))) :: env
    in
    let env = List.fold_left add_funbind env g in
    let errs = List.concat (List.map (fun d -> wf_D d env tyenv) g) in
    (errs, env)
  in
  match p with
  | Program (decls, body, _) -> (
      let initial_env = initial_val_env in
      let initial_env =
        List.fold_left
          (fun env (name, (_, arg_count)) ->
            (name, (dummy_span, Some arg_count, Some arg_count)) :: env )
          initial_fun_env initial_env
      in
      let rec find name (decls : 'a decl list) =
        match decls with
        | [] -> None
        | DFun (n, args, _, loc) :: rest when n = name -> Some loc
        | _ :: rest -> find name rest
      in
      let rec dupe_funbinds decls =
        match decls with
        | [] -> []
        | DFun (name, args, _, loc) :: rest ->
            ( match find name rest with
            | None -> []
            | Some where -> [DuplicateFun (name, where, loc)] )
            @ dupe_funbinds rest
      in
      let all_decls = List.flatten decls in
      let initial_tyenv = StringSet.of_list ["Int"; "Bool"] in
      let help_G (env, exns) g =
        let g_exns, funbinds = wf_G g env initial_tyenv in
        (List.fold_left (fun xs x -> x :: xs) env funbinds, exns @ g_exns)
      in
      let env, exns = List.fold_left help_G (initial_env, dupe_funbinds all_decls) decls in
      debug_printf "In wf_P: %s\n" (ExtString.String.join ", " (env_keys env));
      let exns = exns @ wf_E body env in
      match exns with
      | [] -> Ok p
      | _ -> Error exns )
;;

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in
  let rec helpP (p : sourcespan program) =
    match p with
    | Program (decls, body, tag) ->
        (* This particular desugaring will convert declgroups into ELetRecs *)
        let merge_sourcespans ((s1, _) : sourcespan) ((_, s2) : sourcespan) : sourcespan =
          (s1, s2)
        in
        let wrap_G g body =
          match g with
          | [] -> body
          | f :: r ->
              let span = List.fold_left merge_sourcespans (get_tag_D f) (List.map get_tag_D r) in
              ELetRec (helpG g, body, span)
        in
        Program ([], List.fold_right wrap_G decls (helpE body), tag)
  and helpG g = List.map helpD g
  and helpD d =
    match d with
    | DFun (name, args, body, tag) ->
        let helpArg a =
          match a with
          | BTuple (_, tag) ->
              let name = gensym "argtup" in
              let newbind = BName (name, false, tag) in
              (newbind, [(a, EId (name, tag), tag)])
          | _ -> (a, [])
        in
        let newargs, argbinds = List.split (List.map helpArg args) in
        let newbody = ELet (List.flatten argbinds, body, tag) in
        (BName (name, false, tag), ELambda (newargs, helpE newbody, tag), tag)
  and helpBE bind =
    let b, e, btag = bind in
    let e = helpE e in
    match b with
    | BTuple (binds, ttag) -> (
      match e with
      | EId _ -> expandTuple binds ttag e
      | _ ->
          let newname = gensym "tup" in
          (BName (newname, false, ttag), e, btag) :: expandTuple binds ttag (EId (newname, ttag)) )
    | _ -> [(b, e, btag)]
  and expandTuple binds tag source : sourcespan binding list =
    let tupleBind i b =
      match b with
      | BBlank btag -> []
      | BName (_, _, btag) ->
          [(b, EGetItem (source, ENumber (Int64.of_int i, dummy_span), tag), btag)]
      | BTuple (binds, tag) ->
          let newname = gensym "tup" in
          let newexpr = EId (newname, tag) in
          ( BName (newname, false, tag),
            EGetItem (source, ENumber (Int64.of_int i, dummy_span), tag),
            tag )
          :: expandTuple binds tag newexpr
    in
    let size_check =
      EPrim2 (CheckSize, source, ENumber (Int64.of_int (List.length binds), dummy_span), dummy_span)
    in
    let size_check_bind = (BBlank dummy_span, size_check, dummy_span) in
    size_check_bind :: List.flatten (List.mapi tupleBind binds)
  and helpE e =
    match e with
    | ESeq (e1, e2, tag) -> ELet ([(BBlank tag, helpE e1, tag)], helpE e2, tag)
    | ETuple (exprs, tag) -> ETuple (List.map helpE exprs, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE e, helpE idx, tag)
    | ESetItem (e, idx, newval, tag) -> ESetItem (helpE e, helpE idx, helpE newval, tag)
    | EId (x, tag) -> EId (x, tag)
    | ENumber (n, tag) -> ENumber (n, tag)
    | EBool (b, tag) -> EBool (b, tag)
    | ENil (t, tag) -> ENil (t, tag)
    | EPrim1 (op, e, tag) -> EPrim1 (op, helpE e, tag)
    | EPrim2 (op, e1, e2, tag) -> EPrim2 (op, helpE e1, helpE e2, tag)
    | ELet (binds, body, tag) ->
        let newbinds = List.map helpBE binds in
        List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
    | ELetRec (bindexps, body, tag) ->
        (* ASSUMES well-formed letrec, so only BName bindings *)
        let newbinds = List.map (fun (bind, e, tag) -> (bind, helpE e, tag)) bindexps in
        ELetRec (newbinds, helpE body, tag)
    | EIf (cond, thn, els, tag) -> EIf (helpE cond, helpE thn, helpE els, tag)
    | EApp (name, args, native, tag) -> EApp (helpE name, List.map helpE args, native, tag)
    | ELambda (binds, body, tag) ->
        let expandBind bind =
          match bind with
          | BTuple (_, btag) ->
              let newparam = gensym "tuparg" in
              (BName (newparam, false, btag), helpBE (bind, EId (newparam, btag), btag))
          | _ -> (bind, [])
        in
        let params, newbinds = List.split (List.map expandBind binds) in
        let newbody =
          List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
        in
        ELambda (params, newbody, tag)
  in
  helpP p
;;

(* ASSUMES desugaring is complete *)
let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program (decls, body, tag) ->
        Program (List.map (fun group -> List.map (helpD env) group) decls, helpE env body, tag)
  and helpD env decl =
    match decl with
    | DFun (name, args, body, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, newArgs, helpE env' body, tag)
  and helpB env b =
    match b with
    | BBlank tag -> (b, env)
    | BName (name, allow_shadow, tag) ->
        let name' = sprintf "%s_%d" name tag in
        (BName (name', allow_shadow, tag), (name, name') :: env)
    | BTuple (binds, tag) ->
        let binds', env' = helpBS env binds in
        (BTuple (binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b :: bs ->
        let b', env' = helpB env b in
        let bs', env'' = helpBS env' bs in
        (b' :: bs', env'')
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE env e in
        let bindings', env'' = helpBG env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE env e1, helpE env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE env) es, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE env e, helpE env idx, tag)
    | ESetItem (e, idx, newval, tag) -> ESetItem (helpE env e, helpE env idx, helpE env newval, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE env arg, tag)
    | EPrim2 (op, left, right, tag) -> EPrim2 (op, helpE env left, helpE env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with InternalCompilerError _ -> e )
    | EApp (func, args, native, tag) ->
        let func = helpE env func in
        let call_type =
          (* TODO: If you want, try to determine whether func is a known function name, and if so,
             whether it's a Snake function or a Native function *)
          Snake
        in
        EApp (func, List.map (helpE env) args, call_type, tag)
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG env binds in
        let body' = helpE env' body in
        ELet (binds', body', tag)
    | ELetRec (bindings, body, tag) ->
        let revbinds, env =
          List.fold_left
            (fun (revbinds, env) (b, e, t) ->
              let b, env = helpB env b in
              ((b, e, t) :: revbinds, env) )
            ([], env) bindings
        in
        let bindings' =
          List.fold_left (fun bindings (b, e, tag) -> (b, helpE env e, tag) :: bindings) [] revbinds
        in
        let body' = helpE env body in
        ELetRec (bindings', body', tag)
    | ELambda (binds, body, tag) ->
        let binds', env' = helpBS env binds in
        let body' = helpE env' body in
        ELambda (binds', body', tag)
  in
  rename [] p
;;

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;; ANFING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program ([], body, _) -> AProgram (helpA body, ())
    | Program _ -> raise (InternalCompilerError "decls should have been desugared away")
  and helpC (e : tag expr) : unit cexpr * unit anf_bind list =
    match e with
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec (binds, body, _) ->
        let processBind (bind, rhs, _) =
          match bind with
          | BName (name, _, _) -> (name, helpC rhs)
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                      (string_of_bind bind) ) )
        in
        let names, new_binds_setup = List.split (List.map processBind binds) in
        let new_binds, new_setup = List.split new_binds_setup in
        let body_ans, body_setup = helpC body in
        (body_ans, BLetRec (List.combine names new_binds) :: body_setup)
    | ELambda (args, body, _) ->
        let processBind bind =
          match bind with
          | BName (name, _, _) -> name
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                      (string_of_bind bind) ) )
        in
        (CLambda (List.map processBind args, helpA body, ()), [])
    | ELet ((BTuple (binds, _), exp, _) :: rest, body, pos) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
    | EApp (func, args, native, _) ->
        let func_ans, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (func_ans, new_args, native, ()), func_setup @ List.concat new_setup)
    | ESeq (e1, e2, _) ->
        let e1_ans, e1_setup = helpC e1 in
        let e2_ans, e2_setup = helpC e2 in
        (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)
    | ETuple (args, _) ->
        let new_args, new_setup = List.split (List.map helpI args) in
        (CTuple (new_args, ()), List.concat new_setup)
    | EGetItem (tup, idx, _) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        (CGetItem (tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem (tup, idx, newval, _) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let new_imm, new_setup = helpI newval in
        (CSetItem (tup_imm, idx_imm, new_imm, ()), tup_setup @ idx_setup @ new_setup)
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : unit immexpr * unit anf_bind list =
    match e with
    | ENumber (n, _) -> (ImmNum (n, ()), [])
    | EBool (b, _) -> (ImmBool (b, ()), [])
    | EId (name, _) -> (ImmId (name, ()), [])
    | ENil _ -> (ImmNil (), [])
    | ESeq (e1, e2, _) ->
        let e1_imm, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (e2_imm, e1_setup @ e2_setup)
    | ETuple (args, tag) ->
        let tmp = sprintf "tup_%d" tag in
        let new_args, new_setup = List.split (List.map helpI args) in
        (ImmId (tmp, ()), List.concat new_setup @ [BLet (tmp, CTuple (new_args, ()))])
    | EGetItem (tup, idx, tag) ->
        let tmp = sprintf "get_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        (ImmId (tmp, ()), tup_setup @ idx_setup @ [BLet (tmp, CGetItem (tup_imm, idx_imm, ()))])
    | ESetItem (tup, idx, newval, tag) ->
        let tmp = sprintf "set_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let new_imm, new_setup = helpI newval in
        ( ImmId (tmp, ()),
          tup_setup @ idx_setup @ new_setup @ [BLet (tmp, CSetItem (tup_imm, idx_imm, new_imm, ()))]
        )
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, ()), arg_setup @ [BLet (tmp, CPrim1 (op, arg_imm, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, ()),
          left_setup @ right_setup @ [BLet (tmp, CPrim2 (op, left_imm, right_imm, ()))] )
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (ImmId (tmp, ()), cond_setup @ [BLet (tmp, CIf (cond_imm, helpA _then, helpA _else, ()))])
    | EApp (func, args, native, tag) ->
        let tmp = sprintf "app_%d" tag in
        let new_func, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        ( ImmId (tmp, ()),
          func_setup @ List.concat new_setup @ [BLet (tmp, CApp (new_func, new_args, native, ()))]
        )
    | ELet ([], body, _) -> helpI body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELetRec (binds, body, tag) ->
        let tmp = sprintf "lam_%d" tag in
        let processBind (bind, rhs, _) =
          match bind with
          | BName (name, _, _) -> (name, helpC rhs)
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                      (string_of_bind bind) ) )
        in
        let names, new_binds_setup = List.split (List.map processBind binds) in
        let new_binds, new_setup = List.split new_binds_setup in
        let body_ans, body_setup = helpC body in
        ( ImmId (tmp, ()),
          List.concat new_setup
          @ [BLetRec (List.combine names new_binds)]
          @ body_setup
          @ [BLet (tmp, body_ans)] )
    | ELambda (args, body, tag) ->
        let tmp = sprintf "lam_%d" tag in
        let processBind bind =
          match bind with
          | BName (name, _, _) -> name
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                      (string_of_bind bind) ) )
        in
        (ImmId (tmp, ()), [BLet (tmp, CLambda (List.map processBind args, helpA body, ()))])
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((BTuple (binds, _), exp, _) :: rest, body, pos) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq exp -> ASeq (exp, body, ())
        | BLet (name, exp) -> ALet (name, exp, body, ())
        | BLetRec names -> ALetRec (names, body, ()) )
      ans_setup (ACExpr ans)
  in
  helpP p
;;

let free_vars (e : 'a aexpr) : StringSet.t =
  let rec free_vars_C (e : 'a cexpr) (bound : StringSet.t) : StringSet.t =
    let free_vars_I_list (es : 'a immexpr list) (bound : StringSet.t) : StringSet.t =
      List.fold_left
        (fun free curr -> StringSet.union free (free_vars_I curr bound))
        StringSet.empty es
    in
    match e with
    | CIf (c, t, e, _) ->
        let c_free = free_vars_I c bound in
        let t_free = free_vars_A t bound in
        let e_free = free_vars_A e bound in
        StringSet.union (StringSet.union c_free t_free) e_free
    | CPrim1 (_, op, _) -> free_vars_I op bound
    | CPrim2 (_, op1, op2, _) ->
        let op1_free = free_vars_I op1 bound in
        let op2_free = free_vars_I op2 bound in
        StringSet.union op1_free op2_free
    | CApp (_, args, Native, _) -> free_vars_I_list args bound
    | CApp (func, args, _, _) ->
        let func_free = free_vars_I func bound in
        let args_free = free_vars_I_list args bound in
        StringSet.union func_free args_free
    | CTuple (els, _) -> free_vars_I_list els bound
    | CGetItem (tup, idx, _) ->
        let tup_free = free_vars_I tup bound in
        let idx_free = free_vars_I idx bound in
        StringSet.union tup_free idx_free
    | CSetItem (tup, idx, new_val, _) ->
        let tup_free = free_vars_I tup bound in
        let idx_free = free_vars_I idx bound in
        let new_val_free = free_vars_I new_val bound in
        StringSet.union (StringSet.union tup_free idx_free) new_val_free
    | CLambda (args, body, _) -> free_vars_A body (StringSet.union (StringSet.of_list args) bound)
    | CImmExpr i -> free_vars_I i bound
  and free_vars_I (e : 'a immexpr) (bound : StringSet.t) : StringSet.t =
    match e with
    | ImmNum _ | ImmBool _ | ImmNil _ -> StringSet.empty
    | ImmId (id, _) -> (
      match StringSet.find_opt id bound with
      | Some _ -> StringSet.empty
      | None -> StringSet.singleton id )
  and free_vars_A (e : 'a aexpr) (bound : StringSet.t) : StringSet.t =
    let free_vars_C_list (es : 'a cexpr list) (bound : StringSet.t) : StringSet.t =
      List.fold_left
        (fun free curr -> StringSet.union free (free_vars_C curr bound))
        StringSet.empty es
    in
    match e with
    | ASeq (f, s, _) ->
        let f_free = free_vars_C f bound in
        let s_free = free_vars_A s bound in
        StringSet.union f_free s_free
    | ALet (name, value, body, _) ->
        let value_free = free_vars_C value bound in
        let body_free = free_vars_A body (StringSet.add name bound) in
        StringSet.union value_free body_free
    | ALetRec (binds, body, _) ->
        let names, values = List.split binds in
        let new_bound = StringSet.union (StringSet.of_list names) bound in
        let values_free = free_vars_C_list values new_bound in
        let body_free = free_vars_A body new_bound in
        StringSet.union values_free body_free
    | ACExpr c -> free_vars_C c bound
  in
  free_vars_A e StringSet.empty
;;

let get_fv_info (e : 'a aexpr) : StringSet.t =
  match e with
  | ASeq (_, _, (fvs, _)) | ALet (_, _, _, (fvs, _)) | ALetRec (_, _, (fvs, _)) -> fvs
  | ACExpr c -> (
    match c with
    | CIf (_, _, _, (fvs, _))
     |CLambda (_, _, (fvs, _))
     |CPrim1 (_, _, (fvs, _))
     |CPrim2 (_, _, _, (fvs, _))
     |CApp (_, _, _, (fvs, _))
     |CTuple (_, (fvs, _))
     |CGetItem (_, _, (fvs, _))
     |CSetItem (_, _, _, (fvs, _)) -> fvs
    | CImmExpr i -> (
      match i with
      | ImmBool (_, (fvs, _)) | ImmNil (fvs, _) | ImmNum (_, (fvs, _)) | ImmId (_, (fvs, _)) -> fvs
      ) )
;;

let rec free_vars_cache (prog : 'a aprogram) : (StringSet.t * 'a) aprogram =
  let rec free_vars_C (e : 'a cexpr) : (StringSet.t * 'a) cexpr =
    match e with
    | CIf (c, t, e, tag) ->
        let c_free = free_vars_I c in
        let t_free = free_vars_A t in
        let e_free = free_vars_A e in
        CIf (c_free, t_free, e_free, (free_vars e, tag))
    | CPrim1 (p, op, tag) -> CPrim1 (p, free_vars_I op, (free_vars (ACExpr e), tag))
    | CPrim2 (p, op1, op2, tag) ->
        let op1_free = free_vars_I op1 in
        let op2_free = free_vars_I op2 in
        CPrim2 (p, op1_free, op2_free, (free_vars (ACExpr e), tag))
    | CApp (f, args, Native, tag) ->
        CApp (free_vars_I f, List.map free_vars_I args, Native, (free_vars (ACExpr e), tag))
    | CApp (func, args, ct, tag) ->
        let func_free = free_vars_I func in
        let args_free = List.map free_vars_I args in
        CApp (func_free, args_free, ct, (free_vars (ACExpr e), tag))
    | CTuple (els, tag) -> CTuple (List.map free_vars_I els, (free_vars (ACExpr e), tag))
    | CGetItem (tup, idx, tag) ->
        let tup_free = free_vars_I tup in
        let idx_free = free_vars_I idx in
        CGetItem (tup_free, idx_free, (free_vars (ACExpr e), tag))
    | CSetItem (tup, idx, new_val, tag) ->
        let tup_free = free_vars_I tup in
        let idx_free = free_vars_I idx in
        let new_val_free = free_vars_I new_val in
        CSetItem (tup_free, idx_free, new_val_free, (free_vars (ACExpr e), tag))
    | CLambda (args, body, tag) -> CLambda (args, free_vars_A body, (free_vars (ACExpr e), tag))
    | CImmExpr i -> CImmExpr (free_vars_I i)
  and free_vars_I (e : 'a immexpr) : (StringSet.t * 'a) immexpr =
    match e with
    | ImmNum (n, tag) -> ImmNum (n, (free_vars (ACExpr (CImmExpr e)), tag))
    | ImmBool (b, tag) -> ImmBool (b, (free_vars (ACExpr (CImmExpr e)), tag))
    | ImmNil tag -> ImmNil (free_vars (ACExpr (CImmExpr e)), tag)
    | ImmId (id, tag) -> ImmId (id, (free_vars (ACExpr (CImmExpr e)), tag))
  and free_vars_A (e : 'a aexpr) : (StringSet.t * 'a) aexpr =
    match e with
    | ASeq (f, s, tag) ->
        let f_free = free_vars_C f in
        let s_free = free_vars_A s in
        ASeq (f_free, s_free, (free_vars e, tag))
    | ALet (name, value, body, tag) ->
        let value_free = free_vars_C value in
        let body_free = free_vars_A body in
        ALet (name, value_free, body_free, (free_vars e, tag))
    | ALetRec (binds, body, tag) ->
        let names, values = List.split binds in
        let values_free = List.map free_vars_C values in
        let body_free = free_vars_A body in
        ALetRec (List.combine names values_free, body_free, (free_vars e, tag))
    | ACExpr c -> ACExpr (free_vars_C c)
  in
  match prog with
  | AProgram (body, tag) -> AProgram (free_vars_A body, (free_vars body, tag))
;;

(* We decided to use a tag environment for the outer environment so that we don't have to
   change our implementation of ANF. Also, we think it's unlikely that we will want to
   insert any steps between allocation and compilation.*)
let naive_stack_allocation (prog : (StringSet.t * tag) aprogram) :
    (StringSet.t * tag) aprogram * arg name_envt tag_envt =
  let allocate_name name si = (name, RegOffset (~-si * word_size, RBP)) in
  let rec allocate_A (e : (StringSet.t * tag) aexpr) (si : int) (lambda_tag : tag) :
      arg name_envt tag_envt * int =
    match e with
    | ALet (name, value, body, _) ->
        let name_bind = (lambda_tag, [allocate_name name si]) in
        let value_env, value_si = allocate_C value (si + 1) lambda_tag in
        let body_env, body_si = allocate_A body (si + 1) lambda_tag in
        ((name_bind :: value_env) @ body_env, max value_si body_si)
    | ASeq (f, s, _) ->
        let f_env, f_si = allocate_C f si lambda_tag in
        let s_env, s_si = allocate_A s si lambda_tag in
        (f_env @ s_env, max f_si s_si)
    | ALetRec (binds, body, _) ->
        let binds_env, binds_si =
          List.fold_left
            (fun (prev_env, prev_si) (name, value) ->
              let name_bind = (lambda_tag, [allocate_name name prev_si]) in
              let value_env, _ = allocate_C value (prev_si + 1) lambda_tag in
              ((name_bind :: value_env) @ prev_env, prev_si + 1) )
            ([], si) binds
        in
        let body_env, body_si = allocate_A body binds_si lambda_tag in
        (binds_env @ body_env, body_si)
    | ACExpr c -> allocate_C c si lambda_tag
  and allocate_C (e : (StringSet.t * tag) cexpr) (si : int) (lambda_tag : tag) :
      arg name_envt tag_envt * int =
    match e with
    | CIf (_, t, e, _) ->
        let then_env, then_si = allocate_A t si lambda_tag in
        (* TODO come back and optimize this *)
        let else_env, else_si = allocate_A e then_si lambda_tag in
        (then_env @ else_env, max then_si else_si)
    | CLambda (args, body, (fvs, tag)) ->
        let args_env = List.mapi (fun i a -> allocate_name a ~-(i + 3)) args in
        let free = List.sort compare (StringSet.elements fvs) in
        let free_env, free_si =
          List.fold_left
            (fun (prev_env, i) fv ->
              let current = allocate_name fv i in
              (current :: prev_env, i + 1) )
            ([], 1) free
        in
        let body_env, body_si = allocate_A body free_si tag in
        ((tag, args_env @ free_env) :: body_env, body_si)
    | _ -> ([], si)
  in
  let rec group_tags (env : arg name_envt tag_envt) : arg name_envt tag_envt =
    match env with
    | [] -> []
    | [x] -> [x]
    | (tag1, inner_env1) :: (tag2, inner_env2) :: rest when tag1 = tag2 ->
        group_tags ((tag1, inner_env1 @ inner_env2) :: rest)
    | mapping :: rest -> mapping :: group_tags rest
  in
  match prog with
  | AProgram (body, (_, tag)) ->
      let body_env, _ = allocate_A body 1 tag in
      let sorted_body_env =
        List.sort (fun (tag1, _) (tag2, _) -> compare tag1 tag2) ((tag, []) :: body_env)
      in
      (prog, group_tags sorted_body_env)
;;

let rec interfere (e : (StringSet.t * tag) aexpr) (live : StringSet.t) : grapht =
  let rec help_C (c_e : (StringSet.t * tag) cexpr) : grapht =
    match c_e with
    | CIf (c, t, e, (fvs, _)) -> merge_two (interfere t live) (interfere e live)
    | CLambda _ -> raise (NotYetImplemented "TODO")
    | _ -> Graph.empty
  in
  match e with
  | ASeq (f, s, (fvs, _)) -> merge_two (help_C f) (interfere s live)
  | ALet (name, bound, body, (fvs, _)) ->
      let body_free = StringSet.elements (get_fv_info body) in
      (* let bound_interfere = help_C bound in *)
      let new_graph =
        List.fold_right
          (fun fv prev_graph -> add_edge prev_graph name fv)
          body_free
          (* every bound name should be added as a node so a register is given to it *)
          (Graph.singleton name StringSet.empty)
      in
      merge_two new_graph (interfere body (StringSet.add name live))
  | ALetRec (binds, body, (fvs, _)) -> raise (NotYetImplemented "TODO")
  | ACExpr c_e -> help_C c_e
;;

let min_unused_reg (used : arg list) : arg =
  (* TODO make sure to push and pop native call regs if needed *)
  (* NOTE: excluding R11 because it's our scratch_reg *)
  let reg_priority =
    List.map (fun r -> Reg r) [R10; R12; R13; R14; RBX; RSI; RDI; RCX; RDX; R8; R9]
  in
  let rec min_color_help (reg_priority : arg list) (stack_height : int) : arg =
    match reg_priority with
    | [] ->
        let curr_height_offset = RegOffset (~-stack_height * word_size, RBP) in
        if List.mem curr_height_offset used then
          min_color_help reg_priority (stack_height + 1)
        else
          curr_height_offset
    | to_try :: rest ->
        if List.mem to_try used then
          min_color_help rest stack_height
        else
          to_try
  in
  min_color_help reg_priority 1
;;

let color_graph (g : grapht) (init_env : arg name_envt) : arg name_envt =
  let rec initialize_worklist (g : grapht) (worklist : string list) : string list =
    if Graph.is_empty g then
      worklist
    else
      let sorted_bindings =
        List.sort
          (fun (_, neighbors1) (_, neighbors2) ->
            StringSet.cardinal neighbors1 - StringSet.cardinal neighbors2 )
          (Graph.bindings g)
      in
      let smallest_binding_name, _ = List.hd sorted_bindings in
      initialize_worklist (remove_node g smallest_binding_name) (smallest_binding_name :: worklist)
  in
  let rec color_help (worklist : string list) (colored : arg name_envt) : arg name_envt =
    match worklist with
    | [] -> colored
    | node_name :: rest ->
        let currently_used_colors =
          List.concat_map
            (fun neighbor ->
              match find_opt colored neighbor with
              | None -> []
              | Some arg -> [arg] )
            (get_neighbors g node_name)
        in
        let reg_to_use = min_unused_reg currently_used_colors in
        color_help rest ((node_name, reg_to_use) :: colored)
  in
  color_help (initialize_worklist g []) init_env
;;

let register_allocation (prog : (StringSet.t * tag) aprogram) :
    (StringSet.t * tag) aprogram * arg name_envt tag_envt =
  let rec allocate_A (e : (StringSet.t * tag) aexpr) (in_use : arg list) : arg name_envt tag_envt =
    match e with
    | ALet (name, value, body, _) ->
        let value_env = allocate_C value in_use in
        let body_env = allocate_A body in_use in
        value_env @ body_env
    | ASeq (f, s, _) ->
        let f_env = allocate_C f in_use in
        let s_env = allocate_A s in_use in
        f_env @ s_env
    | ALetRec (binds, body, _) ->
        raise (NotYetImplemented "TODO")
        (* let binds_env = List.concat_map allocate_C (List.map snd binds) in
           let body_env = allocate_A body in
           binds_env @ body_env *)
    | ACExpr c -> allocate_C c in_use
  and allocate_C (e : (StringSet.t * tag) cexpr) (in_use : arg list) : arg name_envt tag_envt =
    match e with
    | CIf (_, t, e, _) ->
        let then_env = allocate_A t in_use in
        let else_env = allocate_A e in_use in
        then_env @ else_env
    | CLambda (args, body, (fvs, tag)) ->
        raise (NotYetImplemented "TODO")
        (* let args_env = List.mapi (fun i a -> (a, RegOffset (i + 3, RBP))) args in
           let body_env = allocate_A body in
           (* TODO fill in current live environment properly *)
           (tag, color_graph (interfere body StringSet.empty) []) :: body_env *)
    | _ -> []
  in
  match prog with
  | AProgram (body, (_, tag)) ->
      let body_env = allocate_A body [] in
      (* let sorted_body_env =
           List.sort (fun (tag1, _) (tag2, _) -> compare tag1 tag2) ((tag, []) :: body_env)
         in *)
      (* TODO maybe include natives in initial environment (in_use too?) *)
      (prog, (tag, color_graph (interfere body StringSet.empty) []) :: body_env)
;;

(* Returns the stack-index (in words) of the deepest stack index used for any
   of the variables in this expression *)
let rec deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet (name, bind, body, _) ->
        List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ALetRec (binds, body, _) ->
        List.fold_left max (helpA body) (List.map (fun (_, bind) -> helpC bind) binds)
    | ASeq (first, rest, _) -> max (helpC first) (helpA rest)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1 (_, i, _) -> helpI i
    | CPrim2 (_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp (_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple (vals, _) -> List.fold_left max 0 (List.map helpI vals)
    | CGetItem (t, _, _) -> helpI t
    | CSetItem (t, _, v, _) -> max (helpI t) (helpI v)
    | CLambda (args, body, _) ->
        let new_env = List.mapi (fun i a -> (a, RegOffset (word_size * (i + 3), RBP))) args @ env in
        deepest_stack body new_env
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNil _ -> 0
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match find env name with
    | RegOffset (bytes, RBP) -> bytes / (-1 * word_size) (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq (e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet (_, bind, body, _) -> 1 + max (helpC bind) (helpA body)
    | ALetRec (binds, body, _) ->
        List.length binds
        + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in
  helpA e
;;

let rec reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [ IInstrComment
      (IMov (Reg RAX, LabelContents "?HEAP_END"), sprintf "Reserving %d words" (size / word_size));
    ISub (Reg RAX, Const (Int64.of_int size));
    ICmp (Reg RAX, Reg heap_reg);
    IJge (Label ok) ]
  @ native_call (Label "?try_gc")
      [ Sized (QWORD_PTR, Reg heap_reg);
        (* alloc_ptr in C *)
        Sized (QWORD_PTR, Const (Int64.of_int size));
        (* bytes_needed in C *)
        Sized (QWORD_PTR, Reg RBP);
        (* first_frame in C *)
        Sized (QWORD_PTR, Reg RSP) (* stack_top in C *) ]
  @ [ IInstrComment
        ( IMov (Reg heap_reg, Reg RAX),
          "assume gc success if returning here, so RAX holds the new heap_reg value" );
      ILabel ok ]

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
(* Additionally, you are provided an initial environment of values that you may want to
   assume should take up the first few stack slots.  See the compiliation of Programs
   below for one way to use this ability... *)
and compile_fun
    (name : string)
    (args : string list)
    (body : (StringSet.t * tag) aexpr)
    (initial_env : arg name_envt tag_envt)
    (tag : tag) =
  let space = deepest_stack body (find initial_env tag) in
  let setup =
    [ILabel name; IPush (Reg RBP); IMov (Reg RBP, Reg RSP)]
    @ (* ISub (Reg RSP, Const (Int64.of_int space))  *)
    replicate (IPush (Sized (QWORD_PTR, Const 0L))) (space + 1)
  in
  let c_body = compile_aexpr body initial_env tag "no_lambda_bound!" in
  let postlude = [IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet] in
  (setup, c_body, postlude)

and compile_aexpr
    (e : (StringSet.t * tag) aexpr)
    (env : arg name_envt tag_envt)
    (lambda_tag : tag)
    (bound_lam_name : string) : instruction list =
  match e with
  | ACExpr x -> compile_cexpr x env lambda_tag bound_lam_name
  | ALet (name, value, body, _) ->
      compile_cexpr value env lambda_tag bound_lam_name
      @ [ IInstrComment
            ( IMov (find_with_tag env lambda_tag name, Reg RAX),
              sprintf "binding %s at tag %d" name lambda_tag ) ]
      @ compile_aexpr body env lambda_tag bound_lam_name
  | ASeq (frs, snd, _) ->
      let c_frs = compile_cexpr frs env lambda_tag bound_lam_name in
      let c_snd = compile_aexpr snd env lambda_tag bound_lam_name in
      c_frs @ c_snd
  | ALetRec (binds, body, (_, tag)) ->
      let compiled_closures =
        List.concat_map
          (fun (name, lam) ->
            let c_lam = compile_cexpr lam env lambda_tag name in
            (* INVARIANT: Compiling each lambda will place the result in RAX.
               Thus, we can just move the result where we want it.
            *)
            c_lam
            @ [ IInstrComment
                  ( IMov (find_with_tag env lambda_tag name, Reg RAX),
                    sprintf "saving lambda %s" name ) ] )
          binds
      in
      let compiled_body = compile_aexpr body env lambda_tag bound_lam_name in
      ILineComment
        (sprintf "Compiling let rec (tagged %d), with vars %s" tag
           (ExtString.String.join ", " (List.map fst binds)) )
      :: compiled_closures
      @ compiled_body

and compile_cexpr
    (e : (StringSet.t * tag) cexpr)
    (env : arg name_envt tag_envt)
    (lambda_tag : tag)
    (bound_lam_name : string) =
  let check_tag (imm : arg) (mask : int64) (tag : int64) (dest : string) : instruction list =
    [ IMov (Reg RAX, imm);
      IAnd (Reg RAX, HexConst mask);
      IMov (Reg scratch_reg, imm);
      ICmp (Reg RAX, Const tag);
      IJne (Label dest) ]
  in
  let check_num_tag (imm : arg) (dest : string) = check_tag imm num_tag_mask num_tag dest in
  let check_tup_tag (imm : arg) (dest : string) = check_tag imm tuple_tag_mask tuple_tag dest in
  let check_bool_tag (imm : arg) (dest : string) = check_tag imm bool_tag_mask bool_tag dest in
  let check_nil (imm : arg) =
    [ IMov (Reg RAX, imm);
      ICmp (Reg RAX, const_nil);
      IMov (Reg scratch_reg, imm);
      IJe (Label "?err_nil_deref") ]
  in
  let check_closure (imm : arg) (dest : string) = check_tag imm closure_tag_mask closure_tag dest in
  let save_and_restore_caller =
    let pushes = List.map (fun x -> IPush (Reg x)) first_six_args_registers in
    let pops = List.map (fun x -> IPop (Reg x)) (List.rev first_six_args_registers) in
    (pushes, pops)
  in
  let check_overflow = [IJo (Label "?err_overflow")] in
  match e with
  | CPrim1 (op, e, (_, tag)) -> (
      let e_reg = compile_imm e env lambda_tag in
      let predicate_prim1_instrs (label : string) (mask : int64) (tag : int64) : instruction list =
        [ (* Move answer to RAX *)
          IMov (Reg RAX, e_reg);
          (* Apply num/bool mask *)
          IAnd (Reg RAX, HexConst mask);
          (* Compare result to num/bool tag *)
          ICmp (Reg RAX, Const tag);
          (* Preload true into RAX *)
          IMov (Reg RAX, const_true);
          (* If matches the tag, jump over next instruction *)
          IJe (Label label);
          (* Set RAX to false if we reach here, meaning isnum/bool false *)
          IMov (Reg RAX, const_false);
          ILabel label ]
      in
      match op with
      | Add1 ->
          check_num_tag e_reg "?err_arith_not_num"
          @ [IMov (Reg RAX, e_reg); IAdd (Reg RAX, Const 2L)]
          @ check_overflow
      | Sub1 ->
          check_num_tag e_reg "?err_arith_not_num"
          @ [IMov (Reg RAX, e_reg); IAdd (Reg RAX, Const (-2L))]
          @ check_overflow
      | IsBool ->
          let is_bool_label = sprintf "is_bool_%d" tag in
          predicate_prim1_instrs is_bool_label bool_tag_mask bool_tag
      | IsNum ->
          let is_num_label = sprintf "is_num_%d" tag in
          predicate_prim1_instrs is_num_label num_tag_mask num_tag
      | IsTuple ->
          let is_tup_label = sprintf "is_tup_%d" tag in
          predicate_prim1_instrs is_tup_label tuple_tag_mask tuple_tag
      | Not ->
          check_bool_tag e_reg "?err_logic_not_bool"
          @ [ IMov (Reg RAX, e_reg);
              IMov (Reg scratch_reg, bool_mask);
              IXor (Reg RAX, Reg scratch_reg) ]
      | Print -> native_call (Label "?print") [e_reg]
      | PrintStack -> native_call (Label "?print_stack") [e_reg; Reg RSP; Reg RBP; Const (-1L)] )
  | CPrim2 (op, left, right, (_, tag)) -> (
      let c_left = compile_imm left env lambda_tag in
      let c_right = compile_imm right env lambda_tag in
      let predicate_prim2_instrs (label : string) (jmp_instr : instruction) : instruction list =
        check_num_tag c_left "?err_comp_not_num"
        @ check_num_tag c_right "?err_comp_not_num"
        @ [ IMov (Reg RAX, c_left);
            IMov (Reg scratch_reg, c_right);
            ICmp (Reg RAX, Reg scratch_reg);
            IMov (Reg RAX, const_true);
            jmp_instr;
            IMov (Reg RAX, const_false);
            ILabel label ]
      in
      match op with
      | Plus ->
          (* TODO maybe cleanup *)
          check_num_tag c_left "?err_arith_not_num"
          @ check_num_tag c_right "?err_arith_not_num"
          @ [ IMov (Reg RAX, c_left);
              IMov (Reg scratch_reg, c_right);
              IAdd (Reg RAX, Reg scratch_reg) ]
          @ check_overflow
      | Minus ->
          check_num_tag c_left "?err_arith_not_num"
          @ check_num_tag c_right "?err_arith_not_num"
          @ [ IMov (Reg RAX, c_left);
              IMov (Reg scratch_reg, c_right);
              ISub (Reg RAX, Reg scratch_reg) ]
          @ check_overflow
      | Times ->
          check_num_tag c_left "?err_arith_not_num"
          @ check_num_tag c_right "?err_arith_not_num"
          @ [ IMov (Reg RAX, c_left);
              ISar (Reg RAX, Const 1L);
              IMov (Reg scratch_reg, c_right);
              IMul (Reg RAX, Reg scratch_reg) ]
          @ check_overflow
      | And | Or -> raise (InternalCompilerError "And and or should've been desugared into ifs.")
      | Greater ->
          let greater_label = sprintf "greater_%d" tag in
          predicate_prim2_instrs greater_label (IJg (Label greater_label))
      | GreaterEq ->
          let greater_eq_label = sprintf "greater_eq_%d" tag in
          predicate_prim2_instrs greater_eq_label (IJge (Label greater_eq_label))
      | Less ->
          let less_label = sprintf "less_%d" tag in
          predicate_prim2_instrs less_label (IJl (Label less_label))
      | LessEq ->
          let less_eq_label = sprintf "less_eq_%d" tag in
          predicate_prim2_instrs less_eq_label (IJle (Label less_eq_label))
      | Eq ->
          let eq_label = sprintf "eq_%d" tag in
          [ IMov (Reg RAX, c_left);
            IMov (Reg scratch_reg, c_right);
            ICmp (Reg RAX, Reg scratch_reg);
            IMov (Reg RAX, const_true);
            IJe (Label eq_label);
            IMov (Reg RAX, const_false);
            ILabel eq_label ]
      | CheckSize ->
          [ IMov (Reg RAX, c_left);
            ISub (Reg RAX, Const tuple_tag);
            IMov (Reg scratch_reg, c_right);
            (* ISar (Reg scratch_reg, Const 1L); *)
            ICmp (Reg scratch_reg, RegOffset (0, RAX));
            IMov (Reg scratch_reg, c_left);
            IJne (Label "?err_tuple_destructure_mismatch");
            IAdd (Reg RAX, Const tuple_tag) ] )
  | CIf (cond, thn, els, (_, tag)) ->
      let done_label = sprintf "done_%d" tag in
      let else_label = sprintf "if_false_%d" tag in
      let c_cond = compile_imm cond env lambda_tag in
      let c_thn = compile_aexpr thn env lambda_tag bound_lam_name in
      let c_els = compile_aexpr els env lambda_tag bound_lam_name in
      check_bool_tag c_cond "?err_if_not_bool"
      @ [ IMov (Reg RAX, c_cond);
          IMov (Reg scratch_reg, const_false);
          ICmp (Reg RAX, Reg scratch_reg);
          IJe (Label else_label) ]
      @ c_thn
      @ [IJmp (Label done_label); ILabel else_label]
      @ c_els @ [ILabel done_label]
  | CTuple (exprs, (_, tag)) ->
      (* TODO: change manual padding creation and total_size calculation to use align_size (test for regressions) *)
      let tup_size = List.length exprs in
      let store_length =
        [IMov (Sized (QWORD_PTR, RegOffset (0, heap_reg)), Const (Int64.of_int (tup_size lsl 1)))]
      in
      let arg_moves =
        List.concat
          (List.mapi
             (fun i e ->
               [ IMov (Reg scratch_reg, compile_imm e env lambda_tag);
                 IMov (Sized (QWORD_PTR, RegOffset ((i + 1) * word_size, heap_reg)), Reg scratch_reg)
               ] )
             exprs )
      in
      let padding =
        if tup_size mod 2 == 0 then
          word_size
        else
          0
      in
      (* element count + (# elements * word_size) + {0 or word_size if even} *)
      let total_size = word_size + (tup_size * word_size) + padding in
      let create_tup_val =
        [ IMov (Reg RAX, Reg heap_reg);
          IOr (Reg RAX, Const tuple_tag);
          IAdd (Reg heap_reg, Const (Int64.of_int total_size)) ]
      in
      reserve total_size tag @ store_length @ arg_moves @ create_tup_val
  | CGetItem (tup, idx, _) ->
      let c_tup = compile_imm tup env lambda_tag in
      let c_idx = compile_imm idx env lambda_tag in
      check_nil c_tup
      @ check_tup_tag c_tup "?err_get_not_tuple"
      @ check_num_tag c_idx "?err_get_not_num"
      @ [ IMov (Reg RAX, c_tup);
          ISub (Reg RAX, Const tuple_tag);
          IMov (Reg scratch_reg, c_idx);
          ICmp (Reg scratch_reg, Const 0L);
          IJl (Label "?err_get_low_index");
          ICmp (Reg scratch_reg, RegOffset (0, RAX));
          IJge (Label "?err_get_high_index");
          IMov (Reg RAX, RegOffsetReg (RAX, scratch_reg, word_size, 0)) ]
  | CSetItem (tup, idx, value, _) ->
      let c_tup = compile_imm tup env lambda_tag in
      let c_idx = compile_imm idx env lambda_tag in
      let c_val = compile_imm value env lambda_tag in
      check_nil c_tup
      @ check_tup_tag c_tup "?err_set_not_tuple"
      @ check_num_tag c_idx "?err_set_not_num"
      @ [ IMov (Reg RAX, c_tup);
          ISub (Reg RAX, Const tuple_tag);
          IMov (Reg scratch_reg, c_idx);
          ICmp (Reg scratch_reg, Const 0L);
          IJl (Label "?err_set_low_index");
          ICmp (Reg scratch_reg, RegOffset (0, RAX));
          IJge (Label "?err_set_high_index");
          IInstrComment
            ( IPush (Reg R10),
              "saving R10 to the stack - we need to use it as a temp for the following mov" );
          IMov (Reg R10, c_val);
          IMov (Sized (QWORD_PTR, RegOffsetReg (RAX, scratch_reg, word_size, word_size)), Reg R10);
          IPop (Reg R10);
          IMov (Reg RAX, c_val) ]
  | CApp (func, args, Native, _) ->
      let name =
        match func with
        | ImmId (name, _) -> name
        | _ -> raise (InternalCompilerError "Native functions should have ImmId function exprs")
      in
      let c_args = List.map (fun a -> compile_imm a env lambda_tag) args in
      native_call (Label name) c_args
  | CApp (func, args, _, _) ->
      let f_imm = compile_imm func env lambda_tag in
      let c_args = List.map (fun a -> compile_imm a env lambda_tag) args in
      check_closure f_imm "?err_call_not_closure" @ call f_imm c_args
  | CLambda (args, body, (fvs, tag)) ->
      let lam_label = sprintf "$lam_%d_start" tag in
      let lam_done_label = sprintf "$lam_%d_end" tag in
      let lam_env = find env tag in
      let arity = List.length args in
      let frees =
        (* TODO Lerner's code does not have recursive function name in free*)
        (* List.sort compare
           (free_vars (ALetRec ([(bound_lam_name, e)], ACExpr (CImmExpr (ImmNum (-1L, tag))), tag))) *)
        List.sort compare (StringSet.elements fvs)
      in
      let num_frees = List.length frees in
      let locals_space =
        deepest_stack body lam_env
        (* try deepest_stack body lam_env
           with InternalCompilerError _ -> raise (InternalCompilerError "AHA3") *)
      in
      let c_body = compile_aexpr body env tag bound_lam_name in
      let total_size = align_size ((3 + num_frees) * word_size) in
      let lambda_body =
        let loadSelf =
          [ IInstrComment
              (IMov (Reg scratch_reg, RegOffset (2 * word_size, RBP)), "\t\\ load self ptr");
            IInstrComment (ISub (Reg scratch_reg, HexConst closure_tag), "\t/ and untag") ]
        in
        let loadFrees =
          List.concat
            (List.mapi
               (fun i fv ->
                 [ IInstrComment
                     ( IMov (Reg RAX, RegOffset ((i + 3) * word_size, scratch_reg)),
                       sprintf "\t\\ load free var: %s" fv );
                   IInstrComment (IMov (find lam_env fv, Reg RAX), "\t/ into its correct slot") ] )
               frees )
        in
        let postlude = [IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet; ILabel lam_done_label] in
        [IPush (Reg RBP); IMov (Reg RBP, Reg RSP)]
        @ replicate (IPush (Sized (QWORD_PTR, Const 0L))) (locals_space + num_frees)
        @ loadSelf @ loadFrees @ c_body @ postlude
      in
      let closure_creation =
        (* let preload_recursive =
             let reg_to_init =
               try Some (find_with_tag env lambda_tag bound_lam_name)
               with InternalCompilerError _ -> None
             in
             match reg_to_init with
             | Some reg_to_init ->
                 [ IInstrComment
                     (IMov (reg_to_init, Reg heap_reg), "\t\\ initialize recursive pointer reg");
                   IInstrComment
                     (IAdd (Sized (QWORD_PTR, reg_to_init), Const closure_tag), "/ and tag it") ]
             | None -> []
           in *)
        let load_closure_args =
          List.concat
            (List.mapi
               (fun i fv ->
                 [ IInstrComment
                     ( IMov (Reg RAX, find_with_tag env lambda_tag fv),
                       sprintf "\t\\ copy %s from arg" fv );
                   IInstrComment
                     (IMov (RegOffset ((i + 3) * word_size, heap_reg), Reg RAX), "\t/ into closure")
                 ] )
               frees )
        in
        let finalize_closure =
          [ IMov (Reg RAX, Reg heap_reg);
            IAdd (Reg RAX, HexConst closure_tag);
            IAdd (Reg heap_reg, Const (Int64.of_int total_size)) ]
        in
        (* preload_recursive@ *)
        [ IInstrComment
            ( IMov (Sized (QWORD_PTR, RegOffset (0, heap_reg)), Const (Int64.of_int arity)),
              "load arity" );
          IInstrComment
            (IMov (Sized (QWORD_PTR, Reg scratch_reg), Label lam_label), "\t\\ load code ptr");
          IInstrComment
            (IMov (Sized (QWORD_PTR, RegOffset (word_size, heap_reg)), Reg scratch_reg), "\t/");
          IInstrComment
            ( IMov
                ( Sized (QWORD_PTR, RegOffset (word_size * 2, heap_reg)),
                  Const (Int64.of_int num_frees) ),
              sprintf "# of fvs (%d)" num_frees ) ]
        @ load_closure_args @ finalize_closure
      in
      [IJmp (Label lam_done_label); ILabel lam_label]
      @ lambda_body @ reserve total_size tag @ closure_creation
  | CImmExpr imm -> [IMov (Reg RAX, compile_imm imm env lambda_tag)]

and compile_imm e env lambda_tag =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> find_with_tag env lambda_tag x
  | ImmNil _ -> const_nil

and args_help args regs =
  match (args, regs) with
  | arg :: args, reg :: regs -> IMov (Sized (QWORD_PTR, Reg reg), arg) :: args_help args regs
  | args, [] -> List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []

and native_call label args =
  (* We know that on entry to every function, RSP is 16-byte aligned.
     We know that every frame is a multiple of 16 bytes.
     The call instruction pushes one return pointer onto the stack.
     The first thing we do is push RBP onto the stack
     So, we add 8 bytes of padding IFF the number of spilled args is *ODD*.
  *)
  let num_stack_args = max (List.length args - 6) 0 in
  let padding_needed = num_stack_args mod 2 <> 0 in
  let setup =
    ( if padding_needed then
      [IInstrComment (IPush (Sized (QWORD_PTR, Const 0L)), "Padding to 16-byte alignment")]
    else
      [] )
    @ args_help args first_six_args_registers
  in
  let teardown =
    ( if num_stack_args = 0 then
      []
    else
      [ IInstrComment
          ( IAdd (Reg RSP, Const (Int64.of_int (word_size * num_stack_args))),
            sprintf "Popping %d arguments" num_stack_args ) ] )
    @
    if padding_needed then
      [IInstrComment (IAdd (Reg RSP, Const (Int64.of_int word_size)), "Unpadding one word")]
    else
      []
  in
  setup @ [ICall label] @ teardown

(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED -- THIS CODE WILL NOT WORK AS WRITTEN *)
and call (closure : arg) args =
  let arity = List.length args in
  let setup = [IMov (Reg RAX, closure); ISub (Reg RAX, HexConst closure_tag)] in
  let arity_checks =
    [ IMov (Reg scratch_reg, RegOffset (0, RAX));
      ICmp (Reg scratch_reg, Const (Int64.of_int arity));
      IJne (Label "?err_call_arity_err") ]
  in
  let pass_args =
    List.concat_map (fun a -> [IMov (Reg scratch_reg, a); IPush (Reg scratch_reg)]) (List.rev args)
  in
  let pushSelf = [IInstrComment (IPush (Sized (QWORD_PTR, closure)), "push closure to stack")] in
  let teardown =
    if arity = 0 then
      []
    else
      [ IInstrComment
          ( IAdd (Reg RSP, Const (Int64.of_int (word_size * (arity + 1)))),
            sprintf "Popping %d arguments" (arity + 1) ) ]
  in
  setup @ arity_checks @ pass_args @ pushSelf @ [ICall (RegOffset (8, RAX))] @ teardown
;;

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : sourcespan program) =
  let wrap_native name arity =
    let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
    [ DFun
        ( name,
          List.map (fun name -> BName (name, false, dummy_span)) argnames,
          EApp
            ( EId (name, dummy_span),
              List.map (fun name -> EId (name, dummy_span)) argnames,
              Native,
              dummy_span ),
          dummy_span ) ]
  in
  match p with
  | Program (declss, body, tag) ->
      Program
        ( List.fold_left
            (fun declss (name, arity) -> wrap_native name arity :: declss)
            declss native_fun_bindings,
          body,
          tag )
;;

let compile_prog (anfed, (env : arg name_envt tag_envt)) =
  let prelude =
    "default rel\n\
     section .text\n\
     extern ?error\n\
     extern ?input\n\
     extern ?print\n\
     extern ?print_stack\n\
     extern ?equal\n\
     extern ?try_gc\n\
     extern ?naive_print_heap\n\
     extern ?HEAP\n\
     extern ?HEAP_END\n\
     extern ?set_stack_bottom\n\
     global ?our_code_starts_here"
  in
  let suffix =
    sprintf
      "\n\
       ?err_comp_not_num:%s\n\
       ?err_arith_not_num:%s\n\
       ?err_logic_not_bool:%s\n\
       ?err_if_not_bool:%s\n\
       ?err_overflow:%s\n\
       ?err_get_not_tuple:%s\n\
       ?err_get_low_index:%s\n\
       ?err_get_high_index:%s\n\
       ?err_nil_deref:%s\n\
       ?err_out_of_memory:%s\n\
       ?err_set_not_tuple:%s\n\
       ?err_set_low_index:%s\n\
       ?err_set_high_index:%s\n\
       ?err_call_not_closure:%s\n\
       ?err_call_arity_err:%s\n\
       ?err_get_not_num:%s\n\
       ?err_set_not_num:%s\n\
       ?err_tuple_destructure_mismatch:%s\n"
      (to_asm (native_call (Label "?error") [Const err_COMP_NOT_NUM; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_ARITH_NOT_NUM; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_LOGIC_NOT_BOOL; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_IF_NOT_BOOL; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_OVERFLOW; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_GET_NOT_TUPLE; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_GET_LOW_INDEX; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_GET_HIGH_INDEX]))
      (to_asm (native_call (Label "?error") [Const err_NIL_DEREF; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_OUT_OF_MEMORY; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SET_NOT_TUPLE; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SET_LOW_INDEX; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SET_HIGH_INDEX; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_CALL_NOT_CLOSURE; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_CALL_ARITY_ERR; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_GET_NOT_NUM; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SET_NOT_NUM; Reg scratch_reg]))
      (to_asm
         (native_call (Label "?error") [Const err_TUPLE_DESTRUCTURE_MISMATCH; Reg scratch_reg]) )
  in
  match anfed with
  | AProgram (body, (_, tag)) ->
      (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
      let prologue, comp_main, epilogue =
        compile_fun "?our_code_starts_here" ["$heap"; "$size"] body env tag
      in
      let heap_start =
        [ ILineComment "heap start";
          IInstrComment
            ( IMov (Sized (QWORD_PTR, Reg heap_reg), Reg (List.nth first_six_args_registers 0)),
              "Load heap_reg with our argument, the heap pointer" );
          IInstrComment
            ( IAdd (Sized (QWORD_PTR, Reg heap_reg), Const 15L),
              "Align it to the nearest multiple of 16" );
          IMov (Reg scratch_reg, HexConst 0xFFFFFFFFFFFFFFF0L);
          IInstrComment
            ( IAnd (Sized (QWORD_PTR, Reg heap_reg), Reg scratch_reg),
              "by adding no more than 15 to it" ) ]
      in
      let set_stack_bottom =
        [IMov (Reg R12, Reg RDI)]
        @ native_call (Label "?set_stack_bottom") [Reg RBP]
        @ [IMov (Reg RDI, Reg R12)]
      in
      let main = prologue @ set_stack_bottom @ heap_start @ comp_main @ epilogue in
      sprintf "%s%s%s\n" prelude (to_asm main) suffix
;;

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let pick_alloc_strategy (strat : alloc_strategy) =
  match strat with
  | Naive -> naive_stack_allocation
  | Register -> register_allocation
;;

let compile_to_string
    ?(no_builtins = false)
    (alloc_strat : alloc_strategy)
    (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> run_if (not no_builtins) (add_phase add_natives add_native_lambdas)
  |> add_phase desugared desugar |> add_phase tagged tag |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase free_var_cached free_vars_cache
  |> add_phase locate_bindings (pick_alloc_strategy alloc_strat)
  |> add_phase result compile_prog
;;
