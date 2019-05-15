open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
                                        with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((cstack, stack, ((s, i, o) as c)) as conf) prg =
  match prg with
  | [] -> conf
  | p::rest ->
    begin match p with
    | BINOP op ->
      let y::x::tail = stack in
      let result = Expr.to_func op (Value.to_int x) (Value.to_int y) in
      eval env (cstack, (Value.of_int result) :: tail, c) rest
    | CONST n -> eval env (cstack, (Value.of_int n) :: stack, c) rest
    | STRING n -> eval env (cstack, (Value.of_string n) :: stack, c) rest
    | LD x -> eval env (cstack, (State.eval s x) :: stack, c) rest
    | ST x ->
      let z::tail = stack in
      eval env (cstack, tail, (State.update x z s, i, o)) rest
    | STA (x, n) ->
      let (value::ixs, stack) = split (n + 1) stack in
      eval env (cstack, stack, (Stmt.update s x value ixs, i, o)) rest
    | LABEL _ -> eval env conf rest
    | JMP l -> eval env conf (env#labeled l)
    | CJMP (mode, l) ->
      let z::tail = stack in
      if ((mode = "z" && (not (Value.to_bool z))) || (mode = "nz" && (Value.to_bool z))) then
        eval env (cstack, tail, c) (env#labeled l)
      else
        eval env (cstack, tail, c) rest
    | BEGIN (_, args, locals) ->
      let s_fun = State.enter s (args @ locals) in
      let store = List.map (fun a -> ST a) args in
      let conf' = eval env (cstack, stack, (s_fun, i, o)) store in
      eval env conf' rest
    | CALL (f, n, p) ->
      if env#is_label f then
        eval env ((rest, s)::cstack, stack, c) (env#labeled f)
      else
        eval env (env#builtin conf f n (not p)) rest
    | END | RET _ -> (match cstack with
      | (rest',s')::cstack' -> eval env (cstack', stack, ((State.leave s s'), i, o)) rest'
      | _ -> conf)
    | _ -> failwith "Unsupported instruction"
    end

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o


let label_generator =
  object
    val mutable counter = 0

    method generate =
      counter <- counter + 1;
      "l_" ^ string_of_int counter
  end

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile_with_label s label =
  let rec compile_expr e =
    let compile_call f args = List.concat (List.map compile_expr (List.rev args)) @ [CALL (f, List.length args, true)] in
    match e with
    | Expr.Const n -> [CONST n]
    | Expr.Array a -> compile_call "$array" (List.rev a)
    | Expr.String n -> [STRING n]
    | Expr.Var x -> [LD x]
    | Expr.Binop (op, x, y) -> compile_expr x @ compile_expr y @ [BINOP op]
    | Expr.Elem (a, i) -> compile_call "$elem" [i; a]
    | Expr.Length a -> compile_call "$length" [a]
    | Expr.Call (f, args) -> compile_call f args
  in
  match s with
  | Stmt.Assign (x, ixs, e) ->
    begin match ixs with
    | [] -> (compile_expr e @ [ST x], false)
    | _ -> let compiled_ixs = List.fold_left (fun p ix -> p @ (compile_expr ix)) [] (List.rev ixs) in
      (compiled_ixs @ compile_expr e @ [STA (x, List.length compiled_ixs)], false)
    end
  | Stmt.Seq (s1, s2) ->
    let label' = label_generator#generate in
    let (compiled1, used1) = compile_with_label s1 label' in
    let (compiled2, used2) = compile_with_label s2 label in
    (compiled1 @ (if used1 then [LABEL label'] else []) @ compiled2, used2)
  | Stmt.Skip -> ([], false)
  | Stmt.If (cond, s1, s2) ->
    let l_else = label_generator#generate in
    let (compiled1, used1) = compile_with_label s1 label in
    let (compiled2, used2) = compile_with_label s2 label in
    (compile_expr cond
      @ [CJMP ("z", l_else)]
      @ compiled1
      @ (if used1 then [] else [JMP label])
      @ [LABEL l_else]
      @ compiled2
      @ (if used2 then [] else [JMP label])
    , true)
  | Stmt.While (cond, body) ->
    let l_cond = label_generator#generate in
    let l_loop = label_generator#generate in
    let (compiled_body, _) = compile_with_label body l_cond in
    ([JMP l_cond; LABEL l_loop]
      @ compiled_body
      @ [LABEL l_cond]
      @ compile_expr cond
      @ [CJMP ("nz", l_loop)]
    , false)
  | Stmt.Repeat (body, cond) ->
    let l_loop = label_generator#generate in
    let (compiled_body, _) = compile_with_label body label in
    ([LABEL l_loop]
      @ compiled_body
      @ compile_expr cond
      @ [CJMP ("z", l_loop)]
    , false)
  | Stmt.Call (f, args) -> (List.concat (List.map compile_expr (List.rev args)) @ [CALL (f, List.length args, false)], false)
  | Stmt.Return e_opt ->
    ((match e_opt with
    | Some e -> (compile_expr e) @ [RET true]
    | _ -> [RET false])
    , false)

let rec compile_main p =
  let label = label_generator#generate in
  let (compiled, used) = compile_with_label p label in
  compiled @ (if used then [LABEL label] else [])

let rec compile_defs defs =
  List.fold_left
    (fun p (name, (args, locals, body)) ->
      let compiled_body = compile_main body in
      p @ [LABEL name] @ [BEGIN (name, args, locals)] @ compiled_body @ [END])
    []
    defs

let rec compile (defs, main) =
  let compiled_main = compile_main main in
  let compiled_defs = compile_defs defs in
  compiled_main @ [END] @ compiled_defs

