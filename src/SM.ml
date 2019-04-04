open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool
                                        with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env ((cstack, stack, ((s, i, o) as c)) as conf) prg =
  match prg with
  | [] -> conf
  | p::rest ->
    begin match p with
    | BINOP op ->
      let y::x::tail = stack in
      let result = Expr.to_func op x y in
      eval env (cstack, result :: tail, c) rest
    | CONST n -> eval env (cstack, n :: stack, c) rest
    | READ ->
      let z::tail = i in
      eval env (cstack, z :: stack, (s, tail, o)) rest
    | WRITE ->
      let z::tail = stack in
      eval env (cstack, tail, (s, i, o @ [z])) rest
    | LD x -> eval env (cstack, State.eval s x :: stack, c) rest
    | ST x ->
      let z::tail = stack in
      eval env (cstack, tail, (State.update x z s, i, o)) rest
    | LABEL _ -> eval env conf rest
    | JMP l -> eval env conf (env#labeled l)
    | CJMP (mode, l) ->
      let z::tail = stack in
      if (mode = "z" && z = 0 || mode = "nz" && z != 0) then
        eval env (cstack, tail, c) (env#labeled l)
      else
        eval env (cstack, tail, c) rest
    | BEGIN (_, args, locals) ->
      let s_fun = State.enter s (args @ locals) in
      let s', stack' =
        List.fold_left
          (fun (s, v::stack) x -> (State.update x v s, stack))
          (s_fun, stack)
          args in
      eval env (cstack, stack', (s', i, o)) rest
    | CALL (f, _, _) -> eval env ((rest, s)::cstack, stack, c) (env#labeled f)
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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

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
  let rec expr e = match e with
    | Expr.Var x -> [LD x]
    | Expr.Const n -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
    | Expr.Call (f, args)   ->
      let compiled_args = List.concat (List.map (expr) (List.rev args)) in
      compiled_args @ [CALL (f, List.length args, true)]
  in
  match s with
  | Stmt.Read x -> ([READ; ST x], false)
  | Stmt.Write e -> (expr e @ [WRITE], false)
  | Stmt.Assign (x, e) -> (expr e @ [ST x], false)
  | Stmt.Seq (s1, s2)  ->
    let label' = label_generator#generate in
    let (compiled1, used1) = compile_with_label s1 label' in
    let (compiled2, used2) = compile_with_label s2 label in
    (compiled1 @ (if used1 then [LABEL label'] else []) @ compiled2, used2)
  | Stmt.Skip -> ([], false)
  | Stmt.If (cond, s1, s2) ->
    let l_else = label_generator#generate in
    let (compiled1, used1) = compile_with_label s1 label in
    let (compiled2, used2) = compile_with_label s2 label in
    (expr cond
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
      @ expr cond
      @ [CJMP ("nz", l_loop)]
    , false)
  | Stmt.RepeatUntil (body, cond) ->
    let l_loop = label_generator#generate in
    let (compiled_body, _) = compile_with_label body label in
    ([LABEL l_loop]
      @ compiled_body
      @ expr cond
      @ [CJMP ("z", l_loop)]
    , false)
  | Stmt.Call (f, args) -> (List.concat (List.map expr (List.rev args)) @ [CALL (f, List.length args, false)], false)
  | Stmt.Return e_opt ->
    ((match e_opt with
    | Some e -> (expr e) @ [RET true]
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
