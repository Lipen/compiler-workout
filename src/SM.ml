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
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env cfg prg =
  match prg with
  | [] -> cfg
  | p::rest ->
    let (cst, st, c) = cfg in
    let (s, i, o) = c in
    begin match p with
    | BINOP op ->
      let y::x::tail = st in
      let result = Expr.eval s (Binop (op, Const x, Const y)) in
      eval env (cst, result :: tail, c) rest
    | CONST n -> eval env (cst, n :: st, c) rest
    | READ ->
      let z::tail = i in
      eval env (cst, z :: st, (s, tail, o)) rest
    | WRITE ->
      let z::tail = st in
      eval env (cst, tail, (s, i, o @ [z])) rest
    | LD x -> eval env (cst, State.eval s x :: st, c) rest
    | ST x ->
      let z::tail = st in
      eval env (cst, tail, (State.update x z s, i, o)) rest
    | LABEL _ -> eval env cfg rest
    | JMP l -> eval env cfg (env#labeled l)
    | CJMP (mode, l) ->
      let z::tail = st in
      if (mode = "z" && z = 0 || mode = "nz" && z != 0) then
        eval env (cst, tail, c) (env#labeled l)
      else
        eval env (cst, tail, c) rest
    | BEGIN (args, locals) ->
      let s_fun = State.push_scope s (args @ locals) in
      let s', st' =
        List.fold_left
          (fun (s, v::st) x -> (State.update x v s, st))
          (s_fun, st)
          args in
      eval env (cst, st', (s', i, o)) rest
    | END -> (match cst with
      | (rest',s')::cst' -> eval env (cst', st, ((State.drop_scope s s'), i, o)) rest'
      | _ -> cfg)
    | CALL f -> eval env ((rest, s)::cst, st, c) (env#labeled f)
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

     val compile : Language.t -> label -> (prg, flag_is_label_used)

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile_with_label s label =
  let rec expr e = match e with
    | Expr.Var x -> [LD x]
    | Expr.Const n -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
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
  | Stmt.Call (f, args) -> (List.concat (List.map expr (List.rev args)) @ [CALL f], false)

let rec compile_main p =
  let label = label_generator#generate in
  let (compiled, used) = compile_with_label p label in
  compiled @ (if used then [LABEL label] else [])

let rec compile_defs defs =
  List.fold_left
    (fun p (name, (args, locals, body)) ->
      let compiled_body = compile_main body in
      p @ [LABEL name] @ [BEGIN (args, locals)] @ compiled_body @ [END])
    []
    defs

let rec compile (defs, main) =
  let compiled_main = compile_main main in
  let compiled_defs = compile_defs defs in
  compiled_main @ [END] @ compiled_defs
