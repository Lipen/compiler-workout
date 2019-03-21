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
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env cfg prg = match prg with
  | [] -> cfg
  | p::rest ->
    let (st, c) = cfg in
    let (s, i, o) = c in
    (match p with
      | BINOP op -> (match st with
        | y::x::tail -> eval env (Expr.eval_op op x y :: tail, c) rest
        | _ -> failwith "Impossible to BINOP")
      | CONST n -> eval env (n :: st, c) rest
      | READ -> (match i with
        | z::tail -> eval env (z :: st, (s, tail, o)) rest
        | _ -> failwith "Impossible to READ")
      | WRITE -> (match st with
        | z::tail -> eval env (tail, (s, i, o @ [z])) rest
        | _ -> failwith "Impossible to WRITE")
      | LD x -> eval env (s x :: st, c) rest
      | ST x -> (match st with
        | z::tail -> eval env (tail, (Expr.update x z s, i, o)) rest
        | _ -> failwith "Impossible to ST")
      | LABEL l -> eval env cfg rest
      | JMP l -> eval env cfg (env#labeled l)
      | CJMP (t, l) -> (match st with
        | z::tail ->
          if (t = "z" && z = 0 || t = "nz" && z != 0) then
            eval env (tail, c) (env#labeled l)
          else
            eval env (tail, c) rest
        | _ -> failwith "Impossible to CJMP")
      | _ -> failwith "Unsupported operation"
    );;

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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o


let label_generator =
  object
    val mutable counter = 0

    method generate =
      counter <- counter + 1;
      "l_" ^ string_of_int counter
  end

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile s =
  let rec expr e = match e with
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  match s with
    | Stmt.Read x        -> [READ; ST x]
    | Stmt.Write e       -> expr e @ [WRITE]
    | Stmt.Assign (x, e) -> expr e @ [ST x]
    | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
    | Stmt.Skip          -> []
    | If (e, s1, s2) ->
      let l_else = label_generator#generate in
      let l_fi = label_generator#generate in
      expr e @ [CJMP ("z", l_else)] @ compile s1 @ [JMP l_fi; LABEL l_else] @ compile s2 @ [LABEL l_fi]
    | While (e, s) ->
      let l_loop = label_generator#generate in
      let l_od = label_generator#generate in
      [LABEL l_loop] @ expr e @ [CJMP ("z", l_od)] @ compile s @ [JMP l_loop; LABEL l_od]
    | RepeatUntil (s, e) ->
      let l_loop = label_generator#generate in
      [LABEL l_loop] @ compile s @ expr e @ [CJMP ("z", l_loop)]
