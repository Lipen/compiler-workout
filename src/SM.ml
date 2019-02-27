open GT

open List

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let rec eval cfg prg =
  let step (st, (s, i, o)) p = match p with
    | BINOP op -> (Syntax.Expr.eval_op op (hd (tl st)) (hd st) :: (tl (tl st)), (s, i, o))
    | CONST n  -> (n :: st, (s, i, o))
    | READ     -> (hd i :: st, (s, tl i, o))
    | WRITE    -> (tl st, (s, i, o @ [hd st]))
    | LD x     -> (s x :: st, (s, i, o))
    | ST x     -> (tl st, (Syntax.Expr.update x (hd st) s, i, o))
  in match prg with
    | [] -> cfg
    | p :: ps -> eval (step cfg p) ps

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile stmt =
  let rec compile_expr e = match e with
    | Syntax.Expr.Const n -> [CONST n]
    | Syntax.Expr.Var   x -> [LD x]
    | Syntax.Expr.Binop (op, l, r) -> compile_expr l @ compile_expr r @ [BINOP op]
  in match stmt with
    | Syntax.Stmt.Read  x -> [READ; ST x]
    | Syntax.Stmt.Write e -> compile_expr e @ [WRITE]
    | Syntax.Stmt.Assign (x, e) -> compile_expr e @ [ST x]
    | Syntax.Stmt.Seq  (p1, p2) -> compile p1 @ compile p2;;
