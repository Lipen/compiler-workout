(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* Utility function to convert option to stored or default value *)
let get_or_default x d =
  match x with
  | Some t -> t
  | None -> d

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)

    let rec eval st expr =
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
      parse:
    !(Ostap.Util.expr
             (fun x -> x)
       (Array.map (fun (a, s) -> a,
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        )
              [|
    `Lefta, ["!!"];
    `Lefta, ["&&"];
    `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
    `Lefta, ["+" ; "-"];
    `Lefta, ["*" ; "/"; "%"];
              |]
       )
       primary);

      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | RepeatUntil of t * Expr.t
                                             with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval c p =
      let (s, i, o) = c in
      match p with
      | Read x ->
        begin match i with
        | z::tail -> (State.update x z s, tail, o)
        | _ -> failwith "Impossible to Read"
        end
      | Write e -> (s, i, o @ [Expr.eval s e])
      | Assign (x, e) -> (State.update x (Expr.eval s e) s, i, o)
      | Seq (p1, p2) -> eval (eval c p1) p2
      | Skip -> c
      | If (cond, s1, s2) -> eval c (if Expr.eval s cond <> 0 then s1 else s2)
      | While (cond, body) -> if Expr.eval s cond != 0 then eval (eval c body) p else c
      | RepeatUntil (body, cond) ->
        let c' = eval c body in
        let (s', _, _) = c' in
        if Expr.eval s' cond = 0 then eval c' p else c'

    let rec build_ite cond s_then elifs s_else =
      let elifs' = match elifs with
        | (elif_cond, elif_then)::rest -> build_ite elif_cond elif_then rest s_else
        | [] -> s_else in
      If (cond, s_then, elifs')

    (* Statement parser *)
    ostap (
      read: "read" "(" x:IDENT ")"  { Read x };
      write: "write" "(" e:!(Expr.parse) ")"  { Write e };
      assign: x:IDENT ":=" e:!(Expr.parse)  { Assign (x, e) };
      skip: "skip"  { Skip };
      ite: "if" cond:!(Expr.parse)
           "then" s_then:parse
                  elifs:(-"elif" !(Expr.parse) -"then" parse)*
                  s_else:(-"else" parse)?
           "fi"
           { build_ite cond s_then elifs (get_or_default s_else Skip) };
      while_loop: "while" cond:!(Expr.parse)
                  "do" body:parse
                  "od"
                  { While (cond, body) };
      for_loop: "for" init:parse "," e:!(Expr.parse) "," cond:parse
                "do" body:parse
                "od"
                { Seq (init, While (e, Seq (body, cond))) };
      repeat_loop: "repeat" body:parse
                   "until" cond:!(Expr.parse)
                   { RepeatUntil (body, cond) };

      seq: s1:statement ";" s2:parse  { Seq (s1, s2) };
      statement: read | write | assign | skip | ite | while_loop | for_loop | repeat_loop;
      parse: seq | statement
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (State.empty, i, []) p in
  o

(* Top-level parser *)
let parse = Stmt.parse
