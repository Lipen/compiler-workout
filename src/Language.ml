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
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns resulting configuration
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

    let rec eval env ((s, i, o, _) as conf) expr =
      match expr with
      | Const n -> (s, i, o, Some n)
      | Var x -> (s, i, o, Some (State.eval s x))
      | Binop (op, x, y) ->
        let (s, i, o, Some rx) = eval env conf x in
        let (s, i, o, Some ry) = eval env (s, i, o, None) y in
        (s, i, o, Some (to_func op rx ry))
      | Call (f, args) ->
        let (s, i, o, args) =
          List.fold_left
            (fun (s, i, o, args) arg ->
              let (s, i, o, Some r) = eval env (s, i, o, None) arg in
              (s, i, o, args @ [r]))
            (s, i, o, [])
            args in
        env#definition env f args (s, i, o, None)
      | _ -> failwith "Unsupported expression type"

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
      | -"(" parse -")"
      | name:IDENT p:("(" args:!(Ostap.Util.list0 parse) ")" {Call (name, args)} | empty {Var name}) {p}
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, a continuation and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    let diamond s1 s2 = match s2 with
      | Skip -> s1
      | _ -> Seq (s1, s2)

    let reverse_condition cond = Expr.Binop ("==", cond, Expr.Const 0)

    let rec eval env ((s, i, o, _) as conf) k stmt =
      match stmt with
      | Read x ->
        begin match i with
        | z::rest -> eval env (State.update x z s, rest, o, None) Skip k
        | _ -> failwith "Impossible to Read"
        end
      | Write e ->
        let (s, i, o, Some r) = Expr.eval env conf e in
        eval env (s, i, o @ [r], None) Skip k
      | Assign (x, e) ->
        let (s, i, o, Some r) = Expr.eval env conf e in
        eval env (State.update x r s, i, o, Some r) Skip k
      | Seq (s1, s2) -> eval env conf (diamond s2 k) s1
      | Skip ->
        begin match k with
        | Skip -> conf
        | _ -> eval env conf Skip k
        end
      | If (cond, s1, s2) ->
        let (s, i, o, Some r) = Expr.eval env conf cond in
        eval env (s, i, o, None) k (if r <> 0 then s1 else s2)
      | While (cond, body) ->
        let (s, i, o, Some r) = Expr.eval env conf cond in
        if (r <> 0) then
          eval env (s, i, o, None) (diamond stmt k) body
        else
          eval env (s, i, o, None) Skip k
      | RepeatUntil (body, cond) ->
        eval env conf (diamond (While (reverse_condition cond, body)) k) body
        (* let c' = eval env (s, i, o, None) Skip body in
        let (s, i, o, Some r) = Expr.eval env c' cond in
        if (r <> 0) then
          eval env (s, i, o, None) k stmt
        else
          c' *)
      | Return e_opt ->
        begin match e_opt with
        | Some e -> Expr.eval env conf e
        | _ -> (s, i, o, None)
        end
      | Call (name, args) ->
        eval env (Expr.eval env conf (Expr.Call (name, args))) Skip k
      | _ -> failwith "Unsupported instruction"

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
      function_call: name:IDENT "(" args:!(Ostap.Util.list0 Expr.parse) ")"  { Call (name, args) };
      return: "return" e:!(Expr.parse)? { Return e };

      seq: s1:statement ";" s2:parse  { Seq (s1, s2) };
      statement: read | write | assign | skip | ite | while_loop | for_loop | repeat_loop | function_call | return;
      parse: seq | statement
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      identifier: IDENT;
      parse: "fun" name:IDENT
             "(" args:!(Ostap.Util.list0 identifier) ")"
             locals:(-"local" !(Ostap.Util.list0 identifier))?
             "{" body:!(Stmt.parse) "}"
             { name, (args, get_or_default locals [], body) }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
