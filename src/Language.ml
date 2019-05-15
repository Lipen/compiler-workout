(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Utility function to convert option to stored or default value *)
let get_or_default x d =
  match x with
  | Some t -> t
  | None -> d

let list_init n f =
  let rec init_list' acc i n f =
    if i >= n then acc
    else init_list' ((f i) :: acc) (i+1) n f
  in List.rev (init_list' [] 0 n f)

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

    let to_bool x = (to_int x) <> 0

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = list_init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* (* S-expressions      *) | Sexp   of string * t list *)
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
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

    let rec eval env ((st, i, o, r) as conf) expr =
      match expr with
      | Var x -> (st, i, o, Some (State.eval st x))
      | Const x -> (st, i, o, Some (Value.of_int x))
      | Array a ->
        let (st, i, o, rs) = eval_list env conf a in
        (st, i, o, Some (Value.of_array rs))
      | String s -> (st, i, o, Some (Value.of_string s))
      | Binop (op, x, y) ->
        let (st1, i1, o1, Some r1) = eval env conf x in
        let (st2, i2, o2, Some r2) = eval env (st1, i1, o1, None) y in
        (st2, i2, o2, Some (Value.of_int (to_func op (Value.to_int r1) (Value.to_int r2))))
      | Elem (a, idx) ->
        let (st, i, o, args) = eval_list env conf [a;idx] in
        Builtin.eval (st, i, o, None) args "$elem"
      | Length a ->
        let (st, i, o, Some a) = eval env conf a in
        let res =
          match a with
          | String s -> Value.of_int (String.length s)
          | Array a -> Value.of_int (List.length a)
        in
        (st, i, o, Some res)
      | Call (f, args) ->
        let eval_args = (fun (st, i, o, values) arg ->
          let (st', i', o', Some value) = eval env (st, i, o, None) arg in
          (st', i', o', values @ [value]))
        in
        let st', i', o', values = List.fold_left eval_args (st, i, o, []) args in
        env#definition env f values (st', i', o', None)
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)

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
       arr);

      primary:
        n:DECIMAL {Const n}
      | c:CHAR {Const (Char.code c)}
      | s:STRING {String (String.sub s 1 (String.length s - 2))}
      | -"[" elems:!(Ostap.Util.list0 parse)  -"]" {Array elems}
      | name:IDENT "(" args:!(Ostap.Util.list0 parse) ")" {Call (name, args)}
      | x:IDENT {Var x}
      | -"(" parse -")";

      arr: e:primary elems:(-"[" !(parse) -"]")* length:(".length")? {
        let e = List.fold_left (fun e id -> Elem (e, id)) e elems in
        match length with
        | Some _ -> Length e
        | _ -> e
      }
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          )
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let diamond s1 s2 = match s2 with
      | Skip -> s1
      | _ -> Seq (s1, s2)

    let reverse_condition cond = Expr.Binop ("==", cond, Expr.Const 0)

    let rec eval env ((s, i, o, _) as conf) k stmt =
      match stmt with
      | Assign (x, ixs, e) ->
        let (s, i, o, ixs) = Expr.eval_list env conf ixs in
        let (s, i, o, Some r) = Expr.eval env (s, i, o, None) e in
        eval env (update s x r ixs, i, o, Some r) Skip k
      | Seq (s1, s2) -> eval env conf (diamond s2 k) s1
      | Skip ->
        begin match k with
        | Skip -> conf
        | _ -> eval env conf Skip k
        end
      | If (cond, s1, s2) ->
        let (s, i, o, Some r) = Expr.eval env conf cond in
        eval env (s, i, o, None) k (if (Value.to_bool r) then s1 else s2)
      | While (cond, body) ->
        let (s, i, o, Some r) = Expr.eval env conf cond in
        if (Value.to_bool r) then
          eval env (s, i, o, None) (diamond stmt k) body
        else
          eval env (s, i, o, None) Skip k
      | Repeat (body, cond) ->
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
      assign: x:IDENT i:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse) {Assign (x, i, e)};
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
                   { Repeat (body, cond) };
      function_call: name:IDENT "(" args:!(Ostap.Util.list0 Expr.parse) ")"  { Call (name, args) };
      return: "return" e:!(Expr.parse)? { Return e };

      seq: s1:statement ";" s2:parse  { Seq (s1, s2) };
      statement: assign | skip | ite | while_loop | for_loop | repeat_loop | function_call | return;
      parse: seq | statement
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
