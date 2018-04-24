(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
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

    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *) 

    let rec eval env ((st, i, o, r) as conf) expr = match expr with
       | Const value -> (st, i, o, Some value)
       | Var   value -> (st, i, o, Some(State.eval st value))
       | Binop (op, exp1, exp2) -> let (_, _, _, Some firstArg) as conf = eval env conf exp1 in
          let (st, i, o, Some secondArg) = eval env conf exp2 
          in (st, i, o, Some (to_func op firstArg secondArg)) 
        | Call (name, args) -> let computedArgs, conf = List.fold_left (fun (acc, conf) arg -> let (_, _, _, Some compArg) as conf = eval env conf arg in compArg::acc, conf) ([], conf) args in
          env#definition env name (List.rev computedArgs) conf

    let ostapBinops operations = 
       let operation op = (ostap ($(op)), fun x y -> Binop (op, x, y)) in 
       List.map operation operations;;

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      primary:
         x:IDENT {Var x}
         | x:DECIMAL {Const x}
         | -"(" parse -")";
       parse:
         !(Ostap.Util.expr(fun x -> x)
          [|
             `Lefta, ostapBinops ["!!"];
             `Lefta, ostapBinops ["&&"];
             `Nona,  ostapBinops [">="; ">"; "<="; "<"; "=="; "!="];
             `Lefta, ostapBinops ["+"; "-"];
             `Lefta, ostapBinops ["*"; "/"; "%"]
           |]
           primary
         )
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    let evalSeq x stmt = match stmt with
    | Skip -> x
    | y    -> Seq (x, y)

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    
     let rec eval env ((state, input, output, r) as conf) k stmt = 
      match stmt with
      | Read x ->
        eval env (match input with
        | head :: tail ->
          (State.update x head state, tail, output, r)
        | _ ->
          failwith "Unexpected end of input") Skip k
      | Write e ->
        eval env (
          let (state, input, output, Some x) = Expr.eval env conf e in
          (state, input, output @ [x], r)) Skip k
      | Assign (x, e) ->
        eval env (
          let (state, input, output, Some rr) = Expr.eval env conf e in
          (State.update x rr state, input, output, r)) Skip k
      | Seq (s1, s2) ->
        eval env conf (evalSeq s2 k) s1
      | Skip ->
        match k with Skip ->
          conf
          | something ->
            eval env conf Skip k
      | If (expr, thenIf, elseIf) ->
        let (_, _, _, Some x) as conf = Expr.eval env conf expr in
        if x <> 0 then (eval env conf k thenIf) else (eval env conf k elseIf)
      | While (expr, loopStmt) ->
        let (_, _, _, Some x) as conf = Expr.eval env conf expr in
        if (x = 0) then eval env conf Skip k else eval env conf (evalSeq stmt k) loopStmt
      | Repeat (loopStmt, expr) -> 
        eval env conf (evalSeq (While (Expr.Binop ("==", expr, Expr.Const 0), loopStmt)) k) loopStmt
      | Call (f, args) ->
        eval env (Expr.eval env conf (Expr.Call (f, args))) k Skip
      | Return res ->
        match res with
        | None ->
          (state, input, output, None)
        | Some resExpr ->
          Expr.eval env conf resExpr

    let rec parseElIfActions elIfActions elseAction =  match elIfActions with
    | [] ->
      elseAction
    | (condition, action)::tailElIfActions ->
      If (condition, action, parseElIfActions tailElIfActions elseAction)

    let parseElse elIfActions elseAction = 
      let elseActionParsed = match elseAction with
      | None ->
        Skip
      | Some action ->
        action
    in parseElIfActions elIfActions elseActionParsed
         
    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      
      stmt:
        "read" "(" x:IDENT ")"          {Read x}
      | "write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT 
        assignmentOrCall: (
          ":=" e:!(Expr.parse)    {Assign (x, e)}
          | "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)}
        ) {assignmentOrCall}
      | %"skip"                         {Skip}
      | %"if" condition: !(Expr.parse) %"then" action:parse 
        elIfActions:(%"elif" !(Expr.parse) %"then" parse)*
        elseAction:(%"else" parse)?
        %"fi"                                              { If (condition, action, parseElse elIfActions elseAction)}
      | %"while" condition: !(Expr.parse) %"do" action:parse %"od"  { While (condition, action) }
      | %"repeat" action:parse %"until" condition: !(Expr.parse)    { Repeat (action, condition) }
      | %"return" e:!(Expr.parse)? {Return e}
      | %"for" initialize:parse "," condition: !(Expr.parse)
        "," increment:parse %"do" action:parse %"od"             { Seq (initialize, While (condition, Seq (action, increment))) }
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
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
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
