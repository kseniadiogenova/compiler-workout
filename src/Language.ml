(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List
open Ostap

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval state expr = match expr with
      | Var v -> state v
      | Const c -> c
      | Binop (op, expr1, expr2) ->
      let e1 = eval state expr1 in
      let e2 = eval state expr2 in
      let numericbool num_to_bool = if num_to_bool != 0 then true else false in
      let boolnumeric bool_to_num = if bool_to_num then 1 else 0 in
      match op with
      | "+" -> (e1 + e2)
      | "-" -> (e1 - e2)
      | "*" -> (e1 * e2)
      | "/" -> (e1 / e2)
      | "%" -> (e1 mod e2)
      | ">" -> boolnumeric (e1 > e2)
      | ">=" -> boolnumeric (e1 >= e2)
      | "<" -> boolnumeric (e1 < e2)
      | "<=" -> boolnumeric (e1 <= e2)
      | "==" -> boolnumeric (e1 == e2)
      | "!=" -> boolnumeric (e1 != e2)
      | "!!" -> boolnumeric (numericbool e1 || numericbool e2)
      | "&&" -> boolnumeric (numericbool e1 && numericbool e2)
      | _ -> failwith "Error!"

      let ostap_for_list ops = 
       let ostap_binop op = (ostap ($(op)), fun x y -> Binop (op, x, y)) in 
       List.map ostap_binop ops
       
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      primary: x:IDENT {Var x} 
              | x:DECIMAL {Const x} 
              | -"(" parse -")";
       parse: 
         !(Util.expr
           (fun x -> x)
           [|
             `Lefta, ostap_for_list ["!!"];
             `Lefta, ostap_for_list ["&&"];
             `Nona,  ostap_for_list [">="; "<="; "<"; ">"; "=="; "!="];
             `Lefta, ostap_for_list ["+"; "-"];
             `Lefta, ostap_for_list ["*"; "/"; "%"]
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (state, instream, outstream) statement = match statement with
       | Read v -> (Expr.update v (hd instream) state, tl instream, outstream)
       | Write expression -> (state, instream, outstream @ [Expr.eval state expression])
       | Assign (variable, expression) -> (Expr.update variable (Expr.eval state expression) state, instream, outstream)
       | Seq (state1, state2) -> eval (eval (state, instream, outstream) state1) state2
       | _ -> failwith "Incorrect statement"

    (* Statement parser *)
    ostap (
      parse: seq | stmt;
       seq: l:stmt -";" r:parse { Seq (l, r) };
       stmt:  "read" -"(" x:IDENT -")" { Read x }
            | "write" -"(" e:!(Expr.parse) -")" { Write e }
            | x:IDENT -":=" e:!(Expr.parse) { Assign (x, e) }
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
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
