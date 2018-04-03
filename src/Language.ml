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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t  with show
                                                                    
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
        | Skip -> (state, instream, outstream)
        | If (expression, s1, s2) -> if Expr.eval state expression != 0 then eval (state, instream, outstream) s1 else eval (state, instream, outstream) s2
        | While  (expression, s) -> if Expr.eval state expression != 0 then eval (eval (state, instream, outstream) s) statement else (state, instream, outstream)
        | Repeat (expression, s) -> 
          let (state', instream', outstream') = eval (state, instream, outstream) s in
          if Expr.eval state' expression == 0 then eval (state', instream', outstream') statement else (state', instream', outstream')

                               
    (* Statement parser *)
    ostap (
      parse: seq | stmt;
       stmt: read | write | assign | if_ | while_ | for_ | repeat_ | skip;
       read: "read" -"(" x:IDENT -")" { Read x };
       write: "write" -"(" e:!(Expr.parse) -")" { Write e };
       assign: x:IDENT -":=" e:!(Expr.parse) { Assign (x, e) };
       if_: "if" e:!(Expr.parse) "then" s:parse "fi" {If (e, s, Skip)} 
          | "if" e:!(Expr.parse) "then" s1:parse else_elif:else_or_elif "fi" {If (e, s1, else_elif)};
       else_or_elif: else_ | elif_;
       else_: "else" s:parse {s};
       elif_: "elif" e:!(Expr.parse) "then" s1:parse s2:else_or_elif {If (e, s1, s2)};
       while_: "while" e:!(Expr.parse) "do" s:parse "od" {While (e, s)};
       for_: "for" init:parse "," e:!(Expr.parse) "," s1:parse "do" s2:parse "od" {Seq (init, While (e, Seq(s2, s1)))};
       repeat_: "repeat" s:parse "until" e:!(Expr.parse) {Repeat (e, s)};
       skip: "skip" {Skip};
       seq: left_st:stmt -";" right_st:parse { Seq (left_st, right_st) }
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

(* Top-level parser *)
let parse = Stmt.parse                                                     
