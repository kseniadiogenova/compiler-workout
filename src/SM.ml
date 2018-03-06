open GT     
open List  
open Language
       
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
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval (stack, (state, instream, outstream)) program = match program with
      | [] -> (stack, (state, instream, outstream))
     | instruction1 :: instruction2-> match instruction1 with
          | CONST c -> eval (c :: stack, (state, instream, outstream)) instruction2
          | READ -> eval (hd instream :: stack, (state, tl instream, outstream)) instruction2
          | WRITE -> eval (tl stack, (state, instream, outstream @ [hd stack])) instruction2
          | LD variable -> eval (state variable :: stack, (state, instream, outstream)) instruction2
          | ST variable -> eval (tl stack, (Expr.update variable (hd stack) state, instream, outstream)) instruction2
          | BINOP binoperation -> 
               let b :: a :: tlstack = stack in
               let res = Expr.eval state (Expr.Binop (binoperation, Expr.Const a, Expr.Const b)) in
               eval (res :: tlstack, (state, instream, outstream)) instruction2
  
  
(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler
     val compile : Language.Stmt.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
  let rec compileExpression expression = match expression with
      | Expr.Const value -> [CONST value]
      | Expr.Var variable -> [LD variable]
      | Expr.Binop (operation, a, b) -> (compileExpression a) @ (compileExpression b) @ [BINOP operation]
  

  let rec compile stmt = match stmt with
      | Stmt.Read v -> [READ; ST v]
      | Stmt.Write expression -> (compileExpression expression) @ [WRITE]
      | Stmt.Assign (variable, expression) -> (compileExpression expression) @ [ST variable]
      | Stmt.Seq (state1, state2) -> (compile state1) @ (compile state2)
