/-
Rewrite evaluateM, its helpers, and the different specific
use cases using do-notation instead of explicit calls to >>=.
-/


inductive Expr (op : Type) where
| const : Int → Expr op
| prim : op → Expr op → Expr op → Expr op

inductive Arith where
| plus
| minus
| times
| div

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))


def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int): Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2