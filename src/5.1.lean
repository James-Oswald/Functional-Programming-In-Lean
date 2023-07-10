/-
Define a function BinTree.mapM. By analogy to mapM for lists,
this function should apply a monadic function to each data 
entry in a tree, as a preorder traversal. The type signature
should be:

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
-/

inductive BinTree (α : Type) where
| leaf : BinTree α
| branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
| leaf => pure leaf
| branch b1 v b2 =>         --Preorder traversal
  f v >>= fun nv =>         --root
  mapM f b1 >>= fun nb1 =>  --left
  mapM f b2 >>= fun nb2 =>  --right
  pure (branch nb1 nv nb2)

/-
First, write a convincing argument that the Monad instance for
Option satisfies the monad contract. Then, consider the
following instance:

instance : Monad Option where
  pure x := some x
  bind opt next := none

Both methods have the correct type. Why does this instance
violate the monad contract?
-/

--Correct instance
instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

#check Pure.pure
#check Bind.bind
#check Monad Option
--#eval pure (some 3 : Option Nat)

--I can't prove the monad contract :(
example [Monad m] (f : Option α → m (Option α)) (o : Option α):
bind (pure o) f = f o := by
  simp [Monad]
  sorry


