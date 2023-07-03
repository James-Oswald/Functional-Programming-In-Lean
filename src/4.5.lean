
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr
/-
Write an instance of HAppend (List α) (NonEmptyList α) (NonEmptyList α)
and test it.
-/

def NonEmptyList.prependListFront : List α -> NonEmptyList α -> NonEmptyList α
| [], nel => nel
| lh :: lt, ⟨nh, []⟩ => ⟨lh, lt ++ [nh]⟩ --kind of feels like cheating lol
| lh :: lt, ⟨nh, nt⟩ => ⟨lh, lt ++ [nh] ++ nt⟩ 

instance : HAppend (List α) (NonEmptyList α) (outParam (NonEmptyList α)) where
  hAppend := NonEmptyList.prependListFront


#eval (⟨1, [2, 3] ⟩ : NonEmptyList Nat)
#eval ([] : List Nat) ++ (⟨1, [2, 3] ⟩ : NonEmptyList Nat)
#eval [1, 2, 3] ++ (⟨4, [5, 6]⟩ : NonEmptyList Nat)
#eval [1, 2, 3] ++ (⟨4, []⟩ : NonEmptyList Nat)

/-
Implement a Functor instance for the binary tree datatype.
-/

--Unsure why they decided to go with a bin tree with no values on leafs, kind of dumb tbh
inductive BinTree (α : Type) where
| leaf : BinTree α
| branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.map {α β : Type} (f : α → β) : BinTree α → BinTree β
| leaf => leaf
| branch b1 v b2 => branch (map f b1) (f v) (map f b2)

instance : Functor BinTree where
  map := BinTree.map

#check (· + 1)
#eval (· + 5) <$> (BinTree.branch 
                    (BinTree.branch (BinTree.leaf) 2 (BinTree.leaf)) 
                    1 
                    (BinTree.branch (BinTree.leaf) 3 (BinTree.leaf)))

