
/-
Define an instance of HMul (PPoint α) α (PPoint α) that multiplies both
projections by the scalar. It should work for any type α for which there
is a Mul α instance. For example,
#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
should yield
{ x := 5.000000, y := 7.400000 }
-/

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def PPoint.scalarMul [Mul α] (p : PPoint α) (s : α) : PPoint α :=
{x := p.x * s, y := p.y * s}

instance {α : Type} [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul := PPoint.scalarMul

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
#eval (⟨5, 6⟩ : PPoint Nat) * 2