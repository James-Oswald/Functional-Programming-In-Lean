/-
An alternative way to represent a positive number is as the successor of some Nat.
Replace the definition of Pos with a structure whose constructor is named succ
that contains a Nat:

structure Pos where
  succ ::
  pred : Nat

Define instances of Add, Mul, ToString, and OfNat that
allow this version of Pos to be used conveniently.
-/

structure Pos where
  succ ::
  pred : Nat

def Pos.plus (a b : Pos) : Pos := succ (a.pred + b.pred + 1)

def Pos.times (a b : Pos) : Pos := succ (((a.pred + 1) * (b.pred + 1)) - 1)

def Pos.str (a : Pos) : String := toString (a.pred + 1)

def Pos.toNat (a : Nat) : Pos := succ (a - 1) 

instance : Add Pos where
  add := Pos.plus

instance : Mul Pos where
  mul := Pos.times

instance : ToString Pos where
  toString := Pos.str

instance : OfNat Pos n where
  ofNat := Pos.toNat n

#eval (2 : Pos) + (3 : Pos)
#eval (2 : Pos) * (3 : Pos)
#eval (5 : Pos) * (100 : Pos)

--Checks out since 0 - 1 for Nats is 0 -> thus Pos ofNat 0 = 1 
#eval (0 : Pos) + (0 : Pos)

/-
Define a datatype that represents only even numbers.
Define instances of Add, Mul, and ToString that allow it to be used conveniently.
OfNat requires a feature that is introduced in the next section.
-/

inductive Even : Type where
| zero : Even
| next : Even -> Even

def Even.add : Even -> Even -> Even
| n, Even.zero => n  
| n, (Even.next m) => Even.next (Even.add n m)

instance : Add Even where
  add := Even.add

def Even.mul : Even -> Even -> Even
| _, Even.zero => Even.zero 
| n, (Even.next m) => n + n + (Even.mul n m)

instance : Mul Even where
  mul := Even.mul

def Even.toNat : Even -> Nat
| Even.zero => 0
| Even.next n => (Even.toNat n) + 2

--Messing around defining this with function composition 
def Even.str : Even -> String := (@toString Nat _) ∘ Even.toNat

instance : ToString Even where
  toString := Even.str 

def ezero := (Even.zero)
def etwo := (Even.next (Even.zero))
def efour := (Even.next (Even.next (Even.zero)))

#eval ezero
#eval etwo
#eval efour
#eval etwo + etwo
#eval etwo * etwo
#eval etwo + efour
#eval efour * efour

--The HTTP one is too much work