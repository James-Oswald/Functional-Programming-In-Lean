
/-
Write an instance of OfNat for the even number datatype from the
previous section's exercises that uses recursive instance search.
For the base instance, it is necessary to write OfNat Even Nat.zero
instead of OfNat Even 0.
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

--Ok time for the real exersize
--Its not entirely clear to me what recursive instance search is used for in this example
--Even does not depend on a type the way point does in the examples
def Even.fromNat : Nat -> Even
| Nat.zero => Even.zero
| (Nat.succ Nat.zero) => Even.zero
| (Nat.succ (Nat.succ n)) => Even.next (Even.fromNat n)

instance: OfNat Even n where
ofNat := Even.fromNat n

#eval (0 : Even)
#eval (1 : Even) --rounds down to nearest even
#eval (2 : Even)
#eval (3 : Even) --rounds down to nearest even
#eval (4 : Even)
#eval (8 : Even)
#eval (8 : Even) + (8 : Even)
#eval (8 : Even) * (8 : Even)


/-
There is a limit to how many times the Lean compiler will attempt a recursive
instance search. This places a limit on the size of even number literals
defined in the previous exercise. Experimentally determine what the limit is.
-/
--I didn't need a recursive instance search, just going to check how big
--i can get it b4 it crashes

--#eval (22222 : Even) --stack overflow
#eval (2222 : Even) --fine
#eval (5000 : Even) --fine
#eval (10000 : Even) --fine
--#eval (20000 : Even) --stack overflow
--#eval (15000 : Even) --stack overflow
--#eval (12500 : Even) --stack overflow
--#eval (11250 : Even) --stack overflow
--#eval (10625 : Even) --stack overflow
#eval (10312 : Even) --fine
#eval (10312 : Even) --fine
#eval (10600 : Even) --fine
--#eval (10620 : Even) --stack overflow
#eval (10610 : Even) --fine
#eval (10614 : Even) --fine
#eval (10614 : Even) --fine
--#eval (10616 : Even) --stack overflow

--Limit is 10614