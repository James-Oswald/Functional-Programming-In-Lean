
def linearSearchRecur [DecidableEq α] : List α -> α -> Nat -> Option Nat 
| [], _, _ => Option.none
| h :: t, e, i => 
if h = e then 
  Option.some i 
else 
  linearSearchRecur t e (i + 1)
  
def linearSearch [DecidableEq α] 
(list : List α) (element : α) : Option Nat :=
linearSearchRecur list element 0

--Linear search will only return an index in the list
theorem indexInRange [DecidableEq α] (l : List α) (e : α) (n : Nat) 
: linearSearch l e = Option.some n -> n < List.length l :=
by{
  intro H;
  rw [linearSearch] at H;
  induction l;
  {
    rw [linearSearchRecur] at H;
    contradiction
  };{
    rw [linearSearchRecur] at H;
    
  }
}

theorem linearSearchCorrect [DecidableEq α] (l : List α) (e : α) (n : Nat): 
linearSearch l e == Option.some n <-> l[n] == e ∧ ¬∃ (m : Nat), m < n -> l[m] == e 
:= by{

}  