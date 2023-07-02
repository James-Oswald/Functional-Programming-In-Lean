
--Write a function to find the last entry in a list. It should return an Option.

def last : List α -> Option α
| [] => Option.none
| [e] => Option.some e
| _ :: t => last t

--Write a function that finds the first entry in a list that satisfies a
-- given predicate. Start the definition with 
-- def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := 
match xs with
| [] => Option.none
| h :: t => if predicate h then Option.some h else List.findFirst? t predicate

--Write a function Prod.swap that swaps the two fields in a pair.
--Start the definition with
-- def Prod.swap {α β : Type} (pair : α × β) : β × α :=

def Prod.swap {α β : Type} (pair : α × β) : β × α :=
Prod.mk pair.snd pair.fst

#eval Prod.swap ⟨`a, `b⟩  

/-
Rewrite the PetName example to use a custom datatype and compare
it to the version that uses Sum.
-/

--Original
def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

--Custom
inductive PetNameCustom : Type
| catName : String -> PetNameCustom
| dogName : String -> PetNameCustom

def animalsCustom : List PetNameCustom :=
  [PetNameCustom.dogName "Spot",
   PetNameCustom.catName "Tiger",
   PetNameCustom.dogName "Fifi",
   PetNameCustom.dogName "Rex", 
   PetNameCustom.catName "Floof"]

def howManyDogsCustom (pets : List PetNameCustom) : Nat :=
  match pets with
  | [] => 0
  | PetNameCustom.dogName _ :: morePets => howManyDogsCustom morePets + 1
  | PetNameCustom.catName _ :: morePets => howManyDogsCustom morePets

/-
Write a function zip that combines two lists into a list of pairs.
The resulting list should be as long as the shortest input list.
Start the definition with 
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=.
-/

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
match xs, ys with
| [], [] => []
| [], _ => []
| _, [] => []
| h1 :: t1, h2 :: t2 => List.cons ⟨h1,h2⟩ (zip t1 t2)

#eval zip [1,2,3,4] [5,6,7,8,9]

/-
Write a polymorphic function take that returns the first n
 entries in a list, where n
 is a Nat. If the list contains fewer than n entries, then the
resulting list should be the input list. 
#eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"],
 and #eval take 1 ["bolete", "oyster"] should yield ["bolete"].
-/

def take : Nat -> List α -> List α
| _, [] => []
| 0, _ :: _ => []
| n + 1, h :: t => h :: (take n t)

#eval take 3 ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"]


--TODO: Revist these two I don't fully get what this is asking
/-
Using the analogy between types and arithmetic, write a function that
distributes products over sums. In other words, it should have
type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).
-/

--def prodOverSum {α β γ : Type} (t : α × (β ⊕ γ)) : _ := 
--Sum (Prod t.fst t.snd.inl) (Prod t.fst t.snd.inr)


def prodOverSum {α β γ : Type} : Prod α (Sum β γ) → Sum (Prod α β) (Prod α γ) :=
sorry

/-
Using the analogy between types and arithmetic, write a function that turns
multiplication by two into a sum. In other words,
it should have type Bool × α → α ⊕ α.
-/

def multsum (a : Prod Bool α) : Sum α α :=
sorry

