
/-
Write a function to find the last entry in a list.
It should return an Option.
-/

def last : List α -> Option α
| [] => Option.none
| [e] => Option.some e
| _ :: t => last t

/-
Write a function that finds the first entry in a list
that satisfies a given predicate. Start the definition with 
def List.findFirst? {α : Type} (xs : List α)
 (predicate : α → Bool) : Option α :=
-/
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := 
match xs with
| [] => Option.none
| h :: t => if predicate h then Option.some h else List.findFirst? t predicate

/-
Write a function Prod.swap that swaps the two fields in a pair.
Start the definition with
def Prod.swap {α β : Type} (pair : α × β) : β × α :=
-/
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
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
   Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals

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

def PetNameCustom.howManyDogs (pets : List PetNameCustom) : Nat :=
  match pets with
  | [] => 0
  | dogName _ :: morePets => howManyDogs morePets + 1
  | catName _ :: morePets => howManyDogs morePets

#eval PetNameCustom.howManyDogs animalsCustom

/-
Write a function zip that combines two lists into a list of pairs.
The resulting list should be as long as the shortest input list.
Start the definition with 
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=.
-/

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
match xs, ys with
| [], _ => []
| _, [] => []
| h1 :: t1, h2 :: t2 => List.cons ⟨h1,h2⟩ (zip t1 t2)

#eval zip [1,2,3,4] [5,6,7,8,9]
#eval zip [1,2,3,4,5,6,7,8,9] [5,6,7,8,9]
#eval zip ([] : List Nat) ([] : List Nat)

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

/-
Using the analogy between types and arithmetic, write a function that
distributes products over sums. In other words, it should have
type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).
-/

--I think im doing something I shouldn't be... I wrote a proof of the type but via 
--via the Curry–Howard correspondence this is a function (or something like that). doing
--#print prodOverSum seems to agree with me.
def prodOverSumProofVersion : α × (β ⊕ γ) → (α × β) ⊕ (α × γ) :=
by{
  unhygienic --I love unhygienic tho :)
  intros H;
  cases H;
  cases snd;
  have H2 : α × β := Prod.mk fst val;
  apply Sum.inl;
  exact H2;
  have H2 : α × γ:= Prod.mk fst val;
  apply Sum.inr;
  exact H2;
}

#print prodOverSumProofVersion
#check Sum

--Ok just kidding now for the real version, unsure how you're supposted to figure
--this out this early in the book, there must be an easier way.
def prodOverSum : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
| (a, (Sum.inl b)) => @Sum.inl _ (α × γ) (Prod.mk a b)
| (a, (Sum.inr g)) => @Sum.inr _ (α × γ) (Prod.mk a g)

/-
Using the analogy between types and arithmetic, write a function that turns
multiplication by two into a sum. In other words,
it should have type Bool × α → α ⊕ α.
-/

def multsumProofVersion: Bool × α -> α ⊕ α := by{
  unhygienic
  intro H;
  cases H;
  apply Sum.inr;
  exact snd;
}

def multSum: Bool × α -> α ⊕ α
| (true, a) => @Sum.inl _ α a  
| (false, a) => @Sum.inr _ α a 
