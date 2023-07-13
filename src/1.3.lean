/-
Define the function joinStringsWith with type
String -> String -> String -> String that creates a
new string by placing its first argument between its
second and third arguments.
joinStringsWith ", " "one" "and another"
should evaluate to 
"one, and another".
-/

def joinStringsWith (s1 s2 s3 : String) : String :=
(String.append s2 (String.append s1 s3))

#eval joinStringsWith ", " "one" "and another"
#check (joinStringsWith)
#check joinStringsWith

/-
What is the type of joinStringsWith ": "?
Check your answer with Lean.
-/

--String->String->String

#check joinStringsWith ": "

/-
Define a function volume with type Nat → Nat → Nat → Nat
that computes the volume of a rectangular prism with the
given height, width, and depth.
-/

def volume (h w d : Nat) : Nat := h * w * d

#check volume

--scratchpad
def NaturalNumber : Type := Nat 
def thirtyEight : NaturalNumber := (38 : Nat)
