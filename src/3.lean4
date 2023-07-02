/-
Prove the following theorems using rfl: 2 + 3 = 5, 15 - 8 = 7,
 "Hello, ".append "world" = "Hello, world". 
 What happens if rfl is used to prove 5 < 18? Why?
-/

example: 2 + 3 = 5 := rfl

example: 15 - 8 = 7 := rfl

example: "Hello, ".append "world" = "Hello, world" := rfl

--example: 5 < 18 := rfl --fails due to type mismatch

/-
Prove the following theorems using by simp:
 2 + 3 = 5, 15 - 8 = 7, "Hello, ".append "world" = "Hello, world", 5 < 18.
-/

example : 2 + 3 = 5 := by simp
example : 15 - 8 = 7 := by simp
example : "Hello, ".append "world" = "Hello, world" := by simp
example : 5 < 18 := by simp

/-
Write a function that looks up the fifth entry in a list.
Pass the evidence that this lookup is safe as an argument to the function.
-/

def fifth (l : List α) (h : l.length > 5) : α := l[5]
