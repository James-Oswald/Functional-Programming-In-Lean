/-
What are the values of the following expressions? Work them out by hand, then enter them into Lean to check your work.

42 + 19
String.append "A" (String.append "B" "C")
String.append (String.append "A" "B") "C"
if 3 == 3 then 5 else 7
if 3 == 4 then "equal" else "not equal"
-/

#eval 42 + 19
#eval String.append "A" (String.append "B" "C")
#eval String.append (String.append "A" "B") "C"
#eval if 3 = 3 then 5 else 7
#eval if 3 = 4 then "equal" else "not equal"