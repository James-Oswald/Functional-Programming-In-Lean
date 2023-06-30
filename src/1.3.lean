def joinStringsWith (s1 s2 s3 : string) : string :=
(string.append s2 (string.append s1 s3))

#eval joinStringsWith ", " "one" "and another"
#check joinStringsWith

def volume (h w d : ℕ) : ℕ := h * w * d

#check volume

def NaturalNumber : Type := ℕ
def thirtyEight : NaturalNumber := (38 : nat)
