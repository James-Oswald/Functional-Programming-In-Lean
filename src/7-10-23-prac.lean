
#check 1 = 1

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

#eval linearSearch [1,2,3,4] 2
#eval linearSearch [1,2,3,4] 5
#check Not

theorem l2: ∀(e : α), e ∈ ([] : List α) -> False :=
by{
  intros e H{
    cases H
  }
}

theorem l3: ∀(p : Prop), ¬¬p -> p :=
by{
  intros p H{
    rewrite [Not, Not] at H
    apply Classical.byContradiction{
      intros np{
        apply H{
          intros{
            contradiction
          }
        }
      }
    }
  }
}  

theorem l4 [DecidableEq α] (t : List α) (h e : α) :
e ∈ h :: t -> e = h ∨ e ∈ t
:= by {
  unhygienic
  intros H{
    cases H{
      simp
    }{
      apply Or.inr{
        exact a_1
      } 
    }
  }
}

theorem l5 [DecidableEq α] (t : List α) (h e : α) :
e ∉ h :: t -> e ≠ h ∧ e ∉ t
:= by {
  sorry
}

theorem l1 [DecidableEq α] (l : List α) (e : α) :
linearSearch l e = none → e ∉ l :=
by{
  unhygienic
  rw [linearSearch]
  induction l{
    rw [linearSearchRecur]
    simp
    apply @Classical.byContradiction (¬e ∈ []){
      intros H {
        have H2 := l3 (e ∈ []) H{
          cases H2
        }
      }
    }
  }{
    intros H{
      rw [linearSearchRecur] at H
      cases Classical.em (head = e){
        simp [h] at H
      }{
        simp [h] at H
        sorry
      }
    }
  }
} 

example [DecidableEq α] (l : List α) (e : α) :
(∃ (i : Nat), linearSearch l e = Option.some i) ∨
linearSearch l e = Option.none :=
by{
  unhygienic
  rw [linearSearch]
  induction l{
    rw [linearSearchRecur]
    simp
  }{
    rw [linearSearchRecur]
    cases Classical.em (head = e){
      rw [if_pos]
      apply Or.inl{
        apply Exists.intro 0{
          rfl
        }
      }
      exact h
    }{
      rw [if_neg]
      cases tail_ih{
        sorry
      }{
        sorry
      }
      exact h
    }
  }
}

-- by {
--   unhygienic
--   rw [linearSearch]
--   induction l with
--   | nil => rw [linearSearchRecur] simp
--   | cons h t => {
--     rw [linearSearchRecur]
--     cases tail_ih{
--       cases h_1{
--         cases Classical.em (h = e){
--           apply Or.inl{
--             apply Exists.intro 0{
--               rw [if_pos]
--               exact h_1
--             }
--           }
--         }{
--           apply Or.inl{
            
--           }
--         } 
--       }
--     }
    
--   }
-- }