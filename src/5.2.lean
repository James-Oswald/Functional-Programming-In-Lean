
/- Check the monad contract for State σ and Except ε. -/

/- The monad contract -/
def monadContract (m : Type → Type) (α β : Type) [Monad m] : Prop :=
-- pure should be a left identity of bind
(∀(f : α → m β) (v : α), bind (pure v) f = f v) ∧ 
--pure should be a right identity of bind
(∀(v : m α), bind v pure = v) ∧
--bind should be associative
(∀(v : m α) (f : α → m β) (g : β → m α), 
  bind (bind v f) g = bind v (fun x => bind (f x) g))

/-
State represents 
-/
def State (σ : Type) (α : Type) : Type := σ → (σ × α)

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s 
      next x s'

example {α β σ : Type} : monadContract (State σ) α β := by{
  rw [monadContract];
  apply And.intro;{
    intros f;
    rw [pure, Applicative.toPure, Monad.toApplicative,
      instMonadState_1]
    simp
    intro v;
    rw [bind, Monad.toBind]
  }
  apply And.intro;{
    intro v;
    rw [bind, Monad.toBind, instMonadState_1]
    simp
    rw [pure, Applicative.toPure, Monad.toApplicative]
  };{
    intro v f g;
    rw [bind, Monad.toBind, instMonadState_1]
  }
}

inductive CExcept (ε : Type) (α : Type) where
  | error : ε → CExcept ε α
  | ok : α → CExcept ε α
deriving BEq, Hashable, Repr

instance : Monad (CExcept ε) where
  pure x := CExcept.ok x
  bind attempt next :=
    match attempt with
    | CExcept.error e => CExcept.error e
    | CExcept.ok x => next x

example {α β σ : Type} : monadContract (CExcept ε) α β := by{
  rw [monadContract];
  apply And.intro;{
    intros f;
    rw [pure, Applicative.toPure, Monad.toApplicative,
      instMonadCExcept]
    simp
    intro v;
    rw [bind, Monad.toBind]
  }
  apply And.intro;{
    intro v;
    rw [bind, Monad.toBind, instMonadCExcept]
    simp
    cases v;
    rw [pure, Applicative.toPure, Monad.toApplicative]
    simp
    rw [pure, Applicative.toPure, Monad.toApplicative]
  };{
    intro v f g;
    rw [bind, Monad.toBind, instMonadCExcept]
    simp;
    cases v;
    simp;
    simp;
  }
}

/-
Adapt the reader monad example so that it can also indicate failure
when the custom operator is not defined, rather than just returning
zero. In other words, given these definitions:

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

do the following:
1) Write suitable pure and bind functions
2) Check that these functions satisfy the Monad contract
3) Write Monad instances for ReaderOption and ReaderExcept
4) Define suitable applyPrim operators and test them with
   evaluateM on some example expressions
-/

--TODO



