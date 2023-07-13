
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

--Type class, takes a Type and returns a type
#check Add      --Type -> Type
#check Add Nat  --Type
--Each instance of the type has a diffrent version
--of the add method, allowing for overrieds
#check @Add.add Nat
#check @Add.add (PPoint Nat)
--To select which varient of Add.add the first type
--paramter is used. The [self : Add α] 
--enforces that an instance for Add α has been created
--and finds it and uses it. 

--Monad takes a map of types from U1 to U2 and maps them to
--A new type in U=max(U1+1, U2) 
#check Option
#check Monad Option
#check Monad List 





#check Option Empty
#check @Option.some Empty


inductive BOption (α : Type) : Type
| none : BOption α
| some : α -> BOption α

instance : Monad BOption where
  pure arg := BOption.some arg
  bind _ _ := BOption.none

def monadContract (m : Type → Type) (α β : Type) [Monad m] : Prop :=
-- pure should be a left identity of bind
(∀(f : α → m β) (v : α), bind (pure v) f = f v) ∧ 
--pure should be a right identity of bind
(∀(v : m α), bind v pure = v) ∧
--bind should be associative
(∀(v : m α) (f : α → m β) (g : β → m α), 
  bind (bind v f) g = bind v (fun x => bind (f x) g))

#check BOption Empty
#check @BOption.some Empty
#check @Empty.rec

example : monadContract BOption Empty β := by{
  unhygienic
  rw [monadContract];
  apply And.intro;{
    intros f v;
    rw [pure, Applicative.toPure, Monad.toApplicative, instMonadBOption]
    simp
    rw [bind, Monad.toBind]
    simp
    --follows from empty type
    trivial
  }
  apply And.intro;
  {
    intros v;
    rw [pure, Applicative.toPure, Monad.toApplicative, instMonadBOption]
    simp
    rw [bind, Monad.toBind]
    simp
    --v can only be BOption.none
    cases v;
    --follows from empty type
    simp [Empty.rec]
    trivial;
  }
  {
    intros v f g;
    rw [bind, Monad.toBind, instMonadBOption];
  }
}

--example: ∀ (φ : Prop) (x : Empty), ¬φ ∧ φ := by apply Empty.rec 