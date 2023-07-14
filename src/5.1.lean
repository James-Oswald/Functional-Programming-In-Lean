/-
Define a function BinTree.mapM. By analogy to mapM for lists,
this function should apply a monadic function to each data 
entry in a tree, as a preorder traversal. The type signature
should be:

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
-/

inductive BinTree (α : Type) where
| leaf : BinTree α
| branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
| leaf => pure leaf
| branch b1 v b2 =>         --Preorder traversal
  f v >>= fun nv =>         --root
  mapM f b1 >>= fun nb1 =>  --left
  mapM f b2 >>= fun nb2 =>  --right
  pure (branch nb1 nv nb2)

/-
First, write a convincing argument that the Monad instance for
Option satisfies the monad contract. Then, consider the
following instance:

instance : Monad Option where
  pure x := some x
  bind opt next := none

Both methods have the correct type. Why does this instance
violate the monad contract?
-/

/-
My convincing argument is a proof in lean that it satisfies the monad contract.
I start by defining a custom version of option and the "legal" monad instance for it.
-/

inductive COption (α : Type) : Type
| none : COption α
| some : α -> COption α

instance : Monad COption where
pure arg := COption.some arg
bind item func := 
  match item with
  | COption.none => COption.none
  | COption.some arg => func arg

/-
Definition of the moand contract as translated from the section in the book
-/
def monadContract (m : Type → Type) (α β : Type) [Monad m] : Prop :=
-- pure should be a left identity of bind
(∀(f : α → m β) (v : α), bind (pure v) f = f v) ∧ 
--pure should be a right identity of bind
(∀(v : m α), bind v pure = v) ∧
--bind should be associative
(∀(v : m α) (f : α → m β) (g : β → m α), 
  bind (bind v f) g = bind v (fun x => bind (f x) g))

--Prove COption satisfies the monad contract
example {α β : Type}: monadContract COption α β 
:= by{
  rw [monadContract]
  apply And.intro;{
    --left identity
    intros f v;
    rw [pure, Applicative.toPure, Monad.toApplicative,
      instMonadCOption]
    simp
    --rw [bind, Monad.toBind]
  }
  apply And.intro;{
    --right identity
    intros v;
    rw [bind, Monad.toBind, instMonadCOption]
    simp;
    cases v;{
      trivial;
    };{
      trivial;
    }
  };{
    --associative
    intros v f g;
    rw [bind, Monad.toBind, instMonadCOption];
    simp;
    cases v;{
      trivial;
    };{
      trivial;
    }
  }
}

/-
Part 2: Why does this instance
violate the monad contract?

Start by defining the new instance
-/
inductive BOption (α : Type) : Type
| none : BOption α
| some : α -> BOption α

instance : Monad BOption where
  pure arg := BOption.some arg
  bind _ _ := BOption.none

/-
Helper theorem for double negation elim
because I was too lazy to look for this
-/
theorem L2: ∀(p : Prop), ¬¬p <-> p :=
by{
  intro p;
  apply Iff.intro;{
    intro H;
    rewrite [Not, Not] at H;
    apply Classical.byContradiction;
    intros np;
    apply H;
    intro;
    contradiction;
  };{
    intro H;
    rewrite [Not, Not];
    intro H2;
    apply H2;
    exact H;
  }
}  

/-
To prove that BOption voilates the monad contract we must show there exists 
some conditions under which it is false, we will show that for every α
other than Empty, BOption voilates the monad contract. We will also
show that it holds when α is empty. 
-/

--The monad contract does hold when α is empty
example : monadContract BOption Empty β := by{
  unhygienic
  rw [monadContract];
  apply And.intro;{
    intros f v;
    rw [pure, Applicative.toPure, Monad.toApplicative, instMonadBOption]
    simp
    --rw [bind, Monad.toBind]
    simp
    --follows from empty type
    trivial
  }
  apply And.intro;
  {
    intros v;
    rw [pure, Applicative.toPure, Monad.toApplicative, instMonadBOption]
    simp
    --rw [bind, Monad.toBind]
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

--Proof that B violates the monad contract for all non-empty types
example {α β : Type} [iα : Nonempty α]:
¬monadContract BOption α β 
:= by{
  unhygienic
  apply Classical.byContradiction _;
  intros H;
  rw [L2] at H;
  rw [monadContract] at H;
  cases H;
  cases right;
  have H2 := left_1 (BOption.some (Classical.choice iα));
  rw [bind, Monad.toBind, instMonadBOption] at H2;
  simp at H2;
}



--Some scratch work and wrong directions in no particular order

--===========================================================

-- example {α β : Type} [iβ : Nonempty β] [iα : Nonempty α]:
-- ¬monadContract BOption α β 
-- := by{
--   rw [monadContract]
--   apply @Classical.byContradiction _;
--   intro H;
--   rw [L2] at H;

-- }


-- --If BOption satisfies the monad contract α is nonempty
-- theorem monadNonempty :
-- monadContract BOption α β -> Nonempty α 
-- := by{
--   unhygienic
--   intros H;
--   apply Classical.byContradiction;
--   intro H2;
--   have H3 : Empty = α := sorry;
--   rw [monadContract] at H;
--   cases H;
--   cases right;

--   -- rw [monadContract] at H;
--   -- have fw : α -> BOption β := fun (_ : α) => BOption.none;
--   -- have 
-- }

-- example (f : α → BOption β) (o : α):
-- bind (pure o) f ≠ f o := by{
  
-- }


-- example [instB: Nonempty β] (f : α → BOption β) (o : α):
-- bind (pure o) f = f o := by{
--   rw [pure, Applicative.toPure, Monad.toApplicative,
--    instMonadBOption]
--   simp
--   rw [bind, Monad.toBind]
--   simp
--   --There exists some function for which
--   --BOption.none ≠ f o
--   have b : β := @Classical.choice β instB{
--     have f1 := (fun (a : α) => BOption.some b){
--       sorry
--     }
--   }
-- }

--Proof that the default instance of Option satisfies the
--monad contract (or at least part of it lmao)
example (f : α → COption β) (o : α):
bind (pure o) f = f o := by{
  rw [pure, Applicative.toPure, Monad.toApplicative,
   instMonadCOption]
  simp
  --rw [bind, Monad.toBind]
}

--Again but using a dedicated Prop so i can prove the
--2nd part of the problem
def monadContractLeft (m : Type → Type) (α β : Type) [Monad m] : Prop :=
∀ (f : α → m β) (o : α), bind (pure o) f = f o

#check @monadContract

--COption satisfies the monad contract
example {α β : Type}: monadContractLeft COption α β
:= by{
  rw [monadContractLeft, pure, Applicative.toPure,
      Monad.toApplicative, instMonadCOption]
  simp
  --rw [bind, Monad.toBind]
  --simp
}

#check Exists.intro

--Some random lemmas I was using for this

--This is such a jank proof of this lmao
theorem L1 (α : Type) (p : α->Prop) :
(¬∀(x : α),p x) <-> (∃(x : α),¬(p x))
:= by{
  rw [Not];
  apply Iff.intro;{
    intro H;
    apply Classical.byContradiction;
    intro H2;
    rw [Not] at H2;
    apply H;
    intro x;
    apply Classical.byContradiction;
    intro H3;
    apply H2;
    apply Exists.intro x;
    exact H3;
  };{
    intros H1 H2;
    apply Exists.elim H1;
    intros x npx;
    have H3 := H2 x;
    trivial
  }
} 

--weaker version of 

--Proof BOption does not satisfy the monad contract. I'm 
--only able to prove this so far assuming β and α are nonempty types
example {α β : Type} [iβ : Nonempty β] [iα : Nonempty α]:
¬monadContractLeft BOption α β
:= by{
  rw [monadContractLeft];
  rewrite [L1];
  have b := @Classical.choice β iβ;
  let f1 := (fun (_ : α) => BOption.some b);
  apply Exists.intro f1;
  rewrite [L1];
  have a := @Classical.choice α iα;
  apply Exists.intro a;
  rw [Not]
  intro H;
  rw [pure, Applicative.toPure,
      Monad.toApplicative, instMonadBOption] at H;
  simp at H;
}

--This is false, monadContract BOption Empty β holds
-- example {α β : Type}:
-- ¬monadContract BOption α β 
-- := by{
--   unhygienic
--   apply Classical.byContradiction _;
--   intros H;
--   rw [L2] at H;
--   rw [monadContract] at H;
--   cases H;
--   cases right;
--   cases Classical.em (Nonempty α);
--   cases Classical.em (Nonempty β);
--   {
--     have H2 := left_1 (BOption.some (Classical.choice h));
--     rw [bind, Monad.toBind, instMonadBOption] at H2;
--     simp at H2;
--   }{
--     have H2 := left_1 (BOption.some (Classical.choice h));
--     rw [bind, Monad.toBind, instMonadBOption] at H2;
--     simp at H2;
--   }{

--   }
-- }