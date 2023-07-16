
-- α is the type of atomic predicates
inductive NDFormula (α : Type) : Type
| prop : α -> NDFormula α
| and : NDFormula α -> NDFormula α -> NDFormula α
| or : NDFormula α -> NDFormula α -> NDFormula α
| not : NDFormula α -> NDFormula α
| imp : NDFormula α -> NDFormula α -> NDFormula α
| iff : NDFormula α -> NDFormula α -> NDFormula α

/-
Any type can be coerced to an atomic predicate of that type
-/
instance: Coe α (NDFormula α) where
coe a := NDFormula.prop a

/-
A standalone ND formula can be coreced to a list of ND formulae with 1 elm
-/
instance: Coe (NDFormula α) (List (NDFormula α)) where
coe a := [a]

notation:max "¬ₙ" p:40 => NDFormula.not p
infixr:35 " ∧ₙ " => NDFormula.and
infixr:30 " ∨ₙ " => NDFormula.or
infixr:25 " →ₙ " => NDFormula.imp
infixr:25 " ->ₙ " => NDFormula.imp
infixr:20 " ↔ₙ " => NDFormula.iff
infixr:20 " <->ₙ " => NDFormula.iff

def test : NDFormula String := "a" ∧ₙ "b" ->ₙ "c"

/-
An interpetation satisfies a given formula
-/
def NDFormula.sat (interpretation : α -> Prop) (formula : NDFormula α) : Prop :=
let i := interpretation
match formula with
  | prop a => interpretation a
  | and f1 f2 => sat i f1 ∧ sat i f2
  | or f1 f2 => sat i f1 ∨ sat i f2
  | not f => ¬sat i f
  | imp f1 f2 => sat i f1 -> sat i f2
  | iff  f1 f2 => sat i f1 <-> sat i f2

infix:15 " ⊨ₙ " => NDFormula.sat
infix:15 " |=ₙ " => NDFormula.sat

/-
A formula of a formal language is a valid formula if and only if it
is true under every possible interpretation of the language.
In propositional logic, they are tautologies.
-/
def NDFormula.valid (formula : NDFormula α) : Prop := 
∀ (interpretation : α -> Prop), NDFormula.sat interpretation formula

prefix:15 " ⊨ₙ  " => NDFormula.valid
prefix:15 " |=ₙ " => NDFormula.valid

example : ⊨ₙ a ∧ₙ b ->ₙ a := 
by{
  rw [NDFormula.valid];
  intro i;
  rw [NDFormula.sat];
  intros H;
  rw [NDFormula.sat] at H;
  cases H;
  trivial;
}

--A simple sequent conditional in the form assumptions ⊢ formula
--see https://en.wikipedia.org/wiki/Sequent#The_form_and_semantics_of_sequents
structure Sequent (α  : Type) where
assumptions : List (NDFormula α) 
formula : NDFormula α

infix:15 " ⊢ₙ " => Sequent.mk
infix:15 " |-ₙ " => Sequent.mk


def Sequent.sat (interpretation : α -> Prop) (sequent : Sequent α) : Prop :=
(∀ (a : NDFormula α), a ∈ sequent.assumptions -> NDFormula.sat interpretation a) ->
NDFormula.sat interpretation sequent.formula

def Sequent.valid (sequent : Sequent α) : Prop :=
∀ (interpretation : α -> Prop), Sequent.sat interpretation sequent

theorem trivialListMembership (e : α) : e ∈ [e] := 
by{
  rw [Membership.mem, List.instMembershipList];
  apply List.Mem.head;
}

example: Sequent.valid (a ∧ₙ b ⊢ₙ a) 
:= by{
  rw [Sequent.valid];
  intro i;
  rw [Sequent.sat];
  intro H;
  have H2 := H (a ∧ₙ b);
  simp at H2;
  have H3 : (a ∧ₙ b) ∈ [a ∧ₙ b] := by apply trivialListMembership;
  have H4 := H2 H3;
  rw [NDFormula.sat] at H4;
  cases H4;
  simp;
  trivial;
}

/-
An infrence rule in natural deduction is a list of premicie sequents
which lead to a conclusion. Aditional restrictions may appear
on the formulae structure or on assumptions via the sequents.
-/
structure InfrenceRule (α  : Type) where
premises : List (Sequent α)
conclusion : Sequent α
restrictions : List (Sequent α) -> Sequent α -> Prop

/-
An infrence rule is satisfiable in some interpretation iff
its premises and restrictions imply its conclusion
-/
def InfrenceRule.sat (interpretation : α -> Prop) (rule : InfrenceRule α) : Prop :=
(∀ (a : Sequent α), a ∈ rule.premises -> Sequent.sat interpretation a) -> 
rule.restrictions rule.premises rule.conclusion ->
Sequent.sat interpretation rule.conclusion

/-
An infrence rule is valid (satisfiable over all interpetations) iff
its premises and restrictions imply its conclusion under any assignment
-/
def InfrenceRule.valid (rule : InfrenceRule α) : Prop :=
∀ (interpretation : α -> Prop), InfrenceRule.sat interpretation rule

def InfrenceRule.noRestrictions : List (Sequent α) -> Sequent α -> Prop 
:= fun _ => (fun _ => True)

def InfrenceRule.Assumption {α : Type} (φ : NDFormula α): InfrenceRule α := 
⟨[], φ ⊢ₙ φ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.Assumption.Valid (φ : NDFormula α) :
InfrenceRule.valid (InfrenceRule.Assumption φ)
:= by{
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [Assumption] at *;
  simp at *;
  rw [Sequent.sat];
  intro f;
  simp at *;
  have H := f φ;
  have H2 : φ ∈ [φ] := by apply trivialListMembership;
  have H3 := H H2;
  exact H3;
}

def InfrenceRule.AndIntro {α : Type} (φ ψ : NDFormula α) (Γ Δ : List (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₙ φ, Δ ⊢ₙ ψ], Γ ++ Δ ⊢ₙ φ ∧ₙ ψ, InfrenceRule.noRestrictions⟩

#check List.Mem.head

theorem dualListMembership (e a: α) : e ∈ [e, a] := by apply List.Mem.head;
theorem dualListMembershipFlip (e a: α) : e ∈ [a, e] := 
by{
  rw [Membership.mem, List.instMembershipList];
  apply List.Mem.tail; 
  apply trivialListMembership;
}

theorem inList (e : α) : e ∈ h :: t -> e = h ∨ e ∈ t 
:= by {
  intros H;
  cases H;
  apply Or.inl;
  rfl;
  apply Or.inr;
  rw [Membership.mem, List.instMembershipList]
  simp;
  assumption;
}    

theorem inAppendedList (e: α) (l1 l2 : List α) : e ∈ l1 -> e ∈ l1 ++ l2
:=by{
  unhygienic
  intro H;
  induction l1;
  contradiction;
  cases inList e H;{
    have headOfL1isHeadOfAppended (h : α) {t l2 : List α} :
    (h :: t) ++ l2 = h :: (t ++ l2) := by rfl; 
    rw [headOfL1isHeadOfAppended];
    simp;
    rw [<-h]
    exact @List.Mem.head α e (tail ++ l2);
    --exact List.Mem.head e (tail ++ l2);
  };{
    apply List.Mem.tail;
    apply tail_ih;
    exact h;
  }
}

theorem inAppendListFlip (e : α) (l1 l2 : List α) : e ∈ l2 -> e ∈ l1 ++ l2
:=by{
  intros H;
  induction l1;
  simp;
  exact H;
  apply List.Mem.tail;
  assumption;
}

theorem InfrenceRule.AndIntro.Valid (φ ψ : NDFormula α) (Γ Δ : List (NDFormula α)) :
InfrenceRule.valid (InfrenceRule.AndIntro φ ψ Γ Δ) :=
by{
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s res;
  rw [AndIntro] at *;
  simp at *;
  rw [Sequent.sat];
  simp;
  intros H;
  rw [NDFormula.sat];
  apply And.intro;
  {
    have si := s (Γ ⊢ₙ φ);
    have H2 : (Γ |-ₙ φ) ∈ [Γ |-ₙ φ, Δ |-ₙ ψ] := by apply dualListMembership;
    have s2 := si H2;
    rw [Sequent.sat] at s2;
    simp at *;
    apply s2;
    intros a q;
    have H3 := H a;
    apply H3;
    apply inAppendedList;
    exact q;
  };{
    have si := s (Δ ⊢ₙ ψ);
    have H2 : (Δ |-ₙ ψ) ∈ [Γ |-ₙ φ, Δ |-ₙ ψ] := by apply dualListMembershipFlip;
    have s2 := si H2;
    rw [Sequent.sat] at s2;
    simp at *;
    apply s2;
    intros a q;
    have H3 := H a;
    apply H3;
    apply inAppendListFlip;
    exact q; 
  }
}

def InfrenceRule.OrIntroRight {α : Type} (φ ψ : NDFormula α) (Γ : List (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₙ φ], Γ ⊢ₙ φ ∨ₙ ψ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.OrIntroRight.Valid (φ ψ : NDFormula α) (Γ : List (NDFormula α)) :
InfrenceRule.valid (InfrenceRule.OrIntroRight φ ψ Γ) :=
by{
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s res;
  rw [OrIntroRight] at *;
  simp at *;
  rw [Sequent.sat];
  simp;
  intros H;
  rw [NDFormula.sat];
  have s2 := s (Γ ⊢ₙ φ);
  rw [Sequent.sat] at s2;
  simp at s2;
  apply Or.inl;
  apply s2;
  apply trivialListMembership;
  exact H;
}

def InfrenceRule.OrIntroLeft {α : Type} (φ ψ : NDFormula α) (Γ : List (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₙ φ], Γ ⊢ₙ ψ ∨ₙ φ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.OrIntroLeft.Valid (φ ψ : NDFormula α) (Γ : List (NDFormula α)) :
InfrenceRule.valid (InfrenceRule.OrIntroLeft φ ψ Γ) :=
by{
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s res;
  rw [OrIntroLeft] at *;
  simp at *;
  rw [Sequent.sat];
  simp;
  intros H;
  rw [NDFormula.sat];
  have s2 := s (Γ ⊢ₙ φ);
  rw [Sequent.sat] at s2;
  simp at s2;
  apply Or.inr;
  apply s2;
  apply trivialListMembership;
  exact H;
}

def InfrenceRule.NotIntro {α : Type} (φ ψ : NDFormula α) (Γ : List (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₙ φ, Γ ⊢ₙ ¬ₙφ], Γ ⊢ₙ ψ ∨ₙ φ, InfrenceRule.noRestrictions⟩