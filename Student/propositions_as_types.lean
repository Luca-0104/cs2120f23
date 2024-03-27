inductive BobStudiesAtUVa
| attendClasses
| paidTUition

inductive MaryStudiesAtUVa
| attendClasses
| paidTUition


-- for empty type
inductive MarkoStudiesAtUVa


def neg (α : Type) := α → Empty

example : neg MarkoStudiesAtUVa :=
λ m : MarkoStudiesAtUVa => nomatch m


-- and
inductive BobStudiesAtUVaAndMaryStudiesAtUVa
| and (b : BobStudiesAtUVa) (m : MaryStudiesAtUVa)

def b : BobStudiesAtUVa := BobStudiesAtUVa.paidTUition
def m : MaryStudiesAtUVa := MaryStudiesAtUVa.paidTUition

example: BobStudiesAtUVaAndMaryStudiesAtUVa :=
  BobStudiesAtUVaAndMaryStudiesAtUVa.and b m


-- or
inductive BobStudiesAtUVaOrMaryStudiesAtUVa
| left (b : BobStudiesAtUVa)
| right (m : MaryStudiesAtUVa)

example : BobStudiesAtUVaOrMaryStudiesAtUVa :=
  BobStudiesAtUVaOrMaryStudiesAtUVa.left b


-- generalize
inductive MyAnd (α β : Type) : Type
| mk (a : α) (b : β)

inductive MyOr (α β : Type) : Type
| inl (a : α)
| inl (b : β)

example MyAnd BobStudiesAtUVa MaryStudiesAtUVa :=
  MyAnd.mk b m

example MyOr BobStudiesAtUVa MaryStudiesAtUVa := MyOr.inl b
example MyOr BobStudiesAtUVa MaryStudiesAtUVa := MyOr.inl m

def MyNot (α : Type) := α → Empty

example : MyNot BobStudiesAtUVa :=  λ b => _ -- Nope
example : MyNot MarkoStudiesAtUVa :=  λ m => nomatch m

/-!
### Prod
-/
#check (1, "Hello")
-- construct prood of the conjunction (introduction rule)
example : Prod BobStudiesAtUVa MaryStudiesAtUVa := Prod.mk b m
example : BobStudiesAtUVa × MaryStudiesAtUVa := ⟨ b, m ⟩
example : BobStudiesAtUVa × MaryStudiesAtUVa := ⟨ b, m ⟩
-- use a proof of the conjunction (elimination rules)
example : BobStudiesAtUVa × MaryStudiesAtUVa → BobStudiesAtUVa := λ p => p.fst
example : BobStudiesAtUVa × MaryStudiesAtUVa → MaryStudiesAtUVa := λ p => p.2

/-!
### Or
-/
#check (@Sum)
-- How to counstruct proof of "or" in our computational style
example : Sum BobStudiesAtUVa MarkoStudiesAtUVa := Sum.inl b -- b is a prood of left
example : BobStudiesAtUVa ⊕ MarkoStudiesAtUVa := Sum.inr _ -- no proof, uninhabited type
-- How to use a proof of a disjunction
example : BobStudiesAtUVa ⊕ MarkoStudiesAtUVa → BobStudiesAtUVa
| (Sum.inl l) => l
| (Sum.inl r) => nomatch r


/-!
A prood that Marko does not study at UVA
-/
example : neg MarkoStudiesAtUVa :=
  λ p :
  MarkoStudiesAtUVa =>
  nomatch p

example : neg (MaryStudiesAtUVa × MarkoStudiesAtUVa) :=
λ p => nomatch p.2

/-! Proof Irrelavent

-/

inductive B : Prop
| paid
| classes

inductive M : Prop
| paid
| classes

inductive K : Prop


example : And B M := And.intro B.paid M.classes
example : B ∧ M := And.intro B.paid M.classes
example : B ∧ M := ⟨ B.paid, M.classes ⟩
def b_and_m_true : B ∧ M := And.intro B.paid M.classes
theorem b_and_m_true' : B ∧ M := And.intro B.paid M.classes

example : B ∧ M -> M := λ bm => bm.right
example : B ∧ M -> B := λ bm => bm.1

theorem foo : B ∧ Not K := ⟨ B.paid, λ k => nomatch k ⟩
example : B ∧ ¬K := foo

example : B ∨ K := Or.inl B.paid

example : B ∨ K → B :=
λ bork => match bork with
| Or.inl b => b
| Or.inr k => nomatch k


-- and A
-- intro
-- elim

-- intro

-- elim
example : B ∧ M → M := λ bm => bm.right
example : B ∧ M → M := λ bm => bm.1

-- example
theorem foo : B ∧ Not k := ⟨  ⟩


-- Or
-- intro
-- elim

-- intro
example : B ∨ K := Or.inl B.paid


-- elim example
example : B ∨ K → B :=
λ bork => match bork with
| Or.inl b => b
| Or.inl k => nomatch k


example :
  ∀ (Raining Sptrinkling Wet : Prop),
    (Raining ∨ Sptrinkling) →
    (Raining → Wet) →
    (Sptrinkling → Wet) →
    Wet :=
λ R S W rors rw sp =>
match rors with
| Or.inl r => rw r
| Or.inl s => sp s

-- Not
-- intro
-- elim

-- intro
def notK : ¬K := λ k => nomatch k

-- elim example (law of no contradiction example)
example (P : Prop) : ¬P → P → False :=
λ np p => np p
