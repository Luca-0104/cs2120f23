-- git pull upstream main
-- if 1st command can't work, run "git remote add upstream https://github.com/kevinsullivan/cs2120f23"

def compose4 {α : Type}: (α → α) → (α → α)
| f => fun a => (f ∘ f ∘ f ∘ f) a

-- fun a means function takes argument a return ()


/-
g after f compositions fuction
-/
def comp' (α β γ : Type) : (β → γ) → (α → β) → (α → γ)
| g, f => fun a => g (f a)
-- use function composition notation
def comp'' (α β γ : Type) : (β → γ) → (α → β) → (α → γ)
| g, f => g ∘ f

/-!
Takes a function and a Nat, return a function
Use function composition notation ∘
-/
def compn' {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, f => λ a => a
| (Nat.succ n'), f => λ a => f (compn' n' f a)

def compn {α : Type}: Nat → (α → α) → (α → α)
| Nat.zero, f => λ a => a
| (Nat.succ n'), f => f ∘ (compn n' f)

#eval (compn 5 Nat.succ) 0
def sq (n : Nat) := n * n
#eval (compn 5 sq) 2




/- !inductive List (α:Type u) where
 | nil: List α
 | cons (head: α)(tail:List α) : List α
 -/

 def e :List Nat := List.nil
 def e':List Nat := []    -- List NOTATION

 def l1: List Nat := List.cons 1 e
 def l1': List Nat := 1::e  -- notation for cons
 def l1'': List Nat := [1]

 def l2 : List Nat := List.cons 0 l1
 #reduce l2

 def list_len {α : Type} : List α -> Nat
 | List.nil => 0
 | (List.cons h t) => 1 + list_len t
 #eval list_len l2



/-!

-/

--
def add : Nat → Nat → Nat
| n, 0 => n
| n, (m' + 1) => Nat.succ (add n m')

#eval add 4 5

/-!
n * m
n + (n * (m - 1))
-/
def mul : Nat → Nat → Nat
| n, 0 => 0
| n, (m' + 1) => add n (mul n m')

#check Nat.mul
#eval mul 5 3

/-!
n^m
m = 0 => 0
m != 0 => n * (n^(m-1))
-/
def exp : Nat → Nat → Nat
| n, 0 => 1
| n, (m' + 1) => mul n (exp n m')

#eval exp 2 3


-- empty
#check @Empty

#check @Unit

#check @Bool

#check @Int

#check @String
