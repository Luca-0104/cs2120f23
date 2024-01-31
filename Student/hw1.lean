-- git pull upstream main
-- if 1st command can't work, run "git remote add upstream https://github.com/kevinsullivan/cs2120f23"

def compose4 {α : Type}:(α → α)->(α → α)
| f=>fun a=>(f ∘ f ∘ f ∘ f) a

fun a means function takes argument a return ()

def compn {α : Type}:(α → α)-> Nat ->(α → α)
| n, f=>fun a=>
| Nat.zero, f => lamda a=>a
|(Nat.success n'),f=>(λ a=>f(compn n' f a))

#eval (compn 5 sq) 2

/- !inductive List (α:Type u) where
 | nil: List α
 | cons (head: α)(tail:List α) : List α
 -/

 def e :List Nat := List.nil
 def e':List Nat := []    -- List NOTATION

 def l1: List Nat :=List.cons 1 e
 def l1': List Nat :=1::e  -- notation for cons
 def l1'': List Nat :=[1]

 def l2 : List Nat :=List.cons 0 l1
 #reduce l2

 def list_len {α : Type} : List α -> Nat
 | List.nil => 0
 | (List.cons h t) =>1 + list_len t
 #eval list_len l2
