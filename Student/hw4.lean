
/-!
New Material
-/

/-!
The fold right funcion
-/

/- version 1: add up numbers in list -/

def folder''' : (Nat → Nat → Nat) → Nat → List Nat → Nat
| _, id, [] => id
| op, id, h::t => op h (folder''' op id t)

def foldr'' : (String → String → String) → String → List String → String
| _, id, [] => id
| op, id, h::t => op h (foldr'' op id t)

def foldr' { α : Type } : (α → α → α) → α → List α → α
| _, id, [] => id
| op, id, h::t => op h (foldr' op id t)

-- def combine : String → Bool → Bool := _

-- def foldr { α β : Type } : (α → β → β) → β → List α → β
-- | op, id, List.nil => id
-- | op, id, h::t =>

#reduce folder''' Nat.add 0 [1, 2, 3, 4, 5]
#reduce folder''' Nat.mul 1 [1, 2, 3, 4, 5]
#reduce folder''' Nat.sub 0 [5, 3, 1]

#eval foldr' String.append "" ["a", "b"]

/-!
write a function fold_str that takes a list of strings and
return a single string in which all the given strings are
appended using String.append
-/

def fold_str : (String → String → String) → String → List String → String
| _, id, [] => id
| op, id, h::t => op h (fold_str op id t)

#eval fold_str String.append "" ["q", "w"]

/-!

-/
-- def foldr : (String → Bool → Bool) → Bool → List String → Bool



/-!
Type universe example of identity function,

-/
