/-!
------------------------------ HW4 starts here ----------------------------------------------------------------
-/
def isEvenLen : String → Bool := λ s => s.length % 2 == 0

def combine : String → Bool → Bool := λ s b => (isEvenLen s) && b

def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

#reduce foldr combine true ["1234", "12345"] --should be false
#reduce foldr combine true ["1234", "1234"] --should be true
#reduce foldr combine true ["", "", ""] --should be true
#reduce foldr combine true ["", "", "1"] --should be false
/-!
------------------------------ HW4 ends here ----------------------------------------------------------------
-/


/-!
HW4 ans
(lecture notes of hw4 class)
-/
def combine_ans : String → Bool → Bool
| s, b => (isEvenLen s) && b

#eval foldr combine_ans true []

def foldr_ {α : Type} : (α → α → α) → α → List α → α
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

#eval foldr_ (Nat.add) 0 [1, 2, 3]
#eval foldr_ (Nat.add) 1 [1, 2, 3]


-- what can go wrong:
-- We can pass a non-identity element

-- rules
-- 1. id is the identiyt element for op
-- 2. op must be associative

/-!
solution:
to prove, for any a in α,
(op a id = a) ∧
(op id a = a)
Then id is the identity element for op
-/

-- "structure" for defining a data type with just single constructor
-- "mk" is the default name of the constructor
-- can access the attributes using my_monoid.op, my_monoid.id, etc. like OOD
structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀ (a : α), op id a = a)
(right_id : ∀ (a : α), op a id = a)


def  a_monoid : my_monoid Nat := my_monoid.mk Nat.add 0 sorry sorry

#check a_monoid.op


/-!
New Material
(Lecture notes of hw3 class)
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
