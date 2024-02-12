/-!

-/

structure my_monoid' (α : Type) where
(op : α → α → α)
(id : α)

/-!
a version of foldr with just one type
parameter, α that instaead of taking op and
id as separate arguments instead takes an one,
an instance of this type. Recall that given such
an object you can access its field values using
dot notation
-/

def foldr' {α : Type} : my_monoid' α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr' m t)

-- test the solustion
#eval foldr' (my_monoid'.mk Nat.add 0) [1, 2, 3, 4, 5]
#eval foldr' (my_monoid'.mk Nat.mul 1) [1, 2, 3, 4, 5]
#eval foldr' (my_monoid'.mk String.append "") ["", "123", "234"]


/-!
What does a monoid do:
It extends a binary operator to be a n-arry operator
-/
def nary_add := foldr' (my_monoid'.mk Nat.add 0)
#eval nary_add [1, 2, 3, 4, 5]

def nary_mul := foldr' (my_monoid'.mk Nat.mul 1)
#eval nary_mul [1, 2, 3, 4, 5]

def nary_append := foldr' (my_monoid'.mk String.append "")
#eval nary_append ["", "123", "456"]

/-!

-/
structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀ (a : α), op id a = a)
(right_id : ∀ (a : α), op a id = a)
(op_assoc: ∀ a b c, op a (op b c) = op (op a b) c)

/-!
define a new version of foldr using the
imporoved structure as an argument
-/

def foldr {α : Type} : my_monoid α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr m t)

/-!

-/
def nat_add_monoid : my_monoid Nat :=
  my_monoid.mk Nat.add 0 sorry sorry sorry

#eval foldr nat_add_monoid [1, 2, 3, 4, 5]
