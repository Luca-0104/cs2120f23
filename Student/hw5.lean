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
