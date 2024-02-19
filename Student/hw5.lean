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

/-!

-/

def nat_add_monoid' : my_monoid Nat :=
  ( Nat.add,
    0,
    λ a => by simp [Nat.add],
    λ a => by simp [Nat.add],
    _,
    _
  )

def nat_mul_monoid'' : my_monoid Nat :=
(
  Nat.mul,
  1,
  λ a => by simp,
  λ a => by simp,
  sorry
)

/-!
Exercise
-/

def nary_mul' : List Nat → Nat := foldr (my_monoid.mk Nat.mul 1 sorry sorry sorry)
#eval nary_mul' [1, 2, 3, 4, 5]

/-!
another mathmetical structure: funcor
-/

#check (@Option)

def pred : Nat → Option Nat
| Nat.zero => Option.none
| (Nat.succ n') => n'

#reduce pred 0
#reduce pred 3


def list_map {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => f h :: list_map f t


def option_map {α β : Type} : (α → β) → Option α → Option β
| f, Option.none => Option.none
| f, (Option.some a) => some (f a)


-- a new structure of Tree
inductive Tree (α : Type) : Type
| empty
-- case 2: (root) (left sub-tree) (right sub-tree)
-- way 1
-- | node : α → Tree α → Tree α → Tree α
-- way 2
| node (a : α) (l r : Tree α) : Tree α




-- map each node in a tree to new nodes using function (α → β)
def tree_map {α β : Type} : (α → β) → Tree α → Tree β
| f, Tree.empty => Tree.empty
| f, (Tree.node a l r) => Tree.node (f a) (tree_map f l) (tree_map f r)


#reduce tree_map Nat.succ Tree.empty


/-!
        1
    2       3
 e   e    e   e

-/
def a_tree := Tree.node 1 (Tree.node 2 Tree.empty Tree.empty) (Tree.node 3 Tree.empty Tree.empty)

#reduce tree_map Nat.succ a_tree



/-!
polymorphism in the type of the container
-/

-- functor is a new Type with the functionality of converting a container of α
-- to a container of β. The container can be chosen by user, like List, Tree, Option, etc.
structure functor {α β : Type} (c : Type → Type) : Type where
map (f : α → β) (ic : c α) : c β

def list_functor {α β : Type} : @functor α β List := functor.mk list_map
def option_functor {α β : Type} : @functor α β Option := functor.mk option_map
#check (@list_functor)

-- convert encapsulates the functor, adding the map function.
def convert {α β : Type} (c : Type → Type) (m : @functor α β c) : (f : α → β) → c α → c β
| f, c => m.map f c

#reduce convert List list_functor Nat.succ [1, 2, 3, 4, 5]
#reduce convert Option option_functor Nat.succ (Option.some 4)

inductive Box (α : Type)
| contents (a : α)


#reduce convert Box
