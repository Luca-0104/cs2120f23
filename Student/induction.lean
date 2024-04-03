#check False.rec




#check Bool.rec
#check Nat.rec
#check List.rec


inductive Tree (α : Type) where
| empty : Tree α
| node (a : α) (l r : Tree α)


#check Tree.rec
