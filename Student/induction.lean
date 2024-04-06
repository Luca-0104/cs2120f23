#check False.rec




#check Bool.rec
/-!
Bool.rec.{u}
  {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) :
  motive t
-/

example : ∀ (b : Bool), !!b = b :=
by
  intros b
  inductive b
  repeat { rfl }

#check Nat.rec
#check List.rec


inductive Tree (α : Type) where
| empty : Tree α
| node (a : α) (l r : Tree α)


#check Tree.rec
