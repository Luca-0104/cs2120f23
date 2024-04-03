example :
∀ (Person : Type)
  (Loves : Person → Person → Prop),
  (∃ (q : Person), ∀ (p : Person), Loves p q) →
  (∀ (p : Person), ∃ (q : Person), Loves p q) :=
λ _ _ sel k => match sel with
| ⟨ joe, every_one_loves_joe ⟩ =>
  ⟨ joe, every_one_loves_joe k ⟩


variable
  (Ball : Type)
  (Heavy : Ball → Type)
  (Red : Ball → Type)

example : (∃ (b : Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b) :=
λ h => match h with
| ⟨ rhb, bisredandheavy ⟩ => ⟨ rhb, bisredandheavy.left ⟩


example : (∃ (b : Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b) :=
λ h => match h with
| ⟨ rhb, bisredandheavy ⟩ => ⟨ rhb, bisredandheavy.left ⟩


example : (∃ (b : Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b) :=
λ h => match h with
| ⟨ rhb, bisredandheavy ⟩ => ⟨ rhb, bisredandheavy.left ⟩
