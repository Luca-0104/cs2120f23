
/-!
#### Proff utilization (elimination)
-/

example (P Q : Prop) : P ∧ Q → Q ∧ P
λ (h : P ∧ Q) => ⟨ h.2, h.1 ⟩

example (P Q : Prop) : P ∧ Q → Q ∧ P
| And.intro p q => And.intro q p


example (P Q : Prop) : P ∧ Q → Q ∧ P
| ⟨ p, q ⟩ => ⟨ q, p ⟩


example (P Q : Prop) : P ∧ Q → Q ∧ P
| ⟨ p, q ⟩ => Or.inl q


example (P Q : Prop) : P ∧ Q → Q ∧ P
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q



#check Classical.em

example (p : Prop) : (¬¬P → P) :=
match (Classical.em P) with
  | Or.inl p => λ _ => p
  | Or.inr np => λ _ => by contradiction


def one_not_eq_zero (n : Nat): n = 1 → n ≠ 0 :=
λ (neq1 : n = 1) => λ neq0 => by
  rw [neq1] at neq0
  cases neq0


def zornz : ∀ (n : Nat), n = 0 ∨ n ≠ 0 :=
λ n => match n with
-- | 0 => (Or.inl rfl)
| 0 => (Or.inl (Eq.refl 0))
| (_ + 1) => Or.inr (λ h => nomatch h)

#reduce zornz 3


variable
  (P : Type)
  (Q : P → Prop)
  (R : Prop)
  (t : P)

#check P
#check Q

#check Q t
#check ∀ (p : P), Q p


inductive IsEven : Nat → Prop
| zero_is_even : IsEven 0
| even_plus_2_even : ∀ (n : Nat), IsEven n → IsEven (n + 2)

open IsEven

example : IsEven 0 := zero_is_even

example : IsEven 4 := even_plus_2_even 2 _

theorem rot_add_assoc:
∀ (a b c : Rotation), (a + b) + c = a + (b + c)
| r0, b, c => _
| r120, b, c => _
| r240, b, c => _
