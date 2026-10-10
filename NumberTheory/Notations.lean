import Mathlib

def ModEq (m a b : ℤ) : Prop := m ∣ (a - b)

notation a " ≡ " b " (mod " m ")" => ModEq m a b

def IsGCD (a b d : ℤ) : Prop :=
  (d ∣ a ∧ d ∣ b) ∧ (∃x y : ℤ, a*x + b*y = d)

notation "IsGCD(" a ", " b ") " d => IsGCD a b d
