import Mathlib

def ModEq (m a b : ℤ) : Prop := m ∣ (a - b)

notation a " ≡ " b " (mod " m ")" => ModEq m a b
