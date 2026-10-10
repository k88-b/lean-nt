import NumberTheory.Notations
import NumberTheory.Theorems


-- перписываем 11 ∣ a² + 9ab + b² как 11 ∣ a² - 2ab + b² + 11ab
-- что равно 11 ∣ (a-b)² + 11ab
-- но 11 ∣ 11ab
-- значит 11 делит и (a-b)²
-- 11 - простое число, применим лемму Евклида
-- значит 11 ∣ (a-b)
-- перпишем 11 ∣ (a² - b²) как 11 ∣ (a-b)(a+b)
-- 11 ∣ (a-b) => 11 ∣ (a-b)(a+b)
-- что закрывает цель
theorem ex7 (a b : ℤ) (h : 11 ∣ (a ^ 2 + 9 * a * b + b ^ 2)) : 11 ∣ (a^2 - b^2) := by
  obtain ⟨k1,hk1⟩ := h
  have h1: a ^ 2 + 9 * a * b + b ^ 2 = (a-b) ^ 2 + 11 * a*b := by ring
  rw [h1] at hk1
  clear h1
  have h1: 11 ∣ (a-b) ^ 2 := by
    use k1 - a*b
    rw [Int.mul_sub, ← hk1]
    ring
  have h2: Prime (11 : ℤ) := by decide
  have h3 := h2.dvd_of_dvd_pow h1
  have h4: a^2 - b^2 = (a-b)*(a+b) := by ring
  rw [h4]
  clear h4
  obtain ⟨k,hk⟩ := h3
  use k*(a+b)
  rw [hk]
  ring
