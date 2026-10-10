import NumberTheory.Notations
import NumberTheory.Theorems


-- сам не до конца понимаю как работает)
-- перепсываем n² + 8n + 15 как (n+4)² -1
-- добавляем в контекст факт: (n+4) ∣ (n+4)²
-- раскрываем его как
-- (n+4)² = (n+4) * k1
-- а также добавим ¬((n+4) | 1)
-- теперь рассуждаем от противного: предположим что
-- n + 4 ∣ (n + 4)² - 1 верно
-- тогда мы можем раскрыть это как
-- (n + 4)² - 1 = (n+4) * k2
-- наша цель - False
-- с помощью тактики apply мы применяем ¬((n+4) | 1) на False
-- наша цель становится - (n+4) | 1
-- используем свидетеля k1-k2
-- цель - 1 = (n+4) * k1 - (n+4) * k2
-- перепишем
-- 1 = (n+4)² - (n+4)² - 1
-- что тривиально
-- тогда мы нашли противоречие
-- мы доказали что (n+4) ∣ 1
-- что противоречит нашему факту 2 ¬((n+4) | 1)
theorem ex10 (n : ℕ) : ¬((n+4) ∣ (n^2 + 8*n + 15)) := by
  have h: n^2 + 8*n +15 = (n+4)^2 -1 := by
    have h1: (n+4) ^ 2 = n^2 + 8*n + 16 := by ring
    rw [h1]
    omega
  rw [h]
  have h1: (n+4) ∣ (n+4) ^ 2 := by
    use n+4
    ring
  have h2: ¬ ((n+4) ∣ 1) := by
    have h3: 1 < n+4 := by
      omega
    have h4: 0 < 1 := by positivity
    exact Nat.not_dvd_of_pos_of_lt (n := 1) (m := (n+4)) h4 h3
  intro h_goal
  obtain ⟨k1,hk1⟩ := h1
  obtain ⟨k2,hk2⟩ := h_goal
  apply h2
  use k1-k2
  have h3 := Nat.mul_sub (n+4) k1 k2
  have h4: (n + 4) ^ 2 - ((n + 4) ^ 2 - 1) = (n + 4) ^ 2 - (n + 4) ^ 2 + 1 := by
    have h5: 1 ≤ (n+4)^2 := by omega
    have h6 := Nat.sub_sub_right ((n+4)^2) h5
    rw [h6]
    omega
  have h5 := Nat.sub_self ((n + 4) ^ 2)
  rw [h3, ← hk1, ← hk2, h4, h5]
