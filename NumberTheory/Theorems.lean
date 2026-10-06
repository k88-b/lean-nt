import Mathlib
import NumberTheory.Notations

theorem mod_refl (m a : ℤ) : a ≡ a (mod m) := by
  unfold ModEq
  use 0
  ring

theorem mod_symm (m a b : ℤ) (h : a ≡ b (mod m)) :  b ≡ a (mod m) := by
  unfold ModEq at *
  obtain ⟨k, hk⟩ := h
  use -k
  have hab: b-a = -(a-b) := by ring
  rw [hab, hk]
  ring

theorem mod_trans (m a b c : ℤ) (h1 : a ≡ b (mod m)) (h2 : b ≡ c (mod m)) : a ≡ c (mod m) := by
  unfold ModEq at *
  have h: a - c = a - b + (b - c) := by ring
  obtain ⟨k1,hk1⟩ := h1
  obtain ⟨k2,hk2⟩ := h2
  rw [hk1, hk2] at h
  rw [h]
  use k1+k2
  ring

theorem mod_add (m a b c d : ℤ)
    (h1 : a ≡ b (mod m))
    (h2 : c ≡ d (mod m)) :
    (a+c) ≡ (b+d) (mod m) := by
  unfold ModEq at *
  have h: a + c - (b + d) = a -b + (c - d) := by ring
  rw [h]
  obtain ⟨k1,hk1⟩ := h1
  obtain ⟨k2,hk2⟩ := h2
  rw [hk1, hk2]
  use k1+k2
  ring

theorem mod_mul_const (m a b c : ℤ) (h : a ≡ b (mod m)) : (a*c) ≡ (b*c) (mod m) := by
  unfold ModEq at *
  obtain ⟨k,hk⟩ := h
  have habc: a * c - b * c = c * (a - b) := by ring
  rw [habc, hk]
  use c * k
  ring

theorem mod_mul (m a b c d : ℤ)
    (h1 : a ≡ b (mod m))
    (h2 : c ≡ d (mod m)) :
    (a*c) ≡ (b*d) (mod m) := by
  have h3 := mod_mul_const m a b c h1
  have h4 := mod_mul_const m c d b h2
  unfold ModEq at *
  have h5 : a * c - b * d = a * c-b * c + (c * b - d * b) := by ring
  rw [h5]
  obtain ⟨k3,hk3⟩ := h3
  obtain ⟨k4,hk4⟩ := h4
  rw [hk3, hk4]
  use k3 + k4
  ring

theorem mod_pow (m a b : ℤ) (n : ℕ) (h : a ≡ b (mod m)) : (a^n) ≡ (b^n) (mod m) := by
  induction n with
  | zero =>
    unfold ModEq at *
    use 0
    ring
  | succ d hd =>
    rw [Int.pow_succ, Int.pow_succ]
    have h1 := mod_mul m (a^d) (b^d) a b hd h
    exact h1

theorem dvd_trans' (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨k1,hk1⟩ := h1
  obtain ⟨k2,hk2⟩ := h2
  rw [hk2, hk1]
  use k1 * k2
  ring

theorem mod_of_dvd (m a b d : ℤ) (h1 : a ≡ b (mod m)) (h2 : d ∣ m) : a ≡ b (mod d) := by
  unfold ModEq at *
  obtain ⟨k1,hk1⟩ := h1
  obtain ⟨k2,hk2⟩ := h2
  rw [hk2] at hk1
  rw [hk1]
  use k2 * k1
  ring

theorem mod_add_const (m a b c : ℤ) (h : a ≡ b (mod m)) : (a + c) ≡ (b+c) (mod m) := by
  unfold ModEq at *
  have h1: a + c - (b + c) = a - b := by ring
  rw [h1]
  exact h
