import Mathlib
import NumberTheory.Notations
import NumberTheory.Theorems

def numDigits (n : ℕ) : ℕ :=
  (Nat.digits 10 n).length

def concatNum (a b : ℕ) : ℕ :=
  a * 10 ^ (numDigits b) + b

def piece : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => concatNum (piece n) (n + 1)

def IsPiece (x : ℕ) : Prop :=
  ∃ n > 1, piece n = x

def HasPrefix12 (x : ℕ) : Prop :=
  ∃ k : ℕ, 12 * (10^k) ≤ x ∧ x < 13 * (10^k)

lemma concat_maintains_prefix {a b : ℕ} (ha : HasPrefix12 a) : HasPrefix12 (concatNum a b) := by
  unfold HasPrefix12 at *
  unfold concatNum at *
  have hage1: 1 < 10 := by omega
  obtain ⟨k,hka⟩ := ha
  have hale1 := Nat.lt_base_pow_length_digits (b := 10) (m := a) hage1
  change a < 10 ^ (Nat.digits 10 a).length at hale1
  use k + numDigits b
  have h := Nat.mul_le_mul_right (10 ^ numDigits b) hka.left
  rw [Nat.mul_assoc 12 (10^k) (10^numDigits b)] at h
  rw [← pow_add] at h
  constructor
  · omega
  · have hpos : 0 < 10 ^ numDigits b := by positivity
    have h_mul := Nat.mul_lt_mul_of_pos_right hka.right hpos
    rw [Nat.mul_assoc 13 (10^k) (10^numDigits b)] at h_mul
    rw [← pow_add] at h_mul
    have hble1 := Nat.lt_base_pow_length_digits (b := 10) (m := b) hage1
    change b < 10 ^ numDigits b at hble1
    have ha1: a + 1 ≤ 13 * 10 ^ k := hka.right
    have h_le : (a+1) * (10^numDigits b) ≤ 13 * 10 ^(k+numDigits b) := by
      calc
        (a+1) * (10^numDigits b) ≤ 13 * (10^k) * (10^numDigits b) := by gcongr
        _ = 13 * (10^k * 10^numDigits b) := by rw [Nat.mul_assoc]
        _ = 13 * 10 ^ (k+numDigits b) := by rw [← Nat.pow_add]
    rw [add_mul, one_mul] at h_le
    omega

lemma piece_has_prefix (n : ℕ) (hn : n > 1) : HasPrefix12 (piece n) := by
  unfold HasPrefix12
  have hn2 : 2 ≤ n := hn
  induction n, hn2 using Nat.le_induction with
  | base =>
    use 0
    constructor
    · change 12 ≤ concatNum (piece 1) (2)
      change 12 ≤ 12
      decide
    · change concatNum (piece 1) (2) < 13
      change 12 < 13
      decide
  | succ d hd ih =>
    change HasPrefix12 (piece (d+1))
    have h := ih hd
    change HasPrefix12 (piece d) at h
    have h_step : piece (d+1) = concatNum (piece d) (d+1) := by
      rcases d with _ | ⟨_ | k ⟩
      · omega
      · omega
      · rfl
    rw [h_step]
    exact concat_maintains_prefix h

lemma piece_invariant {x : ℕ} (h : IsPiece x) : HasPrefix12 x := by
  unfold IsPiece at h
  obtain ⟨k,hk⟩ := h
  rw [← hk.right]
  exact piece_has_prefix k hk.left

lemma mul_not_prefix12 {a b : ℕ} (ha : HasPrefix12 a) (hb : HasPrefix12 b) :
  ¬(HasPrefix12 (a*b)) := by
  unfold HasPrefix12 at *
  rintro ⟨t,ht_le,ht_lt⟩
  obtain ⟨k1,hk1⟩ := ha
  obtain ⟨k2,hk2⟩ := hb
  set K := k1+k2 with hK
  have h1 := Nat.mul_le_mul hk1.left hk2.left
  have h11 : 12 * 10 ^ k1 * (12 * 10 ^ k2) = 144 * 10 ^(k1+k2) := by ring
  rw [h11, ← hK] at h1
  have h2 := Nat.mul_lt_mul'' hk1.right hk2.right
  have h22 : 13 * 10 ^ k1 * (13 * 10 ^ k2) = 169 * 10 ^ (k1+k2) := by ring
  rw [h22, ← hK] at h2
  clear h11 h22
  by_cases ht : t ≤ K + 1
  · have : 13 * 10 ^ t ≤ 130 * 10 ^ K := by
      calc
        13 * 10 ^ t ≤ 13 * 10 ^ (K+1) := by gcongr; decide
        _ = 130 * 10 ^ K := by rw [pow_succ]; ring
    omega
  · push Not at ht
    change K+2 ≤ t at ht
    have : 1200 * 10 ^ K ≤ 12 * 10 ^ t := by
      calc
        1200 * 10 ^ K = 12 * 10 ^ (K+2) := by ring
        _ ≤ 12 * 10 ^ t := by gcongr; decide
    omega

theorem ex5 (a b : ℕ) (ha : IsPiece a) (hb : IsPiece b) : ¬(IsPiece (a * b)) := by
  have h1 := piece_invariant ha
  have h2 := piece_invariant hb
  by_contra h
  have h3 := piece_invariant h
  exact mul_not_prefix12 h1 h2 h3
