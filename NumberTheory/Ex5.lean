import Mathlib
import NumberTheory.Notations
import NumberTheory.Theorems

-- Nat.digits возвращает список цифр числа n по основанию 10
-- length дает длину списка
def numDigits (n : ℕ) : ℕ :=
  (Nat.digits 10 n).length

-- конкатенация определена как:
--  добавляем к числу a такое же колво нулей, как и колво цифр в числе b + само число b
def concatNum (a b : ℕ) : ℕ :=
  a * 10 ^ (numDigits b) + b

-- функция определена рекурсивно
-- рассмотрены 3 случая: для 0 или 1 она вернет 0 или 1 соответсвенно;
-- для числа k мы представляем его как n+1 и возвращаем конкатенацию числа (piece n) и числа n+1
-- пример: для piece 2 мы получим 2 = 1 + 1 => конкатенируем piece 1 и 2 => получаем 12
--                                                                        так как piece 1 равен 1
def piece : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => concatNum (piece n) (n + 1)

-- предикат. Если функция возвращает число, то предикат {false; true}
def IsPiece (x : ℕ) : Prop :=
  ∃ n > 1, piece n = x

-- предикат. начинается ли число x с цифр "12"
-- проверяем как
-- существует ли k такое что 12 ⋆ 10ᵏ ≤ x < 13 ⋆ 10ᵏ
def HasPrefix12 (x : ℕ) : Prop :=
  ∃ k : ℕ, 12 * (10^k) ≤ x ∧ x < 13 * (10^k)

-- если a начинается с "12" то при конкатенации a с любым b мы получим число начинающееся с "12"

-- важную роль в доказательстве этой леммы играет теорема Nat.lt_base_pow_length_digits
-- она гласит что любое число n по основанию b меньше чем b в степени колва числа m
-- m < b ^ (num of digits m)

-- используем свидетеля k + num of digits b
-- если умножим 12 * 10ᵏ ≤ a (нижняя граница) на 10 ^ (num of digits b)
-- получим 12 * 10 ^ (k + num of digits b) ≤ a * 10 ^ (num of digits b)
-- при цели доказательства для нижней границы
--                   12 * 10 ^ (k + num of digits b) ≤ a * 10 ^ (num of digits b) + b
-- что тривиально (a ≤ b => a ≤ b + c) (для ℕ)

-- верхняя граница:
-- a < 13 * 10ᵏ тоже саоме что и
-- a + 1 ≤ 13 * 10ᵏ
-- умножаем на 10 ^ (num of digits b)
-- a * 10 ^ (num of digits b) + 10 ^ (num of digits b) < 13 * 10 ^ (k + num of digits b)
-- при этом мы знаем что b < 10 ^ (num of digits b)
-- и наша цель это
--                a * 10 ^ (num of digits b) + b < 13 * 10 ^ (k + num of digits b)
-- что тривиально по нашему условию b < ...
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

-- кусок начинается с "12"

-- используем индукцию по n
-- база: n = 2
-- доказываем что 12 начинается с 12
-- шаг: n = d + 1
-- перепишем piece d + 1 как concatNum (piece d) (d+1)
-- по предположению индукции piece d начинается с 12
-- используем предыдущюю лемму и закрываем доказательство
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

-- Если x - кусок, тогда x начинается с 12
-- обертка над прошлой леммой.
lemma piece_invariant {x : ℕ} (h : IsPiece x) : HasPrefix12 x := by
  unfold IsPiece at h
  obtain ⟨k,hk⟩ := h
  rw [← hk.right]
  exact piece_has_prefix k hk.left

-- Если мы умножим два числа, которые начинаются с "12"
--                                     то полученное число не будет начинаться с "12"

-- доказываем от противного: пусть a⋆b начинается с "12" c показателем степени t
-- 12 * 10ᵗ ≤ a * b < 13 * 10ᵗ
-- раскрываем интервалы для a и b с показателями степеней k1 и k1 соответственно
-- 12 * 10 ^ k1 ≤ a < 13 * 10 ^ k1
-- 12 * 10 ^ k2 ≤ b < 13 * 10 ^ k2
-- пусть K = k1 + k2
-- умножаем нижние границы
-- 144 * 10 ^ K < a * b
-- верхние
-- a * b < 169 * 10 ^ K
-- разбираем случаи:
-- · t ≤ K + 1
--  тогда 13 * 10 ^ t ≤ 130 * 10 ^ K
--  и a * b > 144 * 10 ^ K
--    a * b < 13 * 10 ^ t
--  противоречие
-- · K + 1 < t
--  перпишем это как K + 2 ≤ t
--  тогда 1200 * 10 ^ K ≤ 12 * 10 ^ t
--  и 12 * 10 ^ t ≤ a * b
--    169 * 10 ^ K > a * b
--  противоречие
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

-- соединяем вместе:
-- a - кусок => начинается с 12
-- b - кусок => начинается с 12
-- предположим противное: a * b - кусок
-- тогда a * b должно начинаться с 12
-- но произведение двух кусков не может начинаться с 12 по раннее доказанной лемме
-- противоречие
theorem ex5 (a b : ℕ) (ha : IsPiece a) (hb : IsPiece b) : ¬(IsPiece (a * b)) := by
  have h1 := piece_invariant ha
  have h2 := piece_invariant hb
  by_contra h
  have h3 := piece_invariant h
  exact mul_not_prefix12 h1 h2 h3
