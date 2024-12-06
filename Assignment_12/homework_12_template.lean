import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 4-/

--Exercise 6.4.3.1

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain hx | hy := even_or_odd n
  · obtain ⟨r, hr⟩ := hx
    have hr1 : 2 * 0 < 2 * r :=
    calc
      2 * 0 = 0 := by ring
      _ < n := by rel [hn]
      _ = 2 * r := by rw [hr]
    cancel 2 at hr1
    obtain ⟨ra, rx, r1, r2⟩ := extract_pow_two r hr1
    use ra + 1, rx
    constructor
    · apply r1
    · calc
        n = 2 * r := by rw [hr]
        _ = 2 * (2 ^ ra * rx) := by rw [r2]
        _ = 2 ^ (ra + 1) * rx := by ring
  · use 0, n
    constructor
    · apply hy
    · ring

/-# Exercise 5-/

------------------------------------------------------------------------------------
--Exercise 9.1.10.1

example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  numbers

------------------------------------------------------------------------------------
--Exercise 9.1.10.2

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp
  use 7
  numbers

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.3

example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  push_neg
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor
  · numbers
  · numbers


/-# Exercise 6-/
------------------------------------------------------------------------------------
--Exercise 9.1.10.6

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  intro a ha
  obtain ⟨k,hk⟩ := ha
  use 4 * k
  calc a = 20 * k := hk
    _ = 5 * (4 * k) := by ring

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.7

example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 15
  constructor
  · use 3
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor <;> numbers



------------------------------------------------------------------------------------
--Exercise 9.2.8.5

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro a ha
  obtain ⟨k, hk⟩ := ha
  constructor
  · use 5 * k + 3
    calc
      a - 1 = (a - 7) + 6 := by ring
      _ = 10 * k + 6 := by rw [hk]
      _ = 2 * (5 * k + 3) := by ring
  · use 2 * k + 1
    calc
      a - 2 = (a - 7) + 5 := by ring
      _ = 10 * k + 5 := by rw [hk]
      _ = 5 * (2 * k + 1) := by ring

/-# Problem 2-/

--Exercise 9.2.8.6

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  sorry

--Exercise 9.3.6.1

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  sorry
