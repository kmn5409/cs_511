import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

--# Exercise 3

--Exercise 6.2.7.1
def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k IH
  · --base case
    use 3
    rw [c]
    numbers
  · -- inductive step
    obtain ⟨x,hx⟩ := IH
    use 3 * x - 4
    calc
    c (k + 1) = 3 * c k - 10 := by rw [c]
      _ = 3 * (2 * x + 1) - 10 := by rw [hx]
      _ = 6 * x - 7 := by ring
      _ = 2 * (3 * x - 4) + 1 := by ring

--Exercise 6.2.7.2
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  · rw [c]; ring
  · rw [c,IH]; ring


--Exercise 6.2.7.3
def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  · --base case
    calc y 0 = 2 := by rw [y]
    _ = 2 ^ 2 ^ 0 := by numbers
  · --inductive step
    calc
      y (k + 1) = (y k) ^ 2 := by rw [y]
      _ = (2 ^ (2 ^ k)) ^ 2 := by rw [IH]
      _ = 2 ^ (2 ^ (k + 1)) := by ring

--# Exercise 4

--Exercise 6.3.6.1
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [b]; ring
  · rw [b]; ring
  · -- inductive
    calc
      b (k + 2) = 5 * b (k + 1) - 6 * b k := by rw [b]
      _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6 * (3 ^ k - 2 ^ k) := by rw [IH1, IH2]
      _ = 5 * 3 * 3 ^ k - 5 * 2 * 2 ^ k - 6 * 3 ^ k + 6 * 2 ^ k := by ring
      _ = 9 * 3 ^ k - 4 * 2 ^ k := by ring
      _ = 3 ^ (k + 2) - 2 ^ (k + 2) := by ring


--Exercise 6.3.6.2
def c' : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c' n

example (n : ℕ) : c' n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [c']; ring
  · rw [c']; ring
  · --inductive
    calc
      c' (k + 2) = 4 * c' k := by rw [c']
      _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw [IH1]
      _ = 2 * 4 * 2 ^ k + 4 * (-2) ^ k := by ring
      _ = 2 * 2 ^ 2 * 2 ^ k + (-2) ^ 2 * (-2) ^ k := by ring
      _ = 2 * 2 ^ (k + 2) + (-2) ^ (k + 2) := by ring

--Exercise 6.3.6.3
def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  · rw [t]; ring
  · rw [t]; ring
  · --inductive step
    calc
      t (k + 2) = 2 * t (k + 1) - t k := by rw [t]
      _ = 2 * (2 * (k + 1) + 5) - (2 * k + 5) := by rw [IH1,IH2]
      _ = 4 * (k + 1) + 10 - (2 * k + 5) := by ring
      _ = 4 * (k + 1) + 5 - 2 * k := by ring
      _ = 4 * k + 4 + 5 - 2 * k := by ring
      _ = 2 * k + 9 := by ring
      _ = 2 * (k + 2) + 5 := by ring

--# Problem 2

--Exercise 6.3.6.5
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  sorry

--Exercise 6.3.6.7
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  sorry
