import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # CS 511 Homework 1 -/

-- Exercise 3:  MoP Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  calc
    w = (( (3 * w) + 1) / 3 ) - (1 / 3) := by ring
    _ = ( 4 / 3 ) - (1 / 3) := by rw [h1]
    _ = 1 := by ring

-- Exercise 4:  MoP Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 := by
  calc
    (a ^ 2 - a + 3) = (a - 3) ^ 2 + 5 * (a - 3) + 9  := by ring
    _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw [h1]
    _ = 4 * (b ^ 2) + 10 * b + 9 := by ring

-- Problem 2:  MoP Exercise 1.3.11
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 := by sorry
