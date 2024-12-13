import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

/-# Exercise 3-/

--Exercise 10.1.5.4

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 2
  numbers

example : Symmetric (· ∼ ·) := by
  sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1,2
  constructor
  numbers
  numbers

example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro x y hy hx
  have h : y + 0 ≡ y + 2 [ZMOD 5] := by calc
    y + 0 = y := by ring
    _ ≡ x + 1 [ZMOD 5] := by rel [hy]
    _ ≡ (y + 1) + 1 [ZMOD 5] := by rel [hx]
    _ = y + 2 := by ring

example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 2,3,4
  constructor
  · numbers
  · constructor
    · numbers
    · numbers

end

/-# Exercise 4-/

--Exercise 10.1.5.5

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y z
  calc
    y + x = x + y := by ring
    _ ≡ 0 [ZMOD 3] := by rel [z]


example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 2
  constructor
  · calc
      1 + 2 = 0 + 1 * 3 := by ring
      _ ≡ 0 [ZMOD 3] := by extra
  · constructor
    · calc
      2 + 1 = 0 + 1 * 3 := by ring
      _ ≡ 0 [ZMOD 3] := by extra
    · numbers

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 4
  constructor
  · calc
      1 + 2 = 0 + 1 * 3 := by ring
      _ ≡ 0 [ZMOD 3] := by extra
  · constructor
    · calc
        2 + 2 + 2 = 0 + 2 * 3 := by ring
        _ ≡ 0 [ZMOD 3] := by extra
    · intro hx
      have h1 := calc
        2 ≡ 2 + 1 * 3 [ZMOD 3] := by extra
        _ = 1 + 4 := by numbers
        _ ≡ 0 [ZMOD 3] := by rel [hx]
      numbers at h1

end

/-# Problem 2-/

--Exercise 10.1.5.6

example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry
