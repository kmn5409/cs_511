import Init.Data.Fin.Basic
import Mathlib.Data.Real.Basic
--import Library.Basic
--import Library.Tactic.Exhaust
--import Library.Tactic.ModEq
import Mathlib.Lean.Meta.Simp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Core
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

--math2001_init
--set_option pp.funBinderTypes true

open Function

def q (x : ℝ) : ℝ := x + 3


--Question 1 Parity_and_Divisibility
--Lean-Github
example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  rw [Odd] at *
  rcases hn with ⟨m, rfl⟩
  use 3 * m + 2
  linarith




/-
LeanDojo
example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  rcases hn with ⟨n, hn⟩
  cases' n with n n
  have ⟨n, hn⟩ := by
    rcases hn with ⟨n, hn⟩
    cases' n with n n <;> cases' n with n n-/

--Question 2 Parity and divisibility
--Lean-Github
example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  convert Nat.le_of_dvd hb hab






--Questions 3 Sets
-- Sets
--LeanGithub

example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  intro a ha
  simp only [Set.mem_setOf_eq] at ha ⊢
  obtain ⟨hr,hb⟩ := ha
  --simp only [ha]
  use 2*hr
  linarith

/-
LeanDojo
example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  refine Set.Subset.theorem_subset?_

  refine Set.Subset.theorem_subset?_
  refine Subset.theorem_subset?_
  refine Set.Subset.theorem_subset?_?_
  refine Set.Subset.theorem_subset_iff.mpr?_
-/

--Question 4 Sets
--LeanGithub
example : {1, 3, 6} ⊆ {t : ℚ | t < 10} := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with (rfl | rfl | rfl)
  · norm_num
  · norm_num
  · norm_num


--Question 5 Proofs_with_Structure_II
-- Required multiple promping to get a suitable answer
--Lean-Github
example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    have h2: 3 * a ≤ 6 := by linarith
    have h3: a ≤ 2 := by linarith
    exact h3
  · intro h
    have h4: 3 * a ≤ 6 := by linarith
    have h5: 3 * a + 1 ≤ 7 := by linarith
    exact h5


/-
LeanDojo
example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  --rw [← by]
  --linarith

  simp example
  refine ⟨fun h =>?_, fun h =>?_⟩
  --refine ⟨fun h ↦?_, fun h ↦?_⟩
  --refine ⟨fun h ↦?_, fun h ↦ by simp [h]⟩
-/

--Question 6 Proof by Calculation
--Lean-Github
example {a b c : ℝ} : a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by
  have h : ∀ x : ℝ, (0 : ℝ) ≤ x ^ 4 + (1 - x) ^ 4 := by
    intro x
    calc (0 : ℝ) ≤ x ^ 2 * x ^ 2 + (1 - x) ^ 2 * (1 - x) ^ 2 := by nlinarith
    _ = x ^ 4 + (1 - x) ^ 4 := by ring
  have h2 : ∀ x y : ℝ, (x ^ 4 + y ^ 4) * (x ^ 4 + y ^ 4) ≤ (x ^ 4 + y ^ 4) * (x ^ 2 + y ^ 2) ^ 2 := by
    intro x y
    nlinarith [h x, h y]
  have h3 : ∀ x y : ℝ, x ^ 4 + y ^ 4 ≤ (x ^ 2 + y ^ 2) ^ 2 := by
    intro x y
    nlinarith [h x, h y]
  have h4 : ∀ x y : ℝ, (x ^ 4 + y ^ 4) * (x ^ 4 + y ^ 4) ≤ (x ^ 4 + y ^ 4) * (x ^ 2 + y ^ 2) ^ 2 := by
    intro x y
    nlinarith [h x, h y]
  intro a b c
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) = a ^ 8 + 8 * a ^ 2 * b ^ 3 * c ^ 3 := by ring
    _ = (a ^ 4) ^ 2 + 2 * 2 * a ^ 4 * (b ^ 2 * c ^ 2) + (b ^ 2 * c ^ 2) ^ 2 - (b ^ 2 * c ^ 2) ^ 2 +
      8 * a ^ 2 * b ^ 3 * c ^ 3 := by ring
    _ = ((a ^ 4 + b ^ 4 + c ^ 4) + (b ^ 2 * c ^ 2)) ^ 2 - (b ^ 2 * c ^ 2) ^ 2 +
      8 * a ^ 2 * b ^ 3 * c ^ 3 := by ring
    _ ≤ ((a ^ 4 + b ^ 4 + c ^ 4) + (b ^ 2 * c ^ 2)) ^ 2 +
      (2 * a ^ 2 * b ^ 3 * c ^ 3 + 2 * a ^ 2 * b ^ 3 * c ^ 3) := by nlinarith
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 + 2 * (a ^ 4 + b ^ 4 + c ^ 4) * (2 * a ^ 2 * b ^ 2 * c ^ 2) +
      4 * (a ^ 2 * b ^ 3 * c ^ 3) ^ 2 := by ring
    _ ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 + 2 * (a ^ 4 + b ^ 4 + c ^ 4) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 +
      4 * (a ^ 2 * b ^ 3 * c ^ 3) ^ 2 := by nlinarith [h3 a (b * c)]
    _ = ((a ^ 4 + b ^ 4 + c ^ 4) + (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) ^ 2 := by ring


--Question 7 Proof by Calculation
--LeanDojo
example {a b c : ℝ} : a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by
  simp only [sq, by]
  simp_rw [by]
  simp only [by]
  simp only [sq_abs]
  simp only [sq, by]

-- Question 8 Proof by calculation (didn't solve it in the first try)

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 := by
--Lean-Github
 -- `rw` is a tactic which works on hypotheses and the goal. `rw hx at hy` would rewrite `hy`
 -- changing `y^2` into `-7` throughout `hy`. The goal is an equation with `x` and `y`, so we
 -- use `rw [hx, hy]` to replace `x` with `2` and `y^2` with `-7` throughout the goal.
 rw [hx, hy]
 -- now the goal is `2 + -7 = -5`, and this is solved by norm_num which is a powerful
 -- tactic for proving arithmetic equality.
 norm_num

--Question 9 Logic
--Lean-Github
example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
 -- exact not_exists
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩
    exact h x hx




--Question 10 Induction
--Lean-Github

example (n : ℕ) : 2 ^ n ≥ n + 1 := by

  induction' n with n hn
  · simp only [pow_zero, Nat.zero_eq, Nat.succ_pos', le_of_lt]
    linarith
  · calc
    2 ^ (n + 1) = 2 * 2 ^ n := pow_succ 2 n
    _ ≥ 2 * (n + 1) := (mul_le_mul_left (by norm_num)).mpr hn
    _ = (n + 1 + 1) + n := by ring
    _ ≥ n + 1 + 1 := by linarith


--Question 11 Parity and divisibility
--Lean-Github
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  convert Nat.pos_of_dvd_of_pos hab hb


--Question 12 Relation
--Lean-Github
example : Reflexive ((·:ℕ) ∣ ·) := by
--From LeanGithub but suggested one_mul but should have been mul_one
 intro n
 use 1
 rw [mul_one]


--Question 13 Logic

example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  --From Lean-Github
  -- Fed it example (P Q : Prop) : P → (P ∨ ¬ Q) := by
 intro hP
 left
 exact hP

--Question 14 Parity and Divisbility
--Lean-Github
example : ¬(5 : ℤ) ∣ 12 := by
 decide


--Question 15 Proofs with Structure
--Lean-Github
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
 cases h with
  | inl h => -- x = 2 case
    rw [h]
    linarith
  | inr h => -- y = -2 case
    rw [h]
    linarith


--Question 16 Logic
--Lean-Github
example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · rintro (hP | hP)
    · exact hP
    · exact hP
  · intro hP
    left
    exact hP
