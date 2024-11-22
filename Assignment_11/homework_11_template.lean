import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Theory.InjectiveSurjective
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function

/-# Exercise 3-/

--Exercise 8.3.10.2

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

example : Inverse u v := by
  dsimp [Inverse]
  constructor
  · ext x
    calc
      (v ∘ u) x = v (u x) := by rfl
      _ = ((u x) - 1) / 5 := by rfl
      _ = ((5 * x + 1) - 1) / 5 := by rfl
      _ = 5 * x / 5 := by ring
      _ = x := by ring
      _ = id x := by rfl
      _ = x := by rfl
  · ext x
    calc
      (u ∘ v) x = u (v x) := by rfl
      _ = 5 * (v x) + 1 := by rfl
      _ = 5 * ((x - 1) / 5) + 1 := by rfl
      _ = x := by ring
      _ = id x := by rfl
      _ = x := by rfl

--Exercise 8.3.10.3

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective]
  intros x1 x2 h1
  apply hf
  apply hg
  apply h1

--Exercise 8.3.10.4

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective]
  intro r
  obtain ⟨y,hy⟩ := hg r
  obtain ⟨x,hx⟩ := hf y
  use x
  calc
    (g ∘ f) x = g (f x) := by rfl
    _ = g y := by rw [hx]
    _ = r := by rw [hy]

/-# Exercise 4-/

--Exercise 8.4.10.1

example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  --use fun ⟨a,b⟩ ↦ (a, a + b)
  use fun ⟨a,b⟩ ↦ (a + b,a)
  dsimp [Inverse]
  constructor
  · ext ⟨r,s⟩
    dsimp
    ring
  · ext ⟨a,b⟩
    dsimp
    ring

--Exercise 8.4.10.2.1

example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (5,1), (3,0)
  dsimp
  constructor
  · numbers
  · numbers

--Exercise 8.4.10.2.2

example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective]
  intro a
  use (a+1,0)
  dsimp
  ring

/-# Problem 2-/

--Exercise 8.3.10.5

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  sorry

--Exercise 8.3.10.7

example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  sorry
