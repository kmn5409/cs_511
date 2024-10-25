import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨hpq, hqp⟩ := h
  constructor
  · intro a
    obtain ⟨h1, h2⟩ := a
    constructor
    · apply hpq
      apply h1
    · apply h2
  · intro b
    obtain ⟨h3,h4⟩ := b
    constructor
    · apply hqp
      apply h3
    · apply h4




--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro a
    obtain h1 | h2 := a
    · right
      apply h1
    · left
      apply h2
  · intro b
    obtain h3 | h4 := b
    · right
      apply h3
    · left
      apply h4

--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro h1
      have : P ∨ Q
      · left
        apply h1
      contradiction
    · intro t
      have: P ∨ Q
      · right
        apply t
      contradiction
  · intro g
    obtain ⟨h2, h3⟩ := g
    intro g1
    obtain h4 | h5 := g1
    · contradiction
    · contradiction

--Exercise 5.1.7.11

@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h1
    have ⟨x, hx⟩ := h1
    obtain ⟨g, r⟩ := h x
    use x
    apply g
    apply hx
  · intro h2
    have ⟨x, hx⟩ := h2
    obtain ⟨d, f⟩ := h x
    use x
    apply f
    apply hx

--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h
    obtain ⟨x, y, h1⟩ := h
    use y, x
    apply h1
  · intro g
    obtain ⟨y, x, g1⟩ := g
    use x, y
    apply g1

--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h1 y x
    apply h1
  · intro h2 x y
    apply h2

--Exercise 5.1.7.14

@[autograded 3]
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

--Exercise 5.2.7.2

@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  sorry
