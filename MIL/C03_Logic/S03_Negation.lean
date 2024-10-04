import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro h
  rcases h with ⟨a, ha⟩
  rcases h a with ⟨x, hx⟩
  have h' := ha x

  have h1 := lt_of_lt_of_le hx h'

  have h1_false := lt_self_iff_false (f x)
  have h1_is_false := h1_false.mp h1
  exact h1_is_false


example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨x, hx⟩
  have h : x + 1 ≤ x := hx (x+1)
  have h': x < x + 1 := by exact lt_add_one x
  exact not_le_of_lt h' h

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  exact h h''

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h''
  exact h

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b leab
    exact le_rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have one_le_zero: (1 : ℝ) ≤ 0 := h monof h'
  have zero_le_one: 0 < 1 := by exact lt_add_one 0
  apply absurd zero_le_one
  apply not_lt_of_le
  exact
  sorry

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  apply (lt_self_iff_false x).mp
  exact
  sorry

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro a
  rw [not_exists] at h
  have ha := h a
  exact ha

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rw [not_exists]
  exact h

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  rw [←not_forall]
  exact h

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  rw [not_forall]
  exact h

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  rw [not_not] at h
  exact h

example (h : Q) : ¬¬Q := by
  rw [not_not]
  exact h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  use x

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  rw [FnHasUb] at h
  dsimp only [FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
