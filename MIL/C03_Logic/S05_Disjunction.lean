import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]

  rw [abs_of_neg h]
  linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
    linarith
  . rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with zero_le_sum | zero_gt_sum
  . rw [abs_of_nonneg zero_le_sum]
    linarith[le_abs_self x, le_abs_self y]
  . rw [abs_of_neg zero_gt_sum]
    linarith[neg_le_abs_self x, neg_le_abs_self y]


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with y_nonneg | y_neg
  . rw [abs_of_nonneg y_nonneg]
    constructor
    . intro h
      left
      exact h

    . intro h
      rcases h with x_lt_y | x_lt_neg_y
      exact x_lt_y
      linarith
  . rw [abs_of_neg y_neg]
    constructor
    . intro x_lt_neg_y
      right
      exact x_lt_neg_y

    . intro h
      rcases h with x_lt_y | x_lt_neg_y
      linarith
      linarith


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with x_nonneg | x_neg
  . rw [abs_of_nonneg x_nonneg]
    constructor
    . intro x_lt_y
      constructor
      linarith
      linarith

    . intro h
      exact h.right
  . rw [abs_of_neg x_neg]
    constructor

    . intro neg_x_lt_y
      constructor
      linarith
      linarith

    . intro h
      linarith


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl|rfl⟩
  linarith[sq_nonneg x, sq_nonneg y]
  linarith[sq_nonneg x, sq_nonneg y]


example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have dif_sq : x^2 - 1 = 0 := by rw [h, sub_self]
  have sq_x : (x + 1)*(x - 1) = 0 := by
    rw [←dif_sq]
    ring

  rcases eq_zero_or_eq_zero_of_mul_eq_zero sq_x with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1


example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have dif_sq : x^2 - y^2 = 0 := by rw [h, sub_self]
  have dif_sq_xy : (x + y)*(x - y) = 0 := by
    rw [←dif_sq]
    ring

  rcases eq_zero_or_eq_zero_of_mul_eq_zero dif_sq_xy with x_plus_y | x_minus_y
  . right
    exact eq_neg_iff_add_eq_zero.mpr x_plus_y
  . left
    exact eq_of_sub_eq_zero x_minus_y


section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by

  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  . intro p_imp_q
    by_cases h : P
    . right
      exact p_imp_q h
    . left
      exact h

  rintro (not_p | q)
  . intro p
    exact absurd p not_p
  . intro p
    exact q
