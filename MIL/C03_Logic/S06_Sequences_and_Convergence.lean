import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn

  have ngeNs := le_of_max_le_left hn
  have ngeNt := le_of_max_le_right hn

  calc
    |s n + t n - (a + b)| =  |s n - a + (t n - b)| := by
      congr
      ring
    |s n - a + (t n - b)| ≤ |s n - a| + |t n - b| := by
      exact abs_add _ _
    |s n - a| + |t n - b| < ε/2 + |t n - b| := by
      exact (add_lt_add_iff_right |t n - b|).mpr (hs n ngeNs)
    ε/2 + |t n - b| < ε/2 + ε/2 := by
      exact (add_lt_add_iff_left (ε / 2)).mpr (ht n ngeNt)
    ε/2 + ε/2 = ε := by norm_num



theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h

  intro ε ε_pos
  dsimp

  have ε_c_pos : 0 < ε / |c| := by
    exact div_pos ε_pos acpos

  rcases cs (ε / |c|) ε_c_pos with ⟨Ns, hs⟩
  use Ns
  intro n
  intro ngeNs
  calc
    |c * s n - c * a| = |c*(s n - a)| := by
      congr
      ring
    |c*(s n - a)| = |c| * |s n - a| := by
      exact abs_mul c (s n - a)
    |c| * |s n - a| < |c| * (ε / |c|) := by
      exact mul_lt_mul_of_pos_left (hs n ngeNs) acpos
    |c| * (ε / |c|) = ε := by
      have c_ne_zero : |c| ≠ 0 := by
        symm
        exact ne_of_lt acpos

      exact mul_div_cancel₀ ε c_ne_zero


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n Nlen

  calc
    |s n| = |s n - a + a| := by
      congr
      ring
    |s n - a + a| ≤ |s n - a| + |a| := by
      exact abs_add_le (s n - a) a
    |s n - a| + |a| < |a| + 1 := by
      linarith [h n Nlen]

  sorry

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩

  use max N₀ N₁
  intro n ngtN
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngtN
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngtN

  calc
    |s n * t n - 0| =  |s n| * |t n - 0| := by
      rw [sub_zero]
      rw [abs_mul]
      rw [sub_zero]
    |s n| * |t n - 0| < B * (B / ε) := by
      have sn_lt_B := h₀ n ngeN₀
      have tn_lt_εdivB := h₁ n ngeN₁

      exact mul_lt_mul'' sn_lt_B tn_lt_εdivB (abs_nonneg _) (abs_nonneg _)



theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
