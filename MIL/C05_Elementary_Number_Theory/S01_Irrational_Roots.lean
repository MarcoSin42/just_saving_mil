import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    apply even_of_even_sqr
    rw [sqr_eq]
    apply dvd_mul_right

  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have  h₁ : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have h₂ : 2 * k ^ 2 = n ^ 2 := by
    have two_neq_zero : 2 ≠ 0 := by
      exact Ne.symm (Nat.zero_ne_add_one 1)
    apply (mul_right_inj' two_neq_zero).mp
    exact h₁
  have  h₃: 2 ∣ n := by
    apply even_of_even_sqr
    rw [←h₂]
    apply dvd_mul_right

  have h₄ : 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd
    exact this
    exact h₃

  have : 2 ∣ 1 := by
    convert h₄
    apply symm
    exact coprime_mn

  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  -- Proof by contradiction
  intro sqr_eq

  have p_dvd_m : p ∣ m := by
    apply prime_p.dvd_of_dvd_pow
    rw [sqr_eq]
    apply dvd_mul_right

  -- ∃ k ∈ ℕ, s.t. m = k * p
  -- This follows from the fact that m is divisible by p, and hence is some multiple of p
  obtain ⟨k, meq⟩ := by
    apply dvd_iff_exists_eq_mul_left.mp p_dvd_m

  have h₁ : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq]
    rw [meq]
    ring
  have h₂ : p * k ^ 2 = n ^ 2 := by
    have p_neq_zero: p ≠ 0 := by
      exact Nat.Prime.ne_zero prime_p
    exact (Nat.mul_right_inj p_neq_zero).mp h₁
  have p_dvd_n : p ∣ n := by
    apply prime_p.dvd_of_dvd_pow
    rw [←h₂]
    apply dvd_mul_right

  have p_dvd_gcd_mn : p ∣ Nat.gcd m n := by
    apply Nat.dvd_gcd
    exact p_dvd_m
    exact p_dvd_n

  /-
  Show that p ∣ 1 follows from the fact that
  1. p is divisor of the gcd of m and n
  2. Since m and n are coprime, this must imply that p is a divisor of 1, by definition of gcd of two coprime numbers
  -/
  have p_dvd_one : p ∣ 1 := by
    convert p_dvd_gcd_mn
    symm
    exact coprime_mn

  -- Finally, we show a contradiction by showing that given our premises we have that 2 ≤ 1 (which is obviously false)
  have two_lt_one : 2 ≤  1 := by
    apply prime_p.two_le.trans
    exact (Nat.Prime.dvd_factorial prime_p).mp p_dvd_one

  norm_num at two_lt_one



#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    sorry
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    sorry
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    sorry
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    sorry
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  sorry

#check multiplicity
