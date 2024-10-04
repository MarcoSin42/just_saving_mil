import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro h x xs
    have fx : f x ∈ f '' s := by
      exact mem_image_of_mem f xs
    exact h fx
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw [← fxeq]
  apply h
  exact xs


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fy⟩
  have y_eq_x := h fy 
  rw [←y_eq_x]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro x ⟨w, w_pre, fw_eq_x⟩
  have h : x ∈ u := by
    have x_eq_fw := Eq.symm fw_eq_x
    exact mem_of_eq_of_mem x_eq_fw w_pre
  exact h
  
example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y yu
  rcases h y with ⟨x, fx_eq_y⟩
  
  use x
  constructor
  . show f x ∈ u
    rw [fx_eq_y]
    exact yu
  exact fx_eq_y

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, fx_eq_y⟩
  use x
  constructor
  have xt := h xs
  exact xt
  exact fx_eq_y

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x xfu
  have xfv : x ∈ f ⁻¹' v := by
    exact h xfu
  exact xfv
  

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  rfl
  

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, xst, fx_eq_y⟩
  constructor
  use x
  constructor
  exact xst.left
  exact fx_eq_y

  rw [←fx_eq_y]
  use x
  constructor
  exact xst.right
  rfl

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₀, x₀s, rfl⟩,⟨x₂, x₂t, fx₂eq⟩⟩
  use x₀
  constructor
  have x₀t : x₀ ∈ t := by
    have fx₀eq : f x₀ = f x₂ := by
      symm
      exact fx₂eq
    have x₀eqx₁ : x₀ = x₂ := by
      exact h fx₀eq
    have x₀t : x₀ ∈ t := by
      exact mem_of_eq_of_mem x₀eqx₁ x₂t
    exact x₀t
  constructor
  exact x₀s
  exact x₀t
  rfl
  

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x₀, x₀s, rfl⟩, ynft⟩
  use x₀
  constructor
  . constructor
    . exact x₀s
    . intro xt
      apply ynft
      use x₀, xt
  rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := fun _ ↦id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  . rintro ⟨⟨x,xs, rfl⟩, fxv⟩
    use x
    constructor
    constructor
    exact xs
    use fxv
    rfl
  . rintro ⟨x, ⟨⟨xs, xfv⟩, fx_eq_y⟩⟩
    constructor
    use x
    have y_eq_fx : y = f x := by
      symm
      exact fx_eq_y
    exact mem_of_eq_of_mem y_eq_fx xfv
  

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨⟨_, xfu⟩, rfl⟩⟩
  constructor
  use x
  exact xfu


example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, xfu⟩
  constructor
  use x
  exact xfu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  constructor
  exact mem_image_of_mem f xs
  right
  exact fxu
  

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  use x
  constructor
  use i
  exact fxeq

  

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp
  intro x h fxeq i
  use x
  constructor
  have xAi := h i
  exact xAi
  exact fxeq


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rcases h i with ⟨x, xai,fx_eq_y⟩
  use x
  constructor
  . intro i'
    rcases h i' with ⟨x', ⟨xai', fx'_eq_y⟩⟩
    have : f x = f x' := by
      rw [fx_eq_y]
      rw [fx'_eq_y]
    have : x = x' := by
      exact injf this
    rw [this]
    exact xai'
  exact fx_eq_y

  

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp
  
example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ypos
  intro h
  calc
    x = √x^2 := by
      symm
      exact sq_sqrt xnonneg
    √x^2 = √y^2 := by
      rw [h]
    √y^2 = y := by
      exact sq_sqrt ypos
    
  

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  dsimp
  intro xsq_eq_ysq

  calc
    x = √(x^2) := by
      symm
      exact sqrt_sq xnonneg
    √(x^2) = √(y^2) := by
      apply congrArg
      exact xsq_eq_ysq
    √(y ^ 2) = y := by
      exact sqrt_sq ynonneg
  

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  constructor
  . rintro ⟨x, ⟨xpos, rfl⟩⟩
    apply sqrt_nonneg
  intro xpos
  use x^2
  constructor
  dsimp at *
  exact sq_nonneg x
  exact sqrt_sq xpos


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  dsimp
  . rintro ⟨x, rfl⟩
    apply pow_two_nonneg
  intro ypos
  use √x
  apply sq_sqrt
  dsimp at *
  exact ypos 
  

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro injf y
    apply injf
    apply inverse_spec
    use y
  intro h x₁ x₂ fx_eq_fy
  
  have y₁ := h x₁
  rw [← y₁]
  rw [← h x₂]
  rw [fx_eq_fy]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro surjf y
    apply inverse_spec
    apply surjf
  intro h₁ y₁
  use inverse f y₁
  apply h₁

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    exact h₁
  
  have h₃ : j ∉ S := by
    rw [←h]
    exact h₁
  
  contradiction

-- COMMENTS: TODO: improve this
end
