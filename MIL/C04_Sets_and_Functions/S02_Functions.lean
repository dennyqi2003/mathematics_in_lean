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

#print mem_image_of_mem
#print image_subset_iff
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h1
    simp only [subset_def, preimage]
    simp
    intro x xs
    simp only [image, subset_def] at h1
    specialize h1 (f x)
    apply h1
    simp
    use x
  · intro h1
    simp only [subset_def, image]
    simp
    intro x h2
    simp only [subset_def, preimage] at h1
    simp at h1
    specialize h1 x h2
    apply h1

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  simp only [subset_def, preimage]
  simp
  intro x1 x2 x2s feq
  simp only [Injective] at h
  have x1x2eq : x2 = x1 := by
    apply h feq
  rw [← x1x2eq]
  apply x2s


example : f '' (f ⁻¹' u) ⊆ u := by
  simp only [subset_def, preimage, image]
  simp


example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  simp only [subset_def, preimage, image]
  simp
  intro x xinu
  simp only [Surjective] at h
  specialize h x
  rcases h with ⟨b, exb⟩
  use b
  constructor
  · rw [exb]
    apply xinu
  · apply exb


example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  simp only [subset_def, image]
  simp
  intro x xins
  simp only [subset_def] at h
  specialize h x xins
  use x


example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  simp only [subset_def, preimage]
  simp
  intro x fxinu
  simp only [subset_def] at h
  specialize h (f x) fxinu
  apply h


example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  simp only [subset_def, preimage]
  simp
  ext x
  constructor <;> simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  simp only [subset_def, image]
  simp
  intro x1 x2 x2ins x2int fx2eqx1
  constructor <;> use x2

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  simp only [subset_def, image]
  simp
  intro x1 h1 x2 h2 h3
  use x2
  have h4 : x2 = x1 := by
    apply h h3
  constructor
  · constructor
    · rw [h4]
      apply h1
    · apply h2
  · apply h3

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  simp only [subset_def, image, mem_diff]
  simp
  intro x1 h1 h2
  use x1
  constructor
  · constructor
    · apply h1
    · by_contra hcontra
      specialize h2 x1 hcontra
      apply h2
      rfl
  · rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  simp only [subset_def, image, mem_diff]
  simp

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  simp only [subset_def, image, inter_def]
  simp
  ext x
  simp
  constructor
  · simp
    intro x1 h1 h2 h3
    use x1
    constructor
    · constructor
      · apply h1
      · rw [h2]
        apply h3
    · apply h2
  · simp
    intro x1 h1 h2 h3
    constructor
    use x1
    rw [← h3]
    apply h2

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  simp only [subset_def, image, inter_def]
  simp
  intro x1 x2 h1 h2 h3
  constructor
  · use x2
  · rw [← h3]
    apply h2

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  simp only [subset_def, image, inter_def]
  simp
  intro x1 h1 h2
  constructor
  · use x1
  · apply h2

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  simp only [subset_def, image, union_def]
  simp
  intro x1 h2
  rcases h2 with h3 | h4
  · left
    use x1
  · right
    apply h4

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  simp only [subset_def, image, mem_iUnion, mem_iUnion₂]
  ext x
  simp
  constructor
  · intro h1
    rcases h1 with ⟨a, ha⟩
    have ⟨h2, h3⟩ := ha
    rcases h2 with ⟨ii, hii⟩
    use ii
    use a
  · intro h1
    rcases h1 with ⟨ii, hii⟩
    rcases hii with ⟨a, ha⟩
    have ⟨h2, h3⟩ := ha
    use a
    constructor
    use ii
    apply h3

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  simp only [subset_def, image, mem_iUnion, mem_iUnion₂]
  simp
  intro a h1 i
  specialize h1 i
  use a

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  simp only [subset_def, image, mem_iUnion, mem_iUnion₂]
  simp
  intro x h1
  have eb : ∃ b, f b = x := by
    specialize h1 i
    rcases h1 with ⟨tmp, htmp⟩
    use tmp
    apply htmp.2
  rcases eb with ⟨b, hb⟩
  rw [← hb] at h1
  use b
  constructor
  · intro ii
    specialize h1 ii
    rcases h1 with ⟨c, hc⟩
    have ⟨hc1, hc2⟩ := hc
    have eqbc : c = b := by
      apply injf hc2
    rw [← eqbc]
    apply hc1
  · apply hb


example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  simp only [preimage, mem_iUnion, mem_iUnion₂]
  ext x
  constructor <;> simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  simp only [preimage, mem_iUnion, mem_iUnion₂]
  ext x
  constructor <;> simp

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
  simp only [InjOn]
  intro x1 h1 x2 h2 sqrteq
  have sqr : (√x1)^2 = (√x2)^2 := by
    congr
  rw [sq_sqrt, sq_sqrt] at sqr
  apply sqr
  apply h2
  apply h1

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  simp only [InjOn]
  intro x1 h1 x2 h2 h
  have h0 : √ (x1^2) = √ (x2^2) := by
    congr
  rw [sqrt_sq, sqrt_sq] at h0
  apply h0
  apply h2
  apply h1

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  simp only [image]
  simp
  ext x
  constructor <;> simp
  · intro x1 h1 h2
    rw [← h2]
    apply sqrt_nonneg
  · intro h1
    use (x^2)
    constructor
    · apply sq_nonneg
    · rw [sqrt_sq]
      apply h1

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  simp only [range]
  simp
  ext x
  constructor <;> simp
  · intro x1 h1
    rw [← h1]
    apply sq_nonneg
  · intro h1
    use (√ x)
    rw [sq_sqrt]
    apply h1

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
  · intro injf
    simp only [LeftInverse]
    intro x
    have h1 : f (inverse f (f x)) = f x := by
      apply inverse_spec
      use x
    apply injf h1
  · intro h0
    simp only [LeftInverse] at h0
    simp only [Injective]
    intro x1 x2 h1
    have tmp : inverse f (f x1) = inverse f (f x2) := by
      congr
    have hx1 : inverse f (f x1) = x1 := by
      apply h0
    have hx2 : inverse f (f x2) = x2 := by
      apply h0
    rw [hx1, hx2] at tmp
    assumption

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro surjf
    simp only [RightInverse, LeftInverse]
    intro x
    simp only [Surjective] at surjf
    specialize surjf x
    rcases surjf with ⟨a, ha⟩
    apply inverse_spec
    use a
  · intro h0
    simp only [RightInverse, LeftInverse] at h0
    simp only [Surjective]
    intro x
    specialize h0 x
    use inverse f x

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
    simp only [S]
    simp
    assumption
  have h₃ : j ∉ S := by
    rw [← h]
    apply h₁
  contradiction

-- COMMENTS: TODO: improve this
end
