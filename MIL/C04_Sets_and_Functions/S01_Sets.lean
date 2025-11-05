import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  simp only [subset_def, inter_def, union_def]
  dsimp
  intro x h1
  rcases h1 with h2 | h3
  · constructor
    · simp only [inter_def, mem_setOf] at h2
      apply h2.1
    · left
      apply h2.2
  · constructor
    · apply h3.1
    · right
      apply h3.2


example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  dsimp only [union_def] at xntu
  dsimp at xntu
  push_neg at xntu
  constructor
  constructor
  apply xs
  apply xntu.1
  apply xntu.2

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s := by
  dsimp only [inter_def]
  apply Subset.antisymm
  intro x
  dsimp
  intro h1
  constructor
  apply h1.2
  apply h1.1
  intro x
  dsimp
  intro h1
  constructor
  apply h1.2
  apply h1.1

example : s ∩ (s ∪ t) = s := by
  dsimp only [inter_def, union_def]
  apply Subset.antisymm
  intro x
  intro h1
  dsimp at h1
  apply h1.1
  intro x
  intro h1
  dsimp
  constructor
  apply h1
  left
  apply h1

example : s ∪ s ∩ t = s := by
  dsimp only [inter_def, union_def]
  apply Subset.antisymm
  intro x
  intro h1
  dsimp at h1
  rcases h1 with h2 | h3
  apply h2
  apply h3.1
  intro x h1
  dsimp
  left
  apply h1

example : s \ t ∪ t = s ∪ t := by
  simp only [union_def, mem_diff]
  ext x
  constructor
  intro h
  dsimp
  dsimp at h
  rcases h with h1 | h2
  left
  apply h1.1
  right
  apply h2
  intro h
  simp
  simp at h
  rcases h with h1 | h2
  by_cases xt: x ∈ t
  right
  apply xt
  left
  constructor
  apply h1
  apply xt
  right
  apply h2

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  simp only [union_def, mem_diff]
  ext x
  constructor
  · intro h
    simp
    simp at h
    constructor
    · rcases h with h1 | h2
      · left
        apply h1.1
      · right
        apply h2.1
    · intro h3
      rcases h with h1 | h2
      · apply h1.2
      · exfalso
        have ⟨h4, h5⟩ := h2
        apply h5 h3
  · intro h
    simp
    simp at h
    have ⟨h1, h2⟩ := h
    rcases h1 with h3 | h4
    · left
      constructor
      apply h3
      apply h2 h3
    · right
      constructor
      apply h4
      by_contra h5
      have : x ∉ t := by
        apply h2 h5
      apply this
      apply h4


def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

#print Nat.Prime.eq_two_or_odd
#print Nat.odd_iff
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  intro h
  simp
  simp at h
  have ⟨h1, h2⟩ := h
  by_cases ng2: 2 < n
  · have h3 : n = 2 ∨ n % 2 = 1 := by
      apply Nat.Prime.eq_two_or_odd h1
    rcases h3 with h4 | h5
    · exfalso
      linarith
    rw [← Nat.odd_iff] at h5
    apply h5
  · exfalso
    apply ng2 h2


#print Prime

#print Nat.Prime
#print Nat.prime_iff
example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  have : x ∈ t := by
    rw [Set.subset_def] at ssubt
    specialize ssubt x xs
    exact ssubt
  constructor
  · specialize h₀ x
    apply h₀ this
  · specialize h₁ x this
    apply h₁

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, h⟩
  use x
  have : x ∈ t := by
    rw [Set.subset_def] at ssubt
    specialize ssubt x h.1
    exact ssubt
  constructor
  · apply this
  · apply h.2.2

end

end



section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h1 j
    rcases h1 with h2 | h3
    · right
      apply h2
    · left
      simp only [mem_iInter] at h3
      specialize h3 j
      apply h3
  · intro h1
    by_cases xs : x ∈ s
    · left
      apply xs
    · right
      simp only [mem_iInter]
      intro i
      specialize h1 i
      rcases h1 with h2 | h3
      · apply h2
      · exfalso
        apply xs h3

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

#print Nat.exists_infinite_primes
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  rw [mem_iUnion₂]
  have existsp : ∃ (q : ℕ), x ≤ q ∧ q ∈ primes := by
    apply Nat.exists_infinite_primes
  rcases existsp with ⟨q, ⟨h1, h2⟩⟩
  use q
  simp
  constructor <;> assumption

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
