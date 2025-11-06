import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

#check Nat.factorial_pos
#check Nat.dvd_factorial
#check Nat.dvd_sub'

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial n + 1 := by
    induction' n with n ih
    · simp
    · simp
      rw [Nat.factorial]
      simp at ih
      apply Right.one_le_mul
      simp
      exact ih
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := by
    apply Nat.dvd_factorial
    apply Nat.Prime.pos pp
    apply ple
  have pdvd1 : p ∣ 1 := by
    have h1 : p ∣ (n.factorial + 1) - (n.factorial) := by
      apply Nat.dvd_sub' pdvd this
    simp at h1
    rw [h1]
  show False
  have h2 : p = 1 := by
    have h1 : p ∣ (n.factorial + 1) - (n.factorial) := by
      apply Nat.dvd_sub' pdvd this
    simp at h1
    apply h1
  rw [h2] at pp
  contradiction
open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto
example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto

end

#check Finset.dvd_prod_of_mem
example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
  Finset.dvd_prod_of_mem _ h

#check Nat.Prime.eq_one_or_self_of_dvd
theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  have h1 : p = 1 ∨ p = q := by
    apply Nat.Prime.eq_one_or_self_of_dvd prime_q
    exact h
  have h2 : ¬ p = 1 := by
    by_contra h2
    rw [h2] at prime_p
    contradiction
  tauto

#check Nat.prime_def_lt
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₀ with ⟨h3, h4⟩
  rcases h₁ with h5 | h7
  · left
    rcases h5 with ⟨c, h6⟩
    rw [h6]
    have cdva : c ∣ a := by
      exact Dvd.intro_left p (id (Eq.symm h6))
    have cgeq0 : c > 0 := by
      refine Nat.zero_lt_of_ne_zero ?_
      by_contra ceq0
      rw [ceq0] at h6
      simp at h6
      rw [h6] at h3
      exact Nat.prime_zero_false h3
    have cleqa : c < a := by
      rw [h6]
      have pgeq1 : 1 < p := by
        exact Nat.Prime.one_lt prime_p
      exact (Nat.lt_mul_iff_one_lt_left cgeq0).mpr pgeq1
    have ceq1 : c = 1 := by
      rw [Nat.prime_def_lt] at h3
      rcases h3 with ⟨ h8, h9⟩
      specialize h9 c cleqa cdva
      assumption
    rw [ceq1]
    norm_num
  · right
    apply ih h4 h7


example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter


#check Finset.prod_pos
#check Nat.succ_le_of_lt
#check dvd_prod_of_mem
#check Nat.le_of_dvd
theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
    simp
    apply Nat.succ_le_of_lt
    apply Finset.prod_pos
    intros i his'
    rw [mem_s'] at his'
    exact Nat.Prime.pos his'
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
    apply dvd_prod_of_mem
    rw [mem_s']
    assumption
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
  have h1: p ≤ 1 := by
    apply Nat.le_of_dvd
    norm_num
    apply this
  rw [Nat.prime_def_lt] at pp
  rcases pp with ⟨h2, h3⟩
  linarith

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

#check Nat.div_dvd_of_dvd
#check Nat.div_lt_self
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  · apply Nat.div_dvd_of_dvd h₀
  · apply Nat.div_lt_self
    linarith
    linarith

#check dvd_mul_of_dvd_right
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  . by_cases h0: Nat.Prime m
    · use m
    · specialize ih m mltn h1 h0
      rcases ih with ⟨pp, h2, h3, h4⟩
      use pp
      constructor
      apply h2
      constructor
      · exact Nat.dvd_trans h3 mdvdn
      · apply h4
  . by_cases h0: Nat.Prime (n/m)
    · use (n/m)
      constructor
      apply h0
      constructor
      exact Nat.div_dvd_of_dvd mdvdn
      apply h1
    · have ndmleqn : n/m<n := by
        refine Nat.div_lt_self ?_ mge2
        by_contra h
        linarith
      specialize ih (n/m) ndmleqn h1 h0
      rcases ih with ⟨pp, h2, h3, h4⟩
      use pp
      constructor
      apply h2
      constructor
      · have ndivmdivn : n/m ∣ n := by
          exact Nat.div_dvd_of_dvd mdvdn
        exact Nat.dvd_trans h3 ndivmdivn
      · apply h4

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

#check mem_of_dvd_prod_primes
#check Nat.prime_three
#check Nat.Prime.dvd_mul
#check dvd_prod_of_mem
#check mem_erase
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
    simp
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    rw [← hs]
    constructor
    apply pp
    apply p4eq
  have pne3 : p ≠ 3 := by
    by_contra peq3
    rw [peq3] at pdvd
    simp at pdvd
    have threedvdx : 3 ∣ ∏ i ∈ s.erase 3, i := by
      rw [Nat.Prime.dvd_mul] at pdvd
      rcases pdvd with h1 | h2
      · have n3div4 : ¬ 3 ∣ 4 := by
          exact of_decide_eq_false rfl
        contradiction
      · assumption
      norm_num
    have : 3 ∈ s.erase 3 := by
      apply mem_of_dvd_prod_primes
      norm_num
      intro n h0
      rw [mem_erase] at h0
      rcases h0 with ⟨h1, h2⟩
      rw [← hs] at h2
      rcases h2 with ⟨h3, h4⟩
      assumption
      assumption
    rw [mem_erase] at this
    rcases this with ⟨h5, h6⟩
    apply h5
    contradiction
  have : p ∣ 4 * ∏ i ∈ erase s 3, i := by
    have pdvdx : p ∣ ∏ i ∈ s.erase 3, i := by
      have pinserase : p ∈ s.erase 3 := by
        exact mem_erase_of_ne_of_mem pne3 ps
      exact dvd_prod_of_mem (fun i ↦ i) pinserase
    exact Dvd.dvd.mul_left pdvdx 4
  have : p ∣ 3 := by
    have qxz : p ∣ (4 * ∏ i ∈ s.erase 3, i + 3) - (4 * ∏ i ∈ s.erase 3, i) := by
      apply Nat.dvd_sub' pdvd this
    simp at qxz
    assumption
  have : p = 3 := by
    refine Nat.Prime.eq_of_dvd_of_prime pp ?_ this
    norm_num
  contradiction
