import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

#check Nat

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  · induction' n with n ih
    · simp
      rw [fac]
      simp
      rw [fac]
    · simp
      rw [fac]
      rw [pow_succ]
      simp at ih
      have h: 2 ≤ n+1+1:= by simp
      rw [mul_comm]
      apply Nat.mul_le_mul
      exact h
      exact ih
section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example : s.sum f = ∑ x ∈ s, f x :=
  rfl

example : s.prod f = ∏ x ∈ s, f x :=
  rfl

example : (range n).sum f = ∑ x ∈ range n, f x :=
  rfl

example : (range n).prod f = ∏ x ∈ range n, f x :=
  rfl

example (f : ℕ → ℕ) : ∑ x ∈ range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x ∈ range n.succ, f x = ∑ x ∈ range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x ∈ range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x ∈ range n.succ, f x = (∏ x ∈ range n, f x) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
  induction' n with n ih
  · simp [fac, prod_range_zero]
  simp [fac, ih, prod_range_succ, mul_comm]

example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring

theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm; apply Nat.div_eq_of_eq_mul_right; norm_num
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, mul_add 6, ← ih]
    ring
end

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | _, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  induction' m with m ih
  · rw [zero_add, zero_add]
  · rw [succ_add, succ_add, succ_add]
    congr

theorem zero_mul (n : MyNat) : mul zero n = zero := by
  induction' n with n ih
  · rfl
  rw [mul, ih, zero_add]

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  induction' n with n ih
  · rw [mul,add,mul]
  · rw [mul,mul,add,add]
    rw [ih]
    simp
    rw [add_assoc, add_assoc]
    have tmp: n.add m = m.add n := by rw[add_comm]
    rw [tmp]

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction' k with k ih
  · rw [add, mul, add]
  · rw [add, mul, mul]
    rw [ih]
    rw [add_assoc]

theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  induction' n with n ih
  · rw [mul, zero_mul]
  · rw [mul, ih, succ_mul]

end MyNat
