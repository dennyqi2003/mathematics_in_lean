import Mathlib

namespace PropositionalLogic

inductive PropLogic where
  | Var (i : Nat) : PropLogic
  | TRUE : PropLogic
  | FALSE : PropLogic
  | Not (φ : PropLogic) : PropLogic
  | And (φ ψ : PropLogic) : PropLogic
  | Or (φ ψ : PropLogic) : PropLogic
deriving Repr, DecidableEq

def Assignment := Nat → Bool

def Interp (β : Assignment) (φ : PropLogic) : Bool :=
  match φ with
  | PropLogic.Var i => β i
  | PropLogic.TRUE => true
  | PropLogic.FALSE => false
  | PropLogic.Not ψ => !(Interp β ψ)
  | PropLogic.And ψ τ => (Interp β ψ) && (Interp β τ)
  | PropLogic.Or ψ τ => (Interp β ψ) || (Interp β τ)

def is_tautology (φ : PropLogic) : Prop :=
  ∀ (β : Assignment), Interp β φ = true

def is_contradiction (φ : PropLogic) : Prop :=
  ∀ (β : Assignment), Interp β φ = false

def is_satisfiable (φ : PropLogic) : Prop :=
  ∃ (β : Assignment), Interp β φ = true

example (a : PropLogic) : is_tautology (PropLogic.Or PropLogic.TRUE (PropLogic.Not a)) :=
by
  unfold is_tautology
  intro b
  simp [Interp]

def Consequence (φ ψ : PropLogic) : Prop :=
  ∀ (β : Assignment), Interp β φ = true → Interp β ψ = true

infix:95 " |= " => Consequence

def PropSet := PropLogic → Prop

def Consequence_set (Φ : PropSet) (ψ : PropLogic) : Prop :=
  ∀ (β : Assignment), (∀ (φ : PropLogic), Φ φ → (Interp β φ = true)) → Interp β ψ = true

infix:95 " |== " => Consequence_set

def Equivalent (φ ψ : PropLogic) : Prop :=
  ∀ (β : Assignment), Interp β φ = Interp β ψ

infix:90 " === " => Equivalent

theorem equiv_iff_mutual_consequence (p q : PropLogic) :
  p === q ↔ ((p |= q) ∧ (q |= p)) := by
  apply Iff.intro
  · intro h
    constructor
    · intro β hp
      specialize h β
      rw [←h]
      exact hp
    · intro β hq
      specialize h β
      rw [h]
      exact hq
  · intro h β
    cases h with | intro h1 h2 =>
    specialize h1 β
    specialize h2 β
    cases hp : Interp β p
    case false =>
      cases hq : Interp β q
      case false => rfl
      case true =>
        have : Interp β p = true := h2 hq
        rw [hp] at this
        contradiction
    case true =>
      have : Interp β q = true := h1 hp
      rw [this]

def SetSingleton (p : PropLogic) : PropSet :=
  fun x => x = p

def SetUnion (P Q : PropSet) : PropSet :=
  fun x => P x ∨ Q x

theorem prop_excluded_middle (φ : PropLogic) : is_tautology (PropLogic.Or φ (PropLogic.Not φ)) := by
  simp [is_tautology]
  intro b
  simp [Interp]

theorem prop_intro_and (φ ψ : PropLogic) : (SetUnion (SetSingleton φ) (SetSingleton ψ)) |== (PropLogic.And φ ψ) := by
  simp [Consequence_set, Consequence, SetUnion, SetSingleton]
  intro b h1 h2
  simp [Interp]
  tauto

theorem prop_elim_and1 (φ ψ : PropLogic) : ((PropLogic.And φ ψ) |= φ) := by
  simp [Consequence]
  intro b h1
  simp [Interp] at h1
  tauto

theorem prop_elim_and2 (φ ψ : PropLogic) :((PropLogic.And φ ψ) |= ψ) := by
  simp [Consequence]
  intro b h1
  simp [Interp] at h1
  tauto

theorem prop_intro_or1 (φ ψ : PropLogic) : (φ |= (PropLogic.Or φ ψ)) := by
  simp [Consequence]
  intro b h1
  simp [Interp]
  tauto

theorem prop_intro_or2 (φ ψ : PropLogic) : (ψ |= (PropLogic.Or φ ψ)) := by
  simp [Consequence]
  intro b h1
  simp [Interp]
  tauto

theorem prop_double_neg (φ : PropLogic) : φ === PropLogic.Not (PropLogic.Not φ) := by
  simp [Equivalent]
  intro b
  simp [Interp]

theorem prop_idempotence1 (φ : PropLogic) : ((PropLogic.And φ φ) === φ) := by
  simp [Equivalent]
  intro b
  simp [Interp]

theorem prop_idempotence2 (φ : PropLogic) : ((PropLogic.Or φ φ) === φ) := by
  simp [Equivalent]
  intro b
  simp [Interp]

theorem prop_comm_and (φ ψ : PropLogic) : PropLogic.And φ ψ === PropLogic.And ψ φ := by
  simp [Equivalent]
  intro b
  simp [Interp]
  exact Bool.and_comm _ _

theorem prop_comm_or (φ ψ : PropLogic) : PropLogic.Or φ ψ === PropLogic.Or ψ φ := by
  simp [Equivalent]
  intro b
  simp [Interp]
  exact Bool.or_comm _ _

theorem prop_assoc_and (φ ψ ξ : PropLogic) : PropLogic.And (PropLogic.And φ ψ) ξ === PropLogic.And φ (PropLogic.And ψ ξ) := by
  simp [Equivalent]
  intro b
  simp [Interp]
  exact Bool.and_assoc _ _ _

theorem prop_assoc_or (φ ψ ξ : PropLogic) : PropLogic.Or (PropLogic.Or φ ψ) ξ === PropLogic.Or φ (PropLogic.Or ψ ξ) := by
  simp [Equivalent]
  intro b
  simp [Interp]
  exact Bool.or_assoc _ _ _

theorem prop_distributive1 (φ ψ ξ : PropLogic) : (PropLogic.Or φ (PropLogic.And ψ ξ) === PropLogic.And (PropLogic.Or φ ψ) (PropLogic.Or φ ξ)) := by
  simp [Equivalent]
  intro b
  simp [Interp]
  exact Bool.or_and_distrib_left _ _ _

theorem prop_distributive2 (φ ψ ξ : PropLogic) : (PropLogic.And φ (PropLogic.Or ψ ξ) === PropLogic.Or (PropLogic.And φ ψ) (PropLogic.And φ ξ)) := by
  simp [Equivalent]
  intro b
  simp [Interp]
  exact Bool.and_or_distrib_left _ _ _

theorem prop_de_morgan1 (φ ψ : PropLogic) : (PropLogic.Not (PropLogic.And φ ψ) === PropLogic.Or (PropLogic.Not φ) (PropLogic.Not ψ)) := by
  simp [Equivalent]
  intro b
  simp [Interp]

theorem prop_de_morgan2 (φ ψ : PropLogic) : (PropLogic.Not (PropLogic.Or φ ψ) === PropLogic.And (PropLogic.Not φ) (PropLogic.Not ψ)) := by
  simp [Equivalent]
  intro b
  simp [Interp]

theorem prop_absorption1 (φ ψ : PropLogic) : (PropLogic.Or φ (PropLogic.And φ ψ) === φ) := by
  simp [Equivalent]
  intro b
  simp [Interp]
  intro h1 h2
  exact h1

theorem prop_absorption2 (φ ψ : PropLogic) : (PropLogic.And φ (PropLogic.Or φ ψ) === φ) := by
  simp [Equivalent]
  intro b
  simp [Interp]
  intro h1
  left
  exact h1

theorem prop_trans_consequence (φ ψ ξ : PropLogic) : (φ |= ψ) → (ψ |= ξ) → (φ |= ξ) := by
  simp [Consequence]
  intro h1 h2 b h3
  specialize h1 b h3
  specialize h2 b h1
  exact h2

theorem prop_trans_equivalence (φ ψ ξ : PropLogic) : (φ === ψ) → (ψ === ξ) → (φ === ξ) := by
  simp [Equivalent]
  intro h1 h2 b
  specialize h1 b
  specialize h2 b
  rw [← h2]
  exact h1

theorem prop_congruence_not (φ1 φ2 : PropLogic) : (φ1 === φ2 → PropLogic.Not φ1 === PropLogic.Not φ2) := by
  simp [Equivalent]
  intro h1 b
  specialize h1 b
  simp [Interp]
  exact h1

theorem prop_congruence_and (φ1 φ2 ψ1 ψ2 : PropLogic) : (φ1 === φ2 → ψ1 === ψ2 → PropLogic.And φ1 ψ1 === PropLogic.And φ2 ψ2) := by
  simp [Equivalent]
  intro h1 h2 b
  specialize h1 b
  specialize h2 b
  simp [Interp]
  rw [h1, h2]

theorem prop_congruence_or (φ1 φ2 ψ1 ψ2 : PropLogic) : (φ1 === φ2 → ψ1 === ψ2 → PropLogic.Or φ1 ψ1 === PropLogic.Or φ2 ψ2) := by
  simp [Equivalent]
  intro h1 h2 b
  specialize h1 b
  specialize h2 b
  simp [Interp]
  rw [h1, h2]

theorem prop_or_elim (Φ : PropSet) (φ1 φ2 ψ : PropLogic) : (SetUnion Φ (SetSingleton φ1)) |== ψ → (SetUnion Φ (SetSingleton φ2)) |== ψ → (SetUnion Φ (SetSingleton (PropLogic.Or φ1 φ2))) |== ψ := by
  simp [Consequence_set, SetUnion, SetSingleton]
  intro h1 h2 b h3
  specialize h1 b
  specialize h2 b
  cases hh: (Interp b (PropLogic.Or φ1 φ2))
  · apply h1
    intro p h3
    simp [Interp] at hh
    rcases hh with ⟨h4, h5⟩
    rcases h3 with h6 | h7
    · specialize h3 p
      apply h3
      left
      exact h6
    · specialize h3 (PropLogic.Or φ1 φ2)
      have h8 : (Interp b (φ1.Or φ2) = true) := by
        apply h3
        simp
      simp [Interp] at h8
      rw [h7]
      rcases h8 with h9 | h10
      · rw [h4] at h9
        contradiction
      · rw [h5] at h10
        contradiction
  · simp [Interp] at hh
    rcases hh with phi1true | phi2true
    · apply h1
      intro p h4
      rcases h4 with h5 | h6
      · apply h3
        left
        exact h5
      · rw [← h6] at phi1true
        exact phi1true
    · apply h2
      intro p h4
      rcases h4 with h5 | h6
      · apply h3
        left
        exact h5
      · rw [← h6] at phi2true
        exact phi2true

theorem prop_contrapositive (Φ : PropSet) (φ ψ : PropLogic) : (SetUnion Φ (SetSingleton (PropLogic.Not φ))) |== ψ → (SetUnion Φ (SetSingleton (PropLogic.Not ψ))) |== φ := by
  simp [Consequence_set, SetUnion, SetSingleton]
  intro h1 b h2
  specialize h1 b
  cases hh: (Interp b φ)
  · have h3 : (Interp b ψ = true) := by
      apply h1
      intro p h3
      rcases h3 with h4 | h5
      · specialize h2 p
        apply h2
        left
        exact h4
      · rw [h5]
        simp [Interp]
        assumption
    have h4 : (Interp b (PropLogic.Not ψ) = false) := by
      simp [Interp]
      assumption
    have h5 : (Interp b φ = true) := by
      specialize h2 (ψ.Not)
      have h6 : Interp b ψ.Not = true := by
        apply h2
        right
        rfl
      rw [h4] at h6
      contradiction
    rw [← h5, ← hh]
  · tauto

def EmptySet : PropSet := fun _ => False

theorem prop_contrapositive_corollary (φ ψ : PropLogic) :
  PropLogic.Not φ |= ψ ↔ PropLogic.Not ψ |= φ := by
  apply Iff.intro
  · let h1 := prop_contrapositive EmptySet φ ψ
    simp [Consequence_set, SetUnion, SetSingleton, EmptySet, Interp] at h1
    simp [Consequence]
    intro h2
    intro b h3
    apply h1
    intro b2 h4
    apply h2
    simp [Interp]
    exact h4
    simp [Interp] at h3
    exact h3
  · let h1 := prop_contrapositive EmptySet ψ φ
    simp [Consequence_set, SetUnion, SetSingleton, EmptySet, Interp] at h1
    simp [Consequence]
    intro h2
    intro b h3
    apply h1
    intro b2 h4
    apply h2
    simp [Interp]
    exact h4
    simp [Interp] at h3
    exact h3

end PropositionalLogic
