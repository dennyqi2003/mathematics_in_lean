import Mathlib
import MIL.DennyQi_LogicEbbinghaus.FirstOrderLogic
open Classical
open FirstOrderLogic

set_option maxHeartbeats 9999999

structure Sequent (S : SymbolSet) where
  antecedent : List (Formula S)
  succedent : Formula S

inductive Derivable (S : SymbolSet) : ((Sequent S) -> Prop) where
  | ReflexivityRule (t):
      Derivable S { antecedent := [], succedent := (Formula.Eq t t) }
  | AssumptionRule (Γ φ) :
      φ ∈ Γ → Derivable S { antecedent := Γ, succedent := φ }
  | AntecedentRule (Γ φ) :
      ∀ Γ', (Γ' ⊆ Γ) -> (Derivable S { antecedent := Γ', succedent := φ }) → Derivable S { antecedent := Γ, succedent := φ }
  | ProofByCasesRule (Γ φ) :
      ∀ ψ, (Derivable S { antecedent := ψ :: Γ, succedent := φ }) → (Derivable S { antecedent := (Formula.Neg ψ) :: Γ, succedent := φ }) → Derivable S { antecedent := Γ, succedent := φ }
  | ContradictionRule (Γ φ) :
      ∀ ψ, (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := ψ }) → (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := (Formula.Neg ψ) }) → Derivable S { antecedent := Γ, succedent := φ }
  | OrRuleForAntecedent (Γ φ ψ ξ) :
      (Derivable S { antecedent := φ :: Γ, succedent := ξ }) → (Derivable S { antecedent := ψ :: Γ, succedent := ξ }) → Derivable S { antecedent := (Formula.Or φ ψ) :: Γ, succedent := ξ }
  | OrRuleForSuccedent1 (Γ φ ψ) :
      (Derivable S { antecedent := Γ, succedent := φ }) → Derivable S { antecedent := Γ, succedent := (Formula.Or φ ψ) }
  | OrRuleForSuccedent2 (Γ φ ψ) :
      (Derivable S { antecedent := Γ, succedent := φ }) → Derivable S { antecedent := Γ, succedent := (Formula.Or ψ φ) }
  | RuleForExistsInSuccedent (Γ x φ t) :
      (Derivable S { antecedent := Γ, succedent := FormulaSubstitution S φ [(x, t)] }) → Derivable S { antecedent := Γ, succedent := (Formula.Exists x φ) }
  | RuleForExistsInAntecedent (Γ x y φ ψ) :
      (∀ ξ ∈ Γ, y ∉ Freevar S ξ) -> (y ∉ Freevar S (Formula.Exists x φ)) → (y ∉ Freevar S ψ) -> (Derivable S { antecedent := (FormulaSubstitution S φ [(x, Term.Var y)]) :: Γ, succedent := ψ }) → Derivable S { antecedent := (Formula.Exists x φ) :: Γ, succedent := ψ }
  | SubstitutionRuleForEquality (Γ x t t' φ) :
      (Derivable S { antecedent := Γ, succedent := (FormulaSubstitution S φ [(x,t)]) }) → Derivable S { antecedent := (Formula.Eq t t') :: Γ, succedent := (FormulaSubstitution S φ [(x,t')]) }

def IsValid (S : SymbolSet) (φ : Formula S) : Prop :=
  ∀ (I : Interp S), FormulaEval S I φ

def IsContradiction (S : SymbolSet) (φ : Formula S) : Prop :=
  ∀ (I : Interp S), ¬ FormulaEval S I φ

def IsSatisfiable (S : SymbolSet) (φ : Formula S) : Prop :=
  ∃ (I : Interp S), FormulaEval S I φ

def Consequence (S : SymbolSet) (φ ψ : Formula S) : Prop :=
  ∀ (I : Interp S), FormulaEval S I φ → FormulaEval S I ψ

def FormulaSet (S : SymbolSet) := (Formula S) → Prop

def Consequence_set (S : SymbolSet) (Φ : FormulaSet S) (ψ : Formula S) : Prop :=
  ∀ (I : Interp S), (∀ (φ : Formula S), (Φ φ) → (FormulaEval S I φ)) → FormulaEval S I ψ

def Equivalent (S : SymbolSet) (φ ψ : Formula S) : Prop :=
  ∀ (I : Interp S), FormulaEval S I φ ↔ FormulaEval S I ψ

lemma equiv_iff_mutual_consequence (S : SymbolSet) (φ ψ : Formula S) :
  (Equivalent S φ ψ) ↔ ((Consequence S φ ψ) ∧ (Consequence S ψ φ))
:= by
  constructor
  · intro h1
    dsimp [Equivalent] at h1
    dsimp [Consequence]
    constructor
    · intro I h2
      rw [← h1 I]
      tauto
    · intro I h2
      rw [h1 I]
      tauto
  · dsimp [Equivalent]
    dsimp [Consequence]
    intro h1 I
    rcases h1 with ⟨h2, h3⟩
    specialize h2 I
    specialize h3 I
    tauto

theorem Soundness_of_Sequent_Calculus
  (S : SymbolSet)
  (seq : Sequent S)
  (hder : Derivable S seq)
  :
  (Consequence_set S {φ | φ ∈ seq.antecedent}  (seq.succedent))
:= by
  induction hder with
  | ReflexivityRule t =>
    simp [Consequence_set, FormulaEval]
  | AssumptionRule Γ φ h =>
    simp [Consequence_set]
    intro I h1
    apply h1
    tauto
  | AntecedentRule Γ φ Γ' hsubset h1 h2=>
    simp [Consequence_set]
    intro I h3
    simp [Consequence_set] at h2
    specialize h2 I
    apply h2
    intro φ' h
    apply h3
    tauto
  | ProofByCasesRule Γ φ ψ h1 h2 h3 h4 =>
    simp [Consequence_set]
    intro I h5
    by_cases hcase : FormulaEval S I ψ
    · simp [Consequence_set] at h3
      apply h3
      intro ξ h6
      have h7 : ξ = ψ ∨ ξ ∈ Γ := by tauto
      by_cases heq : ξ = ψ
      · rw [heq]
        tauto
      · have hin : ξ ∈ Γ := by tauto
        apply h5
        tauto
    · simp [Consequence_set] at h4
      apply h4
      intro ξ h6
      have h7 : ξ = ψ.Neg ∨ ξ ∈ Γ := by tauto
      by_cases heq : ξ = ψ.Neg
      · rw [heq]
        tauto
      · have hin : ξ ∈ Γ := by tauto
        apply h5
        tauto
  | ContradictionRule Γ φ ψ h1 h2 h3 h4 =>
    simp [Consequence_set]
    intro I h5
    by_cases hcase : FormulaEval S I φ.Neg
    · have htrue : FormulaEval S I ψ := by
        simp [Consequence_set] at h3
        specialize h3 I
        apply h3
        intro ξ h6
        have h7 : ξ = φ.Neg ∨ ξ ∈ Γ := by tauto
        by_cases hcase' : ξ = φ.Neg
        · rw [hcase']
          tauto
        · have hin : ξ ∈ Γ := by tauto
          apply h5
          tauto
      have hfalse : FormulaEval S I ψ.Neg := by
        simp [Consequence_set] at h4
        specialize h4 I
        apply h4
        intro ξ h6
        have h7 : ξ = φ.Neg ∨ ξ ∈ Γ := by tauto
        by_cases hcase' : ξ = φ.Neg
        · rw [hcase']
          tauto
        · have hin : ξ ∈ Γ := by tauto
          apply h5
          tauto
      simp [FormulaEval] at hcase
      tauto
    · simp [FormulaEval] at hcase
      tauto
  | OrRuleForAntecedent Γ φ ψ ξ h1 h2 h3 h4 =>
    simp [Consequence_set]
    intro I h5
    have hor := h5 (Formula.Or φ ψ)
    have h0 : FormulaEval S I (φ.Or ψ) := by
      apply hor
      tauto
    have hex : (FormulaEval S I φ) ∨ (FormulaEval S I ψ) := by
      exact Decidable.or_iff_not_and_not.mpr h0
    rcases hex with hc1 | hc2
    · simp [Consequence_set] at h3
      specialize h3 I
      apply h3
      intro ζ h6
      have h7 : ζ = φ ∨ ζ ∈ Γ := by tauto
      rcases h6 with h8 | h9
      · rw [h8]
        tauto
      · apply h5
        tauto
    · simp [Consequence_set] at h4
      specialize h4 I
      apply h4
      intro ζ h6
      have h7 : ζ = ψ ∨ ζ ∈ Γ := by tauto
      rcases h6 with h8 | h9
      · rw [h8]
        tauto
      · apply h5
        tauto
  | OrRuleForSuccedent1 Γ φ ψ h1 h2 =>
    simp [Consequence_set]
    intro I h3
    have hconcl : (FormulaEval S I φ) ∨ (FormulaEval S I ψ) := by
      left
      simp [Consequence_set] at h2
      specialize h2 I
      apply h2
      tauto
    simp [Formula.Or, FormulaEval]
    tauto
  | OrRuleForSuccedent2 Γ φ ψ h1 h2 =>
    simp [Consequence_set]
    intro I h3
    have hconcl : (FormulaEval S I φ) ∨ (FormulaEval S I ψ) := by
      left
      simp [Consequence_set] at h2
      specialize h2 I
      apply h2
      tauto
    simp [Formula.Or, FormulaEval]
    tauto
  | RuleForExistsInSuccedent Γ x φ t h1 h2=>
    simp [Consequence_set]
    intro I h3
    simp [Formula.Exists, FormulaEval]
    simp [Consequence_set] at h2
    specialize h2 I h3
    rw [The_Substitution_Lemma_formula] at h2
    simp at h2
    use TermEval S I t
    simp [AssignmentSubstitution] at h2
    simp [eq_comm]
    tauto
  | RuleForExistsInAntecedent Γ x yy φ ψ h1 h2 h3 h4 h5 =>
    simp [Consequence_set]
    intro I h6
    have h7 : FormulaEval S I (Formula.Exists x φ) := by
      apply h6
      tauto
    simp [Formula.Exists, FormulaEval] at h7
    rcases h7 with ⟨d, h7⟩
    have h8 : FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if y = x then d else I.β y } φ ↔ FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if (y = x || y = yy) then d else I.β y } φ := by
      apply The_Coincidence_Lemma_formula <;> try tauto
      intro x1 hx1
      split_ifs with hif1 hif2 hif3 <;> try rfl
      · simp at hif2
        tauto
      · simp at hif3
        rcases hif3 with hc1 | hc2 <;> try tauto
        rw [hc2] at hx1
        simp [Formula.Exists, Freevar] at h2
        specialize h2 hx1
        rw [← h2] at hif1
        tauto
    have h9 : FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if (y = x || y = yy) then d else I.β y } φ := by
      rw [← h8]
      tauto
    have h10 : FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if (y = x || y = yy) then d else I.β y } φ ↔ FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if (y = yy) then d else I.β y } (FormulaSubstitution S φ [(x,Term.Var yy)]) := by
      rw [The_Substitution_Lemma_formula]
      simp
      apply The_Coincidence_Lemma_formula <;> try tauto
      intro x1 hx1
      split_ifs with hif
      · rcases hif with hif1 | hif2
        · rw [← hif1]
          simp [AssignmentSubstitution, TermEval]
        · rw [← hif2]
          simp [AssignmentSubstitution, TermEval]
      · simp at hif
        rcases hif with ⟨ hif1, hif2 ⟩
        simp [AssignmentSubstitution, TermEval]
        split_ifs with hspl <;> tauto
    have h11 : FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if y = yy then d else I.β y } (FormulaSubstitution S φ [(x, Term.Var yy)]) := by
      tauto
    simp [Consequence_set] at h5
    have h12 := h5 { 𝔸 := I.𝔸, β := fun y ↦ if y = yy then d else I.β y }
    have h13 : FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if y = yy then d else I.β y } ψ := by
      apply h12
      intro ζ hzeta
      have hin : ζ = FormulaSubstitution S φ [(x, Term.Var yy)] ∨ ζ ∈ Γ := by tauto
      rcases hin with hc1 | hc2
      · rw [hc1]
        tauto
      · have h13 : FormulaEval S I ζ := by
          apply h6
          tauto
        have h14 : (FormulaEval S I ζ) ↔ (FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if y = yy then d else I.β y } ζ) := by
          have h14 := The_Coincidence_Lemma_formula S I.𝔸.A I.𝔸.a I.𝔸.a I.β (fun y ↦ if y = yy then d else I.β y) ζ
          apply h14 <;> try tauto
          intro x1 hx1
          split_ifs with hspl <;> try tauto
          rw [hspl] at hx1
          specialize h1 ζ
          tauto
        tauto
    have hconcl : (FormulaEval S I ψ) ↔ (FormulaEval S { 𝔸 := I.𝔸, β := fun y ↦ if y = yy then d else I.β y } ψ) := by
      have h14 := The_Coincidence_Lemma_formula S I.𝔸.A I.𝔸.a I.𝔸.a I.β (fun y ↦ if y = yy then d else I.β y) ψ
      apply h14 <;> try tauto
      intro x1 hx1
      split_ifs with hspl <;> try tauto
      rw [hspl] at hx1
      tauto
    tauto
  | SubstitutionRuleForEquality Γ x t t' φ h1 h2 =>
    simp [Consequence_set]
    intro I h3
    dsimp [Consequence_set] at h2
    specialize h2 I
    have h4 : FormulaEval S I (Formula.Eq t t') := by
      apply h3
      tauto
    simp [FormulaEval] at h4
    rw [The_Substitution_Lemma_formula]
    simp
    rw [← h4]
    have h5 : (∀ (φ : Formula S), {φ | φ ∈ Γ} φ → FormulaEval S I φ) := by
      intro ξ h6
      apply h3
      refine Set.setOf_app_iff.mpr ?_
      right
      tauto
    have h6 := h2 h5
    rw [The_Substitution_Lemma_formula] at h6
    tauto
