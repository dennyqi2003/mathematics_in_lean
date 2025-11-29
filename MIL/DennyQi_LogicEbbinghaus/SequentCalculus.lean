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

theorem Derivable.Tertium_non_datur
  (S : SymbolSet)
  (φ : Formula S)
  :
  (Derivable S { antecedent := [], succedent := Formula.Or φ (Formula.Neg φ) })
:= by
  have hseq1 : (Derivable S { antecedent := [φ], succedent := φ }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq2 : (Derivable S { antecedent := [φ], succedent := Formula.Or φ (Formula.Neg φ) }) := by
    apply Derivable.OrRuleForSuccedent1
    tauto
  have hseq3 : (Derivable S { antecedent := [Formula.Neg φ], succedent := Formula.Neg φ }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq4 : (Derivable S { antecedent := [Formula.Neg φ], succedent := Formula.Or φ (Formula.Neg φ) }) := by
    apply Derivable.OrRuleForSuccedent2
    tauto
  have hseq5 : (Derivable S { antecedent := [], succedent := Formula.Or φ (Formula.Neg φ) }) := by
    apply Derivable.ProofByCasesRule [] (Formula.Or φ (Formula.Neg φ)) (φ) <;> tauto
  exact hseq5

theorem Derivable.Modified_Contradiction_Rule
  (S : SymbolSet)
  (Γ : List (Formula S))
  (φ ψ: Formula S)
  (hseq1 : Derivable S { antecedent := Γ, succedent := ψ })
  (hseq2 : Derivable S { antecedent := Γ, succedent := Formula.Neg ψ })
  :
  (Derivable S { antecedent := Γ, succedent := φ })
:= by
  have hseq3 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := ψ }) := by
    apply Derivable.AntecedentRule ((Formula.Neg φ) :: Γ) ψ Γ
    repeat tauto
  have hseq4 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := Formula.Neg ψ }) := by
    apply Derivable.AntecedentRule ((Formula.Neg φ) :: Γ) (Formula.Neg ψ) Γ
    repeat tauto
  have hseq5 : (Derivable S { antecedent := Γ, succedent := φ }) := by
    apply Derivable.ContradictionRule Γ φ ψ
    repeat tauto
  exact hseq5

theorem Derivable.Chain_Rule
  (S : SymbolSet)
  (Γ : List (Formula S))
  (φ ψ : Formula S)
  (hseq1 : Derivable S { antecedent := Γ, succedent := φ })
  (hseq2 : Derivable S { antecedent := φ :: Γ, succedent := ψ })
  :
  (Derivable S { antecedent := Γ, succedent := ψ })
:= by
  have hseq3 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := φ }) := by
    apply Derivable.AntecedentRule ((Formula.Neg φ) :: Γ) φ Γ
    repeat tauto
  have hseq4 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := Formula.Neg φ }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq5 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := ψ }) := by
    apply Derivable.Modified_Contradiction_Rule S ((Formula.Neg φ) :: Γ) ψ φ <;> tauto
  have hseq6 : (Derivable S { antecedent := Γ, succedent := ψ }) := by
    apply Derivable.ProofByCasesRule Γ ψ φ <;> tauto
  exact hseq6

theorem Derivable.Modus_Ponens
  (S : SymbolSet)
  (Γ : List (Formula S))
  (φ ψ : Formula S)
  (h1 : Derivable S { antecedent := Γ, succedent := Formula.Imply φ ψ })
  (h2 : Derivable S { antecedent := Γ, succedent := φ })
  :
  (Derivable S { antecedent := Γ, succedent := ψ })
:= by
  have hseq1 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := φ }) := by
    apply Derivable.AntecedentRule ((Formula.Neg φ) :: Γ) φ Γ
    repeat tauto
  have hseq2 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := Formula.Neg φ }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq3 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := ψ }) := by
    apply Derivable.Modified_Contradiction_Rule S ((Formula.Neg φ) :: Γ) ψ φ <;> tauto
  have hseq4 : (Derivable S { antecedent := ψ :: Γ, succedent := ψ }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq5 : (Derivable S { antecedent := (Formula.Or (Formula.Neg φ) ψ) :: Γ, succedent := ψ }) := by
    apply Derivable.OrRuleForAntecedent <;> tauto
  have hseq6 : (Derivable S { antecedent := Γ, succedent := ψ }) := by
    simp [Formula.Imply] at h1
    apply Derivable.Chain_Rule S Γ (Formula.Or (Formula.Neg φ) ψ) ψ <;> try tauto
  exact hseq6

theorem Derivable.Modified_Or_Rule
  (S : SymbolSet)
  (Γ : List (Formula S))
  (φ ψ : Formula S)
  (hseq1 : Derivable S { antecedent := Γ, succedent := Formula.Or φ ψ })
  (hseq2 : Derivable S { antecedent := Γ, succedent := Formula.Neg φ })
  :
  (Derivable S { antecedent := Γ, succedent := ψ })
:= by
  have hseq3 : (Derivable S { antecedent := φ :: Γ, succedent := Formula.Neg φ }) := by
    apply Derivable.AntecedentRule (φ :: Γ) (Formula.Neg φ) Γ
    repeat tauto
  have hseq4 : (Derivable S { antecedent := φ :: Γ, succedent := φ }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq5 : (Derivable S { antecedent := φ :: Γ, succedent := ψ }) := by
    apply Derivable.Modified_Contradiction_Rule S (φ :: Γ) ψ φ <;> tauto
  have hseq6 : (Derivable S { antecedent := ψ :: Γ, succedent := ψ }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq7 : (Derivable S { antecedent := (Formula.Or φ ψ) :: Γ, succedent := ψ }) := by
    apply Derivable.OrRuleForAntecedent <;> tauto
  have hseq8 : (Derivable S { antecedent := Γ, succedent := ψ }) := by
    apply Derivable.Chain_Rule S Γ (Formula.Or φ ψ) ψ <;> tauto
  exact hseq8


theorem Derivable.Double_Negation_Elim_Rule
  (S : SymbolSet)
  (Γ : List (Formula S))
  (φ : Formula S)
  (hseq1 : Derivable S { antecedent := Γ, succedent := Formula.Neg (Formula.Neg φ) })
  :
  (Derivable S { antecedent := Γ, succedent := φ })
:= by
  have hseq2 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := Formula.Neg (Formula.Neg φ) }) := by
    apply Derivable.AntecedentRule ((Formula.Neg φ) :: Γ) (Formula.Neg (Formula.Neg φ)) Γ
    repeat tauto
  have hseq3 : (Derivable S { antecedent := (Formula.Neg φ) :: Γ, succedent := Formula.Neg φ }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq4 : (Derivable S { antecedent := Γ, succedent := φ }) := by
    apply Derivable.ContradictionRule Γ φ (Formula.Neg φ) <;> tauto
  exact hseq4

theorem Derivable.Double_Negation_Intro_Rule
  (S : SymbolSet)
  (Γ : List (Formula S))
  (φ : Formula S)
  (hseq1 : Derivable S { antecedent := Γ, succedent := φ })
  :
  (Derivable S { antecedent := Γ, succedent := Formula.Neg (Formula.Neg φ) })
:= by
  have hseq2 : (Derivable S { antecedent := (Formula.Neg (Formula.Neg (Formula.Neg φ))) :: Γ, succedent := φ }) := by
    apply Derivable.AntecedentRule ((Formula.Neg (Formula.Neg (Formula.Neg φ))) :: Γ) φ Γ
    repeat tauto
  have hseq3 : (Derivable S { antecedent := (Formula.Neg (Formula.Neg (Formula.Neg φ))) :: Γ, succedent := Formula.Neg (Formula.Neg (Formula.Neg φ)) }) := by
    apply Derivable.AssumptionRule
    tauto
  have hseq4 : (Derivable S { antecedent := (Formula.Neg (Formula.Neg (Formula.Neg φ))) :: Γ, succedent := Formula.Neg φ }) := by
    apply Derivable.Double_Negation_Elim_Rule S ((Formula.Neg (Formula.Neg (Formula.Neg φ))) :: Γ) (Formula.Neg φ)
    tauto
  have hseq5 : (Derivable S { antecedent := Γ, succedent := Formula.Neg (Formula.Neg φ) }) := by
    apply Derivable.ContradictionRule Γ (Formula.Neg (Formula.Neg φ)) φ <;> tauto
  exact hseq5


def Derivable_set (S : SymbolSet) (Φ : FormulaSet S) (φ : Formula S) :=
    ∃ (Φ₀ : List (Formula S)), (∀ (φ₀ : Formula S), (φ₀ ∈ Φ₀) → (Φ φ₀)) ∧ (Derivable S { antecedent := Φ₀, succedent := φ })

theorem Derivable_set.ReflexivityRule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (t : Term S)
  :
  Derivable_set S Φ (Formula.Eq t t)
:= by
  use []
  constructor
  · simp
  · apply Derivable.ReflexivityRule

theorem Derivable_set.AssumptionRule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ : Formula S)
  (h : Φ φ)
  :
  Derivable_set S Φ φ
:= by
  use [φ]
  constructor
  · intro x hx
    simp at hx
    rw [hx]
    exact h
  · apply Derivable.AssumptionRule
    simp

theorem Derivable_set.AntecedentRule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ : Formula S)
  (Φ' : FormulaSet S)
  (hsubseteq : Φ' ⊆ Φ)
  (hder : Derivable_set S Φ' φ)
  :
  Derivable_set S Φ φ
:= by
  dsimp [Derivable_set] at *
  rcases hder with ⟨Γ, ⟨h1, h2⟩⟩
  use Γ
  constructor <;> tauto

theorem Derivable_set.ProofByCasesRule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ : Formula S)
  (h1 : Derivable_set S (insert ψ Φ) φ)
  (h2 : Derivable_set S (insert ψ.Neg Φ) φ)
  :
  Derivable_set S Φ φ
:= by
  dsimp [Derivable_set] at *
  rcases h1 with ⟨Φ1, ⟨h1, h3⟩⟩
  rcases h2 with ⟨Φ2, ⟨h2, h4⟩⟩
  let Γ1 := Φ1.filter (fun x => x ≠ ψ)
  let Γ2 := Φ2.filter (fun x => x ≠ ψ.Neg)
  let Γ := Γ1 ++ Γ2
  use Γ
  constructor
  · intro ζ hin
    simp [Γ] at hin
    rcases hin with hin1 | hin2
    · simp [Γ1] at hin1
      rcases hin1 with ⟨h5, h6⟩
      specialize h1 ζ h5
      change (ζ = ψ ∨ ζ ∈ Φ) at h1
      rcases h1 with ht1 | ht2 <;> tauto
    · simp [Γ2] at hin2
      rcases hin2 with ⟨h5, h6⟩
      specialize h2 ζ h5
      change (ζ = ψ.Neg ∨ ζ ∈ Φ) at h2
      rcases h2 with ht1 | ht2 <;> tauto
  · apply Derivable.ProofByCasesRule Γ φ ψ
    · apply Derivable.AntecedentRule (ψ :: Γ) φ Φ1 <;> try tauto
      simp [Γ, Γ1]
      intro x hin
      by_cases hc : x = ψ
      · rw [hc]
        tauto
      · apply List.mem_cons_of_mem ψ
        simp
        tauto
    · apply Derivable.AntecedentRule (ψ.Neg :: Γ) φ Φ2 <;> try tauto
      simp [Γ, Γ2]
      intro x hin
      by_cases hc : x = ψ.Neg
      · rw [hc]
        tauto
      · apply List.mem_cons_of_mem ψ.Neg
        simp
        tauto

theorem Derivable_set.ContradictionRule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ : Formula S)
  (h1 : Derivable_set S (insert φ.Neg Φ) ψ)
  (h2 : Derivable_set S (insert φ.Neg Φ) ψ.Neg)
  :
  Derivable_set S Φ φ
:= by
  dsimp [Derivable_set] at *
  rcases h1 with ⟨Φ1, ⟨h1, h3⟩⟩
  rcases h2 with ⟨Φ2, ⟨h2, h4⟩⟩
  let Γ1 := Φ1.filter (fun x => x ≠ φ.Neg)
  let Γ2 := Φ2.filter (fun x => x ≠ φ.Neg)
  let Γ := Γ1 ++ Γ2
  use Γ
  constructor
  · intro ζ hin
    simp [Γ] at hin
    rcases hin with hin1 | hin2
    · simp [Γ1] at hin1
      rcases hin1 with ⟨h5, h6⟩
      specialize h1 ζ h5
      change (ζ = φ.Neg ∨ ζ ∈ Φ) at h1
      rcases h1 with ht1 | ht2 <;> try tauto
    · simp [Γ2] at hin2
      rcases hin2 with ⟨h5, h6⟩
      specialize h2 ζ h5
      change (ζ = φ.Neg ∨ ζ ∈ Φ) at h2
      rcases h2 with ht1 | ht2 <;> tauto
  · apply Derivable.ContradictionRule Γ φ ψ
    · apply Derivable.AntecedentRule (φ.Neg :: Γ) ψ Φ1 <;> try tauto
      simp [Γ, Γ1, Γ2]
      intro x hin
      by_cases hc : x = φ.Neg
      · rw [hc]
        tauto
      · apply List.mem_cons_of_mem φ.Neg
        simp
        tauto
    · apply Derivable.AntecedentRule (φ.Neg :: Γ) ψ.Neg Φ2 <;> try tauto
      simp [Γ, Γ2]
      intro x hin
      by_cases hc : x = φ.Neg
      · rw [hc]
        tauto
      · apply List.mem_cons_of_mem φ.Neg
        simp
        tauto

theorem Derivable_set.OrRuleForAntecedent
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ ξ : Formula S)
  (h1 : Derivable_set S (insert φ Φ) ξ)
  (h2 : Derivable_set S (insert ψ Φ) ξ)
  :
  Derivable_set S (insert (Formula.Or φ ψ) Φ) ξ
:= by
  dsimp [Derivable_set] at *
  rcases h1 with ⟨Φ1, ⟨h1, h3⟩⟩
  rcases h2 with ⟨Φ2, ⟨h2, h4⟩⟩
  let Γ1 := Φ1.filter (fun x => decide (x ≠ φ))
  let Γ2 := Φ2.filter (fun x => decide (x ≠ ψ))
  let Γ := (Formula.Or φ ψ) :: (Γ1 ++ Γ2)
  use Γ
  constructor
  · intro ζ hin
    simp [Γ] at hin
    rcases hin with heq | hin1 | hin2
    · rw [heq]
      apply Set.mem_insert
    · simp [Γ1] at hin1
      rcases hin1 with ⟨h5, h6⟩
      specialize h1 ζ h5
      change (ζ = φ ∨ ζ ∈ Φ) at h1
      rcases h1 with heq_phi | h_in_phi
      · rw [heq_phi] at h6
        simp at h6
      · right
        exact h_in_phi
    · simp [Γ2] at hin2
      rcases hin2 with ⟨h5, h6⟩
      specialize h2 ζ h5
      change (ζ = ψ ∨ ζ ∈ Φ) at h2
      rcases h2 with heq_psi | h_in_phi
      · rw [heq_psi] at h6
        simp at h6
      · right
        exact h_in_phi
  · apply Derivable.OrRuleForAntecedent (Γ1 ++ Γ2) φ ψ ξ
    · apply Derivable.AntecedentRule (φ :: (Γ1 ++ Γ2)) ξ Φ1
      · intro x hx
        simp
        by_cases hc : x = φ
        · left
          exact hc
        · right
          left
          simp [Γ1]
          exact ⟨hx, hc⟩
      · exact h3
    · apply Derivable.AntecedentRule (ψ :: (Γ1 ++ Γ2)) ξ Φ2
      · intro x hx
        simp
        by_cases hc : x = ψ
        · left
          exact hc
        · right
          right
          simp [Γ2]
          exact ⟨hx, hc⟩
      · exact h4

theorem Derivable_set.OrRuleForSuccedent1
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ : Formula S)
  (h : Derivable_set S Φ φ)
  :
  Derivable_set S Φ (Formula.Or φ ψ)
:= by
  rcases h with ⟨Γ, ⟨hsub, hder⟩⟩
  use Γ
  constructor
  · exact hsub
  · apply Derivable.OrRuleForSuccedent1
    exact hder

theorem Derivable_set.OrRuleForSuccedent2
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ : Formula S)
  (h : Derivable_set S Φ φ)
  :
  Derivable_set S Φ (Formula.Or ψ φ)
:= by
  rcases h with ⟨Γ, ⟨hsub, hder⟩⟩
  use Γ
  constructor
  · exact hsub
  · apply Derivable.OrRuleForSuccedent2
    exact hder

theorem Derivable_set.RuleForExistsInSuccedent
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ : Formula S)
  (x : Nat)
  (t : Term S)
  (h : Derivable_set S Φ (FormulaSubstitution S φ [(x, t)]))
  :
  Derivable_set S Φ (Formula.Exists x φ)
:= by
  rcases h with ⟨Γ, ⟨hsub, hder⟩⟩
  use Γ
  constructor
  · exact hsub
  · apply Derivable.RuleForExistsInSuccedent
    exact hder

theorem Derivable_set.RuleForExistsInAntecedent
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ : Formula S)
  (x y : Nat)
  (hy_phi : y ∉ Freevar S (Formula.Exists x φ))
  (hy_psi : y ∉ Freevar S ψ)
  (hy_Phi : ∀ ξ, Φ ξ → y ∉ Freevar S ξ)
  (h : Derivable_set S (insert (FormulaSubstitution S φ [(x, Term.Var y)]) Φ) ψ)
  :
  Derivable_set S (insert (Formula.Exists x φ) Φ) ψ
:= by
  dsimp [Derivable_set] at *
  let φ_subst := FormulaSubstitution S φ [(x, Term.Var y)]
  rcases h with ⟨Φ1, ⟨h1, h2⟩⟩
  let Γ := Φ1.filter (fun z => z ≠ φ_subst)
  use (Formula.Exists x φ) :: Γ
  constructor
  · intro ζ hin
    simp [Γ] at hin
    rcases hin with hin1 | hin2
    · rw [hin1]
      change (Formula.Exists x φ) = (Formula.Exists x φ) ∨ Φ (Formula.Exists x φ)
      left
      rfl
    · rcases hin2 with ⟨h3, h4⟩
      specialize h1 ζ h3
      change (ζ = φ_subst ∨ Φ ζ) at h1
      rcases h1 with heq | h_in_Phi
      · exfalso
        apply h4
        exact heq
      · right
        exact h_in_Phi
  · apply Derivable.RuleForExistsInAntecedent Γ x y φ ψ
    · intro ξ hξ
      simp [Γ] at hξ
      rcases hξ with ⟨h_in_Phi1, h_neq⟩
      specialize h1 ξ h_in_Phi1
      change (ξ = φ_subst ∨ Φ ξ) at h1
      rcases h1 with heq | h_in_Phi
      · exfalso
        apply h_neq
        exact heq
      · apply hy_Phi
        exact h_in_Phi
    · exact hy_phi
    · exact hy_psi
    · apply Derivable.AntecedentRule (φ_subst :: Γ) ψ Φ1
      · intro z hz
        simp
        by_cases heq : z = φ_subst
        · left
          exact heq
        · right
          simp [Γ]
          constructor
          · exact hz
          · exact heq
      · exact h2

theorem Derivable_set.SubstitutionRuleForEquality
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ : Formula S)
  (x : Nat)
  (t t' : Term S)
  (h : Derivable_set S Φ (FormulaSubstitution S φ [(x,t)]))
  :
  Derivable_set S (insert (Formula.Eq t t') Φ) (FormulaSubstitution S φ [(x,t')])
:= by
  dsimp [Derivable_set] at *
  rcases h with ⟨Γ, ⟨hsub, hder⟩⟩
  use (Formula.Eq t t') :: Γ
  constructor
  · intro ζ hin
    simp at hin
    rcases hin with heq | hin_gamma
    · rw [heq]
      apply Set.mem_insert
    · right
      apply hsub
      exact hin_gamma
  · apply Derivable.SubstitutionRuleForEquality
    exact hder

theorem Derivable_set.Tertium_non_datur
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ : Formula S)
  :
  Derivable_set S Φ (Formula.Or φ φ.Neg)
:= by
  use []
  constructor
  · simp
  · apply Derivable.Tertium_non_datur

theorem Derivable_set.Chain_Rule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ : Formula S)
  (h1 : Derivable_set S Φ φ)
  (h2 : Derivable_set S (insert φ Φ) ψ)
  :
  Derivable_set S Φ ψ
:= by
  dsimp [Derivable_set] at *
  rcases h1 with ⟨Φ1, ⟨hsub1, hder1⟩⟩
  rcases h2 with ⟨Φ2, ⟨hsub2, hder2⟩⟩
  let Γ2 := Φ2.filter (fun x => x ≠ φ)
  let Γ := Φ1 ++ Γ2
  use Γ
  constructor
  · intro ζ hin
    simp [Γ] at hin
    rcases hin with hin1 | hin2
    · apply hsub1
      exact hin1
    · simp [Γ2] at hin2
      rcases hin2 with ⟨h_in_phi2, h_neq_phi⟩
      specialize hsub2 ζ h_in_phi2
      change (ζ = φ ∨ Φ ζ) at hsub2
      rcases hsub2 with heq | h_in_phi
      · exfalso
        apply h_neq_phi
        exact heq
      · exact h_in_phi
  · apply Derivable.Chain_Rule S Γ φ ψ
    · apply Derivable.AntecedentRule Γ φ Φ1
      · intro x hx
        simp [Γ]
        left
        exact hx
      · exact hder1
    · apply Derivable.AntecedentRule (φ :: Γ) ψ Φ2
      · intro x hx
        by_cases heq : x = φ
        · rw [heq]
          apply List.mem_cons_self
        · apply List.mem_cons_of_mem
          simp [Γ]
          right
          simp [Γ2]
          constructor
          · exact hx
          · simp [heq]
      · exact hder2

theorem Derivable_set.Modus_Ponens
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ : Formula S)
  (h1 : Derivable_set S Φ (Formula.Imply φ ψ))
  (h2 : Derivable_set S Φ φ)
  :
  Derivable_set S Φ ψ
:= by
  rcases h1 with ⟨Γ1, ⟨hsub1, hder1⟩⟩
  rcases h2 with ⟨Γ2, ⟨hsub2, hder2⟩⟩
  use Γ1 ++ Γ2
  constructor
  · intro x hx; simp at hx; rcases hx with h|h; apply hsub1 x h; apply hsub2 x h
  · apply Derivable.Modus_Ponens S (Γ1 ++ Γ2) φ ψ
    · apply Derivable.AntecedentRule _ _ Γ1 _ hder1; simp
    · apply Derivable.AntecedentRule _ _ Γ2 _ hder2; simp

theorem Derivable_set.Modified_Or_Rule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ ψ : Formula S)
  (h1 : Derivable_set S Φ (Formula.Or φ ψ))
  (h2 : Derivable_set S Φ φ.Neg)
  :
  Derivable_set S Φ ψ
:= by
  rcases h1 with ⟨Γ1, ⟨hsub1, hder1⟩⟩
  rcases h2 with ⟨Γ2, ⟨hsub2, hder2⟩⟩
  use Γ1 ++ Γ2
  constructor
  · intro x hx; simp at hx; rcases hx with h|h; apply hsub1 x h; apply hsub2 x h
  · apply Derivable.Modified_Or_Rule S (Γ1 ++ Γ2) φ ψ
    · apply Derivable.AntecedentRule _ _ Γ1 _ hder1; simp
    · apply Derivable.AntecedentRule _ _ Γ2 _ hder2; simp

theorem Derivable_set.Double_Negation_Elim_Rule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ : Formula S)
  (h : Derivable_set S Φ (Formula.Neg (Formula.Neg φ)))
  :
  Derivable_set S Φ φ
:= by
  rcases h with ⟨Γ, ⟨hsub, hder⟩⟩
  use Γ
  constructor; exact hsub
  apply Derivable.Double_Negation_Elim_Rule
  exact hder

theorem Derivable_set.Double_Negation_Intro_Rule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ : Formula S)
  (h : Derivable_set S Φ φ)
  :
  Derivable_set S Φ (Formula.Neg (Formula.Neg φ))
:= by
  rcases h with ⟨Γ, ⟨hsub, hder⟩⟩
  use Γ
  constructor; exact hsub
  apply Derivable.Double_Negation_Intro_Rule
  exact hder

theorem Derivable_set.Modified_Contradiction_Rule
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (ψ : Formula S)
  (h1 : Derivable_set S Φ ψ)
  (h2 : Derivable_set S Φ ψ.Neg)
  (φ : Formula S)
  :
  Derivable_set S Φ φ
:= by
  dsimp [Derivable_set] at h1
  dsimp [Derivable_set] at h2
  rcases h1 with ⟨Φ1, ⟨h1, h3⟩⟩
  rcases h2 with ⟨Φ2, ⟨h2, h4⟩⟩
  have h5 : Derivable S { antecedent := Φ1 ++ Φ2, succedent := ψ } := by
    apply Derivable.AntecedentRule (Φ1 ++ Φ2) ψ Φ1
    simp
    apply h3
  have h6 : Derivable S { antecedent := Φ1 ++ Φ2, succedent := ψ.Neg } := by
    apply Derivable.AntecedentRule (Φ1 ++ Φ2) ψ.Neg Φ2
    simp
    apply h4
  have h7 : Derivable S { antecedent := Φ1 ++ Φ2, succedent := φ } := by
    apply Derivable.Modified_Contradiction_Rule S (Φ1 ++ Φ2) φ ψ <;> try tauto
  dsimp [Derivable_set]
  use (Φ1 ++ Φ2)
  constructor
  · intro ζ hin
    simp at hin
    rcases hin with hin1 | hin2
    · apply h1 ; tauto
    · apply h2 ; tauto
  · tauto
