import Mathlib
import MIL.DennyQi_LogicEbbinghaus.FirstOrderLogic
import MIL.DennyQi_LogicEbbinghaus.SequentCalculus
import MIL.DennyQi_LogicEbbinghaus.Soundness
open Classical
open FirstOrderLogic

set_option maxHeartbeats 9999999

def Consistent (S : SymbolSet) (Φ : FormulaSet S) :=
  ∀ (φ : Formula S), ¬ ((Derivable_set S Φ φ) ∧ (Derivable_set S Φ (φ.Neg)))

def Inconsistent (S : SymbolSet) (Φ : FormulaSet S) :=
  ¬ Consistent S Φ

def Satisfiable_set (S : SymbolSet) (Φ : FormulaSet S) :=
  ∃ (I : Interp S), ∀ (φ : Formula S), (Φ φ) -> FormulaEval S I φ

lemma Inconsisten_eqdef (S : SymbolSet) (Φ : FormulaSet S) :
  Inconsistent S Φ ↔ (∀ (φ : Formula S), (Derivable_set S Φ φ))
:= by
  dsimp [Inconsistent, Consistent]
  simp
  constructor
  · intro h1
    rcases h1 with ⟨ψ, ⟨h1, h2⟩⟩
    intro φ
    apply Derivable_set.Modified_Contradiction_Rule S Φ ψ h1 h2 φ
  · intro h1
    let (p : Formula S) := Formula.Eq (Term.Var 0) (Term.Var 0)
    dsimp [Derivable_set] at h1
    have h2 := h1 p
    have h3 := h1 p.Neg
    use p
    constructor
    · rcases h2 with ⟨Φ₀, ⟨h4, h5⟩⟩
      dsimp [Derivable_set]
      tauto
    · rcases h2 with ⟨Φ₀, ⟨h4, h5⟩⟩
      dsimp [Derivable_set]
      tauto

lemma Satisfiable_implies_Consistent
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (h_sat : Satisfiable_set S Φ)
  :
  Consistent S Φ
:= by
  dsimp [Satisfiable_set] at *
  rcases h_sat with ⟨I, h1⟩
  by_contra h2
  dsimp [Consistent] at *
  simp at h2
  rcases h2 with ⟨φ, ⟨h2, h3⟩⟩
  have hfalse : FormulaEval S I (Formula.Neg (Formula.Eq (Term.Var 0) (Term.Var 0))) -> False := by
    simp [FormulaEval]
  apply hfalse
  have h4 : Derivable_set S Φ (Formula.Neg (Formula.Eq (Term.Var 0) (Term.Var 0))) := by
    apply Derivable_set.Modified_Contradiction_Rule S Φ φ h2 h3 (Formula.Neg (Formula.Eq (Term.Var 0) (Term.Var 0)))
  dsimp [Derivable_set] at h4
  rcases h4 with ⟨Φ₀, ⟨h4, h5⟩⟩
  have hs := Soundness_of_Sequent_Calculus S { antecedent := Φ₀, succedent := (Formula.Eq (Term.Var 0) (Term.Var 0)).Neg } h5
  simp [Consequence_set] at hs
  specialize hs I
  apply hs
  intro ζ hze
  apply h1
  tauto

lemma derivable_eq_union_inc
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (φ : Formula S)
  :
  (Derivable_set S Φ φ) ↔ Inconsistent S (Φ ∪ {φ.Neg})
:= by
  constructor
  · intro h1
    have h2 : Derivable_set S (Φ ∪ {φ.Neg}) φ := by
      apply Derivable_set.AntecedentRule S (Φ ∪ {φ.Neg}) φ Φ <;> try tauto
    have h3 : Derivable_set S (Φ ∪ {φ.Neg}) φ.Neg := by
      apply Derivable_set.AssumptionRule
      tauto
    dsimp [Inconsistent, Consistent]
    simp
    use φ
    simp at *
    tauto
  · intro h1
    rw [Inconsisten_eqdef] at h1
    apply Derivable_set.ProofByCasesRule S Φ φ φ
    · apply Derivable_set.AssumptionRule S (insert φ Φ) φ
      tauto
    · have h2 := h1 φ
      rw [Set.union_singleton] at h2
      exact h2

def contra_formula (S : SymbolSet) : Formula S := (Formula.Eq (Term.Var 0) (Term.Var 0)).Neg

def tauto_formula (S : SymbolSet) : Formula S := (Formula.Eq (Term.Var 0) (Term.Var 0))

lemma tauto_formula_derivable (S : SymbolSet) (Φ : FormulaSet S) :
  Derivable_set S Φ (tauto_formula S) := by
  use []
  constructor
  · simp
  · dsimp [tauto_formula]
    apply Derivable.ReflexivityRule

lemma unsat_implies_conseq_contra (S : SymbolSet) (Φ : FormulaSet S) :
  (¬ (Satisfiable_set S Φ)) → Consequence_set S Φ (contra_formula S)
:= by
  intro h_unsat I h_model
  exfalso
  apply h_unsat
  use I

lemma derivable_contra_implies_inc (S : SymbolSet) (Φ : FormulaSet S) :
  Derivable_set S Φ (contra_formula S) → Inconsistent S Φ
:= by
  intro h_der_false
  rw [Inconsisten_eqdef]
  intro φ
  have h_refl := tauto_formula_derivable S Φ
  apply Derivable_set.Modified_Contradiction_Rule S Φ (Formula.Eq (Term.Var 0) (Term.Var 0))
  · exact h_refl
  · exact h_der_false

lemma completeness_iff_con_imply_sat
  (S : SymbolSet)
  :
  (∀ (Φ : FormulaSet S) (φ : Formula S), (Consequence_set S Φ φ) → (Derivable_set S Φ φ))
  ↔
  (∀ (Φ : FormulaSet S), (Consistent S Φ) → (Satisfiable_set S Φ))
:= by
  constructor
  · intro h_comp Φ h_con
    by_contra h_unsat
    have h_conseq : Consequence_set S Φ (contra_formula S) :=
      unsat_implies_conseq_contra S Φ h_unsat
    have h_der : Derivable_set S Φ (contra_formula S) :=
      h_comp Φ (contra_formula S) h_conseq
    have h_inc : Inconsistent S Φ :=
      derivable_contra_implies_inc S Φ h_der
    unfold Consistent at h_con
    contradiction
  · intro h_model_existence Φ φ h_conseq
    rw [derivable_eq_union_inc]
    by_contra h_con_union
    dsimp [Inconsistent] at h_con_union
    have hcon : Consistent S (Φ ∪ {φ.Neg}) := by tauto
    have h_sat : Satisfiable_set S (Φ ∪ {φ.Neg}) := by
      apply h_model_existence (Φ ∪ {φ.Neg})
      tauto
    rcases h_sat with ⟨I, h_I⟩
    have h_mod_phi : ∀ ψ, Φ ψ → FormulaEval S I ψ := by
      intro ψ h_in
      apply h_I
      apply Set.mem_union_left
      exact h_in
    have h_mod_neg_phi : FormulaEval S I φ.Neg := by
      apply h_I
      apply Set.mem_union_right
      apply Set.mem_singleton
    specialize h_conseq I
    have h_mod_phi_true : FormulaEval S I φ := h_conseq h_mod_phi
    simp [FormulaEval] at h_mod_neg_phi
    contradiction

lemma cons_imply_sat
  (S : SymbolSet)
  (Φ : FormulaSet S)
  (hcon : Consistent S Φ)
  :
  (Satisfiable_set S Φ)
:= by
  sorry

theorem Completeness_of_Sequent_Calculus
  (S : SymbolSet)
  (seq : Sequent S)
  (h : Consequence_set S {φ | φ ∈ seq.antecedent}  (seq.succedent))
  :
  (Derivable S seq)
:= by
  rcases seq with ⟨Φ, φ⟩
  have hl := cons_imply_sat S
  have hiff := completeness_iff_con_imply_sat S
  have hll : (∀ (Φ : FormulaSet S) (φ : Formula S), Consequence_set S Φ φ → Derivable_set S Φ φ) := by
    rw [hiff]
    tauto
  specialize hll {ψ | ψ ∈ Φ} φ
  simp [Derivable_set] at hll
  have hcon : Consequence_set S {ψ | ψ ∈ Φ} φ := by
    tauto
  specialize hll hcon
  rcases hll with ⟨Γ, ⟨h1, h2⟩⟩
  apply Derivable.AntecedentRule Φ φ Γ <;> tauto
