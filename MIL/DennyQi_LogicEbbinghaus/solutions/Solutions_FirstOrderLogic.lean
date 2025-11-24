import Mathlib
namespace FirstOrderLogic
open Classical

structure SymbolSet where
  RelSymbol : Nat → Type
  FuncSymbol : Nat → Type
  ConstSymbol : Type

inductive Term (S : SymbolSet) where
  | Var (i : Nat) : Term S
  | Const (c : S.ConstSymbol) : Term S
  | Func (n : Nat) (f : S.FuncSymbol n) (args : Fin n → Term S) : Term S

inductive Formula (S : SymbolSet) where
  | Eq (t1 t2 : Term S) : Formula S
  | Rel (n : Nat) (R : S.RelSymbol n) (args : Fin n → Term S) : Formula S
  | Neg (φ : Formula S) : Formula S
  | And (φ ψ : Formula S) : Formula S
  | Forall (x : Nat) (φ : Formula S) : Formula S

def Formula.Or {S : SymbolSet} (φ ψ : Formula S) : Formula S :=
  Formula.Neg (Formula.And (Formula.Neg φ) (Formula.Neg ψ))

def Formula.Imply {S : SymbolSet} (φ ψ : Formula S) : Formula S :=
  Formula.Neg (Formula.And φ (Formula.Neg ψ))

def Formula.Iff {S : SymbolSet} (φ ψ : Formula S) : Formula S :=
  Formula.And (Formula.Imply φ ψ) (Formula.Imply ψ φ)

def Formula.Exists {S : SymbolSet} (x : Nat) (φ : Formula S) : Formula S :=
  Formula.Neg (Formula.Forall x (Formula.Neg φ))

def VarOfTerm (S : SymbolSet) (t : Term S) : Set Nat :=
  match t with
  | Term.Var i => {i}
  | Term.Const _ => ∅
  | Term.Func n _ arg => { x | ∃ (j : Fin n), x ∈ (VarOfTerm S (arg j))}

def ConstOfTerm (S : SymbolSet) (t : Term S) : Set S.ConstSymbol :=
  match t with
  | Term.Var _ => ∅
  | Term.Const c => {c}
  | Term.Func _ _ arg => { x | ∃ i, x ∈ ConstOfTerm S (arg i) }

def FuncOfTerm (S : SymbolSet) (t : Term S) : Set (Σ n, S.FuncSymbol n) :=
  match t with
  | Term.Var _ => ∅
  | Term.Const _ => ∅
  | Term.Func n f arg => { ⟨n, f⟩ } ∪ { x | ∃ i, (x ∈ (FuncOfTerm S (arg i))) }

def ConstOfFormula (S : SymbolSet) (φ : Formula S) : Set S.ConstSymbol :=
  match φ with
  | Formula.Eq t1 t2 => (ConstOfTerm S t1) ∪ (ConstOfTerm S t2)
  | Formula.Rel n _ arg => { x | ∃ (j : Fin n), x ∈ (ConstOfTerm S (arg j))}
  | Formula.Neg φ => ConstOfFormula S φ
  | Formula.And φ ψ => (ConstOfFormula S φ) ∪ (ConstOfFormula S ψ)
  | Formula.Forall _ φ => ConstOfFormula S φ

def FuncOfFormula (S : SymbolSet) (φ : Formula S) : Set (Σ n, S.FuncSymbol n) :=
  match φ with
  | Formula.Eq t1 t2 => (FuncOfTerm S t1) ∪ (FuncOfTerm S t2)
  | Formula.Rel n _ arg => { x | ∃ (j : Fin n), x ∈ (FuncOfTerm S (arg j))}
  | Formula.Neg φ => FuncOfFormula S φ
  | Formula.And φ ψ => (FuncOfFormula S φ) ∪ (FuncOfFormula S ψ)
  | Formula.Forall _ φ => FuncOfFormula S φ

def RelOfFormula (S : SymbolSet) (φ : Formula S) : Set (Σ n, S.RelSymbol n) :=
  match φ with
  | Formula.Eq _ _ => ∅
  | Formula.Rel n R _ => {⟨n, R⟩}
  | Formula.Neg φ => RelOfFormula S φ
  | Formula.And φ ψ => (RelOfFormula S φ) ∪ (RelOfFormula S ψ)
  | Formula.Forall _ φ => RelOfFormula S φ

def Freevar (S : SymbolSet) (φ : Formula S) : Set Nat :=
  match φ with
  | Formula.Eq t1 t2 => (VarOfTerm S t1) ∪ (VarOfTerm S t2)
  | Formula.Rel n _ arg => { x | ∃ (j : Fin n), x ∈ (VarOfTerm S (arg j))}
  | Formula.Neg φ => Freevar S φ
  | Formula.And φ ψ => (Freevar S φ) ∪ (Freevar S ψ)
  | Formula.Forall x φ => (Freevar S φ) \ {x}

def IsSentence (S : SymbolSet) (φ : Formula S) : Prop :=
  Freevar S φ = ∅

def Universe := Type

structure SymbolInterp (S : SymbolSet) (A : Universe) where
  RelInterp (n : Nat) (R : S.RelSymbol n) : (Fin n → A) → Prop
  FuncInterp (n : Nat) (f : S.FuncSymbol n) : (Fin n → A) → A
  ConstInterp (c : S.ConstSymbol) : A

structure Model (S : SymbolSet) where
  A : Universe
  a : SymbolInterp S A

def Assignment (A : Universe) := Nat → A

structure Interp (S : SymbolSet) where
  𝔸 : Model S
  β : Assignment 𝔸.A

def TermEval (S : SymbolSet) (I : Interp S) (t : Term S) : I.𝔸.A :=
  match t with
  | Term.Var i => I.β i
  | Term.Const c => I.𝔸.a.ConstInterp c
  | Term.Func n f arg => I.𝔸.a.FuncInterp n f (fun i => TermEval S I (arg i))

def FormulaEval (S : SymbolSet) (I : Interp S) (φ : Formula S) : Prop :=
  match φ with
  | Formula.Eq t1 t2 => (TermEval S I t1) = (TermEval S I t2)
  | Formula.Rel n R arg => I.𝔸.a.RelInterp n R (fun i => TermEval S I (arg i))
  | Formula.Neg φ => ¬ (FormulaEval S I φ)
  | Formula.And φ ψ => (FormulaEval S I φ) ∧ (FormulaEval S I ψ)
  | Formula.Forall x φ =>
      ∀ (d : I.𝔸.A),
      FormulaEval S { 𝔸 := I.𝔸, β := fun y => if y = x then d else I.β y } φ

def FormulaEval_model (S : SymbolSet) (𝔸 : Model S) (φ : Formula S) : Prop := ∀ (β : Assignment 𝔸.A), FormulaEval S { 𝔸 := 𝔸, β := β } φ

theorem coincidence_lemma_term
  (S : SymbolSet)
  (A : Type)
  (a1 a2 : SymbolInterp S A)
  (β1 β2 : Assignment A)
  (t : Term S)
  (h_const : ∀ c ∈ ConstOfTerm S t, a1.ConstInterp c = a2.ConstInterp c)
  (h_func : ∀ (n : Nat) (f : S.FuncSymbol n),
    ⟨n, f⟩ ∈ FuncOfTerm S t → a1.FuncInterp n f = a2.FuncInterp n f)
  (h_var : ∀ x ∈ VarOfTerm S t, β1 x = β2 x)
  :
  let I1 := { 𝔸 := { A := A, a := a1 }, β := β1 }
  let I2 := { 𝔸 := { A := A, a := a2 }, β := β2 }
  TermEval S I1 t = TermEval S I2 t
:= by
  induction t with
  | Var i =>
    simp [TermEval]
    apply h_var
    simp [VarOfTerm]
  | Const c =>
    simp [TermEval]
    apply h_const
    simp [ConstOfTerm]
  | Func n f args ih =>
    simp [TermEval]
    let h1 := h_func n f
    rw [h1]
    · congr
      funext i
      apply ih
      · intro c hc
        apply h_const
        simp [ConstOfTerm]
        use i
      · intro n' f' hf'
        apply h_func
        simp [FuncOfTerm]
        right
        use i
      · intro x hv
        apply h_var
        simp [VarOfTerm]
        use i
    · simp [FuncOfTerm]

theorem coincidence_lemma_formula
  (S : SymbolSet)
  (A : Type)
  (a1 a2 : SymbolInterp S A)
  (β1 β2 : Assignment A)
  (φ : Formula S)
  (h_func : ∀ (n : Nat) (f : S.FuncSymbol n),
    ⟨n, f⟩ ∈ FuncOfFormula S φ → a1.FuncInterp n f = a2.FuncInterp n f)
  (h_rel : ∀ (n : Nat) (R : S.RelSymbol n),
    ⟨n, R⟩ ∈ RelOfFormula S φ → a1.RelInterp n R = a2.RelInterp n R)
  (h_const : ∀ c ∈ ConstOfFormula S φ, a1.ConstInterp c = a2.ConstInterp c)
  (h_freevar : ∀ x ∈ Freevar S φ, β1 x = β2 x)
  :
  let I1 := { 𝔸 := { A := A, a := a1 }, β := β1 }
  let I2 := { 𝔸 := { A := A, a := a2 }, β := β2 }
  FormulaEval S I1 φ ↔ FormulaEval S I2 φ
:= by
  revert β1 β2
  induction φ with
  | Eq t1 t2 =>
    intro β1 β2 h_freevar
    simp [FormulaEval]
    apply Eq.congr
    · apply coincidence_lemma_term
      · intro c hc
        apply h_const
        simp [ConstOfFormula]
        left
        exact hc
      · intro n f hf
        apply h_func
        simp [FuncOfFormula]
        left
        exact hf
      · intro x hx
        apply h_freevar
        simp [Freevar]
        left
        exact hx
    · apply coincidence_lemma_term
      · intro c hc
        apply h_const
        simp [ConstOfFormula]
        right
        exact hc
      · intro n f hf
        apply h_func
        simp [FuncOfFormula]
        right
        exact hf
      · intro x hx
        apply h_freevar
        simp [Freevar]
        right
        exact hx
  | Rel n R args =>
    intro β1 β2 h_freevar
    simp [FormulaEval]
    let h0 := h_rel n R
    rw [h0]
    · apply Eq.to_iff
      congr
      funext i
      apply coincidence_lemma_term
      · intro c hc
        apply h_const
        simp [ConstOfFormula]
        use i
      · intro n f hf
        apply h_func
        simp [FuncOfFormula]
        use i
      · intro x hx
        apply h_freevar
        simp [Freevar]
        use i
    · simp [RelOfFormula]
  | Neg φ ih =>
    intro β1 β2 h_freevar
    simp [FormulaEval]
    apply not_congr
    apply ih
    · intro n f hf
      apply h_func
      simp [FuncOfFormula]
      exact hf
    · intro n R hR
      apply h_rel
      simp [RelOfFormula]
      exact hR
    · intro c hc
      apply h_const
      simp [ConstOfFormula]
      exact hc
    · intro x hx
      apply h_freevar
      simp [Freevar]
      exact hx
  | And φ ψ ih1 ih2 =>
    intro β1 β2 h_freevar
    simp [FormulaEval]
    apply and_congr
    · apply ih1
      · intro n f hf
        apply h_func
        simp [FuncOfFormula]
        left
        exact hf
      · intro n R hR
        apply h_rel
        simp [RelOfFormula]
        left
        exact hR
      · intro c hc
        apply h_const
        simp [ConstOfFormula]
        left
        exact hc
      · intro x hx
        apply h_freevar
        simp [Freevar]
        left
        exact hx
    · apply ih2
      · intro n f hf
        apply h_func
        simp [FuncOfFormula]
        right
        exact hf
      · intro n R hR
        apply h_rel
        simp [RelOfFormula]
        right
        exact hR
      · intro c hc
        apply h_const
        simp [ConstOfFormula]
        right
        exact hc
      · intro x hx
        apply h_freevar
        simp [Freevar]
        right
        exact hx
  | Forall x φ ih =>
    intro β1 β2 h_freevar
    simp [FormulaEval]
    apply forall_congr'
    intro a
    apply ih
    · intro n f hf
      apply h_func
      simp [FuncOfFormula]
      exact hf
    · intro n R hR
      apply h_rel
      simp [RelOfFormula]
      exact hR
    · intro c hc
      apply h_const
      simp [ConstOfFormula]
      exact hc
    · intro x' hx'
      by_cases hxeqx' :(x = x')
      · simp [hxeqx']
      · have hxeqx'' : ¬ x' = x := by tauto
        simp [hxeqx'']
        apply h_freevar
        simp [Freevar]
        constructor
        · exact hx'
        · exact hxeqx''

structure ModelIso (S : SymbolSet) (𝔸 𝔹 : Model S) extends 𝔸.A ≃ 𝔹.A where
  map_rel : ∀ (n : Nat) (R : S.RelSymbol n) (args : Fin n → 𝔸.A), 𝔸.a.RelInterp n R args ↔ 𝔹.a.RelInterp n R (toFun ∘ args)
  map_func : ∀ (n : Nat) (f : S.FuncSymbol n) (args : Fin n → 𝔸.A), toFun (𝔸.a.FuncInterp n f args) = 𝔹.a.FuncInterp n f (toFun ∘ args)
  map_const : ∀ (c : S.ConstSymbol), toFun (𝔸.a.ConstInterp c) = 𝔹.a.ConstInterp c

def IsomorphicModel (S : SymbolSet) (𝔸 𝔹 : Model S) : Prop := Nonempty (ModelIso S 𝔸 𝔹)

lemma term_isomorphism_with_assignment
  (S : SymbolSet)
  (𝔸 𝔹 : Model S)
  (π : ModelIso S 𝔸 𝔹)
  (β : Assignment 𝔸.A)
  (t : Term S)
  :
  π.toFun (TermEval S { 𝔸 := 𝔸, β := β } t) = TermEval S { 𝔸 := 𝔹, β := π.toFun ∘ β } t
:= by
  induction t with
  | Var i =>
    simp [TermEval]
  | Const c =>
    simp [TermEval]
    apply π.map_const
  | Func n f args ih =>
    simp only [TermEval]
    rw [π.map_func]
    congr
    funext i
    apply ih

lemma formula_isomorphism_with_assignment
  (S : SymbolSet)
  (𝔸 𝔹 : Model S)
  (π : ModelIso S 𝔸 𝔹)
  (β : Assignment 𝔸.A)
  (φ : Formula S)
  :
  FormulaEval S { 𝔸 := 𝔸, β := β } φ ↔ FormulaEval S { 𝔸 := 𝔹, β := π.toFun ∘ β } φ
:= by
  revert β
  induction φ with
  | Eq t1 t2 =>
    intro β
    simp only [FormulaEval]
    rw [← term_isomorphism_with_assignment S 𝔸 𝔹 π β t1, ← term_isomorphism_with_assignment S 𝔸 𝔹 π β t2]
    exact Iff.symm (Equiv.apply_eq_iff_eq π.toEquiv)
  | Rel n R args =>
    intro β
    simp only [FormulaEval]
    rw [π.map_rel]
    apply Eq.to_iff
    congr
    funext i
    apply term_isomorphism_with_assignment S 𝔸 𝔹 π β (args i)
  | Neg φ ih =>
    intro β
    simp only [FormulaEval]
    exact not_congr (ih β)
  | And φ ψ ih1 ih2 =>
    intro β
    simp only [FormulaEval]
    exact and_congr (ih1 β) (ih2 β)
  | Forall x φ ih =>
    intro β
    simp only [FormulaEval]
    apply Equiv.forall_congr π.toEquiv
    intro a
    let ih' := ih (fun y ↦ if y = x then a else β y)
    rw [ih']
    apply Eq.to_iff
    congr
    funext y
    by_cases hcases: y = x
    · exact apply_ite π.toFun (y = x) a (β y)
    · exact apply_ite π.toFun (y = x) a (β y)

theorem isomorphism_lemma
  (S : SymbolSet)
  (𝔸 𝔹 : Model S)
  (h_iso : IsomorphicModel S 𝔸 𝔹)
  (φ : Formula S)
  :
  FormulaEval_model S 𝔸 φ ↔ FormulaEval_model S 𝔹 φ
:= by
  cases h_iso with | intro π =>
  · simp [FormulaEval_model]
    constructor
    · intro h0 β
      let hlemma := formula_isomorphism_with_assignment S 𝔸 𝔹 π (π.invFun ∘ β) φ
      specialize h0 (π.invFun ∘ β)
      rw [hlemma] at h0
      have to_inv_eq_id : π.toFun ∘ π.invFun ∘ β = β := by
        funext x
        simp
      rw [to_inv_eq_id] at h0
      exact h0
    · intro h0 β
      let hlemma := formula_isomorphism_with_assignment S 𝔸 𝔹 π β φ
      specialize h0 (π.toFun ∘ β)
      rw [← hlemma] at h0
      exact h0

end FirstOrderLogic
