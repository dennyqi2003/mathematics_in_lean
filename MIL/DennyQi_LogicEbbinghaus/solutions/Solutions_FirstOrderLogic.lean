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

def VarOfTerm (S : SymbolSet) (t : Term S) : List Nat :=
  match t with
  | Term.Var i => {i}
  | Term.Const _ => ∅
  | Term.Func _ _ args => (List.ofFn (fun i => VarOfTerm S (args i))).flatten

def ConstOfTerm (S : SymbolSet) (t : Term S) : Set S.ConstSymbol :=
  match t with
  | Term.Var _ => ∅
  | Term.Const c => {c}
  | Term.Func _ _ args => { x | ∃ i, x ∈ ConstOfTerm S (args i) }

def FuncOfTerm (S : SymbolSet) (t : Term S) : Set (Σ n, S.FuncSymbol n) :=
  match t with
  | Term.Var _ => ∅
  | Term.Const _ => ∅
  | Term.Func n f args => { ⟨n, f⟩ } ∪ { x | ∃ i, (x ∈ (FuncOfTerm S (args i))) }

def ConstOfFormula (S : SymbolSet) (φ : Formula S) : Set S.ConstSymbol :=
  match φ with
  | Formula.Eq t1 t2 => (ConstOfTerm S t1) ∪ (ConstOfTerm S t2)
  | Formula.Rel n _ args => { x | ∃ (j : Fin n), x ∈ (ConstOfTerm S (args j))}
  | Formula.Neg φ => ConstOfFormula S φ
  | Formula.And φ ψ => (ConstOfFormula S φ) ∪ (ConstOfFormula S ψ)
  | Formula.Forall _ φ => ConstOfFormula S φ

def FuncOfFormula (S : SymbolSet) (φ : Formula S) : Set (Σ n, S.FuncSymbol n) :=
  match φ with
  | Formula.Eq t1 t2 => (FuncOfTerm S t1) ∪ (FuncOfTerm S t2)
  | Formula.Rel n _ args => { x | ∃ (j : Fin n), x ∈ (FuncOfTerm S (args j))}
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

def Freevar (S : SymbolSet) (φ : Formula S) : List Nat :=
  match φ with
  | Formula.Eq t1 t2 => (VarOfTerm S t1) ++ (VarOfTerm S t2)
  | Formula.Rel _ _ args => (List.ofFn (fun i => VarOfTerm S (args i))).flatten
  | Formula.Neg ψ => Freevar S ψ
  | Formula.And ψ ξ => (Freevar S ψ) ++ (Freevar S ξ)
  | Formula.Forall x ψ => (Freevar S ψ).filter (fun y => y != x)

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
  | Term.Func n f args => I.𝔸.a.FuncInterp n f (fun i => TermEval S I (args i))

def FormulaEval (S : SymbolSet) (I : Interp S) (φ : Formula S) : Prop :=
  match φ with
  | Formula.Eq t1 t2 => (TermEval S I t1) = (TermEval S I t2)
  | Formula.Rel n R args => I.𝔸.a.RelInterp n R (fun i => TermEval S I (args i))
  | Formula.Neg φ => ¬ (FormulaEval S I φ)
  | Formula.And φ ψ => (FormulaEval S I φ) ∧ (FormulaEval S I ψ)
  | Formula.Forall x φ => ∀ (d : I.𝔸.A), FormulaEval S { 𝔸 := I.𝔸, β := fun y => if y = x then d else I.β y } φ

def FormulaEval_model (S : SymbolSet) (𝔸 : Model S) (φ : Formula S) : Prop :=
  ∀ (β : Assignment 𝔸.A), FormulaEval S { 𝔸 := 𝔸, β := β } φ

theorem The_Coincidence_Lemma_term
  (S : SymbolSet)
  (A : Type)
  (a1 a2 : SymbolInterp S A)
  (β1 β2 : Assignment A)
  (t : Term S)
  (h_const : ∀ c ∈ ConstOfTerm S t, a1.ConstInterp c = a2.ConstInterp c)
  (h_func : ∀ (n : Nat) (f : S.FuncSymbol n), ⟨n, f⟩ ∈ FuncOfTerm S t → a1.FuncInterp n f = a2.FuncInterp n f)
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
    exact List.mem_of_mem_head? rfl
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

theorem The_Coincidence_Lemma_formula
  (S : SymbolSet)
  (A : Type)
  (a1 a2 : SymbolInterp S A)
  (β1 β2 : Assignment A)
  (φ : Formula S)
  (h_func : ∀ (n : Nat) (f : S.FuncSymbol n), ⟨n, f⟩ ∈ FuncOfFormula S φ → a1.FuncInterp n f = a2.FuncInterp n f)
  (h_rel : ∀ (n : Nat) (R : S.RelSymbol n), ⟨n, R⟩ ∈ RelOfFormula S φ → a1.RelInterp n R = a2.RelInterp n R)
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
    · apply The_Coincidence_Lemma_term
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
    · apply The_Coincidence_Lemma_term
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
      apply The_Coincidence_Lemma_term
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
        tauto

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

theorem The_Isomorphism_Lemma
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

def VarSubstitution (S : SymbolSet) (x : Nat) (sublist : List (Nat × Term S)) : Term S :=
  match sublist with
  | [] => Term.Var x
  | (y, t) :: res => if x = y then t else VarSubstitution S x res

def TermSubstitution (S : SymbolSet) (t : Term S) (sublist : List (Nat × Term S)) : Term S :=
  match t with
  | Term.Var x => VarSubstitution S x sublist
  | Term.Const c => Term.Const c
  | Term.Func n f args => Term.Func n f (fun i => TermSubstitution S (args i) sublist)

def ListMax (l : List Nat) : Nat := l.foldr max 0

def TermMaxVar (S : SymbolSet) (t : Term S) : Nat :=
  match t with
  | Term.Var i => i
  | Term.Const _ => 0
  | Term.Func _ _ args => ListMax (List.ofFn (fun i => TermMaxVar S (args i)))

def MaxVarInFormula (S : SymbolSet) (φ : Formula S) : Nat :=
  match φ with
  | Formula.Eq t1 t2 => max (TermMaxVar S t1) (TermMaxVar S t2)
  | Formula.Rel _ _ args => ListMax (List.ofFn (fun i => TermMaxVar S (args i)))
  | Formula.Neg φ => MaxVarInFormula S φ
  | Formula.And φ ψ => max (MaxVarInFormula S φ) (MaxVarInFormula S ψ)
  | Formula.Forall x φ => max x (MaxVarInFormula S φ)

def MaxVarInSublist (S : SymbolSet) (sublist : List (Nat × Term S)) : Nat :=
  ListMax ((sublist.map (fun p => p.2)).map (TermMaxVar S))

def FormulaRank (S : SymbolSet) (φ : Formula S) : Nat :=
  match φ with
  | Formula.Eq _ _ => 0
  | Formula.Rel _ _ _ => 0
  | Formula.Neg ψ => (FormulaRank S ψ) + 1
  | Formula.And ψ ξ => (FormulaRank S ψ) + (FormulaRank S ξ) + 1
  | Formula.Forall _ ψ => (FormulaRank S ψ) + 1

def FormulaSubstitution (S : SymbolSet) (φ : Formula S) (sublist : List (Nat × Term S)) : Formula S :=
  match φ with
  | Formula.Eq t1 t2 => Formula.Eq (TermSubstitution S t1 sublist) (TermSubstitution S t2 sublist)
  | Formula.Rel n R args => Formula.Rel n R (fun i => TermSubstitution S (args i) sublist)
  | Formula.Neg ψ => Formula.Neg (FormulaSubstitution S ψ sublist)
  | Formula.And ψ ξ => Formula.And (FormulaSubstitution S ψ sublist) (FormulaSubstitution S ξ sublist)
  | Formula.Forall x ψ =>
      let sublist' := sublist.filter (fun p => (p.1 ∈ (Freevar S (Formula.Forall x ψ))))
      if sublist'.isEmpty then
        Formula.Forall x ψ
      else
        let u := (max (MaxVarInFormula S ψ) (MaxVarInSublist S sublist')) + 1
        Formula.Forall u (FormulaSubstitution S ψ ((x, Term.Var u) :: sublist'))
termination_by FormulaRank S φ
decreasing_by
  all_goals
    simp only [FormulaRank]
    linarith

lemma substitution_preserves_formula_rank (S : SymbolSet) (φ : Formula S) (sublist: List (Nat × Term S)) : (FormulaRank S (FormulaSubstitution S φ sublist)) = (FormulaRank S φ)
:= by
  revert sublist
  induction φ with
  | Eq t1 t2 =>
    intro sublist
    simp only [FormulaSubstitution, FormulaRank]
  | Rel n R args =>
    intro sublist
    simp only [FormulaSubstitution, FormulaRank]
  | Neg φ ih =>
    intro sublist
    simp only [FormulaSubstitution, FormulaRank]
    apply Nat.succ_inj'.mpr
    apply ih
  | And φ ψ ih1 ih2 =>
    intro sublist
    simp only [FormulaSubstitution, FormulaRank]
    rw [ih1 sublist, ih2 sublist]
  | Forall x φ ih =>
    intro sublist
    simp only [FormulaSubstitution, FormulaRank]
    split_ifs with h0
    · rfl
    · simp only [FormulaRank]
      rw [ih]

def AssignmentSubstitution (S : SymbolSet) (A : Universe) (β : Assignment A) (sublist : List (Nat × A)) : Assignment A :=
  fun y =>
    match sublist with
    | [] => β y
    | (x, a) :: res => ((if x = y then a else (AssignmentSubstitution S A β res) y))

theorem The_Substitution_Lemma_term
  (S : SymbolSet)
  (I : Interp S)
  (t : Term S)
  (sublist : List (Nat × Term S))
  :
  TermEval S I (TermSubstitution S t sublist) = TermEval S { 𝔸 := I.𝔸, β := (AssignmentSubstitution S I.𝔸.A I.β (sublist.map (fun p => (p.1, TermEval S I p.2)))) } t
:= by
  induction t with
  | Var x =>
    simp only [TermSubstitution]
    induction sublist with
    | nil =>
      simp [AssignmentSubstitution, VarSubstitution]
    | cons cur res ih =>
      simp [AssignmentSubstitution, VarSubstitution]
      by_cases heq : (x = cur.1)
      · simp [heq, TermEval]
      · simp [heq, TermEval]
        split_ifs with hif
        · rw [hif] at heq
          tauto
        · apply ih
  | Const c =>
    simp only [TermSubstitution, TermEval]
  | Func n f args ih =>
    simp only [TermSubstitution, TermEval]
    congr
    funext i
    apply ih

lemma assignment_subst_empty_eq_self (S : SymbolSet) (A : Universe) (β : Assignment A) (l : List (Nat × A)) (x : Nat) (h : ∀ p ∈ l, p.1 ≠ x) : AssignmentSubstitution S A β l x = β x := by
  induction l with
  | nil =>
    simp [AssignmentSubstitution]
  | cons head tail ih =>
    simp [AssignmentSubstitution]
    have h_head_neq : head.1 ≠ x := h head (List.mem_cons_self _ _)
    rw [if_neg h_head_neq]
    apply ih
    intro p hp
    apply h p (List.mem_cons_of_mem _ hp)

lemma le_list_max (l : List Nat) (n : Nat) (h : n ∈ l) : n ≤ ListMax l := by
  induction l with
  | nil => contradiction
  | cons cur res ih =>
    simp [ListMax, List.foldr] at *
    rcases h with h1 | h2
    · left
      linarith
    · right
      apply ih
      exact h2

lemma max_var_in_sublist_le_cons (S : SymbolSet) (cur : Nat × Term S) (res : List (Nat × Term S)) :
  MaxVarInSublist S res ≤ MaxVarInSublist S (cur :: res) := by
  simp [MaxVarInSublist, ListMax, List.foldr]

lemma var_le_term_max_var (S : SymbolSet) (t : Term S) (x : Nat) :
  x ∈ VarOfTerm S t → x ≤ TermMaxVar S t := by
  induction t with
  | Var i =>
    simp [VarOfTerm, TermMaxVar]
    intro h1
    exact List.le_maximum_of_mem h1 rfl
  | Const c =>
    simp [VarOfTerm, TermMaxVar]
  | Func n f args ih =>
    simp [VarOfTerm, TermMaxVar]
    intro i h1
    have h0 := le_list_max (List.ofFn fun i ↦ TermMaxVar S (args i)) (TermMaxVar S (args i))
    trans TermMaxVar S (args i)
    · apply ih
      apply h1
    · apply h0
      simp

theorem max_var_in_term_le_sublist (S : SymbolSet)
  (t : Term S)
  (sublist : List (Nat × Term S))
  (h : ∃ k, (k, t) ∈ sublist) :
  TermMaxVar S t ≤ MaxVarInSublist S sublist
:= by
  rcases h with ⟨k, h⟩
  simp [MaxVarInSublist]
  have h0 := le_list_max (List.map (TermMaxVar S ∘ fun p ↦ p.2) sublist)
  apply h0
  simp
  use k
  use t

lemma var_le_max_var_in_formula (S : SymbolSet) (φ : Formula S) (x : Nat) :
  x ∈ Freevar S φ → x ≤ MaxVarInFormula S φ :=
by
  induction φ with
  | Eq t1 t2 =>
    simp [Freevar, MaxVarInFormula]
    intro h1
    rcases h1 with h2 | h3
    · left
      apply var_le_term_max_var
      apply h2
    · right
      apply var_le_term_max_var
      apply h3
  | Rel n R args =>
    simp [Freevar, MaxVarInFormula]
    intro i h1
    have h2 := var_le_term_max_var S (args i) x h1
    have h3 := le_list_max (List.ofFn fun i ↦ TermMaxVar S (args i)) (TermMaxVar S (args i))
    trans TermMaxVar S (args i)
    · exact h2
    · apply h3
      simp
  | Neg ψ ih =>
    simp [Freevar, MaxVarInFormula]
    exact ih
  | And ψ ξ ih1 ih2 =>
    simp [Freevar, MaxVarInFormula]
    intro h1
    rcases h1 with h2 | h3
    · left
      apply ih1 h2
    · right
      apply ih2 h3
  | Forall y ψ ih =>
    intro h1
    simp [Freevar] at h1
    rcases h1 with ⟨h2, h3⟩
    simp [MaxVarInFormula]
    right
    tauto

lemma fresh_var_subst_equivalence
  (S : SymbolSet)
  (I : Interp S)
  (d : I.𝔸.A)
  (sublist : List (Nat × Term S))
  (u1 u2 x : Nat)
  (h_u1_fresh : MaxVarInSublist S sublist < u1)
  (h_u2_fresh : MaxVarInSublist S sublist < u2)
  (h_x_u1 : x < u1)
  (h_x_u2 : x < u2)
  :
  AssignmentSubstitution S I.𝔸.A (fun y ↦ if y = u1 then d else I.β y)
    (sublist.map (fun p ↦ (p.1, TermEval S { 𝔸 := I.𝔸, β := fun y ↦ if y = u1 then d else I.β y } p.2))) x
  =
  AssignmentSubstitution S I.𝔸.A (fun y ↦ if y = u2 then d else I.β y)
    (sublist.map (fun p ↦ (p.1, TermEval S { 𝔸 := I.𝔸, β := fun y ↦ if y = u2 then d else I.β y } p.2))) x
:= by
  induction sublist with
  | nil =>
    simp [AssignmentSubstitution]
    have ne1 : x ≠ u1 := ne_of_lt h_x_u1
    have ne2 : x ≠ u2 := ne_of_lt h_x_u2
    simp [ne1, ne2]
  | cons cur res ih =>
    rcases cur with ⟨k, t⟩
    have ht1 : TermMaxVar S t < u1 := by
      simp [MaxVarInSublist] at h_u1_fresh
      have hle := le_list_max (TermMaxVar S t :: List.map (TermMaxVar S ∘ fun p ↦ p.2) res) (TermMaxVar S t)
      have h0 : (TermMaxVar S t ≤ ListMax (TermMaxVar S t :: List.map (TermMaxVar S ∘ fun p ↦ p.2) res)) := by
        apply hle
        simp
      linarith
    have ht2 : TermMaxVar S t < u2 := by
      simp [MaxVarInSublist] at h_u2_fresh
      have hle := le_list_max (TermMaxVar S t :: List.map (TermMaxVar S ∘ fun p ↦ p.2) res) (TermMaxVar S t)
      have h0 : (TermMaxVar S t ≤ ListMax (TermMaxVar S t :: List.map (TermMaxVar S ∘ fun p ↦ p.2) res)) := by
        apply hle
        simp
      linarith
    simp [AssignmentSubstitution]
    split_ifs with heq
    · apply The_Coincidence_Lemma_term
      · intro c hc
        rfl
      · intro n f hf
        rfl
      · intro x' hx'
        have h1 := var_le_term_max_var S t x' hx'
        have h2 : x' < u1 := by linarith
        have h4 : x' < u2 := by linarith
        split_ifs with h5 h6
        · rfl
        · linarith
        · linarith
        · rfl
    · apply ih
      · have hneq1 := max_var_in_sublist_le_cons S (k,t) res
        linarith
      · have hneq2 := max_var_in_sublist_le_cons S (k,t) res
        linarith

theorem The_Substitution_Lemma_formula
  (S : SymbolSet)
  (I : Interp S)
  (φ : Formula S)
  (sublist : List (Nat × Term S))
  :
  FormulaEval S I (FormulaSubstitution S φ sublist) ↔ FormulaEval S { 𝔸 := I.𝔸, β := (AssignmentSubstitution S I.𝔸.A I.β (sublist.map (fun p => (p.1, TermEval S I p.2)))) } φ
:= by
  revert I sublist
  induction φ with
  | Eq t1 t2 =>
    intro I sublist
    simp only [FormulaSubstitution]
    have hlemma1 := The_Substitution_Lemma_term S I t1 sublist
    have hlemma2 := The_Substitution_Lemma_term S I t2 sublist
    exact Eq.congr hlemma1 hlemma2
  | Rel n R args =>
    intro I sublist
    simp only [FormulaSubstitution, FormulaEval]
    apply Eq.to_iff
    congr
    funext i
    apply The_Substitution_Lemma_term
  | Neg φ ih =>
    intro I sublist
    simp only [FormulaSubstitution]
    apply not_congr
    apply ih
  | And φ ψ ih1 ih2 =>
    intro I sublist
    simp only [FormulaSubstitution]
    apply and_congr
    · apply ih1
    · apply ih2
  | Forall x φ ih =>
    intro I sublist
    simp only [FormulaSubstitution, FormulaEval]
    split_ifs with hif
    · simp only [FormulaEval]
      apply forall_congr'
      intro a
      apply The_Coincidence_Lemma_formula
      · intros
        rfl
      · intros
        rfl
      · intros
        rfl
      · intro x1 hfreevar
        by_cases hxeqx1 : x1 = x
        · simp [hxeqx1]
        · simp [hxeqx1]
          have h1 : x1 ∈ Freevar S (Formula.Forall x φ) := by
            simp only [Freevar]
            apply List.mem_filter.mpr
            constructor
            · exact hfreevar
            · exact bne_iff_ne.mpr hxeqx1
          have h2 : ∀ q ∈ sublist, q.1 ≠ x1 := by
            intro q hq
            simp at hif
            specialize hif q.1 q.2 hq
            exact Ne.symm (ne_of_mem_of_not_mem h1 hif)
          have h3 : ∀ q ∈ sublist.map (fun p => (p.1, TermEval S I p.2)), q.1 ≠ x1 := by
            intro q hq
            rw [List.mem_map] at hq
            rcases hq with ⟨a, ⟨h3, h4⟩⟩
            specialize h2 a h3
            by_contra h5
            rw [← h5] at h2
            rw [← h4] at h2
            simp at h2
          rw [assignment_subst_empty_eq_self S I.𝔸.A I.β (sublist.map (fun p => (p.1, TermEval S I p.2))) x1 h3]
    · simp only [FormulaEval]
      apply forall_congr'
      intro d
      set u := MaxVarInFormula S φ ⊔ MaxVarInSublist S (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) sublist) + 1 with hu
      rw [ih]
      apply The_Coincidence_Lemma_formula
      · intros ; rfl
      · intros ; rfl
      · intros ; rfl
      · intro x1 hfreevar
        split_ifs with heq
        · simp [heq]
          rw [heq] at hfreevar
          clear x1 heq
          simp [AssignmentSubstitution, TermEval]
        · simp [AssignmentSubstitution]
          split_ifs with heq'
          · tauto
          · induction sublist with
            | nil => simp at hif
            | cons cur res ih' =>
              rcases cur with ⟨b, t⟩
              simp
              by_cases hy : b = x1
              · rw [hy]
                have h1 : x1 ∈ Freevar S (Formula.Forall x φ) := by
                  simp [Freevar]
                  rw [hy] at hif
                  constructor
                  · exact hfreevar
                  · exact heq
                rw [List.filter_cons_of_pos]
                · simp [AssignmentSubstitution]
                  apply The_Coincidence_Lemma_term
                  · intros; rfl
                  · intros; rfl
                  · intro x' h2
                    split_ifs with heq''
                    · have hxu : x' < u := by
                        rw [hu]
                        have neq1 := max_var_in_term_le_sublist S t (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) ((b, t) :: res))
                        have neq2 := var_le_term_max_var S t x' h2
                        have neq3 : x' ≤ MaxVarInSublist S (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) ((b, t) :: res)) := by
                          trans (TermMaxVar S t)
                          · exact neq2
                          · apply neq1
                            use b
                            simp
                            rw [hy]
                            exact h1
                        have neq4 : MaxVarInSublist S (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) ((b, t) :: res)) <  MaxVarInFormula S φ ⊔ MaxVarInSublist S (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) ((b, t) :: res)) + 1 := by
                          simp_arith
                        linarith
                      linarith
                    · rfl
                · simp [h1]
              · simp [AssignmentSubstitution]
                split_ifs
                by_cases hcase: (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) res).isEmpty = true
                · simp at hcase
                  have hempty := assignment_subst_empty_eq_self S I.𝔸.A I.β (List.map (fun p ↦ (p.1, TermEval S I p.2)) res) x1
                  rw [hempty]
                  · have h_x1_ne_u : x1 ≠ u := by
                      have h_lt : x1 < u := by
                        rw [hu]
                        have hle := var_le_max_var_in_formula S φ x1 hfreevar
                        simp_arith
                        left
                        exact hle
                      linarith
                    by_cases h_filter_b : decide (b ∈ Freevar S (Formula.Forall x φ))
                    · simp [h_filter_b]
                      simp [AssignmentSubstitution]
                      split_ifs
                      rw [List.filter_eq_nil_iff.mpr]
                      · simp [AssignmentSubstitution]
                        intro hcon
                        tauto
                      · intro tmp
                        rcases tmp with ⟨tmp1, tmp2⟩
                        intro htmp
                        specialize hcase tmp1 tmp2 htmp
                        simp
                        exact hcase
                    · simp [h_filter_b]
                      rw [List.filter_eq_nil_iff.mpr]
                      · simp [AssignmentSubstitution]
                        intro hcon
                        tauto
                      · intro tmp
                        rcases tmp with ⟨tmp1, tmp2⟩
                        intro htmp
                        specialize hcase tmp1 tmp2 htmp
                        simp
                        exact hcase
                  · simp [Freevar] at hcase
                    simp
                    intro a' b' x' t' h1 h2 h3
                    specialize hcase x' t' h1
                    by_contra hcontra
                    rw [← hcontra] at hfreevar
                    rw [h2] at hcase
                    have h4 := hcase hfreevar
                    rw [hcontra] at h4
                    tauto
                · rw [← ih']
                  · by_cases h_filter_b : decide (b ∈ Freevar S (Formula.Forall x φ))
                    · simp [h_filter_b]
                      simp [AssignmentSubstitution]
                      split_ifs
                      have ind_h := ih' hcase
                      simp at ind_h
                      rw [ind_h]
                      set u' := MaxVarInFormula S φ ⊔ MaxVarInSublist S (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) res) + 1 with hu'
                      have hfresh := fresh_var_subst_equivalence S I d (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) res) u u' x1
                      rw [hfresh]
                      · exact ind_h
                      · rw [hu]
                        have hnew := max_var_in_sublist_le_cons S (b,t) (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) res)
                        simp_arith
                        right
                        simp [List.filter_cons]
                        split_ifs with h0
                        · tauto
                        · tauto
                      · rw [hu']
                        simp_arith
                      · rw [hu]
                        have hneq : (x1 ≤ MaxVarInFormula S φ) := by
                          apply var_le_max_var_in_formula
                          tauto
                        simp_arith
                        tauto
                      · rw [hu']
                        have hneq : (x1 ≤ MaxVarInFormula S φ) := by
                          apply var_le_max_var_in_formula
                          tauto
                        simp_arith
                        tauto
                    · simp [h_filter_b]
                      set u' := MaxVarInFormula S φ ⊔ MaxVarInSublist S (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) res) + 1 with hu'
                      have hfresh := fresh_var_subst_equivalence S I d (List.filter (fun p ↦ decide (p.1 ∈ Freevar S (Formula.Forall x φ))) res) u u' x1
                      rw [hfresh]
                      · rw [hu]
                        simp_arith
                        right
                        simp [List.filter_cons, h_filter_b]
                      · rw [hu']
                        simp_arith
                      · rw [hu]
                        have hneq : (x1 ≤ MaxVarInFormula S φ) := by
                          apply var_le_max_var_in_formula
                          tauto
                        simp_arith
                        tauto
                      · rw [hu']
                        have hneq : (x1 ≤ MaxVarInFormula S φ) := by
                          apply var_le_max_var_in_formula
                          tauto
                        simp_arith
                        tauto
                  · exact hcase
                  · rfl

end FirstOrderLogic
