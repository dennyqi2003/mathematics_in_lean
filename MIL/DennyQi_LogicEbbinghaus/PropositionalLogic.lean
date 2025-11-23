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
  sorry

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
  sorry

def SetSingleton (p : PropLogic) : PropSet :=
  fun x => x = p

def SetUnion (P Q : PropSet) : PropSet :=
  fun x => P x ∨ Q x

theorem prop_excluded_middle (φ : PropLogic) : is_tautology (PropLogic.Or φ (PropLogic.Not φ)) := by
  sorry

theorem prop_intro_and (φ ψ : PropLogic) : (SetUnion (SetSingleton φ) (SetSingleton ψ)) |== (PropLogic.And φ ψ) := by
  sorry

theorem prop_elim_and1 (φ ψ : PropLogic) :
  ((PropLogic.And φ ψ) |= φ) := by
  sorry

theorem prop_elim_and2 (φ ψ : PropLogic) :
  ((PropLogic.And φ ψ) |= ψ) := by
  sorry

theorem prop_intro_or1 (φ ψ : PropLogic) :
  (φ |= (PropLogic.Or φ ψ)) := by
  sorry

theorem prop_intro_or2 (φ ψ : PropLogic) :
  (ψ |= (PropLogic.Or φ ψ)) := by
  sorry

theorem prop_double_neg (φ : PropLogic) :
  φ === PropLogic.Not (PropLogic.Not φ) := by
  sorry

theorem prop_idempotence1 (φ : PropLogic) :
  ((PropLogic.And φ φ) === φ) := by
  sorry

theorem prop_idempotence2 (φ : PropLogic) :
  ((PropLogic.Or φ φ) === φ) := by
  sorry

theorem prop_comm_and (φ ψ : PropLogic) :
  PropLogic.And φ ψ === PropLogic.And ψ φ := by
  sorry

theorem prop_comm_or (φ ψ : PropLogic) :
  PropLogic.Or φ ψ === PropLogic.Or ψ φ := by
  sorry

theorem prop_assoc_and (φ ψ chi : PropLogic) :
  PropLogic.And (PropLogic.And φ ψ) chi === PropLogic.And φ (PropLogic.And ψ chi) := by
  sorry

theorem prop_assoc_or (φ ψ chi : PropLogic) :
  PropLogic.Or (PropLogic.Or φ ψ) chi === PropLogic.Or φ (PropLogic.Or ψ chi) := by
  sorry

theorem prop_distributive1 (φ ψ chi : PropLogic) :
  (PropLogic.Or φ (PropLogic.And ψ chi) === PropLogic.And (PropLogic.Or φ ψ) (PropLogic.Or φ chi)) := by
  sorry

theorem prop_distributive2 (φ ψ chi : PropLogic) :
  (PropLogic.And φ (PropLogic.Or ψ chi) === PropLogic.Or (PropLogic.And φ ψ) (PropLogic.And φ chi)) := by
  sorry

theorem prop_de_morgan1 (φ ψ : PropLogic) :
  (PropLogic.Not (PropLogic.And φ ψ) === PropLogic.Or (PropLogic.Not φ) (PropLogic.Not ψ)) := by
  sorry

theorem prop_de_morgan2 (φ ψ : PropLogic) :
  (PropLogic.Not (PropLogic.Or φ ψ) === PropLogic.And (PropLogic.Not φ) (PropLogic.Not ψ)) := by
  sorry

theorem prop_absorption1 (φ ψ : PropLogic) :
  (PropLogic.Or φ (PropLogic.And φ ψ) === φ) := by
  sorry

theorem prop_absorption2 (φ ψ : PropLogic) :
  (PropLogic.And φ (PropLogic.Or φ ψ) === φ) := by
  sorry

theorem prop_trans_consequence (φ ψ chi : PropLogic) :
  (φ |= ψ) → (ψ |= chi) → (φ |= chi) := by
  sorry

theorem prop_trans_equivalence (φ ψ chi : PropLogic) :
  (φ === ψ) → (ψ === chi) → (φ === chi) := by
  sorry

theorem prop_congruence_not (φ1 φ2 : PropLogic) :
  (φ1 === φ2 → PropLogic.Not φ1 === PropLogic.Not φ2) := by
  sorry

theorem prop_congruence_and (φ1 φ2 ψ1 ψ2 : PropLogic) :
  (φ1 === φ2 → ψ1 === ψ2 → PropLogic.And φ1 ψ1 === PropLogic.And φ2 ψ2) := by
  sorry

theorem prop_congruence_or (φ1 φ2 ψ1 ψ2 : PropLogic) :
  (φ1 === φ2 → ψ1 === ψ2 → PropLogic.Or φ1 ψ1 === PropLogic.Or φ2 ψ2) := by
  sorry

theorem prop_or_elim (Φ : PropSet) (φ1 φ2 ψ : PropLogic) :
  (SetUnion Φ (SetSingleton φ1)) |== ψ →
  (SetUnion Φ (SetSingleton φ2)) |== ψ →
  (SetUnion Φ (SetSingleton (PropLogic.Or φ1 φ2))) |== ψ := by
  sorry

theorem prop_contrapositive (Φ : PropSet) (φ ψ : PropLogic) :
  (SetUnion Φ (SetSingleton (PropLogic.Not φ))) |== ψ →
  (SetUnion Φ (SetSingleton (PropLogic.Not ψ))) |== φ := by
  sorry

def EmptySet : PropSet := fun _ => False

theorem prop_contrapositive_corollary (φ ψ : PropLogic) :
  PropLogic.Not φ |= ψ ↔ PropLogic.Not ψ |= φ := by
    sorry

end PropositionalLogic
