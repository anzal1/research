import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Qutrit

abbrev F := ZMod 3
abbrev Site := F × F
abbrev Word (n : ℕ) := Fin n → Site

def det (p q : Site) : F := p.1 * q.2 - p.2 * q.1
def symp {n} (v w : Word n) : F := ∑ i, det (v i) (w i)
def occupied (p : Site) : ℕ := if p = 0 then 0 else 1
def weight {n} (w : Word n) : ℕ := ∑ i, occupied (w i)

/-- Intersection of a normalizer with its symplectic orthogonal. -/
def radical {n} (N : Submodule F (Word n)) : Submodule F (Word n) where
  carrier := {v | v ∈ N ∧ ∀ w ∈ N, symp v w = 0}
  zero_mem' := by simp [symp, det]
  add_mem' := by
    rintro a b ⟨ha, pa⟩ ⟨hb, pb⟩
    refine ⟨N.add_mem ha hb, fun w hw => ?_⟩
    rw [show symp (a+b) w = symp a w + symp b w by
      simp only [symp, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change ((a i).1 + (b i).1) * (w i).2 - ((a i).2 + (b i).2) * (w i).1 = _
      unfold det
      ring]
    simp [pa w hw, pb w hw]
  smul_mem' := by
    rintro t a ⟨ha, pa⟩
    refine ⟨N.smul_mem t ha, fun w hw => ?_⟩
    rw [show symp (t • a) w = t * symp a w by
      simp only [symp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (t * (a i).1) * (w i).2 - (t * (a i).2) * (w i).1 = _
      unfold det
      ring]
    simp [pa w hw]

/-- Normalizer form of the additive stabilizer parameter formulas.
The last clause requires the minimum to be attained. -/
def HasParameters (n k d c : ℕ) (N : Submodule F (Word n)) : Prop :=
  Module.finrank F N + c = n + k ∧
  Module.finrank F (radical N) + k + c = n ∧
  IsLeast {t | ∃ w ∈ N, w ∉ radical N ∧ weight w = t} d

end Qutrit
