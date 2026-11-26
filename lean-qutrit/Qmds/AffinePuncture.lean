import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.LinearCombination

/-! Full-support Hermitian moment certificates on disjoint affine base-field lines. -/
namespace AffinePuncture

open Polynomial Finset
open scoped BigOperators

variable {F K : Type*} [Field F] [Field K]

private theorem weighted_eval {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (v : ι → K) (hv : Set.InjOn v s) (p : K[X]) (hp : p.natDegree < s.card - 1) :
    ∑ i ∈ s, p.eval (v i) * Lagrange.nodalWeight s v i = 0 := by
  have hdeg : p.degree < (s.card : WithBot ℕ) :=
    degree_le_natDegree.trans_lt (show (↑p.natDegree : WithBot ℕ) < ↑s.card from
      WithBot.coe_lt_coe.mpr (show p.natDegree < s.card by omega))
  have h := congrArg (fun g : K[X] => g.coeff (s.card-1)) (Lagrange.eq_interpolate hv hdeg)
  simp only [Lagrange.interpolate_apply, finset_sum_coeff, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt hp] at h
  rw [h]
  apply sum_congr rfl
  intro i hi
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
    ← Lagrange.nodal_erase_eq_nodal_div hi, coeff_C_mul, ← card_erase_of_mem hi,
    ← Lagrange.natDegree_nodal (v := v), coeff_natDegree, (Lagrange.nodal_monic ..).leadingCoeff,
    mul_one]

/-- On any chosen six or more points of one line, the same nonzero
base-field weights annihilate all nine Hermitian moments. -/
theorem line_moments [DecidableEq F] (φ : F →+* K) (σ : K →+* K)
    (hfix : ∀ x, σ (φ x) = φ x) (b : K) (s : Finset F) (hs : 6 ≤ s.card) :
    ∃ w : F → F, (∀ t ∈ s, w t ≠ 0) ∧ ∀ i j : Fin 3,
      ∑ t ∈ s, φ (w t) * (b + φ t)^i.val * σ ((b + φ t)^j.val) = 0 := by
  refine ⟨Lagrange.nodalWeight s id, fun _ ht =>
    Lagrange.nodalWeight_ne_zero Function.injective_id.injOn ht, ?_⟩
  intro i j
  let p : K[X] := (C b + X)^i.val * (C (σ b) + X)^j.val
  have hp : p.natDegree ≤ i.val + j.val := by
    dsimp [p]
    apply natDegree_mul_le.trans
    simp [natDegree_pow, add_comm (C _) X]
  have h := weighted_eval s φ φ.injective.injOn p (by have := i.isLt; have := j.isLt; omega)
  rw [← h]
  apply sum_congr rfl
  intro t _
  simp [p, Lagrange.nodalWeight, hfix]
  ring

/-- A length between six and rq can be distributed over r lines with
each occupied line holding between six and q points. -/
private theorem partition (q r n : ℕ) (hq : 11 ≤ q) (hn : 6 ≤ n) (hmax : n ≤ r*q) :
    ∃ a : Fin r → ℕ, (∑ i, a i) = n ∧ ∀ i, a i ≤ q ∧ (a i = 0 ∨ 6 ≤ a i) := by
  induction r generalizing n with
  | zero => simp at hmax; omega
  | succ r ih =>
    by_cases h : n ≤ q
    · refine ⟨Fin.cons n (fun _ => 0), by simp [Fin.sum_univ_succ], ?_⟩
      exact Fin.cases ⟨h,Or.inr hn⟩ (fun _ => ⟨Nat.zero_le _,Or.inl rfl⟩)
    · let k := min q (n-6)
      have hk : 6 ≤ k ∧ k ≤ q ∧ k ≤ n-6 := by dsimp [k]; omega
      obtain ⟨a,ha,hsize⟩ := ih (n-k) (by omega) (by
        rw [Nat.succ_mul] at hmax
        by_cases hr : r = 0
        · subst r; simp at hmax; omega
        have hcap : q ≤ r*q := by simpa using Nat.mul_le_mul_right q (show 1 ≤ r by omega)
        dsimp [k]; omega)
      refine ⟨Fin.cons k a, by simp [Fin.sum_univ_succ,ha]; omega, ?_⟩
      exact Fin.cases ⟨hk.2.1,Or.inr hk.1⟩ hsize

/-- The affine part of the degree-two conic puncture code has every
support size from 6 to q² over a base field with q ≥ 11 elements.
The line index is embedded in F and β is outside the base field. -/
theorem all_affine_lengths [Fintype F] [DecidableEq F]
    (φ : F →+* K) (σ : K →+* K) (hfix : ∀ x, σ (φ x) = φ x)
    (β : K) (hβ : β ∉ Set.range φ) (n : ℕ)
    (hq : 11 ≤ Fintype.card F) (hn : 6 ≤ n) (hmax : n ≤ Fintype.card F ^ 2) :
    let point := fun p : F × F => β * φ p.1 + φ p.2
    Function.Injective point ∧ ∃ (s : F → Finset F) (w : F → F → F),
      (∑ b, (s b).card) = n ∧ (∀ b t, t ∈ s b → w b t ≠ 0) ∧
      ∀ i j : Fin 3, ∑ b, ∑ t ∈ s b,
        φ (w b t) * point (b,t)^i.val * σ (point (b,t)^j.val) = 0 := by
  classical
  dsimp only
  constructor
  · rintro ⟨b,t⟩ ⟨c,u⟩ he
    change β * φ b + φ t = β * φ c + φ u at he
    have hbc : b = c := by
      by_contra hne
      apply hβ
      refine ⟨(u-t)/(b-c), ?_⟩
      rw [map_div₀, map_sub, map_sub, div_eq_iff (sub_ne_zero.mpr (φ.injective.ne hne))]
      linear_combination -he
    subst c
    exact Prod.ext rfl (φ.injective (add_left_cancel he))
  · obtain ⟨a,ha,hsize⟩ := partition (Fintype.card F) (Fintype.card F) n hq hn
      (by simpa [pow_two] using hmax)
    let e := Fintype.equivFin F
    have pick (b : F) : ∃ s : Finset F, s.card = a (e b) :=
      Finset.exists_subset_card_eq (s := Finset.univ) (by simpa using (hsize (e b)).1) |>.imp
        fun _ h => h.2
    choose s hs using pick
    have block (b : F) : ∃ w : F → F, (∀ t ∈ s b, w t ≠ 0) ∧ ∀ i j : Fin 3,
        ∑ t ∈ s b, φ (w t) * (β * φ b + φ t)^i.val * σ ((β * φ b + φ t)^j.val) = 0 := by
      rcases (hsize (e b)).2 with h | h
      · have hz : s b = ∅ := card_eq_zero.mp ((hs b).trans h)
        exact ⟨fun _ => 0, by simp [hz], by simp [hz]⟩
      · exact line_moments φ σ hfix _ _ (by rw [hs]; exact h)
    choose w hw hmoment using block
    exact ⟨s,w,by simpa only [hs,e.sum_comp] using ha, hw,
      fun i j => Finset.sum_eq_zero fun b _ => hmoment b i j⟩


end AffinePuncture
