import Qutrit.Basic

namespace Qutrit

abbrev Coeff := Fin 8 → F

/-- Coefficients 0–3 specify a binary cubic, 4–7 the independent hull shifts.
The final four coordinates are two signed copies of each quadratic remainder. -/
def encode (v : Coeff) : Word 12 :=
  let a := v 0
  let b := v 1
  let c := v 2
  let d := v 3
  ![(a,b+v 4), (a,-v 4), (a+b+c+d,b-c+v 5), (a+b+c+d,-v 5),
    (a-b+c-d,-(b+c)+v 6), (a-b+c-d,-v 6), (d,c+v 7), (d,-v 7),
    (a-c,b-d), (a-c,-(b-d)), (a+c-d,b-c-d), (a+c-d,-(b-c-d))]

def encoder : Coeff →ₗ[F] Word 12 where
  toFun := encode
  map_add' := by
    intro a b
    funext i
    fin_cases i <;> apply Prod.ext <;> simp [encode] <;> ring
  map_smul' := by
    intro t a
    funext i
    fin_cases i <;> apply Prod.ext <;> simp [encode, smul_eq_mul] <;> ring

def normalizer : Submodule F (Word 12) := LinearMap.range encoder

theorem encode_injective : Function.Injective encode := by
  intro a b h
  have ha := congrArg (fun w : Word 12 => (w 0).1) h
  have hd := congrArg (fun w : Word 12 => (w 6).1) h
  have hc := congrArg (fun w : Word 12 => (w 8).1) h
  have hb := congrArg (fun w : Word 12 => (w 8).2) h
  have h₄ := congrArg (fun w : Word 12 => (w 1).2) h
  have h₅ := congrArg (fun w : Word 12 => (w 3).2) h
  have h₆ := congrArg (fun w : Word 12 => (w 5).2) h
  have h₇ := congrArg (fun w : Word 12 => (w 7).2) h
  simp [encode] at ha hd hc hb h₄ h₅ h₆ h₇
  rw [ha] at hc
  rw [hd] at hb
  simp at hc hb
  funext i
  fin_cases i <;> assumption

/-- The restricted alternating form, factored through the four cubic coefficients. -/
def cubicGram (v w : Coeff) : F :=
  (v 0 * w 1 - v 1 * w 0) + (v 0 * w 2 - v 2 * w 0) +
  (v 1 * w 3 - v 3 * w 1) - (v 2 * w 3 - v 3 * w 2)

theorem gram (v w : Coeff) : symp (encode v) (encode w) = cubicGram v w := by
  simp [symp, det, cubicGram, encode, Fin.sum_univ_succ]
  ring_nf
  rw [show (2 : F) = -1 by decide]
  ring

def logicalZero (v : Coeff) := v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0

private theorem gram_kernel (a b c d : F) :
    -b-c = 0 → a-d = 0 → a+d = 0 → b-c = 0 →
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by revert a b c d; decide

theorem radical_iff (v : Coeff) : encode v ∈ radical normalizer ↔ logicalZero v := by
  constructor
  · intro h
    have orth (w : Coeff) := h.2 (encode w) (show encode w ∈ normalizer from ⟨w,rfl⟩)
    apply gram_kernel
    · simpa [gram,cubicGram,sub_eq_add_neg] using orth ![1,0,0,0,0,0,0,0]
    · simpa [gram,cubicGram,sub_eq_add_neg] using orth ![0,1,0,0,0,0,0,0]
    · simpa [gram,cubicGram,sub_eq_add_neg] using orth ![0,0,1,0,0,0,0,0]
    · simpa [gram,cubicGram,sub_eq_add_neg] using orth ![0,0,0,1,0,0,0,0]
  · rintro ⟨ha,hb,hc,hd⟩
    refine ⟨⟨_,rfl⟩, ?_⟩
    rintro w ⟨b,rfl⟩
    change symp (encode v) (encode b) = 0
    simp [gram,cubicGram,ha,hb,hc,hd]

private def logical : Coeff →ₗ[F] (Fin 4 → F) :=
  LinearMap.pi fun i => LinearMap.proj (i.castLE (by decide))

private theorem logicalKer (v : Coeff) : v ∈ (LinearMap.ker logical) ↔ logicalZero v := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  · rintro ⟨ha,hb,hc,hd⟩
    show logical v = 0
    funext i
    fin_cases i <;> assumption

theorem dimensions : Module.finrank F normalizer = 8 ∧
    Module.finrank F (radical normalizer) = 4 := by
  have hi : Function.Injective encoder := encode_injective
  have hs : Function.Surjective logical := by
    intro p
    refine ⟨![p 0,p 1,p 2,p 3,0,0,0,0], ?_⟩
    funext i
    fin_cases i <;> rfl
  have hk := logical.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hk
  have he : radical normalizer = (LinearMap.ker logical).map encoder := by
    ext w
    constructor
    · intro hw
      obtain ⟨a, rfl⟩ := hw.1
      exact ⟨a, (logicalKer a).2 ((radical_iff a).1 hw), rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact (radical_iff a).2 ((logicalKer a).1 ha)
  rw [he, ← (Submodule.equivMapOfInjective encoder hi (LinearMap.ker logical)).finrank_eq,
    show normalizer = (LinearMap.range encoder) from rfl, LinearMap.finrank_range_of_inj hi,
    Module.finrank_fin_fun]
  omega

private def pairMin (x y : F) : ℕ :=
  if x ≠ 0 then 2 else if y ≠ 0 then 1 else 0

private theorem pair_bound (x y h : F) :
    pairMin x y ≤ occupied (x,y+h) + occupied (x,-h) := by revert x y h; decide

/-- Only 80 nonzero cubics. The four independently shiftable pairs are
bounded first, so this check does not enumerate hull coefficients. -/
private theorem cubic_bound (a b c d : F) :
    ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
    9 ≤ pairMin a b + pairMin (a+b+c+d) (b-c) +
      pairMin (a-b+c-d) (-(b+c)) + pairMin d c +
      occupied (a-c,b-d) + occupied (a-c,-(b-d)) +
      occupied (a+c-d,b-c-d) + occupied (a+c-d,-(b-c-d)) := by
  revert a b c d
  decide

theorem weight_lower (v : Coeff) (hn : encode v ∉ radical normalizer) :
    9 ≤ weight (encode v) := by
  rw [radical_iff] at hn
  have h := cubic_bound (v 0) (v 1) (v 2) (v 3) hn
  have h₀ := pair_bound (v 0) (v 1) (v 4)
  have h₁ := pair_bound (v 0+v 1+v 2+v 3) (v 1-v 2) (v 5)
  have h₂ := pair_bound (v 0-v 1+v 2-v 3) (-(v 1+v 2)) (v 6)
  have h₃ := pair_bound (v 3) (v 2) (v 7)
  simp only [weight, Fin.sum_univ_succ, encode, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  omega

theorem witness_parameters : HasParameters 12 2 9 6 normalizer := by
  obtain ⟨hN,hR⟩ := dimensions
  refine ⟨by omega, by omega, ?_, ?_⟩
  · let v : Coeff := ![0,-1,0,1,0,0,0,0]
    exact ⟨encode v, ⟨v,rfl⟩, by simp [radical_iff,logicalZero,v], by decide⟩
  · rintro t ⟨w,⟨a,rfl⟩,hn,rfl⟩
    exact weight_lower a hn

end Qutrit
