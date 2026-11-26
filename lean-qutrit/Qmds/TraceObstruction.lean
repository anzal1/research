import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

namespace TraceObstruction

open FiniteField

variable {K : Type*} [Field K] [Fintype K]

set_option maxRecDepth 8192 in
/-- Multiplying by a suitable power of a norm-one element makes the
coefficient fixed under Frobenius. Here 257 is prime. -/
private theorem exponent (i : Fin 256) (hi : i ≠ 0) :
    ∃ j : Fin 257, (1 + 255 * j.val * i.val) % 257 = 0 := by
  revert i
  decide

/-- Every one-term candidate in the Ball–Vilar full-length criterion at
q=256 has a root. The constant c is any element of the fixed subfield. -/
theorem monomial_on_norm_fiber (hK : Fintype.card K = 65536)
    (i : Fin 256) (hi : i ≠ 0) (e c : K) (hc : c^256 = c) :
    ∃ x : K, x^257 = c ∧ (e*x^i.val)^256 = e*x^i.val := by
  let y := c^128
  have hy : y^256 = y := by
    dsimp [y]; rw [← pow_mul, Nat.mul_comm, pow_mul, hc]
  have hy2 : y^257 = c := by
    change y^(256+1) = c
    rw [pow_succ, hy, ← pow_two]
    change (c^128)^2 = c
    rw [← pow_mul]; exact hc
  by_cases he : e = 0
  · exact ⟨y, by simp [he,hy2]⟩
  have hperiod : e^65535 = 1 := by simpa [hK] using pow_card_sub_one_eq_one e he
  obtain ⟨j,hj⟩ := exponent i hi
  let u := e^(255*j.val)
  have hu : u^257 = 1 := by
    dsimp [u]; rw [← pow_mul, show 255*j.val*257 = 65535*j.val by omega,
      pow_mul, hperiod, one_pow]
  obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero hj
  have hu' : e*u^i.val = (e^257)^k := by
    dsimp [u]; rw [← pow_mul, ← pow_mul, ← hk, pow_add, pow_one]
  have hf : (e^257)^256 = e^257 := by
    rw [← pow_mul, show 257*256 = 65535+257 by decide, pow_add, hperiod, one_mul]
  have hfixed : (e*(u*y)^i.val)^256 = e*(u*y)^i.val := by
    rw [mul_pow u y, ← mul_assoc, hu', mul_pow]
    rw [← pow_mul (e^257), Nat.mul_comm k 256, pow_mul, hf,
      ← pow_mul y, Nat.mul_comm i.val 256, pow_mul, hy]
  exact ⟨u*y, by rw [mul_pow,hu,one_mul,hy2], hfixed⟩

variable [CharP K 2]

omit [Fintype K] in
private theorem twice_zero (z : K) : z+z = 0 := by
  rw [← two_mul, CharP.ofNat_eq_zero K 2, zero_mul]

theorem monomial_has_root (hK : Fintype.card K = 65536)
    (i : Fin 256) (hi : i ≠ 0) (e c : K) (hc : c^256 = c) :
    ∃ x : K, e*x^i.val + (e*x^i.val)^256 + c + x^257 = 0 := by
  obtain ⟨x,hn,hf⟩ := monomial_on_norm_fiber hK i hi e c hc
  exact ⟨x, by rw [hf, twice_zero, zero_add, hn, twice_zero]⟩

/-- On the unit circle, conjugation interchanges exponents i and 257−i.
After rescaling the circle this excludes every reciprocal two-term candidate. -/
theorem reciprocal_binomial_has_root (hK : Fintype.card K = 65536)
    (i j : Fin 256) (hi : i ≠ 0) (hij : i.val + j.val = 257)
    (a b c : K) (hc : c^256 = c) :
    ∃ x : K, let z := a*x^i.val + b*x^j.val
             z + z^256 + c + x^257 = 0 := by
  let y := c^128
  have hy : y^256 = y := by
    dsimp [y]; rw [← pow_mul, Nat.mul_comm, pow_mul, hc]
  have hy2 : y^257 = c := by
    rw [show 257 = 256+1 by decide, pow_succ, hy, ← pow_two]
    dsimp [y]; rw [← pow_mul]; exact hc
  let A := a*y^i.val
  let B := b*y^j.val
  obtain ⟨u,hu,hf⟩ := monomial_on_norm_fiber hK i hi (A+B^256) 1 (by simp)
  have hinv (z : K) : (z^256)^256 = z := by
    rw [← pow_mul, show 256*256 = Fintype.card K by omega, FiniteField.pow_card]
  have hconj : (u^i.val)^256 = u^j.val := by
    have he : i.val*256 = (i.val-1)*257+j.val := by
      have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
      omega
    rw [← pow_mul, he, pow_add, Nat.mul_comm (i.val-1), pow_mul, hu, one_pow, one_mul]
  have hback : (u^j.val)^256 = u^i.val := by rw [← hconj, hinv]
  have frob (x z : K) : (x+z)^256 = x^256 + z^256 :=
    add_pow_expChar_pow x z 2 8
  simp only [mul_pow, frob,hconj,hinv] at hf
  refine ⟨y*u, ?_⟩
  dsimp only
  simp only [mul_pow y u, hy2, hu, mul_one, ← mul_assoc]
  change A*u^i.val + B*u^j.val + (A*u^i.val + B*u^j.val)^256 + c + c = 0
  rw [frob,mul_pow A,mul_pow B,hconj,hback]
  calc
    _ = (A+B^256)*u^i.val + (A^256+B)*u^j.val + (c+c) := by ring
    _ = 0 := by rw [hf, twice_zero, twice_zero, add_zero]


end TraceObstruction
