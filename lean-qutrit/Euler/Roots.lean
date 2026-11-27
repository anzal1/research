import Euler.Sieve
import Mathlib.Data.ZMod.Basic

namespace EulerSixth

/-- Lift the sixth roots of unity one base-seven digit at a time. -/
private def liftRoots : Nat → List Nat
  | 0 => [0]
  | k+1 => (liftRoots k).flatMap fun s =>
    ((List.range 7).map fun t => s + 7^k*t).filter fun u => u^6 % (7^(k+1)) == 1 % (7^(k+1))

private theorem lift_complete (k r : Nat) (bound : r < 7^k)
    (h : r^6 % (7^k) = 1 % (7^k)) : r ∈ liftRoots k := by
  induction k generalizing r with
  | zero => simp at bound; simpa [liftRoots] using bound
  | succ k ih =>
    have d : 7^k ∣ 7^(k+1) := ⟨7, by rw [pow_succ]⟩
    have hs := congrArg (· % 7^k) h
    simp only [Nat.mod_mod_of_dvd _ d] at hs
    have hm : r % 7^k ∈ liftRoots k :=
      ih _ (Nat.mod_lt _ (Nat.pow_pos (by decide))) (by rw [← Nat.pow_mod]; exact hs)
    have ht : r / 7^k < 7 := (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).2
      (by simpa [pow_succ, Nat.mul_comm] using bound)
    exact List.mem_flatMap.mpr ⟨_,hm,List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨_,List.mem_range.mpr ht, Nat.mod_add_div _ _⟩, beq_iff_eq.mpr h⟩⟩

def roots : List Nat := [1, 34967, 34968, 82681, 82682, 117648]

private theorem roots_correct (r : Nat) (hr : r < 117649) (h : r^6 % 117649 = 1) :
    r ∈ roots := by
  have mem := lift_complete 6 r hr h
  have checked : (liftRoots 6).all (fun x => roots.contains x) = true := by decide +kernel
  exact List.contains_iff_mem.mp (List.all_eq_true.mp checked _ mem)

theorem root_ratio {a z : Nat} (hz : ¬7 ∣ z)
    (eq : a^6 % 117649 = z^6 % 117649) :
    ∃ r ∈ roots, a % 117649 = (r*z) % 117649 := by
  let w := ZMod.unitOfCoprime (n:=117649) z
    ((show Nat.Prime 7 by decide).coprime_pow_of_not_dvd (m:=6) hz)
  let ratio : ZMod 117649 := (a : ZMod 117649) * ↑(w⁻¹)
  have back : ratio * z = (a : ZMod 117649) := by
    change (a : ZMod 117649) * ↑(w⁻¹) * ↑w = _
    simp [mul_assoc]
  have he : (a : ZMod 117649)^6 = (z : ZMod 117649)^6 := by
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff' _ _ _).2 eq
  have one : ratio^6 = 1 := by
    calc
      ratio^6 = (z : ZMod 117649)^6 * (↑(w⁻¹) : ZMod 117649)^6 := by dsimp only [ratio]; rw [mul_pow, he]
      _ = ((↑w : ZMod 117649) * ↑(w⁻¹))^6 := by rw [mul_pow]; rfl
      _ = 1 := by simp
  have castEq : ((ratio.val^6 : Nat) : ZMod 117649) = ((1 : Nat) : ZMod 117649) := by
    simpa using one
  have rmem := roots_correct ratio.val (ZMod.val_lt _) ((ZMod.natCast_eq_natCast_iff' _ _ _).1 castEq)
  refine ⟨ratio.val, rmem, (ZMod.natCast_eq_natCast_iff' _ _ _).1 ?_⟩
  simpa using back.symm

end EulerSixth
