import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
namespace EulerSixth

/-- Lander and Parkin's 1966 counterexample, included as a positive control. -/
theorem lander_parkin : 27^5 + 84^5 + 110^5 + 133^5 = (144 : Nat)^5 := by decide +kernel

def Equation (a b c z : Nat) : Prop := a^6 + 2*b^6 + 2*c^6 = z^6

private def tag (p x : Nat) := if x % p = 0 then 0 else 1
private theorem tag_le (p x : Nat) : tag p x ≤ 1 := by unfold tag; split <;> decide

private theorem splitPrime {a b c z p m : Nat} (eqn : Equation a b c z)
    (hm : 5 < m) (d : p ∣ m)
    (table : ∀ r : Fin m, r.val^6 % m = tag p r.val) :
    p ∣ b ∧ p ∣ c ∧ (p ∣ a ↔ p ∣ z) := by
  have value (x : Nat) : x^6 ≡ tag p x [MOD m] := by
    change x^6 % m = tag p x % m
    rw [Nat.mod_eq_of_lt (by have := tag_le p x; omega : tag p x < m), Nat.pow_mod]
    have h := table ⟨x % m, Nat.mod_lt _ (by omega)⟩
    simpa only [tag,Nat.mod_mod_of_dvd _ d] using h
  have h := ((value a).add ((value b).mul_left 2)).add ((value c).mul_left 2)
  rw [show a^6 + 2*b^6 + 2*c^6 = z^6 from eqn] at h
  have ht := (value z).symm.trans h
  change tag p z % m = (tag p a + 2*tag p b + 2*tag p c) % m at ht
  have h₁ := tag_le p a
  have h₂ := tag_le p b
  have h₃ := tag_le p c
  have h₄ := tag_le p z
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at ht
  simp only [Nat.dvd_iff_mod_eq_zero]
  unfold tag at ht
  split at ht <;> split at ht <;> split at ht <;> split at ht <;> omega

theorem localConditions {a b c z : Nat} (h : Equation a b c z) :
    (2 ∣ b ∧ 2 ∣ c ∧ (2 ∣ a ↔ 2 ∣ z)) ∧
    (3 ∣ b ∧ 3 ∣ c ∧ (3 ∣ a ↔ 3 ∣ z)) ∧
    (7 ∣ b ∧ 7 ∣ c ∧ (7 ∣ a ↔ 7 ∣ z)) :=
  ⟨splitPrime (m:=8) h (by decide) (by decide) (by decide +kernel),
   splitPrime (m:=9) h (by decide) (by decide) (by decide +kernel),
   splitPrime (m:=7) h (by decide) (by decide) (by decide +kernel)⟩

/-- Applies to unbounded naturals, even when a solution has a common factor. -/
theorem double_pair_sieve {a b c z : Nat} (h : Equation a b c z) :
    42 ∣ b ∧ 42 ∣ c ∧ a^6 % (2*42^6) = z^6 % (2*42^6) := by
  obtain ⟨⟨b2,c2,_⟩,⟨b3,c3,_⟩,⟨b7,c7,_⟩⟩ := localConditions h
  have combine (n : Nat) (h2 : 2 ∣ n) (h3 : 3 ∣ n) (h7 : 7 ∣ n) : 42 ∣ n := by
    have h6 : 6 ∣ n := (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3
    exact (show Nat.Coprime 6 7 by decide).mul_dvd_of_dvd_of_dvd h6 h7
  refine ⟨combine b b2 b3 b7, combine c c2 c3 c7, ?_⟩
  obtain ⟨u,rfl⟩ := combine b b2 b3 b7
  obtain ⟨v,rfl⟩ := combine c c2 c3 c7
  have hz : z^6 = a^6 + (u^6+v^6)*(2*42^6) := by
    rw [← h]; ring
  rw [hz, Nat.add_mul_mod_self_right]

end EulerSixth
