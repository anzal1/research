import Euler.Blocks

namespace EulerSixth

set_option maxRecDepth 16000

private theorem rangeAt {n : Nat} {f : Nat → Bool} (h : (List.range n).all f = true)
    (j : Nat) (hj : j < n) : f j = true :=
  (List.all_eq_true (l := List.range n) (p := f)).mp h j (List.mem_range.mpr hj)

private theorem excluded_of_blocks (z : Nat)
    (hz : z < 117649) : excluded z = true := by
  let i := z / 1024
  have hi : i < 115 := by dsimp [i]; omega
  have row := rangeAt (n := 1024)
    (f := fun j => decide (117649 ≤ 1024*i+j) || excluded (1024*i+j))
    (checked_blocks i hi) (z%1024) (Nat.mod_lt _ (by decide))
  dsimp only [i] at row
  rw [Nat.div_add_mod] at row
  simpa only [show ¬117649 ≤ z by omega, decide_false, Bool.false_or] using row

private theorem excludeUnit {a b c z : Nat} (ha : 0 < a) (hz : z < 117649) (hlt : a < z)
    (h2 : ¬2 ∣ z) (h3 : ¬3 ∣ z) (h7 : ¬7 ∣ z) (h : Equation a b c z) : False := by
  have e := (double_pair_sieve h).2.2
  have eq7 := congrArg (· % 117649) e
  simp only [Nat.mod_mod_of_dvd _ (by decide : 117649 ∣ 2*42^6)] at eq7
  obtain ⟨r,hr,ar⟩ := root_ratio h7 eq7
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt hz)] at ar
  have row := excluded_of_blocks z hz
  have unit : unitBase z = true := by
    simp only [unitBase, Bool.and_eq_true,bne_iff_ne]
    simp only [Nat.dvd_iff_mod_eq_zero] at h2 h3 h7
    exact ⟨⟨h2,h3⟩,h7⟩
  simp only [excluded, unit, Bool.not_true, Bool.false_or] at row
  have reject := List.all_eq_true.mp row r hr
  change (!possible (r*z%117649) z) = true at reject
  rw [←ar, possible_of_solution ha hlt h] at reject
  exact Bool.noConfusion reject

private theorem excluded_below (z : Nat) :
    ∀ a b c : Nat, 0 < a → 0 < b → 0 < c → z < 117649 → ¬Equation a b c z := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
    intro a b c ha hb hc hz eqn
    have hlt : a < z := (Nat.pow_lt_pow_iff_left (by decide : 6 ≠ 0)).mp (by
      have := Nat.pow_pos hb (n:=6)
      change a^6 + 2*b^6 + 2*c^6 = z^6 at eqn
      omega)
    have reduce (p : Nat) (hp : 1 < p) (pa : p ∣ a) (pb : p ∣ b)
        (pc : p ∣ c) (pz : p ∣ z) : False := by
      obtain ⟨A,rfl⟩ := pa
      obtain ⟨B,rfl⟩ := pb
      obtain ⟨C,rfl⟩ := pc
      obtain ⟨Z,hZ⟩ := pz
      rw [hZ] at eqn hz hlt
      have Zpos : 0 < Z := Nat.pos_of_mul_pos_left (by omega : 0 < p*Z)
      have Zlt : Z < z := by rw [hZ]; simpa using Nat.mul_lt_mul_of_pos_right hp Zpos
      apply ih Z Zlt A B C (Nat.pos_of_mul_pos_left ha) (Nat.pos_of_mul_pos_left hb)
        (Nat.pos_of_mul_pos_left hc) (by omega)
      apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < p) (n:=6))
      calc
        p^6 * (A^6 + 2*B^6 + 2*C^6) = (p*A)^6 + 2*(p*B)^6 + 2*(p*C)^6 := by ring
        _ = (p*Z)^6 := eqn
        _ = p^6*Z^6 := Nat.mul_pow _ _ _
    obtain ⟨⟨b2,c2,az2⟩,⟨b3,c3,az3⟩,⟨b7,c7,az7⟩⟩ := localConditions eqn
    by_cases h2 : 2 ∣ z
    · exact reduce 2 (by decide) (az2.mpr h2) b2 c2 h2
    by_cases h3 : 3 ∣ z
    · exact reduce 3 (by decide) (az3.mpr h3) b3 c3 h3
    by_cases h7 : 7 ∣ z
    · exact reduce 7 (by decide) (az7.mpr h7) b7 c7 h7
    exact excludeUnit ha hz hlt h2 h3 h7 eqn

/-- For five positive sixth powers with two repeated pairs, the right-hand
base must be at least 7^6. Common factors are allowed. -/
theorem double_pair_bound {a b c z : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (eqn : a^6 + 2*b^6 + 2*c^6 = z^6) : 117649 ≤ z := by
  exact Nat.le_of_not_gt (fun hz => excluded_below z a b c ha hb hc hz eqn)

/-- Three copies of one positive sixth power and two of another never sum
to a sixth power. The second base may even be zero. -/
theorem triple_pair_impossible (u v z : Nat) (hu : 0 < u) :
    3*u^6 + 2*v^6 ≠ z^6 := by
  induction u using Nat.strong_induction_on generalizing v z with
  | h u ih =>
    intro eqn
    have h : Equation u u v z := by unfold Equation; omega
    obtain ⟨du, dv, az⟩ := (localConditions h).1
    obtain ⟨Z, hZ⟩ := az.mp du
    obtain ⟨U, hU⟩ := du
    obtain ⟨V, hV⟩ := dv
    apply ih U (by omega) V Z (by omega)
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2^6)
    calc
      2^6 * (3*U^6 + 2*V^6) = 3*(2*U)^6 + 2*(2*V)^6 := by ring
      _ = (2*Z)^6 := by simpa only [hU, hV, hZ] using eqn
      _ = 2^6 * Z^6 := Nat.mul_pow _ _ _

#print axioms lander_parkin
#print axioms double_pair_sieve
#print axioms double_pair_bound
#print axioms triple_pair_impossible

end EulerSixth
