import Euler.Roots

namespace EulerSixth

abbrev modulus := 10978063488

def unitBase (z : Nat) := z % 2 != 0 && z % 3 != 0 && z % 7 != 0

private def twoResidues (q t : Nat) :=
  (List.range q).any fun u => (List.range q).any fun v => (u^6 + v^6) % q == t % q

private theorem residues_present {q : Nat} (hq : 0 < q) (u v : Nat) :
    twoResidues q (u^6 + v^6) = true := by
  apply List.any_eq_true.mpr
  refine ⟨u%q, List.mem_range.mpr (Nat.mod_lt _ hq), List.any_eq_true.mpr ?_⟩
  refine ⟨v%q, List.mem_range.mpr (Nat.mod_lt _ hq), beq_iff_eq.mpr ?_⟩
  have hu : (u%q)^6 ≡ u^6 [MOD q] := (Nat.pow_mod u 6 q).symm
  have hv : (v%q)^6 ≡ v^6 [MOD q] := (Nat.pow_mod v 6 q).symm
  exact hu.add hv

def possible (a z : Nat) : Bool :=
  0 < a && a < z && a^6 % modulus == z^6 % modulus &&
    let t := (z^6-a^6)/modulus
    twoResidues 8 t && twoResidues 9 t && twoResidues 31 t

theorem possible_of_solution {a b c z : Nat} (ha : 0 < a) (hlt : a < z)
    (h : Equation a b c z) : possible a z = true := by
  obtain ⟨⟨u,rfl⟩,⟨v,rfl⟩,he⟩ := double_pair_sieve h
  have hz : z^6 = a^6 + (u^6+v^6)*modulus := by rw [←h]; unfold modulus; ring
  have ht : (z^6-a^6)/modulus = u^6+v^6 := by
    rw [hz, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (by decide : 0 < modulus)]
  simp only [possible, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ht]
  exact ⟨⟨⟨ha,hlt⟩,he⟩,⟨⟨residues_present (by decide) u v, residues_present (by decide) u v⟩,
    residues_present (by decide) u v⟩⟩

def excluded (z : Nat) := !unitBase z || roots.all fun r => !possible (r*z%117649) z

def block (i : Nat) := (List.range 1024).all fun j => decide (117649 ≤ 1024*i+j) || excluded (1024*i+j)

end EulerSixth
