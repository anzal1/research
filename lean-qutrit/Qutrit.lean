import Qutrit.Witness
import Qutrit.Upper

namespace Qutrit

theorem optimal_additive_distance :
    IsGreatest {d | ∃ N : Submodule F (Word 12), HasParameters 12 2 d 6 N} 9 :=
  ⟨⟨normalizer, witness_parameters⟩, fun _ ⟨_, h⟩ => distance_upper h⟩

#print axioms witness_parameters
#print axioms distance_upper
#print axioms optimal_additive_distance

end Qutrit
