import Shannon.Boxes
import Shannon.Cores.C03505
import Shannon.Cores.C03523
import Shannon.Cores.C03606
import Shannon.Cores.C04505
import Shannon.Cores.C04606
import Shannon.Cores.C12646
import Shannon.Cores.C13640
import Shannon.Cores.C16531
import Shannon.Cores.C20635
import Shannon.Cores.C22336
import Shannon.Cores.C22346
import Shannon.Cores.C22435
import Shannon.Cores.C22445
import Shannon.Cores.C35236
import Shannon.Cores.C35326
import Shannon.Cores.C36165
import Shannon.Cores.C45323
import Shannon.Cores.C45424
import Shannon.Cores.C46323
import Shannon.Cores.C46406
import Shannon.Cores.C46424
import Shannon.Cores.C46460

namespace Shannon.Seven

set_option maxRecDepth 16000

private theorem core_0_3505 (c : Nat → Letter) : ¬Packing appendix 0 1279 c :=
  excluded_by_formula C03505.ids C03505.edges (by decide +kernel) C03505.unsat c

private theorem core_0_3523 (c : Nat → Letter) : ¬Packing appendix 0 1291 c :=
  excluded_by_formula C03523.ids C03523.edges (by decide +kernel) C03523.unsat c

private theorem core_0_3606 (c : Nat → Letter) : ¬Packing appendix 0 1329 c :=
  excluded_by_formula C03606.ids C03606.edges (by decide +kernel) C03606.unsat c

private theorem core_0_4505 (c : Nat → Letter) : ¬Packing appendix 0 1622 c :=
  excluded_by_formula C04505.ids C04505.edges (by decide +kernel) C04505.unsat c

private theorem core_0_4606 (c : Nat → Letter) : ¬Packing appendix 0 1672 c :=
  excluded_by_formula C04606.ids C04606.edges (by decide +kernel) C04606.unsat c

private theorem core_1_2646 (c : Nat → Letter) : ¬Packing appendix 1 1014 c :=
  excluded_by_formula C12646.ids C12646.edges (by decide +kernel) C12646.unsat c

private theorem core_1_3640 (c : Nat → Letter) : ¬Packing appendix 1 1351 c :=
  excluded_by_formula C13640.ids C13640.edges (by decide +kernel) C13640.unsat c

private theorem core_1_6531 (c : Nat → Letter) : ¬Packing appendix 1 2325 c :=
  excluded_by_formula C16531.ids C16531.edges (by decide +kernel) C16531.unsat c

private theorem core_2_0635 (c : Nat → Letter) : ¬Packing appendix 2 320 c :=
  excluded_by_formula C20635.ids C20635.edges (by decide +kernel) C20635.unsat c

private theorem core_2_2336 (c : Nat → Letter) : ¬Packing appendix 2 860 c :=
  excluded_by_formula C22336.ids C22336.edges (by decide +kernel) C22336.unsat c

private theorem core_2_2346 (c : Nat → Letter) : ¬Packing appendix 2 867 c :=
  excluded_by_formula C22346.ids C22346.edges (by decide +kernel) C22346.unsat c

private theorem core_2_2435 (c : Nat → Letter) : ¬Packing appendix 2 908 c :=
  excluded_by_formula C22435.ids C22435.edges (by decide +kernel) C22435.unsat c

private theorem core_2_2445 (c : Nat → Letter) : ¬Packing appendix 2 915 c :=
  excluded_by_formula C22445.ids C22445.edges (by decide +kernel) C22445.unsat c

private theorem core_3_5236 (c : Nat → Letter) : ¬Packing appendix 3 1840 c :=
  excluded_by_formula C35236.ids C35236.edges (by decide +kernel) C35236.unsat c

private theorem core_3_5326 (c : Nat → Letter) : ¬Packing appendix 3 1882 c :=
  excluded_by_formula C35326.ids C35326.edges (by decide +kernel) C35326.unsat c

private theorem core_3_6165 (c : Nat → Letter) : ¬Packing appendix 3 2154 c :=
  excluded_by_formula C36165.ids C36165.edges (by decide +kernel) C36165.unsat c

private theorem core_4_5323 (c : Nat → Letter) : ¬Packing appendix 4 1879 c :=
  excluded_by_formula C45323.ids C45323.edges (by decide +kernel) C45323.unsat c

private theorem core_4_5424 (c : Nat → Letter) : ¬Packing appendix 4 1929 c :=
  excluded_by_formula C45424.ids C45424.edges (by decide +kernel) C45424.unsat c

private theorem core_4_6323 (c : Nat → Letter) : ¬Packing appendix 4 2222 c :=
  excluded_by_formula C46323.ids C46323.edges (by decide +kernel) C46323.unsat c

private theorem core_4_6406 (c : Nat → Letter) : ¬Packing appendix 4 2260 c :=
  excluded_by_formula C46406.ids C46406.edges (by decide +kernel) C46406.unsat c

private theorem core_4_6424 (c : Nat → Letter) : ¬Packing appendix 4 2272 c :=
  excluded_by_formula C46424.ids C46424.edges (by decide +kernel) C46424.unsat c

private theorem core_4_6460 (c : Nat → Letter) : ¬Packing appendix 4 2296 c :=
  excluded_by_formula C46460.ids C46460.edges (by decide +kernel) C46460.unsat c

/-- No assignment of the omitted coordinate to all 367 published shadows
and one arbitrary additional shadow gives a 368-word packing. -/
theorem no_single_coordinate_extension (axis : Fin 5) (extra : Fin 2401) (c : Nat → Letter) :
    ¬Packing appendix axis.val extra.val c := by
  intro pack
  have member := residual_of_packing axis.isLt extra.isLt pack
  rcases axis with ⟨a,ha⟩
  rcases extra with ⟨p,hp⟩
  change Packing appendix a p c at pack
  change p ∈ residual a at member
  rcases (by omega : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4) with h|h|h|h|h <;> subst a
  · simp only [residual,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with h|h|h|h|h <;> subst p
    · exact core_0_3505 c pack
    · exact core_0_3523 c pack
    · exact core_0_3606 c pack
    · exact core_0_4505 c pack
    · exact core_0_4606 c pack
  · simp only [residual,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with h|h|h <;> subst p
    · exact core_1_2646 c pack
    · exact core_1_3640 c pack
    · exact core_1_6531 c pack
  · simp only [residual,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with h|h|h|h|h <;> subst p
    · exact core_2_0635 c pack
    · exact core_2_2336 c pack
    · exact core_2_2346 c pack
    · exact core_2_2435 c pack
    · exact core_2_2445 c pack
  · simp only [residual,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with h|h|h <;> subst p
    · exact core_3_5236 c pack
    · exact core_3_5326 c pack
    · exact core_3_6165 c pack
  · simp only [residual,List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with h|h|h|h|h|h <;> subst p
    · exact core_4_5323 c pack
    · exact core_4_5424 c pack
    · exact core_4_6323 c pack
    · exact core_4_6406 c pack
    · exact core_4_6424 c pack
    · exact core_4_6460 c pack

end Shannon.Seven
