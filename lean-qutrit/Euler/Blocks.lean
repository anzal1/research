import Euler.Check

/-! Each page is a separate kernel computation so the replay has bounded memory. -/
namespace EulerSixth
set_option Elab.async false
set_option maxRecDepth 16000

private def page (p : Nat) := (List.range 8).all fun j => block (8*p+j)
private theorem page0 : page 0 = true := by decide +kernel
private theorem page1 : page 1 = true := by decide +kernel
private theorem page2 : page 2 = true := by decide +kernel
private theorem page3 : page 3 = true := by decide +kernel
private theorem page4 : page 4 = true := by decide +kernel
private theorem page5 : page 5 = true := by decide +kernel
private theorem page6 : page 6 = true := by decide +kernel
private theorem page7 : page 7 = true := by decide +kernel
private theorem page8 : page 8 = true := by decide +kernel
private theorem page9 : page 9 = true := by decide +kernel
private theorem page10 : page 10 = true := by decide +kernel
private theorem page11 : page 11 = true := by decide +kernel
private theorem page12 : page 12 = true := by decide +kernel
private theorem page13 : page 13 = true := by decide +kernel
private theorem page14 : page 14 = true := by decide +kernel
private theorem pages (p : Nat) (hp : p < 15) : page p = true := by
  match p with
  | 0 => exact page0
  | 1 => exact page1
  | 2 => exact page2
  | 3 => exact page3
  | 4 => exact page4
  | 5 => exact page5
  | 6 => exact page6
  | 7 => exact page7
  | 8 => exact page8
  | 9 => exact page9
  | 10 => exact page10
  | 11 => exact page11
  | 12 => exact page12
  | 13 => exact page13
  | 14 => exact page14
  | n+15 => omega

theorem checked_blocks (i : Nat) (hi : i < 115) : block i = true := by
  have h := List.all_eq_true.mp (pages (i/8) (by omega)) (i%8)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [Nat.div_add_mod] using h

end EulerSixth
