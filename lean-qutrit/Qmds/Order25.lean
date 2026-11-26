import Qmds.BinaryCertificate
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.LinearCombination

namespace Qmds.Order25

open BinaryCertificate
variable {K : Type*} [Field K] [CharP K 2]

-- Successive quotients and remainders of squaring modulo the degree-50 obstruction.
private def firstTen : List (ℕ × ℕ) := [
    (0x0, 0x4),
    (0x0, 0x10),
    (0x0, 0x100),
    (0x0, 0x10000),
    (0x0, 0x100000000),
    (0x4010, 0x10095b18d3b10),
    (0x401050757535, 0xa0b41795c045),
    (0x1104404dddd2, 0x12dbd49655da3),
    (0x41045561bfca, 0xe03c9d3ccd2f),
    (0x1505545a8b88, 0x229cb898dba5d)]
private def nextForty : List (ℕ × ℕ) := [
    (0x1015111c04d13, 0x3109fca37ef92),
    (0x1401140f0d5b1, 0x5194a04da605),
    (0x4414413370f, 0x29d1220defc8e),
    (0x1101145dcb7e0, 0x1b419acb325b4),
    (0x5150002ccbd1, 0x3816360658671),
    (0x1505515fcb8a4, 0x2f55e21915d65),
    (0x1150000da3d78, 0x7ca4960405e9),
    (0x5554157fdb0, 0x23d6fbcb30cf1),
    (0x1011511842a29, 0xc44568c4c318),
    (0x1401110f584c, 0x25df3381dd64c),
    (0x1041444d7b9b6, 0x18c585610bd46),
    (0x5000517d766e, 0x1806dab2f105a),
    (0x5014552d7d70, 0x36df6e36efd34),
    (0x1454455a6286f, 0x3ad86b6b96cef),
    (0x1514144e96271, 0x261dffddc2094),
    (0x1054011970609, 0x1a069ad804d29),
    (0x51141429a8e5, 0x1a13835c9a7d4),
    (0x51145078acd7, 0x1a9a0a71d94d7),
    (0x5104443cb586, 0x1142575ef3d33),
    (0x40545075160e, 0x3a9aa19fa7f2b),
    (0x1514544f93426, 0x58da1977c3),
    (0x4510407, 0x1a9ad8178f212),
    (0x51044428f187, 0x139959adbfe93),
    (0x41404535d8e9, 0x3389e38d971dc),
    (0x1410105e05938, 0x3b9a7764f08e8),
    (0x1510554ad4113, 0x1dc947c4de683),
    (0x5441512f0112, 0x2710f6c51a577),
    (0x1050015922726, 0xf9e45e25a593),
    (0x1555144fe78b, 0x2e8ab459bebde),
    (0x1155440df472c, 0x3dd92a86a1338),
    (0x1540011eec083, 0x29c9f463e2513),
    (0x1101115dca7d8, 0x78548a1a445d),
    (0x5515516bbf8, 0xc971596bfe29),
    (0x1415554f4766, 0x1210122d23887),
    (0x41104125f098, 0x2591aebf6ae0d),
    (0x1041050c6bfae, 0x3893641d1cddf),
    (0x1504515a9e1ba, 0x30c27d809c70f),
    (0x1404544f0ab93, 0x240960cee6016),
    (0x104401496c7ee, 0x3d8f7c58cd8da),
    (0x1540455ff82e6, 0x2)]

private def r10 : P := bits 0x229cb898dba5d

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem certificate (x : K) (hm : ev x obstruction = 0) :
    x^(2^50 : ℕ) = x ∧ x^(2^10 : ℕ) ≠ x := by
  have ten := chain_sound x obstruction X hm firstTen (by decide +kernel)
  have ex : ev x X = x := by simp [X,ev]
  rw [show lastR X firstTen = r10 by rfl, ex, show firstTen.length = 10 by rfl] at ten
  have forty := chain_sound x obstruction r10 hm nextForty (by decide +kernel)
  rw [show lastR r10 nextForty = X by decide, ex, show nextForty.length = 40 by rfl] at forty
  constructor
  · rw [ten, ← pow_mul] at forty
    exact forty.symm
  · intro bad
    have identity : trim (plus (times (bits 0x11c35ae2a44d3) obstruction)
      (times (bits 0x210656cfb2b46) (plus r10 X))) = one := by decide +kernel
    have he := congrArg (ev x) identity
    have eo : ev x one = 1 := by simp [one,ev]
    simp only [ev_trim,ev_plus,ev_times,ten,bad,ex,hm,CharTwo.add_self_eq_zero,
      mul_zero,eo] at he
    exact zero_ne_one he

/-- The five angular traces are constrained by the fifth Dickson polynomial.
For order 25, its value is a primitive fifth root plus its inverse. -/
private theorem angular {a b : K} (hab : a*b=1) (ha : a^25=1) (hn : a^5 ≠ 1) :
    let t := a+b
    (t^5+t^3+t)^2 + (t^5+t^3+t) + 1 = 0 := by
  dsimp only
  have five : (5 : K) = 1 := by
    rw [show (5 : K) = 2*(2:K)+1 by norm_num,CharTwo.two_eq_zero]; simp
  have hd : (a+b)^5+(a+b)^3+(a+b) = a^5+b^5 := calc
    _ = (a+b)^5 - 5*(a*b)*(a+b)^3 + 5*(a*b)^2*(a+b) := by
      rw [hab,five]; simp [CharTwo.sub_eq_add]
    _ = _ := by ring
  rw [hd,CharTwo.add_sq]
  let u := a^5
  let v := b^5
  have huv : u*v = 1 := by simp [u,v,← mul_pow,hab]
  have hu : u^5 = 1 := by simpa [u,← pow_mul] using ha
  have hsum : u^4+u^3+u^2+u+1 = 0 := by
    have hz : (u-1)*(u^4+u^3+u^2+u+1) = 0 := by linear_combination hu
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)
  have hne : u ≠ 0 := by intro h; simp [h] at huv
  change u^2+v^2+(u+v)+1 = 0
  apply mul_left_cancel₀ (pow_ne_zero 2 hne)
  linear_combination hsum + (u*v+1+u)*(huv)

omit [CharP K 2] in
/-- Fixed by two Frobenius powers implies fixed by their gcd power. -/
private theorem fixed_gcd {z : K} (hz : z ≠ 0) {h : ℕ}
    (hh : z^(2^h : ℕ)=z) (h50 : z^(2^50 : ℕ)=z) (hg : h.gcd 50 = 10) :
    z^(2^10 : ℕ) = z := by
  have pred (m : ℕ) (hm : z^(2^m : ℕ)=z) : orderOf z ∣ 2^m-1 := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply mul_right_cancel₀ hz
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow m 2 (by decide)), hm, one_mul]
  have hgcd := Nat.dvd_gcd (pred h hh) (pred 50 h50)
  rw [Nat.pow_sub_one_gcd_pow_sub_one,hg] at hgcd
  have he := orderOf_dvd_iff_pow_eq_one.mp hgcd
  rw [show (2^10 : ℕ) = (2^10-1)+1 by decide, pow_succ,he,one_mul]

/-- Uniform Ball–Vilar witness for the admissible exponents. -/
theorem no_roots [Fintype K] (h q d : ℕ) (hq : q = 2^h)
    (hpos : 0 < h) (hcard : Fintype.card K = q^2)
    (hgcd : h.gcd 50 = 10) (h25 : 25 ∣ q+1) (hd : 5*d = q+1)
    (e : K) (he : orderOf e = 25) (x : K) :
    1 + x^(q+1) + e*x^d + (e*x^d)^q ≠ 0 := by
  have hqpos : 0 < q := hq ▸ pow_pos (by decide) _
  have hqeven : q / 2 * 2 = q := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hq,pow_succ,Nat.mul_div_cancel _ (by decide)]
  have hdpos : 0 < d := by omega
  by_cases hx : x = 0
  · simp [hx,zero_pow hdpos.ne',zero_pow hqpos.ne']
  let N := x^(q+1)
  have hN : N^q=N := by
    have hh := FiniteField.pow_card x
    rw [hcard] at hh
    dsimp [N]
    rw [← pow_mul,show (q+1)*q=q^2+q by ring,pow_add,hh,pow_succ,mul_comm]
  let y := N^(q/2)
  have hy : y ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hx)
  have hyq : y^q = y := by dsimp [y]; rw [pow_right_comm,hN]
  have hy2 : y^2 = N := by dsimp [y]; rw [← pow_mul,hqeven,hN]
  have hyn : y^(q+1)=N := by rw [pow_succ,hyq,← pow_two,hy2]
  let v := (x/y)^d
  have hv : v^5=1 := by
    dsimp [v]
    rw [← pow_mul,Nat.mul_comm d,hd,div_pow,hyn]
    exact div_self (pow_ne_zero _ hx)
  let z := y^d
  have hz : z ≠ 0 := pow_ne_zero _ hy
  have hzq : z^q = z := by dsimp [z]; rw [pow_right_comm,hyq]
  have hz5 : z^5=N := by dsimp [z]; rw [← pow_mul,Nat.mul_comm d,hd,hyn]
  let a := e*v
  have ha5 : a^5=e^5 := by simp [a,mul_pow,hv]
  have ha : a^25=1 := by
    rw [show 25=5*5 by decide,pow_mul,ha5,← pow_mul]
    simpa [he] using pow_orderOf_eq_one e
  have hn : a^5≠1 := by
    intro h1
    have hh := orderOf_dvd_iff_pow_eq_one.mpr (ha5 ▸ h1)
    rw [he] at hh
    exact (by decide : ¬25 ∣ 5) hh
  have hab : a*a^q=1 := by
    obtain ⟨k,hk⟩ := h25
    rw [← pow_succ',hk,pow_mul,ha,one_pow]
  have hw : e*x^d=a*z := by
    dsimp [a,v,z]; rw [mul_assoc,← mul_pow,div_mul_cancel₀ _ hy]
  intro bad
  rw [hw,mul_pow,hzq] at bad
  have ht : z*(a+a^q)=z^5+1 := by
    rw [hz5,← CharTwo.add_eq_zero]
    change 1 + N + a*z + a^q*z = 0 at bad
    linear_combination bad
  obtain ⟨h50,h10⟩ := certificate z (obstruction_vanishes ht (angular hab ha hn))
  exact h10 (fixed_gcd hz (hq ▸ hzq) h50 hgcd)

/-- Cyclicity supplies an element of order 25. -/
theorem witness_exists [Fintype K] (h q d : ℕ) (hq : q = 2^h)
    (hpos : 0 < h) (hcard : Fintype.card K = q^2)
    (hgcd : h.gcd 50 = 10) (h25 : 25 ∣ q+1) (hd : 5*d = q+1) :
    ∃ e : K, orderOf e = 25 ∧ ∀ x : K, 1 + x^(q+1) + e*x^d + (e*x^d)^q ≠ 0 := by
  classical
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units,Nat.card_eq_fintype_card,hcard] at hg
  have hqpos : 1 ≤ q := hq ▸ Nat.one_le_pow _ _ (by decide)
  have hfactor : q^2-1=(q+1)*(q-1) := by
    obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    rw [hr,Nat.succ_sub_one]; change (r+1)^2-1=(r+1+1)*r
    rw [show (r+1)^2=(r+1+1)*r+1 by ring, Nat.add_sub_cancel]
  have hv : 25 ∣ orderOf g := hg ▸ hfactor ▸ dvd_mul_of_dvd_left h25 _
  have hne : orderOf g ≠ 0 := orderOf_pos g |>.ne'
  let e := g^(orderOf g / 25)
  have he : orderOf (e : K) = 25 := by
    rw [orderOf_units]; exact orderOf_pow_orderOf_div hne hv
  exact ⟨e,he,no_roots h q d hq hpos hcard hgcd h25 hd e he⟩

theorem ball_vilar_1024 :
    ∃ e : GaloisField 2 20, ∀ x : GaloisField 2 20,
      1 + x^1025 + e*x^205 + (e*x^205)^1024 ≠ 0 := by
  classical
  letI := Fintype.ofFinite (GaloisField 2 20)
  obtain ⟨e,_,hw⟩ := witness_exists (K := GaloisField 2 20) 10 1024 205
    (by decide) (by decide)
    (by rw [← Nat.card_eq_fintype_card,GaloisField.card 2 20 (by decide)]; decide)
    (by decide) (by decide) (by decide)
  exact ⟨e,hw⟩

/-- Four residue classes of even exponents, starting at 10, 30, 70 and 90.
The degree lies in exactly the range allowed by the full-length GRS criterion. -/
theorem ball_vilar_family (k r : ℕ) (hr : r = 10 ∨ r = 30 ∨ r = 70 ∨ r = 90) :
    let h := 100*k+r
    let q := 2^h
    let d := (q+1)/5
    1 ≤ d ∧ d ≤ q-1 ∧ ∃ e : GaloisField 2 (2*h), orderOf e = 25 ∧
      ∀ x : GaloisField 2 (2*h), 1 + x^(q+1) + e*x^d + (e*x^d)^q ≠ 0 := by
  dsimp only
  let h := 100*k+r
  let q := 2^h
  have hp : 0 < h := by dsimp [h]; omega
  have hg : h.gcd 50 = 10 := by
    rw [show h = r+50*(2*k) by dsimp [h]; ring, Nat.gcd_add_mul_left_left]
    rcases hr with h | h | h | h <;> subst r <;> decide
  have h25 : 25 ∣ q+1 := by
    have per : 2^100 ≡ 1 [MOD 25] := by decide
    have res : 2^r+1 ≡ 0 [MOD 25] := by
      rcases hr with h | h | h | h <;> subst r <;> decide
    apply Nat.modEq_zero_iff_dvd.mp
    dsimp [q,h]
    rw [pow_add,pow_mul]
    exact (((per.pow k).mul_right (2^r)).add_right 1).trans (by simpa using res)
  have hd := Nat.mul_div_cancel' ((by decide : 5 ∣ 25).trans h25)
  have hqpos : 0 < q := pow_pos (by decide) _
  let K := GaloisField 2 (2*h)
  have hdeg : 2*h ≠ 0 := by omega
  letI : NeZero (2*h) := ⟨hdeg⟩
  letI := Fintype.ofFinite K
  have hc : Fintype.card K=q^2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2*h) hdeg]
    dsimp [q]; rw [Nat.mul_comm 2 h,pow_mul]
  exact ⟨by change 1 ≤ (q+1)/5; omega, by change (q+1)/5 ≤ q-1; omega,
    witness_exists h q ((q+1)/5) rfl hp hc hg h25 hd⟩

end Qmds.Order25
