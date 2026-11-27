import Qmds.Order29Data
import Qmds.FullLength

namespace Qmds.Order29
open BinaryCertificate RayCertificate Data
variable {K : Type*} [Field K] [CharP K 2]
set_option maxRecDepth 20000

private def shape : B :=
  let M := add (power modulus zvar 5) [one]
  let L := product modulus [scalar] zvar
  add (add (power modulus M 5) (product modulus (power modulus M 3) (power modulus L 2)))
    (add (product modulus M (power modulus L 4)) (product modulus [bits 0x2a] (power modulus L 5)))

private theorem shape_eq : norm shape = f := by decide +kernel

omit [CharP K 2] in
private theorem valZ (t z : K) : val t z zvar = z := by simp [zvar, one,val,ev]

private theorem radial_certificate (t z : K) (hm : ev t modulus = 0) (hf : val t z f = 0) :
    z^(2^70 : Nat)=z ∧ z^(2^14 : Nat)≠z := by
  have h1 := RayCertificate.chain_sound t z hm hf zvar rows0 check0
  change val t z r1 = (val t z zvar)^(2^7 : Nat) at h1
  rw [valZ] at h1
  have h2 := RayCertificate.chain_sound t z hm hf r1 rows1 check1
  change val t z r2 = (val t z r1)^(2^7 : Nat) at h2
  rw [h1, ← pow_mul] at h2
  change val t z r2 = z^(2^14 : Nat) at h2
  have h3 := RayCertificate.chain_sound t z hm hf r2 rows2 check2
  change val t z r3 = (val t z r2)^(2^7 : Nat) at h3
  rw [h2, ← pow_mul] at h3
  have h4 := RayCertificate.chain_sound t z hm hf r3 rows3 check3
  change val t z r4 = (val t z r3)^(2^7 : Nat) at h4
  rw [h3, ← pow_mul] at h4
  have h5 := RayCertificate.chain_sound t z hm hf r4 rows4 check4
  change val t z r5 = (val t z r4)^(2^7 : Nat) at h5
  rw [h4, ← pow_mul] at h5
  have h6 := RayCertificate.chain_sound t z hm hf r5 rows5 check5
  change val t z r6 = (val t z r5)^(2^7 : Nat) at h6
  rw [h5, ← pow_mul] at h6
  have h7 := RayCertificate.chain_sound t z hm hf r6 rows6 check6
  change val t z r7 = (val t z r6)^(2^7 : Nat) at h7
  rw [h6, ← pow_mul] at h7
  have h8 := RayCertificate.chain_sound t z hm hf r7 rows7 check7
  change val t z r8 = (val t z r7)^(2^7 : Nat) at h8
  rw [h7, ← pow_mul] at h8
  have h9 := RayCertificate.chain_sound t z hm hf r8 rows8 check8
  change val t z r9 = (val t z r8)^(2^7 : Nat) at h9
  rw [h8, ← pow_mul] at h9
  have h10 := RayCertificate.chain_sound t z hm hf r9 rows9 check9
  change val t z r10 = (val t z r9)^(2^7 : Nat) at h10
  rw [h9, ← pow_mul] at h10
  constructor
  · rw [show r10 = zvar by decide, valZ] at h10
    exact h10.symm
  · intro hz
    have he := congrArg (val t z) Data.unit
    rw [norm_sound, add_sound, product_sound _ _ _ _ _ hm, product_sound _ _ _ _ _ hm,
      add_sound, valZ, h2, hz, CharTwo.add_self_eq_zero, hf, mul_zero, mul_zero, add_zero] at he
    simp [val,one,ev] at he

private theorem dickson (a b : K) (hab : a*b=1) : (a+b)^5+(a+b)^3+(a+b) = a^5+b^5 := by
  have five : (5 : K) = 1 := by
    rw [show (5 : K) = 2*(2:K)+1 by norm_num,CharTwo.two_eq_zero]; simp
  calc
    _ = (a+b)^5 - 5*(a*b)*(a+b)^3 + 5*(a*b)^2*(a+b) := by rw [hab,five]; simp [CharTwo.sub_eq_add]
    _ = _ := by ring

private theorem trace_modulus (w : K) (ho : orderOf w=29) : ev (w+w^28) modulus = 0 := by
  let phi := bits 0x1fffffff
  let tracePoly := bits 0x10000002
  have hw : w^29=1 := by simpa [ho] using pow_orderOf_eq_one w
  have hn : w ≠ 1 := by intro he; simp [he] at ho
  have sum : (w-1)*ev w phi = w^29-1 := by
    change (w-1)*ev w (List.replicate 29 true) = w^29-1
    simp [ev,List.replicate]; ring
  have hp : ev w phi = 0 := (mul_eq_zero.mp (sum.trans (by rw [hw,sub_self]))).resolve_left (sub_ne_zero.mpr hn)
  have a : ev w tracePoly = w+w^28 := by
    change ev w (false :: true :: List.replicate 26 false ++ [true]) = w+w^28
    simp [ev,List.replicate]; ring
  have check : compose phi tracePoly modulus = [] := by decide +kernel
  rw [←a, ←compose_sound w phi tracePoly modulus hp, check]; rfl

private theorem equation (t z angle : K) (hm : ev t modulus = 0)
    (hz : (ev t scalar*z)*angle = z^5+1)
    (ha : angle^5+angle^3+angle = t^5+t^3+t) : val t z f = 0 := by
  have d : ev t (bits 0x2a) = t^5+t^3+t := by
    change ev t [false,true,false,true,false,true] = _; simp [ev]; ring
  rw [←shape_eq,norm_sound]
  simp only [shape,add_sound,power_sound _ _ _ _ _ hm,product_sound _ _ _ _ _ hm,valZ,d,val,
    ev,one,mul_zero, add_zero, if_true]
  have zero : angle^5+angle^3+angle+(t^5+t^3+t)=0 := by rw [ha,CharTwo.add_self_eq_zero]
  rw [←hz]
  linear_combination (ev t scalar*z)^5 * zero

private theorem fixed_ev {t : K} {q h : Nat} (hq : q=2^h) (ht : t^q=t) (p : P) :
    (ev t p)^q = ev t p := by
  induction p with
  | nil => simp [ev,hq]
  | cons b p ih =>
    have frob (x y : K) : (x+y)^q=x^q+y^q := by rw [hq,add_pow_char_pow]
    cases b <;> simp [ev,frob,mul_pow,ht,ih]

/-- A single angular orbit of order 29 suffices at every admissible exponent. -/
theorem no_roots [Fintype K] (h q d : Nat) (hq : q=2^h) (hpos : 0<h)
    (hc : Fintype.card K=q^2) (hg : h.gcd 70=14) (h29 : 29 ∣ q+1) (hd : 5*d=q+1)
    (w : K) (ho : orderOf w=29) (x : K) :
    let t := w+w^q
    let e := ev t scalar*w
    1+x^(q+1)+e*x^d+(e*x^d)^q ≠ 0 := by
  dsimp only
  have qpos : 0<q := hq ▸ pow_pos (by decide) _
  have evenQ : q/2*2=q := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hq,pow_succ,Nat.mul_div_cancel _ (by decide)]
  have wn : w ≠ 0 := by intro hh; simp [hh] at ho
  have hw : w^29=1 := by simpa [ho] using pow_orderOf_eq_one w
  have wu : w*w^q=1 := by
    obtain ⟨k,hk⟩ := h29
    rw [←pow_succ',hk,pow_mul,hw,one_pow]
  have w28 : w^q=w^28 := by apply mul_left_cancel₀ wn; rw [wu,←pow_succ']; exact hw.symm
  let t := w+w^q
  have tf : t^q=t := by
    have double : (w^q)^q=w := by rw [←pow_mul,←pow_two,←hc,FiniteField.pow_card]
    have fr (a b : K) : (a+b)^q=a^q+b^q := by rw [hq,add_pow_char_pow]
    dsimp [t]; rw [fr,double,add_comm]
  let l := ev t scalar
  have lf : l^q=l := fixed_ev hq tf _
  have hm : ev t modulus=0 := by simpa only [t,w28] using trace_modulus w ho
  by_cases hx : x=0
  · simp [hx,zero_pow (by omega : d ≠ 0),zero_pow qpos.ne']
  let N := x^(q+1)
  have hN : N^q=N := by
    dsimp [N]; rw [←pow_mul,show (q+1)*q=q^2+q by ring,pow_add,←hc,FiniteField.pow_card,pow_succ,mul_comm]
  let y := N^(q/2)
  have hy : y≠0 := pow_ne_zero _ (pow_ne_zero _ hx)
  have yf : y^q=y := by dsimp [y]; rw [pow_right_comm,hN]
  have yn : y^(q+1)=N := by rw [pow_succ,yf,←pow_two]; dsimp [y]; rw [←pow_mul,evenQ,hN]
  let v := (x/y)^d
  have v5 : v^5=1 := by
    dsimp [v]; rw [←pow_mul,Nat.mul_comm d,hd,div_pow,yn]; exact div_self (pow_ne_zero _ hx)
  let z := y^d
  have zf : z^q=z := by dsimp [z]; rw [pow_right_comm,yf]
  have z5 : z^5=N := by dsimp [z]; rw [←pow_mul,Nat.mul_comm d,hd,yn]
  let a := w*v
  have a5 : a^5=w^5 := by simp [a,mul_pow,v5]
  have au : a*a^q=1 := by
    have vu : v*v^q=1 := by rw [←pow_succ',←hd,pow_mul,v5,one_pow]
    calc
      a*a^q = (w*w^q)*(v*v^q) := by dsimp [a]; rw [mul_pow]; ring
      _ = 1 := by rw [wu,vu,mul_one]
  have ang := dickson a (a^q) au
  rw [pow_right_comm a q 5,a5,←pow_right_comm w q 5,←dickson w (w^q) wu] at ang
  have term : (l*w)*x^d = l*a*z := by
    have wr : w*x^d=a*z := by
      dsimp [a,v,z]; rw [mul_assoc,←mul_pow,div_mul_cancel₀ _ hy]
    calc
      (l*w)*x^d = l*(w*x^d) := mul_assoc _ _ _
      _ = l*(a*z) := congrArg (l*·) wr
      _ = l*a*z := (mul_assoc _ _ _).symm
  intro bad
  change 1+N+(l*w)*x^d+((l*w)*x^d)^q=0 at bad
  rw [term,mul_pow,mul_pow,lf,zf] at bad
  have relation : (l*z)*(a+a^q)=z^5+1 := by
    rw [z5,←CharTwo.add_eq_zero]; linear_combination bad
  obtain ⟨p70,p14⟩ := radial_certificate t z hm (equation t z _ hm relation ang)
  exact p14 (Order25.fixed_gcd (pow_ne_zero _ hy) (hq ▸ zf) p70 hg)

noncomputable local instance (n : Nat) : Fintype (GaloisField 2 n) := Fintype.ofFinite _

/-- Four even-exponent classes outside the previous order-25 construction. -/
theorem full_length_family (k r : Nat) (hr : r=14 ∨ r=42 ∨ r=98 ∨ r=126) :
    let h := 140*k+r
    FullLength.HasOrthogonalGRS (GaloisField 2 (2*h)) (2^h) := by
  dsimp only
  let h := 140*k+r
  let q := 2^h
  let K := GaloisField 2 (2*h)
  have hp : 0<h := by dsimp [h]; omega
  have hc : Fintype.card K=q^2 := by
    rw [←Nat.card_eq_fintype_card,GaloisField.card 2 (2*h) (by omega)]
    dsimp [q]; rw [Nat.mul_comm 2 h,pow_mul]
  have hg : h.gcd 70=14 := by
    rw [show h=r+70*(2*k) by dsimp [h]; ring, Nat.gcd_add_mul_left_left]
    rcases hr with h|h|h|h <;> subst r <;> decide
  have h145 : 145 ∣ q+1 := by
    have per : 2^140 ≡ 1 [MOD 145] := by decide
    have res : 2^r+1 ≡ 0 [MOD 145] := by rcases hr with h|h|h|h <;> subst r <;> decide
    apply Nat.modEq_zero_iff_dvd.mp
    dsimp [q,h]; rw [pow_add,pow_mul]
    exact (((per.pow k).mul_right (2^r)).add_right 1).trans (by simpa using res)
  have h29 := (by decide : 29 ∣ 145).trans h145
  have hd := Nat.mul_div_cancel' ((by decide : 5 ∣ 145).trans h145)
  obtain ⟨w,ho⟩ := Order25.exists_order_on_circle (K:=K) rfl hc h29
  have qpos : 1≤q := Nat.one_le_pow h 2 (by decide)
  exact FullLength.grs_of_witness h q ((q+1)/5) rfl hp hc (by omega) _ (no_roots h q _ rfl hp hc hg h29 hd w ho)

theorem full_length_16384 : FullLength.HasOrthogonalGRS (GaloisField 2 28) 16384 :=
  full_length_family 0 14 (Or.inl rfl)
end Qmds.Order29
