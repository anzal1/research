import Qmds.Order25
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Finset.Option

/-! Extended generalized Reed–Solomon evaluation on the full projective line.
The point at infinity reads the top coefficient, with multiplier one. -/
namespace Qmds.FullLength

open Finset
open scoped BigOperators

variable {K : Type*} [Field K]

def row (q : ℕ) (v : K → K) (i : Fin (q-1)) : Option K → K
  | some x => v x * x^i.val
  | none => if i.val = q-2 then 1 else 0

def encode (q : ℕ) (v : K → K) (a : Fin (q-1) → K) (p : Option K) : K :=
  ∑ i, a i * row q v i p

/-- Any q−1 transmitted coordinates uniquely determine the message. This is
the MDS information-set property for the displayed GRS encoder. -/
def DeterminesMessage (q : ℕ) (v : K → K) : Prop :=
  ∀ (s : Finset (Option K)), s.card = q-1 → ∀ a b : Fin (q-1) → K,
    (∀ p ∈ s, encode q v a p = encode q v b p) → a=b

private theorem information_sets (q : ℕ) (hq : 2 ≤ q) (v : K → K) (hv : ∀ x, v x ≠ 0) :
    DeterminesMessage q v := by
  classical
  intro s hs a b agree
  let last : Fin (q-1) := ⟨q-2, by omega⟩
  have infinity (c : Fin (q-1) → K) : encode q v c none = c last := by
    unfold encode
    rw [sum_eq_single last]
    · simp [row,last]
    · intro i _ hin
      have hn : i.val ≠ q-2 := fun h => hin (Fin.ext h)
      simp [row,hn]
    · simp
  let P := Polynomial.ofFn (q-1) (a-b)
  have eval_eq (x : K) (c : Fin (q-1) → K) :
      encode q v c (some x) = v x*(Polynomial.ofFn (q-1) c).eval x := by
    rw [Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finset_sum,mul_sum]
    unfold encode
    apply sum_congr rfl; intro i _
    rw [Polynomial.eval_monomial,row]; ring
  have roots (x : K) (hx : x ∈ s.eraseNone) : P.eval x=0 := by
    have he := agree (some x) (mem_eraseNone.mp hx)
    rw [eval_eq,eval_eq] at he
    simp only [P,map_sub,Polynomial.eval_sub,sub_eq_zero]
    exact mul_left_cancel₀ (hv x) he
  by_contra hab
  have hn : P ≠ 0 := by
    intro hz
    have z : a-b=0 := Polynomial.injective_ofFn _ (hz.trans (Polynomial.ofFn_zero _).symm)
    exact hab (sub_eq_zero.mp z)
  have hg : P.natDegree < q-1 := Polynomial.ofFn_natDegree_lt (by omega) _
  apply hn (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P s.eraseNone roots ?_)
  by_cases hi : none ∈ s
  · have ha := agree none hi
    rw [infinity,infinity] at ha
    have hcoeff : P.coeff (q-2)=0 := by
      rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)]; exact sub_eq_zero.mpr ha
    have hlt : P.natDegree ≠ q-2 := by
      intro he
      exact (Polynomial.leadingCoeff_ne_zero.mpr hn) (he ▸ hcoeff : P.coeff P.natDegree=0)
    rw [card_eraseNone_of_mem hi,hs]; omega
  · rw [card_eraseNone_of_not_mem hi,hs]; exact hg

/-- Full-length, dimension-(q−1) GRS evaluation with nonzero column
multipliers, with Hermitian orthogonality for every pair of messages. -/
def HasOrthogonalGRS (K : Type*) [Field K] [Fintype K] (q : ℕ) : Prop :=
  ∃ v : K → K, (∀ x, v x ≠ 0) ∧ DeterminesMessage q v ∧ ∀ a b : Fin (q-1) → K,
    ∑ p : Option K, encode q v a p * (encode q v b p)^q = 0

variable [Fintype K] [CharP K 2]

omit [CharP K 2] in
private theorem sum_top : ∑ x : K, x^(Fintype.card K-1) = -1 := by
  classical
  have hp : Fintype.card K-1 ≠ 0 := by have := Fintype.one_lt_card (α := K); omega
  have f (x : K) : x^(Fintype.card K-1) = 1 - (if x=0 then 1 else 0) := by
    by_cases hx : x=0
    · simp [hx,zero_pow hp]
    · simp [hx,FiniteField.pow_card_sub_one_eq_one x hx]
  simp [f,sum_sub_distrib]

private theorem rows_to_messages (h q : ℕ) (hq : q=2^h) (v : K → K)
    (H : ∀ i j : Fin (q-1), ∑ p : Option K, row q v i p * (row q v j p)^q = 0)
    (a b : Fin (q-1) → K) :
    ∑ p : Option K, encode q v a p * (encode q v b p)^q = 0 := by
  have frob (f : Fin (q-1) → K) : (∑ i, f i)^q = ∑ i, (f i)^q := by
    simpa only [hq] using sum_pow_char_pow 2 h univ f
  calc
    _ = ∑ p : Option K, ∑ i, ∑ j, (a i*(b j)^q)*(row q v i p*(row q v j p)^q) := by
      apply sum_congr rfl; intro p _
      simp only [encode,frob,sum_mul,mul_sum,mul_pow]
      rw [sum_comm]
      exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))
    _ = ∑ i, ∑ j, (a i*(b j)^q)*(∑ p, row q v i p*(row q v j p)^q) := by
      rw [sum_comm]
      apply sum_congr rfl; intro i _
      rw [sum_comm]; simp only [mul_sum]
    _ = 0 := by simp [H]

/-- From a zero-free norm-plus-trace monomial to an actual Hermitian
self-orthogonal extended GRS code, including its coordinate at infinity. -/
theorem grs_of_witness (h q d : ℕ) (hq : q=2^h) (hpos : 0<h)
    (hc : Fintype.card K=q^2) (hd : d ≤ q-1) (e : K)
    (hw : ∀ x : K, 1+x^(q+1)+e*x^d+(e*x^d)^q ≠ 0) : HasOrthogonalGRS K q := by
  classical
  have htwo : 2 ≤ q := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hq,pow_succ]; have := Nat.one_le_pow k 2 (by decide); omega
  have hhalf : q/2*2=q := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hq,pow_succ,Nat.mul_div_cancel _ (by decide)]
  have doubleFrob (x : K) : (x^q)^q=x := by rw [← pow_mul,← pow_two,← hc,FiniteField.pow_card]
  have addFrob (a b : K) : (a+b)^q=a^q+b^q := by rw [hq,add_pow_char_pow]
  let W := fun x : K => 1+x^(q+1)+e*x^d+(e*x^d)^q
  let v := fun x : K => (W x)^(q/2)
  have base (x : K) : (W x)^q=W x := by
    simp only [W,addFrob,one_pow,pow_succ,mul_pow,doubleFrob]; ring
  have norm (x : K) : v x*(v x)^q=W x := by
    dsimp only [v]
    rw [pow_right_comm,base,← pow_two,← pow_mul,hhalf,base]
  have hv (x : K) : v x ≠ 0 := pow_ne_zero _ (hw x)
  refine ⟨v, hv, information_sets q htwo v hv, rows_to_messages h q hq v ?_⟩
  intro i j
  let m := i.val + q*j.val
  have it : i.val ≤ q-2 := by have := i.isLt; omega
  have jt : j.val ≤ q-2 := by have := j.isLt; omega
  have top : (q-2)+q*(q-2)+(q+1)=q^2-1 := by
    obtain ⟨l,hl⟩ := Nat.exists_eq_add_of_le htwo
    rw [hl]; simp only [Nat.add_sub_cancel_left]
    have : (2+l)^2=(l+(2+l)*l+(2+l+1))+1 := by ring
    omega
  have bound (a b : Fin (q-1)) : a.val+q*b.val+(q+1) ≤ q^2-1 := by
    have ha := a.isLt; have hb := b.isLt
    have := Nat.mul_le_mul_left q (by omega : b.val ≤ q-2)
    omega
  have low (a b : Fin (q-1)) : ∑ x : K, (e*x^d)*x^(a.val+q*b.val)=0 := by
    simp_rw [mul_assoc,← pow_add,← mul_sum]
    rw [FiniteField.sum_pow_lt_card_sub_one K _ (by rw [hc]; have := bound a b; omega),mul_zero]
  have high : ∑ x : K, (e*x^d)^q*x^m=0 := by
    have swap (x : K) : (x^(j.val+q*i.val))^q=x^m := by
      dsimp only [m]
      rw [pow_add,mul_pow,pow_right_comm x j.val q,pow_mul x q i.val,
        pow_right_comm (x^q) i.val q,doubleFrob,pow_add,pow_mul,mul_comm]
    calc
      _ = ∑ x : K, ((e*x^d)*x^(j.val+q*i.val))^q := by simp only [mul_pow,swap]
      _ = (∑ x : K, (e*x^d)*x^(j.val+q*i.val))^q := by
        have frob (f : K → K) : (∑ x, f x)^q=∑ x, (f x)^q := by rw [hq,sum_pow_char_pow]
        exact (frob _).symm
      _ = 0 := by rw [low,zero_pow (by omega : q ≠ 0)]
  have basic : ∑ x : K, x^m=0 :=
    FiniteField.sum_pow_lt_card_sub_one K _ (by rw [hc]; dsimp [m]; have := bound i j; omega)
  have aff : ∑ x : K, row q v i (some x)*(row q v j (some x))^q =
      ∑ x : K, x^(m+(q+1)) := by
    have term (x : K) : row q v i (some x)*(row q v j (some x))^q =
        x^m+x^(m+(q+1))+(e*x^d)*x^m+(e*x^d)^q*x^m := calc
      _ = (v x*(v x)^q)*x^m := by simp only [row,m,pow_add,pow_mul,mul_pow,pow_right_comm _ j.val q]; ring
      _ = _ := by rw [norm]; simp only [W,pow_add]; ring
    simp only [term,sum_add_distrib,basic,zero_add,high,add_zero]
    rw [low i j,add_zero]
  rw [Fintype.sum_option,aff]
  by_cases hi : i.val = q-2
  · by_cases hj : j.val = q-2
    · have he : m+(q+1)=Fintype.card K-1 := by simpa [m,hi,hj,hc] using top
      rw [he,sum_top]; simp [row,hi,hj]
    · have strict := Nat.mul_lt_mul_of_pos_left (by omega : j.val < q-2) (by omega : 0<q)
      rw [FiniteField.sum_pow_lt_card_sub_one K _ (by rw [hc]; dsimp [m]; omega)]
      simp [row,hj,zero_pow (by omega : q≠0)]
  · have := Nat.mul_le_mul_left q jt
    rw [FiniteField.sum_pow_lt_card_sub_one K _ (by rw [hc]; dsimp [m]; omega)]
    simp [row,hi]

noncomputable local instance (n : ℕ) : Fintype (GaloisField 2 n) := Fintype.ofFinite _

theorem full_length_family (k r : ℕ) (hr : r=10 ∨ r=30 ∨ r=70 ∨ r=90) :
    let h := 100*k+r
    HasOrthogonalGRS (GaloisField 2 (2*h)) (2^h) := by
  let h := 100*k+r
  have hp : 0<h := by dsimp [h]; omega
  obtain ⟨_,hd,e,_,hw⟩ := Order25.ball_vilar_family k r hr
  apply grs_of_witness h (2^h) _ rfl hp _ hd e hw
  rw [← Nat.card_eq_fintype_card,GaloisField.card 2 (2*h) (by omega),Nat.mul_comm 2 h,pow_mul]

theorem full_length_1024 : HasOrthogonalGRS (GaloisField 2 20) 1024 :=
  full_length_family 0 10 (Or.inl rfl)

end Qmds.FullLength
