import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-! Binary polynomial arithmetic used only to verify public certificates.
Lists are little-endian; trailing zeros are discarded for comparison. -/
namespace Qmds.BinaryCertificate

abbrev P := List Bool

def plus : P → P → P
  | [], q => q
  | b :: p, [] => b :: p
  | b :: p, c :: q => (b.xor c) :: plus p q

def times : P → P → P
  | [], _ => []
  | false :: p, q => false :: times p q
  | true :: p, q => plus q (false :: times p q)

def trim : P → P
  | [] => []
  | b :: p => let q := trim p; if !b && q.isEmpty then [] else b :: q

variable {K : Type*} [Field K] [CharP K 2]

def ev (x : K) : P → K
  | [] => 0
  | b :: p => (if b then 1 else 0) + x * ev x p

theorem ev_plus (x : K) (p q : P) : ev x (plus p q) = ev x p + ev x q := by
  induction p generalizing q with
  | nil => simp [plus,ev]
  | cons b p ih =>
    cases q with
    | nil => simp [plus,ev]
    | cons c q =>
      cases b <;> cases c <;> simp [plus,ev,ih] <;>
        (ring_nf <;> simp [CharTwo.two_eq_zero])

theorem ev_times (x : K) (p q : P) : ev x (times p q) = ev x p * ev x q := by
  induction p with
  | nil => simp [times,ev]
  | cons b p ih => cases b <;> simp [times,ev,ev_plus,ih] <;> ring

omit [CharP K 2] in
theorem ev_trim (x : K) (p : P) : ev x (trim p) = ev x p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases b <;> simp [trim,ev,ih]
    all_goals split <;> simp_all [ev, ← ih]

def sq (p : P) := times p p
def fifth (p : P) := times (sq (sq p)) p

@[simp] theorem ev_sq (x : K) (p : P) : ev x (sq p) = (ev x p)^2 := by
  simp [sq,ev_times,pow_two]
@[simp] theorem ev_fifth (x : K) (p : P) : ev x (fifth p) = (ev x p)^5 := by
  simp [fifth,ev_times]; ring

def X : P := [false,true]
def one : P := [true]

-- Clear the denominator in D₅((X⁵+1)/X)² + D₅((X⁵+1)/X) + 1.
def obstruction : P :=
  let m := plus (fifth X) one
  let d := plus (plus (fifth m) (times (times (sq m) m) (sq X))) (times m (sq (sq X)))
  plus (plus (sq d) (times d (fifth X))) (sq (fifth X))

theorem obstruction_vanishes {x t : K} (h : x*t = x^5+1)
    (ht : (t^5+t^3+t)^2 + (t^5+t^3+t) + 1 = 0) : ev x obstruction = 0 := by
  simp only [obstruction,ev_plus,ev_times,ev_sq,ev_fifth,X,one,ev,
    Bool.false_eq_true, if_false, if_true, mul_zero, add_zero, mul_one, zero_add]
  rw [← h]
  linear_combination x^10 * ht

-- A bounded decoder keeps reduction structural in the kernel.
def bitsAux : ℕ → ℕ → P
  | 0, _ => []
  | n+1, k => if k = 0 then [] else (k % 2 == 1) :: bitsAux n (k / 2)

def bits (n : ℕ) := bitsAux 64 n

/-- Every step witnesses r² = quotient * modulus + next in F₂[X]. -/
def chain (modulus r : P) : List (ℕ × ℕ) → Bool
  | [] => true
  | (q,s) :: rest =>
      trim (sq r) == trim (plus (times (bits q) modulus) (bits s)) &&
      chain modulus (bits s) rest

def lastR (r : P) : List (ℕ × ℕ) → P
  | [] => r
  | (_,s) :: rest => lastR (bits s) rest

theorem chain_sound (x : K) (modulus r : P) (hm : ev x modulus = 0)
    (steps : List (ℕ × ℕ)) (h : chain modulus r steps = true) :
    ev x (lastR r steps) = (ev x r) ^ (2^steps.length) := by
  induction steps generalizing r with
  | nil => simp [lastR]
  | cons pair rest ih =>
    rcases pair with ⟨q,s⟩
    simp only [chain,Bool.and_eq_true,beq_iff_eq] at h
    have he := congrArg (ev x) h.1
    simp only [ev_trim,ev_sq,ev_plus,ev_times,hm,mul_zero,zero_add] at he
    rw [lastR,ih _ h.2,← he,← pow_mul,List.length_cons,pow_succ,Nat.mul_comm 2]
end Qmds.BinaryCertificate
