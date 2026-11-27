import Qmds.BinaryCertificate

/-! A polynomial in Z with coefficients in F₂[T]/(m). Arithmetic is verified
at arbitrary field elements t,z satisfying the two supplied equations. -/
namespace Qmds.RayCertificate
open BinaryCertificate
abbrev B := List P
variable {K : Type*} [Field K] [CharP K 2]

def reduce (m : P) : P → P
  | [] => []
  | b :: p =>
    let a := trim (b :: reduce m p)
    if a.length < m.length then a else trim (plus a m)

theorem reduce_sound (t : K) (m p : P) (hm : ev t m = 0) :
    ev t (reduce m p) = ev t p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    simp only [reduce]
    split <;> simp only [ev_trim, ev_plus, hm, add_zero, ev, ih]

def mult (m a b : P) : P := if a.isEmpty || b.isEmpty then [] else reduce m (times a b)

theorem mult_sound (t : K) (m a b : P) (hm : ev t m = 0) :
    ev t (mult m a b) = ev t a * ev t b := by
  cases a <;> cases b <;> simp [mult, ev, reduce_sound t _ _ hm, ev_times]

def val (t z : K) : B → K
  | [] => 0
  | a :: p => ev t a + z * val t z p

def add : B → B → B
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => trim (plus a b) :: add p q

theorem add_sound (t z : K) (p q : B) : val t z (add p q) = val t z p + val t z q := by
  induction p generalizing q with
  | nil => simp [add,val]
  | cons a p ih =>
    cases q with
    | nil => simp [add,val]
    | cons b q => simp only [add,val,ev_trim,ev_plus,ih]; ring

def norm : B → B
  | [] => []
  | a :: p => let r := norm p; if a.isEmpty && r.isEmpty then [] else a :: r

theorem norm_sound (t z : K) (p : B) : val t z (norm p) = val t z p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [norm]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      obtain ⟨ha,hr⟩ := h
      have aa : a = [] := List.isEmpty_iff.mp ha
      have rr : norm p = [] := List.isEmpty_iff.mp hr
      rw [rr] at ih
      simp [aa, ←ih,val,ev]
    · simp only [val,ih]

def scale (m a : P) (p : B) := p.map (mult m a)

theorem scale_sound (t z : K) (m a : P) (p : B) (hm : ev t m = 0) :
    val t z (scale m a p) = ev t a * val t z p := by
  induction p with
  | nil => simp [scale,val]
  | cons b p ih => simp only [scale,List.map_cons,val,mult_sound t _ _ _ hm] at *; rw [ih]; ring

def product (m : P) : B → B → B
  | [], _ => []
  | a :: p, q => add (scale m a q) ([] :: product m p q)

theorem product_sound (t z : K) (m : P) (p q : B) (hm : ev t m = 0) :
    val t z (product m p q) = val t z p * val t z q := by
  induction p with
  | nil => simp [product,val]
  | cons a p ih => simp only [product, add_sound, scale_sound t z _ _ _ hm,val,ev,ih]; ring

def square (m : P) : B → B
  | [] => []
  | a :: p => mult m a a :: [] :: square m p

theorem square_sound (t z : K) (m : P) (p : B) (hm : ev t m = 0) :
    val t z (square m p) = (val t z p)^2 := by
  induction p with
  | nil => simp [square,val]
  | cons a p ih => simp only [square,val,ev,mult_sound t _ _ _ hm,ih,CharTwo.add_sq]; ring

def power (m : P) (a : B) : Nat → B
  | 0 => [one]
  | n+1 => norm (product m a (power m a n))

theorem power_sound (t z : K) (m : P) (a : B) (n : Nat) (hm : ev t m = 0) :
    val t z (power m a n) = (val t z a)^n := by
  induction n with
  | zero => simp [power,val,one,ev]
  | succ n ih => rw [power,norm_sound,product_sound _ _ _ _ _ hm,ih,pow_succ,mul_comm]

def compose (m a : P) : P → P
  | [] => []
  | b :: p => trim (plus (if b then one else []) (mult m a (compose m a p)))

theorem compose_sound (t : K) (m a p : P) (hm : ev t m = 0) :
    ev t (compose m a p) = ev (ev t a) p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases b <;> simp [compose,ev_trim,ev_plus,mult_sound _ _ _ _ hm,ih,one,ev]

def decode (p : List Nat) : B := p.map bits
def step (m : P) (f a b c : B) : Bool :=
  norm (square m a) == norm (add (product m b f) c)

theorem step_sound (t z : K) {m : P} {f a b c : B} (hm : ev t m = 0)
    (hf : val t z f = 0) (h : step m f a b c = true) : val t z c = (val t z a)^2 := by
  have he := congrArg (val t z) (beq_iff_eq.mp h : norm (square m a) = norm (add (product m b f) c))
  simpa only [norm_sound,square_sound t z _ _ hm,add_sound,product_sound t z _ _ _ hm,hf,
    mul_zero,zero_add] using he.symm

def chain (m : P) (f a : B) : List (List Nat × List Nat) → Bool
  | [] => true
  | (b,c) :: rest => step m f a (decode b) (decode c) && chain m f (decode c) rest

def last (a : B) : List (List Nat × List Nat) → B
  | [] => a
  | (_,c) :: rest => last (decode c) rest

theorem chain_sound (t z : K) {m : P} {f : B} (hm : ev t m = 0)
    (hf : val t z f = 0) (a : B) (steps : List (List Nat × List Nat))
    (h : chain m f a steps = true) : val t z (last a steps) = (val t z a)^(2^steps.length : Nat) := by
  induction steps generalizing a with
  | nil => simp [last]
  | cons pair rest ih =>
    obtain ⟨b,c⟩ := pair
    simp only [chain,Bool.and_eq_true] at h
    obtain ⟨hs,hr⟩ := h
    rw [last, ih _ hr,step_sound t z hm hf hs,← pow_mul,List.length_cons,pow_succ,Nat.mul_comm 2]
end Qmds.RayCertificate
