import Mathlib.Data.List.Basic

/-! A four-coordinate shadow is an integer in base seven. Words keep their
order in the published appendix, including repeated shadows. -/
namespace Shannon.Seven

abbrev Letter := BitVec 3

/-- On letters 0 through 6, confusability means equality or cyclic adjacency. -/
def near (a b : Letter) : Bool :=
  a == b || a + 1 == b || b + 1 == a || (a == 0 && b == 6) || (b == 0 && a == 6)

def digit (v i : Nat) : Letter := BitVec.ofNat 3 (v / 7^i % 7)

def close4 (x y : Nat) : Bool :=
  near (digit x 0) (digit y 0) && near (digit x 1) (digit y 1) &&
  near (digit x 2) (digit y 2) && near (digit x 3) (digit y 3)

/-- Drop coordinate a, counting from the left in a five-digit word. -/
def project (a w : Nat) : Nat :=
  let place := 7^(4-a)
  w / (7*place)*place + w%place

/-- Packed list of published words, using fifteen bits per base-seven word. -/
def word (data i : Nat) := (data >>> (15*i)) % 32768

def point (data a p i : Nat) := if i=367 then p else project a (word data i)

/-- Color the 368 four-coordinate projections by their missing cycle letter.
The first 367 projections are prescribed. The last projection is p. -/
structure Packing (data a p : Nat) (c : Nat → Letter) : Prop where
  valid : ∀ i, i < 368 → c i ≠ 7
  separate : ∀ i j, i < j → j < 368 →
    close4 (point data a p i) (point data a p j) = true → near (c i) (c j) = false

abbrev Edge := Nat × Nat

def edgeOK (data a p : Nat) (e : Edge) : Bool :=
  decide (e.1 < e.2) && decide (e.2 < 368) &&
    close4 (point data a p e.1) (point data a p e.2)

def labelsOK (c : Nat → Letter) (e : Edge) : Bool :=
  c e.1 != 7 && c e.2 != 7 && !near (c e.1) (c e.2)

theorem constraints {data a p : Nat} {c : Nat → Letter} (h : Packing data a p c)
    (edges : List Edge) (cert : edges.all (edgeOK data a p) = true) :
    edges.all (labelsOK c) = true := by
  rw [List.all_eq_true] at cert ⊢
  intro e he
  have good := cert e he
  simp only [edgeOK,Bool.and_eq_true,decide_eq_true_eq] at good
  obtain ⟨⟨hlt,hstop⟩,hc⟩ := good
  simp [labelsOK,h.separate _ _ hlt hstop hc]
  exact ⟨h.valid _ (Nat.lt_trans hlt hstop),h.valid _ hstop⟩

def clique (i j k : Nat) : List Edge := [(i,j),(i,k),(j,k),(i,367),(j,367),(k,367)]

theorem clique_excludes {data a p : Nat} {c : Nat → Letter} {i j k : Nat}
    (cert : (clique i j k).all (edgeOK data a p) = true) : ¬Packing data a p c := by
  intro h
  have bounds := constraints h _ cert
  simp only [clique,List.all_cons,List.all_nil, Bool.and_eq_true, and_true,
    labelsOK,near] at bounds
  have impossible : ∀ x y z w : Letter, ¬(
      (((x != 7 && y != 7) && !near x y) = true) ∧
      (((x != 7 && z != 7) && !near x z) = true) ∧
      (((y != 7 && z != 7) && !near y z) = true) ∧
      (((x != 7 && w != 7) && !near x w) = true) ∧
      (((y != 7 && w != 7) && !near y w) = true) ∧
      (((z != 7 && w != 7) && !near z w) = true)) := by decide +kernel
  apply impossible (c i) (c j) (c k) (c 367)
  simpa only [Bool.and_eq_true,near] using bounds

end Shannon.Seven
