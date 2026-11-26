import Shannon.Geometry
import Mathlib.Tactic.Sat.FromLRAT

/-! An LRAT certificate produces an ordinary Lean proof of the empty clause.
The clauses below are all satisfied by any packing of the prescribed shadows. -/
namespace Shannon.Seven

open Sat

/-- Keep mathlib's proof of the empty clause, before propositional reification. -/
elab "checked_lrat " cnf:term:max lrat:term:max : term <= target => do
  let read (stx : Lean.Syntax) := unsafe Lean.Elab.Term.evalTerm String (Lean.mkConst ``String) stx
  let (_, _, _, proof) ← Mathlib.Tactic.Sat.fromLRATAux (← read cnf) (← read lrat)
    (← Lean.Elab.Term.mkAuxName `shannonLrat)
  -- The kernel compares the DIMACS formula with the independently defined encoding.
  return Lean.mkConst (← Lean.Meta.mkAuxLemma [] target proof)

private def turn (x z : Letter) : Letter := BitVec.ofNat 3 ((x.toNat + 7 - z.toNat) % 7)

private theorem turn_valid : ∀ x z : Letter, (turn x z).toNat < 7 := by decide +kernel
private theorem turn_self : ∀ z : Letter, turn z z = 0 := by decide +kernel
private theorem turn_separates : ∀ x y z : Letter,
    (x != 7 && y != 7 && !near x y) = true → near (turn x z) (turn y z) = false := by
  decide +kernel

private def variableId (v b : Nat) := 7 * v + b
private def palette (v : Nat) : Clause := (List.range 7).map fun b => .pos (variableId v b)
private def forbidden (i j b d : Nat) : Clause := [.neg (variableId i b), .neg (variableId j d)]
private def edgeClauses (e : Edge) : Fmla := (List.range 7).flatMap fun b =>
  ((List.range 7).filter fun d => near (.ofNat 3 b) (.ofNat 3 d)).map fun d =>
    forbidden e.1 e.2 b d

private def anchor (v : Nat) : Clause := [Literal.pos (variableId v 0)]

def encoding (n : Nat) (edges : List Edge) : Fmla :=
  ((List.range n).map palette ++ edges.flatMap edgeClauses) ++ [anchor (n-1)]

private def assignment (colors : Nat → Letter) : Valuation :=
  fun t => colors (t / 7) = BitVec.ofNat 3 (t % 7)

private theorem assignment_at {colors : Nat → Letter} {v b : Nat} (hb : b < 7) :
    assignment colors (variableId v b) ↔ colors v = BitVec.ofNat 3 b := by
  unfold assignment variableId
  have h₁ : (7*v+b)/7 = v := by omega
  have h₂ : (7*v+b)%7 = b := by omega
  rw [h₁,h₂]

private theorem clause_of_literal {v : Valuation} {l : Literal} {cl : List Literal}
    (mem : l ∈ cl) (h : ¬v.neg l) : v.satisfies cl := by
  induction cl with
  | nil => cases mem
  | cons a rest ih =>
    intro ha
    rcases List.mem_cons.mp mem with e | hr
    · subst a
      exact (h ha).elim
    · exact ih hr

private theorem encoding_model (n : Nat) (edges : List Edge) (f : Nat → Letter)
    (valid : ∀ i, (f i).toNat < 7) (root : f (n-1) = 0)
    (sep : ∀ e ∈ edges, near (f e.1) (f e.2) = false) :
    (assignment f).satisfies_fmla (encoding n edges) := by
  constructor
  intro cl hcl
  simp only [encoding, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_singleton] at hcl
  rcases hcl with (⟨v,_,rfl⟩ | ⟨e,he,hm⟩) | rfl
  · let b := (f v).toNat
    apply clause_of_literal (l := .pos (variableId v b))
    · exact List.mem_map.mpr ⟨b, List.mem_range.mpr (valid v), rfl⟩
    · intro hn
      apply hn
      exact (assignment_at (valid v)).2 (by simp)
  · simp only [edgeClauses,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range] at hm
    obtain ⟨b,hb,d,⟨hd,hadj⟩,rfl⟩ := hm
    intro hi hj
    have eqi := (assignment_at hb).1 hi
    have eqj := (assignment_at hd).1 hj
    rw [←eqi,←eqj,sep e he] at hadj
    contradiction
  · intro hn
    exact hn ((assignment_at (by decide : 0 < 7)).2 root)

def originalEdges (ids : List Nat) (edges : List Edge) : List Edge :=
  edges.map fun e => (ids.getD e.1 367, ids.getD e.2 367)

theorem excluded_by_formula {data axis extra : Nat} (ids : List Nat) (edges : List Edge)
    (cert : (originalEdges ids edges).all (edgeOK data axis extra) = true)
    (unsat : (encoding ids.length edges).proof []) (c : Nat → Letter) :
    ¬Packing data axis extra c := by
  intro pack
  let g := fun i => c (ids.getD i 367)
  let z := g (ids.length-1)
  let f := fun i => turn (g i) z
  apply unsat (assignment f)
  apply encoding_model ids.length edges f (fun i => turn_valid (g i) z) (turn_self z)
  intro e he
  apply turn_separates
  apply List.all_eq_true.mp (constraints pack _ cert) (ids.getD e.1 367, ids.getD e.2 367)
  exact List.mem_map.mpr ⟨e,he,rfl⟩

end Shannon.Seven
