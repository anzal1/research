import Qutrit.Basic

namespace Qutrit

open Module Submodule

private def restrictSites (s : Finset (Fin 12)) : Word 12 →ₗ[F] (s → Site) :=
  LinearMap.pi fun i => LinearMap.proj i.val

private theorem vanishes {s : Finset (Fin 12)} {w : Word 12} :
    w ∈ (LinearMap.ker (restrictSites s)) ↔ ∀ i ∈ s, w i = 0 := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i,hi⟩
  · intro h
    exact funext fun i => h i i.property

/-- Pick three erased sites that eliminate at least three independent
degrees of freedom from a four-dimensional radical. -/
private theorem choose_sites (R : Submodule F (Word 12)) (hr : finrank F R = 4) :
    ∃ s : Finset (Fin 12), s.card = 3 ∧ finrank F ↥(R ⊓ (LinearMap.ker (restrictSites s))) ≤ 1 := by
  classical
  let E (s : Finset (Fin 12)) := R ⊓ (LinearMap.ker (restrictSites s))
  have hstep (t : ℕ) (ht : t ≤ 3) :
      ∃ s : Finset (Fin 12), s.card = t ∧ finrank F (E s) ≤ 4-t := by
    induction t with
    | zero =>
      exact ⟨∅,rfl,(finrank_mono (show E ∅ ≤ R from inf_le_left)).trans hr.le⟩
    | succ t ih =>
      obtain ⟨s,hs,hd⟩ := ih (by omega)
      have pick : ∃ i, i ∉ s ∧ (E s ≠ ⊥ → ∃ w ∈ E s, w i ≠ 0) := by
        by_cases hz : E s = ⊥
        · obtain ⟨i,hi⟩ : ∃ i, i ∉ s := by
            by_contra! h
            have he : s = Finset.univ := Finset.eq_univ_of_forall h
            simp [he] at hs
            omega
          exact ⟨i,hi,fun h => (h hz).elim⟩
        · obtain ⟨w,hw,hn⟩ := exists_mem_ne_zero_of_ne_bot hz
          obtain ⟨i,hi⟩ : ∃ i, w i ≠ 0 := by
            by_contra! h
            exact hn (funext h)
          exact ⟨i,fun h => hi (vanishes.mp hw.2 i h),fun _ => ⟨w,hw,hi⟩⟩
      obtain ⟨i,hi,hw⟩ := pick
      have hle : E (insert i s) ≤ E s := by
        intro w h
        exact ⟨h.1,vanishes.mpr fun j hj => vanishes.mp h.2 j (Finset.mem_insert_of_mem hj)⟩
      refine ⟨insert i s, by simp [hi,hs], ?_⟩
      by_cases hz : E s = ⊥
      · rw [show E (insert i s) = ⊥ from le_bot_iff.mp (hz ▸ hle), finrank_bot]
        exact Nat.zero_le _
      · obtain ⟨w,hmem,hne⟩ := hw hz
        have hlt : E (insert i s) < E s := lt_of_le_of_ne hle fun he => by
          have hnew : w ∈ E (insert i s) := he ▸ hmem
          exact hne (vanishes.mp hnew.2 i (Finset.mem_insert_self ..))
        have := finrank_lt_finrank_of_lt hlt
        omega
  exact hstep 3 (by decide)

private theorem light_of_vanishing {s : Finset (Fin 12)} (hs : s.card = 3)
    {w : Word 12} (hw : w ∈ (LinearMap.ker (restrictSites s))) : weight w ≤ 9 := by
  classical
  let support := Finset.univ.filter fun i => w i ≠ 0
  have hsub : support ⊆ Finset.univ \ s := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h =>
      (Finset.mem_filter.mp hi).2 (vanishes.mp hw i h)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hs] at hcard
  have he : weight w = support.card := by
    simpa only [weight, occupied, support, ite_not, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun i => w i ≠ 0) Finset.univ)
  omega

/-- At this entanglement cost any additive normalizer has a logical word
supported on at most nine sites, including when the code is degenerate. -/
theorem distance_upper {N : Submodule F (Word 12)} {d : ℕ}
    (h : HasParameters 12 2 d 6 N) : d ≤ 9 := by
  classical
  obtain ⟨hN,hR,hmin⟩ := h
  obtain ⟨s,hs,hsmall⟩ := choose_sites (radical N) (by omega)
  let f := (restrictSites s).comp N.subtype
  have hcap := (LinearMap.range f).finrank_le
  have hd : finrank F (s → Site) = 6 := by simp [Module.finrank_pi_fintype, Site, Module.finrank_prod, hs]
  change finrank F (LinearMap.range f) ≤ finrank F (s → Site) at hcap
  rw [hd] at hcap
  have hrank := f.finrank_range_add_finrank_ker
  have he : (LinearMap.ker f).map N.subtype = N ⊓ (LinearMap.ker (restrictSites s)) := by
    ext w
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,ha⟩
    · intro hw
      exact ⟨⟨w,hw.1⟩,hw.2,rfl⟩
  have hdim := finrank_map_subtype_eq N (LinearMap.ker f)
  rw [he] at hdim
  have hn : ¬ N ⊓ (LinearMap.ker (restrictSites s)) ≤ radical N ⊓ (LinearMap.ker (restrictSites s)) := by
    intro hh
    have := finrank_mono hh
    omega
  obtain ⟨w,hw,hout⟩ := SetLike.not_le_iff_exists.mp hn
  have hnr : w ∉ radical N := fun h => hout ⟨h,hw.2⟩
  exact (hmin.2 ⟨w,hw.1,hnr,rfl⟩).trans (light_of_vanishing hs hw.2)

end Qutrit
