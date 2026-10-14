import AndersonAC.S78Metric.Range

open scoped BigOperators
set_option autoImplicit false
namespace AndersonAC.SolS78

/-- Consecutive intervals in a strictly ordered list of positions have disjoint
edge indices, all contained in the original path's edge range. -/
theorem sum_ordered_intervals_le (n len : ℕ) (hn : 0 < n)
    (p : Fin n ↪o ℕ) (hp : ∀ j, p j < len) (f : ℕ → ℕ) :
    (∑ j : Fin (n - 1), ∑ i ∈ Finset.Ico
      (p ⟨j.val, by omega⟩) (p ⟨j.val + 1, by omega⟩), f i) ≤
      ∑ i ∈ Finset.range (len - 1), f i := by
  let J (j : Fin (n - 1)) := Finset.Ico
    (p ⟨j.val, by omega⟩) (p ⟨j.val + 1, by omega⟩)
  have hd : ∀ a ∈ (Finset.univ : Finset (Fin (n - 1))),
      ∀ b ∈ Finset.univ, a ≠ b → Disjoint (J a) (J b) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro i hia hib
    have ha := Finset.mem_Ico.mp hia
    have hb := Finset.mem_Ico.mp hib
    rcases lt_or_gt_of_ne hab with h | h
    · have hab' : (⟨a.val + 1, by omega⟩ : Fin n) ≤ ⟨b.val, by omega⟩ := by
        simp only [Fin.le_iff_val_le_val]
        have := Fin.lt_iff_val_lt_val.mp h
        omega
      have := p.monotone hab'
      omega
    · have hba' : (⟨b.val + 1, by omega⟩ : Fin n) ≤ ⟨a.val, by omega⟩ := by
        simp only [Fin.le_iff_val_le_val]
        have := Fin.lt_iff_val_lt_val.mp h
        omega
      have := p.monotone hba'
      omega
  have hsub : Finset.univ.biUnion J ⊆ Finset.range (len - 1) := by
    intro i hi
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    have hiend := (Finset.mem_Ico.mp hj).2
    have hjlen := hp ⟨j.val + 1, by omega⟩
    apply Finset.mem_range.mpr
    omega
  change (∑ j : Fin (n - 1), ∑ i ∈ J j, f i) ≤ _
  rw [← Finset.sum_biUnion hd]
  exact Finset.sum_le_sum_of_subset hsub

end AndersonAC.SolS78
