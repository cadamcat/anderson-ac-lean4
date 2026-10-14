import AndersonAC.S78.Definitions

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78
open AndersonAC.S78

/-- Nested active sets carry every retained site back to the initial endpoint. -/
theorem active_initial_of_active {d m k : ℕ} {t b : ℝ}
    {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r) :
    ∀ (a : Fin (k + 1)) (i : Torus d m),
      i ∈ (I.state a).active → i ∈ (I.state 0).active := by
  intro a
  induction a using Fin.induction with
  | zero =>
      intro i hi
      exact hi
  | succ a ih =>
      intro i hi
      exact ih i (I.nested a hi)

/-- On coordinates retained through a prefix, the normalized inverse change is
the sum of the survivor increments. -/
theorem normalizedInverse_telescopes_active {d m k : ℕ} {t b : ℝ}
    {r : Torus d m → ℂ} (I : AssemblyInput d m k t b r) :
    ∀ (a : Fin (k + 1)) (i j : Torus d m),
      i ∈ (I.state a).active → j ∈ (I.state a).active →
      normalizedInverse (I.state a) t i j =
        normalizedInverse (I.state 0) t i j +
          ∑ q ∈ (Finset.univ.filter (fun q : Fin k => q.val < a.val)),
            survivorDifference (I.state q.castSucc) (I.state q.succ) t i j := by
  classical
  intro a
  induction a using Fin.induction with
  | zero =>
      intro i j hi hj
      simp
  | succ a ih =>
      intro i j hi hj
      have hiPrev : i ∈ (I.state a.castSucc).active := I.nested a hi
      have hjPrev : j ∈ (I.state a.castSucc).active := I.nested a hj
      have hprev := ih i j hiPrev hjPrev
      have hfilter :
          Finset.univ.filter (fun q : Fin k => q.val < a.succ.val) =
            insert a (Finset.univ.filter (fun q : Fin k => q.val < a.castSucc.val)) := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        simp only [Fin.val_succ, Fin.val_castSucc]
        constructor
        · intro h
          by_cases hqa : q.val = a.val
          · left
            exact Fin.ext hqa
          · right
            omega
        · intro h
          rcases h with h | h
          · subst q
            simp
          · omega
      have haNot : a ∉ Finset.univ.filter (fun q : Fin k => q.val < a.castSucc.val) := by
        simp
      have hdelta :
          survivorDifference (I.state a.castSucc) (I.state a.succ) t i j =
            normalizedInverse (I.state a.succ) t i j -
              normalizedInverse (I.state a.castSucc) t i j := by
        simp [survivorDifference, hi, hj]
      calc
        normalizedInverse (I.state a.succ) t i j =
            normalizedInverse (I.state a.castSucc) t i j +
              survivorDifference (I.state a.castSucc) (I.state a.succ) t i j := by
                rw [hdelta]
                ring
        _ = (normalizedInverse (I.state 0) t i j +
              ∑ q ∈ Finset.univ.filter (fun q : Fin k => q.val < a.castSucc.val),
                survivorDifference (I.state q.castSucc) (I.state q.succ) t i j) +
              survivorDifference (I.state a.castSucc) (I.state a.succ) t i j := by
                rw [hprev]
        _ = normalizedInverse (I.state 0) t i j +
              (∑ q ∈ Finset.univ.filter (fun q : Fin k => q.val < a.castSucc.val),
                survivorDifference (I.state q.castSucc) (I.state q.succ) t i j +
                survivorDifference (I.state a.castSucc) (I.state a.succ) t i j) := by ring
        _ = normalizedInverse (I.state 0) t i j +
              ∑ q ∈ Finset.univ.filter (fun q : Fin k => q.val < a.succ.val),
                survivorDifference (I.state q.castSucc) (I.state q.succ) t i j := by
                rw [hfilter, Finset.sum_insert haNot]
                ring

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.normalizedInverse_telescopes_active
#print axioms AndersonAC.SolS78.active_initial_of_active
