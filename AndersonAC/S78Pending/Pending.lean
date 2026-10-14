import AndersonAC.S78Pending.Probability
import AndersonAC.S78Extract.Extract
import AndersonAC.S78WRec.Final

open scoped BigOperators ENNReal
open MeasureTheory
open AndersonAC.S78
set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

/-- The pending-site estimate follows by covering with the full deterministic
witness family, bounding its partition sum, and closing the scalar recursion. -/
theorem pending_site_bound_proof (d : ℕ) (hd : 3 ≤ d) (c C : ℝ)
    (hc : 0 < c) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ (m n₀ : ℕ) (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (H : PendingHistory d m n₀ Ω), N ≤ n₀ → H.C = C →
      (∀ j x, MeasurableSet (H.pending j x)) → (∀ a, MeasurableSet (H.birth a)) →
      (∀ S : Finset (BirthLabel (Torus d m)),
        μ (⋂ a ∈ S, H.birth a) ≤ ENNReal.ofReal (witnessWeight c S)) →
      ∀ j x, n₀ ≤ j → clearingScheduled j m →
        μ (H.pending j x) ≤ ENNReal.ofReal (birthBound (historyExponent d c) j) := by
  exact pending_site_bound_from_helpers d hd c C hc hC
    (extract_witness_proof d hd C hC)
    (witness_support_proof d hd)
    (witness_recursion_proof d hd)

end AndersonAC.SolS78
