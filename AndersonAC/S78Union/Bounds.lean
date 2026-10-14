import AndersonAC.S78.Definitions

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

namespace AndersonAC.SolS78Union

theorem finite_union_bound {Ω ι : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (event : ι → Set Ω) (p : ℝ)
    (hp : ∀ i ∈ S, μ (event i) ≤ ENNReal.ofReal p) :
    μ (⋃ i ∈ S, event i) ≤ ENNReal.ofReal ((S.card : ℝ) * p) := by
  classical
  by_cases hp0 : 0 ≤ p
  · calc
      μ (⋃ i ∈ S, event i) ≤ ∑ i ∈ S, μ (event i) :=
        measure_biUnion_finset_le S event
      _ ≤ ∑ i ∈ S, ENNReal.ofReal p := by
        exact Finset.sum_le_sum fun i hi => hp i hi
      _ = ENNReal.ofReal ((S.card : ℝ) * p) := by
        simp [Finset.sum_const, ENNReal.ofReal_mul]
  · have hpneg : p < 0 := lt_of_not_ge hp0
    have hevent_zero : ∀ i ∈ S, μ (event i) = 0 := by
      intro i hi
      have hle : μ (event i) ≤ 0 := by
        simpa [ENNReal.ofReal_eq_zero.mpr (le_of_lt hpneg)] using hp i hi
      exact le_antisymm hle bot_le
    calc
      μ (⋃ i ∈ S, event i) ≤ ∑ i ∈ S, μ (event i) :=
        measure_biUnion_finset_le S event
      _ = 0 := by
        rw [Finset.sum_eq_zero]
        intro i hi
        exact hevent_zero i hi
      _ = ENNReal.ofReal ((S.card : ℝ) * p) := by
        rw [ENNReal.ofReal_eq_zero.mpr
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_lt hpneg))]

end AndersonAC.SolS78Union

namespace AndersonAC.SolS78

open AndersonAC.S78

theorem cutoff_probability_bound_proof {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d m J : ℕ)
    (pending : Torus d m → Set Ω) (q : ℝ)
    (hp : ∀ x, μ (pending x) ≤ ENNReal.ofReal (birthBound q J)) :
    μ (⋃ x, pending x) ≤ ENNReal.ofReal ((4 : ℝ) ^ (20 * d * m) * birthBound q J) := by
  classical
  have hpBound : ∀ x ∈ (Finset.univ : Finset (Torus d m)),
      μ (pending x) ≤ ENNReal.ofReal (birthBound q J) := by
    intro x _
    exact hp x
  have hfinite := AndersonAC.SolS78Union.finite_union_bound μ
    (Finset.univ : Finset (Torus d m)) pending (birthBound q J) hpBound
  have hcard : (Fintype.card (Torus d m) : ℝ) =
      (4 : ℝ) ^ (20 * d * m) := by
    rw [OAI.Anderson.torus_card, OAI.Anderson.sideLength]
    rw [Nat.cast_pow, Nat.cast_pow]
    rw [← pow_mul]
    congr 1
    ring
  have hsum : μ (⋃ x, pending x) ≤
      ENNReal.ofReal ((Fintype.card (Torus d m) : ℝ) * birthBound q J) := by
    simpa using hfinite
  calc
    μ (⋃ x, pending x) ≤
        ENNReal.ofReal ((Fintype.card (Torus d m) : ℝ) * birthBound q J) := hsum
    _ = ENNReal.ofReal ((4 : ℝ) ^ (20 * d * m) * birthBound q J) := by
      rw [hcard]

theorem late_failure_bound_proof {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Finset ℕ) (event : ℕ → Set Ω) (p : ℝ)
    (hp : ∀ n ∈ S, μ (event n) ≤ ENNReal.ofReal p) :
    μ (⋃ n ∈ S, event n) ≤ ENNReal.ofReal ((S.card : ℝ) * p) := by
  exact AndersonAC.SolS78Union.finite_union_bound μ S event p hp

end AndersonAC.SolS78
