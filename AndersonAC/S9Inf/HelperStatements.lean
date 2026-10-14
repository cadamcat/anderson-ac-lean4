import AndersonAC.S9.Blueprint

/-! Frozen helper contracts for WP12 part B. They assert no proofs. -/

noncomputable section

open MeasureTheory Filter OAI.Anderson
open scoped Topology

namespace AndersonAC.SolS9Inf

def latticeDistance {d : ℕ} (x y : Site d) : ℕ := ∑ j, Int.natAbs (x j - y j)

def shortestPathCount {d : ℕ} (x y : Site d) : ℕ :=
  (latticeDistance x y).factorial / ∏ j, (Int.natAbs (x j - y j)).factorial

/-- Exact type of the owned `S9.shortest_path_coefficient`, with
definitionally identical local distance, path count and basis vector. -/
def ShortestPathCoefficientStatement : Prop :=
  ∀ {d : ℕ} (coupling : ℝ) (ω : Configuration d) (x y : Site d),
    (∀ n : ℕ, n < latticeDistance x y →
      ((hamiltonian coupling ω ^ n) (AndersonAC.Blueprint.delta y)) x = 0) ∧
    ((hamiltonian coupling ω ^ latticeDistance x y) (AndersonAC.Blueprint.delta y)) x =
      (-1 : ℂ) ^ latticeDistance x y * (shortestPathCount x y : ℂ) ∧
    0 < shortestPathCount x y

/-- Continuity in positive height reduces finite-boundary events to
countable tests, including the positivity/zero/nonzero events used in
Fubini and the rank-one mismatch argument. -/
def BoundaryEventMeasurabilityStatement : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (f : Ω → ℝ → ℂ),
    (∀ η : ℝ, 0 < η → Measurable (fun ω => f ω η)) →
    (∀ ω, ContinuousOn (f ω) (Set.Ioi (0 : ℝ))) →
    MeasurableSet {ω | ∃ w : ℂ, Tendsto (f ω) (𝓝[>] 0) (𝓝 w)} ∧
    MeasurableSet {ω | ∃ w : ℂ, Tendsto (f ω) (𝓝[>] 0) (𝓝 w) ∧ 0 < w.im} ∧
    MeasurableSet {ω | ∃ w : ℂ, Tendsto (f ω) (𝓝[>] 0) (𝓝 w) ∧ w.im = 0} ∧
    MeasurableSet {ω | ∃ w : ℂ, Tendsto (f ω) (𝓝[>] 0) (𝓝 w) ∧ w ≠ 0}

/-- Bounded pointwise potential variation is continuous in the strong
operator topology on ℓ². This supplies the configuration measurability
needed for the actual Green entries, without assuming norm continuity. -/
def PotentialStrongContinuityStatement : Prop :=
  ∀ {d : ℕ} (v : StateSpace d),
    Continuous (fun ω : Configuration d => potentialOperator ω v)

end AndersonAC.SolS9Inf
