import AndersonAC.S78.AssemblyForms
import AndersonAC.S78.AssemblyEstimates
import AndersonAC.S78.MatrixReset
import AndersonAC.S78Extract.TorusGeometry
import AndersonAC.S78SpatialForm.SpatialForm

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

theorem assembly_graph_connected {d m k : ℕ} {t b : ℝ} {r : Torus d m → ℂ}
    (I : AssemblyInput d m k t b r) : (nnGraph d m).Connected := by
  have ht := I.positive.1
  have ht1 := I.positive.2.1
  have hν : 0 ≤ nu d := by unfold nu delta; positivity
  have hDs : 1 ≤ I.Ds := by
    have hpow : 1 ≤ t ^ (-8 - nu d) := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith : -8 - nu d ≤ 0))
    exact hpow.trans I.scaleRadius.1
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have he := I.embedded
    simp only [hm0, OAI.Anderson.sideLength, Nat.mul_zero, pow_zero, Nat.cast_one] at he
    linarith
  exact nnGraph_connected_of_pos hm

/-- The exact committed assembly conclusion after its two analytic estimates
and finite Schur-minimum theorem have been supplied. The spatial-form input
and torus connectivity are proved dependencies, not additional assumptions. -/
theorem committed_assembly_of_estimates (hfin : FiniteFormInput)
    (hmat : AssemblyMatrixBounds) (henergy : AssemblyEnergyBounds)
    (d : ℕ) (hd : 3 ≤ d) (C c P : ℝ) (hC : 1 ≤ C) (hc : 0 < c) (hP : 0 ≤ P) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧ ∀ (m k : ℕ) (t b : ℝ) (r : Torus d m → ℂ)
      (I : AssemblyInput d m k t b r), I.C = C → I.c = c → I.P = P → t < t₀ →
      ∀ a : Fin (k + 1),
      matrixNorm (squareKernel (normalizedInverse (I.state a) t)) ≤
        matrixNorm (squareKernel (normalizedInverse (I.state 0) t)) + t ^ (0.10 * delta) ∧
      (∀ i ∈ (I.state a).active, ‖(I.state a).g i i - r i‖ ≤ C' * t ^ (0.42 * delta - (d : ℝ) * nu d)) ∧
      (∀ i, (rowFour (normalizedInverse (I.state a) t) i) ^ (1 / 4 : ℝ) ≤
        (0.7 ^ (1 / 4 : ℝ) + C' * t ^ (0.0225 * delta - (d : ℝ) * nu d)) * t ^ ((1 + delta) / 4) ∧
        rowFour (normalizedInverse (I.state a) t) i < 0.8 * t ^ (1 + delta)) ∧
      constantKernel (I.state a).active (endpointEnergy (I.state a) r t) ∧
      (∀ f, |∑ q : Fin k with q.val < a.val, operationEnergyError I q f| ≤
        t ^ (0.10 * delta) * endpointEnergy (I.state 0) r t f) ∧
      (∀ y, neutral (I.state a).active y →
        (1 + t ^ (0.10 * delta))⁻¹ * inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) r t) y ≤
          inverseEnergy (I.state a).active (endpointEnergy (I.state a) r t) y ∧
        inverseEnergy (I.state a).active (endpointEnergy (I.state a) r t) y ≤
          (1 - t ^ (0.10 * delta))⁻¹ * inverseEnergy (I.state 0).active (endpointEnergy (I.state 0) r t) y) := by
  obtain ⟨C', tM, hC', htM, hM⟩ := hmat d hd C c P hC hc hP
  obtain ⟨tE, htE, hE⟩ := henergy d hd C c P hC hc hP
  obtain ⟨tR, htR, hR⟩ := reset_radius_small (0.10 * delta) (1 / 2)
    (by norm_num [delta]) (by norm_num)
  refine ⟨C', min tM (min tE tR), hC', lt_min htM (lt_min htE htR), ?_⟩
  intro m k t b r I hIC hIc hIP hsmall a
  have htM' : t < tM := hsmall.trans_le (min_le_left _ _)
  have htE' : t < tE := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htR' : t < tR := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hε : t ^ (0.10 * delta) < 1 :=
    (hR t I.positive.1 htR').trans_lt (by norm_num)
  have herrors : ∀ (q : Fin (k + 1)) (f : Torus d m → ℝ),
      |assemblyError I q f| ≤ t ^ (0.10 * delta) * endpointEnergy (I.state 0) r t f :=
    hE m k t b r I hIC hIc hIP htE'
  have hforms := assembly_forms_of_error I spatialFormInput_proof hfin
    (assembly_graph_connected I) (t ^ (0.10 * delta)) (Real.rpow_nonneg I.positive.1.le _) hε herrors
  have hmatrix := hM m k t b r I hIC hIc hIP htM' a
  exact ⟨hmatrix.1, hmatrix.2.1, hmatrix.2.2, (hforms a).1, herrors a, (hforms a).2.2⟩

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.assembly_graph_connected
#print axioms AndersonAC.SolS78.committed_assembly_of_estimates
