import AndersonAC.AgentS6.Location
import AndersonAC.AgentS6.HeatDrift
import AndersonAC.S6.Range
import AndersonAC.S6.Ridge

/-! Every pivot of a stopped trial lies within `ℓ/2` of the core
(06-clearing.tex:772–784 and 1060–1063, equation `clearing-proposed-location`), by induction over
heats: range localization (Lemma 6.2, with the §2 Ward input) on the collapsed geometry,
leverage ≤ projection diagonal, the metric comparison, and `S6.pivot_location`. -/

noncomputable section
open scoped BigOperators Topology Matrix
open Filter Set MeasureTheory

namespace AndersonAC.AgentS6

open AndersonAC.S6

section Reindex

variable {R B B' : Type*} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]
  [Fintype B'] [DecidableEq B']

theorem matrixRange_reindex (C : Matrix R B ℂ) (e : B' ≃ B) :
    matrixRange (C.submatrix id e) = matrixRange C := by
  set P : Matrix B B' ℂ := (1 : Matrix B B ℂ).submatrix id e
  set Q : Matrix B' B ℂ := (1 : Matrix B' B' ℂ).submatrix id e.symm
  have hCP : C.submatrix id e = C * P := by
    ext i b; simp [P, Matrix.mul_apply, Matrix.one_apply]
  have hPQ : P * Q = 1 := by
    ext a b
    simp only [P, Q, Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    rw [Finset.sum_eq_single (e.symm b)]
    · simp [eq_comm]
    · intro x _ hx
      simp [hx]
    · simp
  have hC : C = C * P * Q := by rw [Matrix.mul_assoc, hPQ, Matrix.mul_one]
  apply le_antisymm
  · rw [hCP]
    unfold matrixRange
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    exact LinearMap.range_comp_le_range _ _
  · conv_lhs => rw [hC]
    rw [hCP]
    unfold matrixRange
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same (A := C * P)]
    exact LinearMap.range_comp_le_range _ _

theorem projectionWeight_reindex (C : Matrix R B ℂ) (e : B' ≃ B) (i : R) :
    projectionWeight (C.submatrix id e) i = projectionWeight C i := by
  have key : ∀ K1 K2 : Submodule ℂ (EuclideanSpace ℂ R), K1 = K2 →
      ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).symm K1.starProjection i i).re =
        ((Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ)).symm K2.starProjection i i).re := by
    rintro _ _ rfl; rfl
  exact key _ _ (matrixRange_reindex C e)

theorem exteriorGeometry_reindex {d : ℕ} {ρ : R → ℝ} {H : Matrix R R ℂ} {C : Matrix R B ℂ}
    {t : ℝ} {r : R → ℂ} (e : B' ≃ B) (h : ExteriorGeometry d ρ H C t r) :
    ExteriorGeometry d ρ H (C.submatrix id e) t r :=
  ⟨h.radius_nonneg, h.decomposition, by rw [matrixRange_reindex]; exact h.exterior_source⟩

end Reindex

theorem distanceToCore_metric {ι : Type*} [Fintype ι] (dist D : ι → ι → ℝ) (core : Finset ι)
    (s : ℝ) (hs : 0 ≤ s) (h : ∀ i j, dist i j / 2 - s ≤ D i j) (i : ι) :
    distanceToCore dist core i / 2 - s ≤ distanceToCore D core i := by
  unfold distanceToCore
  split_ifs with hc
  · refine Finset.le_inf' hc _ fun b hb => ?_
    have := Finset.inf'_le (dist i) hb
    linarith [h i b]
  · linarith

universe u

/-- All running pivots are located (for small `t`, uniformly). -/
theorem trial_pivots_located (hWard : AndersonAC.Blueprint.WardInput) (d : ℕ) (c K Cloc : ℝ)
    (hc : 0 < c) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
      (core : Finset (Fin n)) (t : ℝ) (r : Ω → Fin n → ℂ) (g0 : Ω → Matrix (Fin n) (Fin n) ℂ)
      (order : Fin n ≃ Fin (Fintype.card (Fin n))) (q : StoppedTrial (Ω := Ω) core t r g0 order)
      (dist : Fin n → Fin n → ℝ) (collapsed : ℕ → Ω → Fin n → Fin n → ℝ) (ell : ℝ),
      0 < t → t < t0 → (∀ ω, BroadBounds c K (r ω)) →
      TrialLocalInput q μ d c K Cloc dist collapsed ell →
      ∀ k ω, k < q.stop ω → distanceToCore dist core (q.pivot k ω) < ell / 2 := by
  by_cases hcK : c ≤ K
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro Ω _ μ n core t r g0 order q dist collapsed ell _ _ hb _ k ω _
    exfalso
    obtain ⟨-, hi⟩ := hb ω
    obtain ⟨-, h1, h2⟩ := hi (q.pivot k ω)
    exact hcK (h1.trans h2)
  obtain ⟨a, L, ha, hL, hloc⟩ := range_localization hWard d c K hc hcK
  have hL2 : 0 < L ^ 2 := by positivity
  refine ⟨min (min (1 / 64) (2 * (a / 1024) / L ^ 2)) 1, by positivity, ?_⟩
  intro Ω _ μ n core t r g0 order q dist collapsed ell ht htT hb hin
  have ht1 : t ≤ 1 := (lt_of_lt_of_le htT (min_le_right _ _)).le
  have htp : t < min (1 / 64) (2 * (a / 1024) / L ^ 2) := lt_of_lt_of_le htT (min_le_left _ _)
  have hs : 0 ≤ t ^ (-(103 / 100 : ℝ)) := Real.rpow_nonneg ht.le _
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ω hk
  have hprior : ∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2 :=
    fun j hj => ih j hj ω (by omega)
  obtain ⟨H, hgeo⟩ := hin.range_geometry k ω hk.le hprior
  set e : Fin (Fintype.card {b // b ∈ core}) ≃ {b // b ∈ core} := (Fintype.equivFin _).symm
  have hgeo' := exteriorGeometry_reindex e hgeo
  obtain ⟨-, hdecay⟩ := hloc (Fintype.card {b // b ∈ core}) n t (r ω) _ H _ ht ht1 (hb ω) hgeo'
  set C := trialCross t (r ω) (q.state k ω) with hC
  set m := trialWeights t (r ω) (q.state k ω) (q.ridge k ω) with hmdef
  have hτ := q.running_ridge k ω hk
  have hmetric := distanceToCore_metric dist (collapsed k ω) core _ hs
    (hin.metric k ω hk.le hprior)
  have hm : ∀ i, m i ≤ L ^ 2 * Real.exp (-2 * a * t *
      max (distanceToCore dist core i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) := by
    intro i
    have h1 : m i ≤ projectionWeight C i := ((ridge_calculus C _ hτ).2.2.2.2.1 i).2
    have h2 := hdecay i
    rw [projectionWeight_reindex] at h2
    have h3 : max (distanceToCore dist core i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0 ≤
        max (distanceToCore (collapsed k ω) core i - 1) 0 :=
      max_le_max (by linarith [hmetric i]) le_rfl
    have h4 : Real.exp (-2 * a * t * max (distanceToCore (collapsed k ω) core i - 1) 0) ≤
        Real.exp (-2 * a * t *
          max (distanceToCore dist core i / 2 - t ^ (-(103 / 100 : ℝ)) - 1) 0) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ 2 * a * t := by positivity
      nlinarith
    calc m i ≤ projectionWeight C i := h1
      _ ≤ _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 hL2.le
  have hx : 2 * leverageScale t ≤ m (q.pivot k ω) := by
    rw [hmdef, q.pivot_max k ω hk]
    exact (q.running_cap k ω hk).1
  exact pivot_location_at ha hL2 ht htp m (distanceToCore dist core) ell hin.ell_lower hm _ hx

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.trial_pivots_located
