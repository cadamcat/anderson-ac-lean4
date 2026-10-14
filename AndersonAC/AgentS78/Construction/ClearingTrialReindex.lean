import AndersonAC.AgentS78.Construction.ClearingTrialProof

/-!
# transport of a stopped trial along `ι ≃ Fin n`

Proposition 6.6 and `trial_pivots_located` are stated for trials indexed by `Fin n`; the
clearing trial is indexed by the active sites. `trialReindex_proof : TrialReindexStatement`
transports a `StoppedTrial` and its `TrialLocalInput` along an equivalence `e : ι ≃ Fin n`
(rows and core are relabelled; ridges, residuals, stop, outcome and history are unchanged).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78.TrialReindex

open AndersonAC.S6

/-! ## Matrix facts under relabelling -/

section MatrixFacts

variable {R R' B B' : Type*} [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']

theorem ridgeGram_submatrix (C : Matrix R B ℂ) (f : R' ≃ R) (g : B' ≃ B) (τ : ℝ) :
    ridgeGram (C.submatrix f g) τ = (ridgeGram C τ).submatrix g g := by
  ext a b
  simp only [ridgeGram, gram, Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, g.injective.eq_iff]
  congr 1
  exact Equiv.sum_comp f (fun r => star (C r (g a)) * C r (g b))

theorem ridgeProjection_submatrix (C : Matrix R B ℂ) (f : R' ≃ R) (g : B' ≃ B) (τ : ℝ) :
    ridgeProjection (C.submatrix f g) τ = (ridgeProjection C τ).submatrix f f := by
  unfold ridgeProjection
  rw [ridgeGram_submatrix, Matrix.inv_submatrix_equiv, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

theorem leverage_submatrix (C : Matrix R B ℂ) (f : R' ≃ R) (g : B' ≃ B) (τ : ℝ) (i : R') :
    leverage (C.submatrix f g) τ i = leverage C τ (f i) := by
  unfold leverage
  rw [ridgeProjection_submatrix]
  rfl

theorem maxWeight_comp (m : R → ℝ) (f : R' ≃ R) : maxWeight (fun i => m (f i)) = maxWeight m := by
  unfold maxWeight
  congr 1
  rw [← Finset.map_univ_equiv f, Finset.sup_map]
  rfl

theorem totalWeight_comp (m : R → ℝ) (f : R' ≃ R) :
    totalWeight (fun i => m (f i)) = totalWeight m := by
  unfold totalWeight
  exact Equiv.sum_comp f m

theorem maxWeight_leverage_submatrix (C : Matrix R B ℂ) (f : R' ≃ R) (g : B' ≃ B) (τ : ℝ) :
    maxWeight (leverage (C.submatrix f g) τ) = maxWeight (leverage C τ) := by
  have : leverage (C.submatrix f g) τ = fun i => leverage C τ (f i) :=
    funext (leverage_submatrix C f g τ)
  rw [this, maxWeight_comp]

theorem ridgeThreshold_submatrix (C : Matrix R B ℂ) (f : R' ≃ R) (g : B' ≃ B) (l : ℝ) :
    ridgeThreshold (C.submatrix f g) l = ridgeThreshold C l := by
  unfold ridgeThreshold
  simp_rw [maxWeight_leverage_submatrix]

theorem chooseRidge_submatrix (C : Matrix R B ℂ) (f : R' ≃ R) (g : B' ≃ B) (l τ : ℝ) :
    chooseRidge (C.submatrix f g) l τ = chooseRidge C l τ := by
  unfold chooseRidge
  rw [maxWeight_leverage_submatrix, ridgeThreshold_submatrix]

theorem rangeProjection_submatrix (C : Matrix R B ℂ) (f : R' ≃ R) (g : B' ≃ B) :
    rangeProjection (C.submatrix f g) = (rangeProjection C).submatrix f f := by
  have h1 : Tendsto (ridgeProjection (C.submatrix f g)) (𝓝[>] 0)
      (𝓝 (rangeProjection (C.submatrix f g))) := AndersonAC.S6.ridge_limit _
  have h2 : Tendsto (fun τ => (ridgeProjection C τ).submatrix f f) (𝓝[>] 0)
      (𝓝 ((rangeProjection C).submatrix f f)) :=
    ((continuous_id.matrix_submatrix f f).tendsto _).comp (AndersonAC.S6.ridge_limit C)
  have h3 : ridgeProjection (C.submatrix f g) = fun τ => (ridgeProjection C τ).submatrix f f :=
    funext (ridgeProjection_submatrix C f g)
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

theorem projectionWeight_submatrix (C : Matrix R B ℂ) (f : R' ≃ R) (g : B' ≃ B) (i : R') :
    projectionWeight (C.submatrix f g) i = projectionWeight C (f i) := by
  unfold projectionWeight
  rw [rangeProjection_submatrix]
  rfl

theorem scattering_submatrix (t : ℝ) (r : R → ℂ) (G : Matrix R R ℂ) (f : R' ≃ R) :
    scattering t (fun i => r (f i)) (G.submatrix f f) = (scattering t r G).submatrix f f := by
  ext a b
  simp [scattering, scatteringOfDamping, sqrtDamping, imagDamping, Matrix.one_apply,
    f.injective.eq_iff]

theorem dampedMatrix_submatrix (M : Matrix R R ℝ) (t : ℝ) (r : R → ℂ) (f : R' ≃ R) :
    dampedMatrix (M.submatrix f f) t (fun i => r (f i)) = (dampedMatrix M t r).submatrix f f := by
  ext a b
  simp [dampedMatrix, Matrix.diagonal_apply, f.injective.eq_iff]

theorem card_filter_comp (P : R → Prop) [DecidablePred P] (f : R' ≃ R) :
    (Finset.univ.filter (fun i => P (f i))).card = (Finset.univ.filter P).card := by
  rw [← Finset.card_map f.toEmbedding]
  congr 1
  ext x
  simp [Finset.mem_map_equiv]

theorem toEuclideanLin_apply' (X : Matrix R B ℂ) (w : EuclideanSpace ℂ B) (i : R) :
    (Matrix.toEuclideanLin X w) i = ∑ b, X i b * w b := by
  simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]

/-- Row relabelling of the exterior geometry. -/
theorem exteriorGeometry_rows {d : ℕ} {ρ : R → ℝ} {H : Matrix R R ℂ} {C : Matrix R B ℂ}
    {t : ℝ} {r : R → ℂ} (f : R' ≃ R) (h : ExteriorGeometry d ρ H C t r) :
    ExteriorGeometry d (fun i => ρ (f i)) (H.submatrix f f) (C.submatrix f id) t
      (fun i => r (f i)) := by
  obtain ⟨J, K, hJ, hK, hH, hJ1, hJdeg, hJρ, hKρ⟩ := h.decomposition
  refine ⟨fun i => h.radius_nonneg (f i), ⟨J.submatrix f f, K.submatrix f f, hJ.submatrix f,
    hK.submatrix f, ?_, fun i j => hJ1 (f i) (f j), fun i => ?_, fun i j hij => hJρ _ _ hij,
    fun i j hij => hKρ _ _ hij⟩, ?_⟩
  · rw [hH, ← dampedMatrix_submatrix]
    rfl
  · calc _ = ((Finset.univ.filter fun j => J (f i) j ≠ 0).card : ℝ) := by
          rw [← card_filter_comp (fun j => J (f i) j ≠ 0) f]; rfl
      _ ≤ _ := hJdeg (f i)
  · intro w hw i hi
    obtain ⟨v, rfl⟩ := hw
    have hsrc := h.exterior_source (Matrix.toEuclideanLin C v) ⟨v, rfl⟩ (f i) hi
    have hD : (sqrtDamping (imagDamping (fun i => r (f i))))⁻¹ =
        ((sqrtDamping (imagDamping r))⁻¹).submatrix f f := by
      rw [← Matrix.inv_submatrix_equiv]
      congr 1
      ext a b
      simp [sqrtDamping, imagDamping, Matrix.diagonal_apply, f.injective.eq_iff]
    rw [hD, Matrix.submatrix_mul_equiv]
    simp only [toEuclideanLin_apply'] at hsrc ⊢
    rw [← hsrc]
    simp only [Matrix.submatrix_apply, id]
    exact Equiv.sum_comp f
      (fun j => (H * (sqrtDamping (imagDamping r))⁻¹) (f i) j * ∑ b, C j b * v b)

end MatrixFacts

/-! ## Relabelled trial states -/

section States

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)

/-- The subtype of a finset and of its image. -/
def sEquiv (s : Finset ι) : {i // i ∈ s} ≃ {i // i ∈ s.map e.toEmbedding} :=
  e.subtypeEquiv (fun a => by simp)

@[simp] theorem sEquiv_symm_val (s : Finset ι) (i : {i // i ∈ s.map e.toEmbedding}) :
    ((sEquiv e s).symm i).val = e.symm i.val := rfl

@[simp] theorem sEquiv_val (s : Finset ι) (i : {i // i ∈ s}) :
    ((sEquiv e s) i).val = e i.val := rfl

/-- A trial state with relabelled sites. -/
def mapState {core : Finset ι} (s : TrialState core) : TrialState (core.map e.toEmbedding) where
  active := s.active.map e.toEmbedding
  core_active := Finset.map_subset_map.mpr s.core_active
  M := s.M.submatrix (sEquiv e s.active).symm (sEquiv e s.active).symm
  symmetric := s.symmetric.submatrix _
  hatG := s.hatG.submatrix e.symm e.symm

variable {core : Finset ι}

@[simp] theorem mapState_active (s : TrialState core) :
    (mapState e s).active = s.active.map e.toEmbedding := rfl

@[simp] theorem mapState_hatG (s : TrialState core) :
    (mapState e s).hatG = s.hatG.submatrix e.symm e.symm := rfl

theorem trialInverse_map (t : ℝ) (r : ι → ℂ) (s : TrialState core) :
    trialInverse t (fun i => r (e.symm i)) (mapState e s) =
      (trialInverse t r s).submatrix (sEquiv e s.active).symm (sEquiv e s.active).symm := by
  unfold trialInverse activeInverse
  rw [← Matrix.inv_submatrix_equiv, ← dampedMatrix_submatrix]
  rfl

theorem trialCross_map (t : ℝ) (r : ι → ℂ) (s : TrialState core) :
    trialCross t (fun i => r (e.symm i)) (mapState e s) =
      (trialCross t r s).submatrix e.symm (sEquiv e core).symm := by
  ext i b
  simp only [Matrix.submatrix_apply]
  unfold trialCross
  dsimp only
  by_cases hi : e.symm i ∈ s.active
  · have hi' : i ∈ (mapState e s).active := by simpa [Finset.mem_map_equiv] using hi
    rw [dif_pos hi', dif_pos hi]
    by_cases hc : e.symm i ∈ core
    · have hc' : i ∈ core.map e.toEmbedding := by simpa [Finset.mem_map_equiv] using hc
      rw [if_pos hc', if_pos hc]
    · have hc' : i ∉ core.map e.toEmbedding := by simpa [Finset.mem_map_equiv] using hc
      rw [if_neg hc', if_neg hc, trialInverse_map]
      have := congrFun (congrFun (scattering_submatrix t (fun i : {i // i ∈ s.active} => r i)
        (trialInverse t r s) (sEquiv e s.active).symm) ⟨i, hi'⟩)
        ⟨b.val, (mapState e s).core_active b.property⟩
      exact this
  · have hi' : i ∉ (mapState e s).active := by simpa [Finset.mem_map_equiv] using hi
    rw [dif_neg hi', dif_neg hi]

theorem trialWeights_map (t : ℝ) (r : ι → ℂ) (s : TrialState core) (τ : ℝ) (i : Fin n) :
    trialWeights t (fun i => r (e.symm i)) (mapState e s) τ i = trialWeights t r s τ (e.symm i) := by
  unfold trialWeights
  rw [trialCross_map, leverage_submatrix]

theorem maxWeight_trialWeights_map (t : ℝ) (r : ι → ℂ) (s : TrialState core) (τ : ℝ) :
    maxWeight (trialWeights t (fun i => r (e.symm i)) (mapState e s) τ) =
      maxWeight (trialWeights t r s τ) := by
  unfold trialWeights
  rw [trialCross_map, maxWeight_leverage_submatrix]

theorem chooseRidge_map (t : ℝ) (r : ι → ℂ) (s : TrialState core) (l τ : ℝ) :
    chooseRidge (trialCross t (fun i => r (e.symm i)) (mapState e s)) l τ =
      chooseRidge (trialCross t r s) l τ := by
  rw [trialCross_map, chooseRidge_submatrix]

theorem projectionReady_map (t : ℝ) (r : ι → ℂ) (s : TrialState core) :
    projectionReady t (fun i => r (e.symm i)) (mapState e s) ↔ projectionReady t r s := by
  unfold projectionReady
  simp_rw [trialCross_map, projectionWeight_submatrix]
  exact ⟨fun h i => by simpa using h (e i), fun h i => h _⟩

theorem budgetsHold_map (t : ℝ) (g0 hg : Matrix ι ι ℂ) :
    BudgetsHold t (g0.submatrix e.symm e.symm) (hg.submatrix e.symm e.symm) ↔
      BudgetsHold t g0 hg := by
  have hsq : ∀ i, sqRow (scaledInverse t (hg.submatrix e.symm e.symm -
      g0.submatrix e.symm e.symm)) i = sqRow (scaledInverse t (hg - g0)) (e.symm i) := by
    intro i
    unfold sqRow scaledInverse
    exact Equiv.sum_comp e.symm (fun j => ‖((Real.sqrt t : ℂ) • (hg - g0)) (e.symm i) j‖ ^ 2)
  have hhs : hsSq (scaledInverse t (hg.submatrix e.symm e.symm - g0.submatrix e.symm e.symm)) =
      hsSq (scaledInverse t (hg - g0)) := by
    unfold hsSq
    simp_rw [hsq]
    exact Equiv.sum_comp e.symm _
  unfold BudgetsHold
  rw [hhs]
  simp_rw [hsq]
  refine and_congr ?_ (and_congr ?_ Iff.rfl)
  · simp only [Matrix.submatrix_apply]
    constructor
    · intro h i j; simpa using h (e i) (e j)
    · intro h i j; exact h _ _
  · constructor
    · intro h i; simpa using h (e i)
    · intro h i; exact h _

end States

section Heat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n) {core : Finset ι}

theorem heatTransition_map {t : ℝ} {r : ι → ℂ} {s s' : TrialState core} {x : ι} {ξ : ℝ}
    (h : HeatTransition t r s s' x ξ) :
    HeatTransition t (fun i => r (e.symm i)) (mapState e s) (mapState e s') (e x) ξ := by
  obtain ⟨hx, hxc, hact, hne, hM, hG⟩ := h
  have hx' : e x ∈ (mapState e s).active := by simpa using hx
  have hsx : (sEquiv e s.active).symm ⟨e x, hx'⟩ = ⟨x, hx⟩ := Subtype.ext (by simp)
  refine ⟨hx', by simpa using hxc, ?_, ?_, ?_, ?_⟩
  · simp [hact, Finset.map_erase]
  · show s.M ((sEquiv e s.active).symm ⟨e x, hx'⟩) ((sEquiv e s.active).symm ⟨e x, hx'⟩) + ξ ≠ 0
    rw [hsx]; exact hne
  · intro i j hi hj
    have hi0 : e.symm i.val ∈ s.active := by simpa [Finset.mem_map_equiv] using hi
    have hj0 : e.symm j.val ∈ s.active := by simpa [Finset.mem_map_equiv] using hj
    have key := hM ((sEquiv e s'.active).symm i) ((sEquiv e s'.active).symm j) hi0 hj0
    show s'.M ((sEquiv e s'.active).symm i) ((sEquiv e s'.active).symm j) =
      s.M ((sEquiv e s.active).symm ⟨i, hi⟩) ((sEquiv e s.active).symm ⟨j, hj⟩) -
        s.M ((sEquiv e s.active).symm ⟨i, hi⟩) ((sEquiv e s.active).symm ⟨e x, hx'⟩) *
          s.M ((sEquiv e s.active).symm ⟨e x, hx'⟩) ((sEquiv e s.active).symm ⟨j, hj⟩) /
        (s.M ((sEquiv e s.active).symm ⟨e x, hx'⟩) ((sEquiv e s.active).symm ⟨e x, hx'⟩) + ξ)
    rw [hsx, key]
    rfl
  · intro i j
    have key := hG (e.symm i) (e.symm j)
    simp only [mapState_hatG, Matrix.submatrix_apply]
    rw [key]
    congr 1
    by_cases hi : e.symm i ∈ s'.active
    · have hi' : i ∈ (mapState e s').active := by simpa [Finset.mem_map_equiv] using hi
      rw [dif_pos hi, dif_pos hi']
      by_cases hj : e.symm j ∈ s'.active
      · have hj' : j ∈ (mapState e s').active := by simpa [Finset.mem_map_equiv] using hj
        rw [dif_pos hj, dif_pos hj', trialInverse_map]
        rfl
      · have hj' : j ∉ (mapState e s').active := by simpa [Finset.mem_map_equiv] using hj
        rw [dif_neg hj, dif_neg hj']
    · have hi' : i ∉ (mapState e s').active := by simpa [Finset.mem_map_equiv] using hi
      rw [dif_neg hi, dif_neg hi']

end Heat

/-! ## The relabelled stopped trial -/

section Trial

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] {n : ℕ} (e : ι ≃ Fin n)

/-- The relabelled tie order. -/
def orderMap (order : ι ≃ Fin (Fintype.card ι)) : Fin n ≃ Fin (Fintype.card (Fin n)) :=
  e.symm.trans (order.trans (finCongr (Fintype.card_congr e)))

variable {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ} {g0 : Ω → Matrix ι ι ℂ}
  {order : ι ≃ Fin (Fintype.card ι)}

/-- A stopped trial with relabelled sites. -/
def mapTrial (q : StoppedTrial (Ω := Ω) core t r g0 order) :
    StoppedTrial (Ω := Ω) (core.map e.toEmbedding) t (fun ω i => r ω (e.symm i))
      (fun ω => (g0 ω).submatrix e.symm e.symm) (orderMap e order) where
  state k ω := mapState e (q.state k ω)
  ridge := q.ridge
  pivot k ω := e (q.pivot k ω)
  residual := q.residual
  stop := q.stop
  outcome := q.outcome
  history := q.history
  damping_adapted :=
    (continuous_pi fun i => continuous_apply (e.symm i)).comp_stronglyMeasurable
      q.damping_adapted
  initial_active ω := by
    simp only [mapState_active, q.initial_active ω, Finset.map_univ_equiv]
  start_entries ω := by
    simp only [mapState_hatG, q.start_entries ω]
  start_ridge ω := by
    rw [chooseRidge_map]
    exact q.start_ridge ω
  initial_inverse ω i j := by
    rw [trialInverse_map]
    exact q.initial_inverse ω _ _
  finite_stop := q.finite_stop
  stopping := q.stopping
  running_budgets k ω hk := (budgetsHold_map e t _ _).mpr (q.running_budgets k ω hk)
  running_ridge := q.running_ridge
  pivot_max k ω hk := by
    rw [trialWeights_map, maxWeight_trialWeights_map, e.symm_apply_apply]
    exact q.pivot_max k ω hk
  pivot_tie k ω i hk h := by
    rw [trialWeights_map, trialWeights_map, e.symm_apply_apply] at h
    have := q.pivot_tie k ω (e.symm i) hk h
    simp only [orderMap, Equiv.trans_apply, e.symm_apply_apply, Fin.le_def, finCongr_apply,
      Fin.coe_cast] at this ⊢
    exact this
  running_cap k ω hk := by
    rw [maxWeight_trialWeights_map]
    exact q.running_cap k ω hk
  heat k ω hk := heatTransition_map e (q.heat k ω hk)
  ridge_rule k ω hk := by
    rw [chooseRidge_map]
    exact q.ridge_rule k ω hk
  done_iff ω := by
    rw [mapState_hatG, budgetsHold_map, projectionReady_map]
    exact q.done_iff ω
  fail_reason ω h := by
    rw [mapState_hatG, budgetsHold_map, maxWeight_trialWeights_map]
    exact q.fail_reason ω h
  entries_adapted k i j := q.entries_adapted k (e.symm i) (e.symm j)
  cross_adapted k := by
    simp_rw [trialCross_map]
    exact (continuous_id.matrix_submatrix _ _).comp_stronglyMeasurable (q.cross_adapted k)
  ridge_predictable := q.ridge_predictable
  pivot_predictable k := (measurable_of_countable e).comp (q.pivot_predictable k)
  residual_revealed := q.residual_revealed
  outcome_measurable := q.outcome_measurable

end Trial

section Local

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] {n : ℕ} (e : ι ≃ Fin n)
  {core : Finset ι} {t : ℝ} {r : Ω → ι → ℂ} {g0 : Ω → Matrix ι ι ℂ}
  {order : ι ≃ Fin (Fintype.card ι)}

theorem distanceToCore_map' (dist : ι → ι → ℝ) (i : Fin n) :
    distanceToCore (fun a b => dist (e.symm a) (e.symm b)) (core.map e.toEmbedding) i =
      distanceToCore dist core (e.symm i) := by
  have := AndersonAC.AgentS78.distanceToCore_map e dist core (e.symm i)
  rwa [e.apply_symm_apply] at this

/-- Transport of the local input. -/
theorem trialLocalInput_map (q : StoppedTrial (Ω := Ω) core t r g0 order) (μ : Measure Ω)
    (d : ℕ) (c K Cloc : ℝ) (dist : ι → ι → ℝ) (collapsed : ℕ → Ω → ι → ι → ℝ) (ell : ℝ)
    (h : TrialLocalInput q μ d c K Cloc dist collapsed ell) :
    TrialLocalInput (mapTrial e q) μ d c K Cloc (fun a b => dist (e.symm a) (e.symm b))
      (fun k ω a b => collapsed k ω (e.symm a) (e.symm b)) ell := by
  have hloc : ∀ k ω, (∀ j < k, distanceToCore (fun a b => dist (e.symm a) (e.symm b))
      (core.map e.toEmbedding) ((mapTrial e q).pivot j ω) < ell / 2) →
      ∀ j < k, distanceToCore dist core (q.pivot j ω) < ell / 2 := by
    intro k ω hk j hj
    have := hk j hj
    simp only [mapTrial] at this
    rwa [AndersonAC.AgentS78.distanceToCore_map] at this
  refine
    { dist_nonneg := fun i j => h.dist_nonneg _ _
      dist_symm := fun i j => h.dist_symm _ _
      dist_triangle := fun i j k => h.dist_triangle _ _ _
      dist_self := fun i => h.dist_self _
      ell_lower := h.ell_lower
      ell_upper := h.ell_upper
      core_ball := ?_
      shells := fun i m => ?_
      volume := fun i L hL => ?_
      metric := fun k ω hk hp i j => h.metric k ω hk (hloc k ω hp) _ _
      range_geometry := fun k ω hk hp => ?_
      resolvent_decay := fun k ω hk hp i j => ?_
      residual_bound := fun k ω hk hp => ?_
      residual_integrable := h.residual_integrable
      residual_square_integrable := h.residual_square_integrable
      residual_mean := fun k => ?_
      residual_variance := fun k => ?_ }
  · obtain ⟨c0, hc0⟩ := h.core_ball
    refine ⟨e c0, fun b hb => ?_⟩
    rw [Finset.mem_map_equiv] at hb
    simpa using hc0 _ hb
  · have := card_filter_comp (fun j => (m : ℝ) ≤ dist (e.symm i) j ∧ dist (e.symm i) j < m + 1)
      e.symm
    rw [this]
    exact h.shells _ m
  · have := card_filter_comp (fun j => dist (e.symm i) j ≤ L) e.symm
    rw [this]
    exact h.volume _ L hL
  · obtain ⟨H, hH⟩ := h.range_geometry k ω hk (hloc k ω hp)
    refine ⟨H.submatrix e.symm e.symm, ?_⟩
    have h1 := exteriorGeometry_rows e.symm hH
    have h2 := AndersonAC.AgentS6.exteriorGeometry_reindex (sEquiv e core).symm h1
    have hC : trialCross t (fun i => r ω (e.symm i)) ((mapTrial e q).state k ω) =
        ((trialCross t (r ω) (q.state k ω)).submatrix e.symm id).submatrix id
          (sEquiv e core).symm := by
      show trialCross t (fun i => r ω (e.symm i)) (mapState e (q.state k ω)) = _
      rw [trialCross_map, Matrix.submatrix_submatrix]
      rfl
    rw [hC]
    convert h2 using 2 with i'
    rw [distanceToCore_map' e (collapsed k ω) i']
  · show ‖scaledInverse t (trialInverse t (fun i => r ω (e.symm i))
        (mapState e (q.state k ω))) i j‖ ≤ _
    rw [trialInverse_map]
    exact h.resolvent_decay k ω hk (hloc k ω hp) _ _
  · have hp' : distanceToCore dist core (q.pivot k ω) < ell / 2 := by
      have := hp
      simp only [mapTrial] at this
      rwa [AndersonAC.AgentS78.distanceToCore_map] at this
    exact h.residual_bound k ω hk hp'
  · filter_upwards [h.residual_mean k] with ω hω hk hp
    have hp' : distanceToCore dist core (q.pivot k ω) < ell / 2 := by
      have := hp
      simp only [mapTrial] at this
      rwa [AndersonAC.AgentS78.distanceToCore_map] at this
    exact hω hk hp'
  · obtain ⟨η, hη, hae⟩ := h.residual_variance k
    refine ⟨η, hη, ?_⟩
    filter_upwards [hae] with ω hω hk hp
    have hp' : distanceToCore dist core (q.pivot k ω) < ell / 2 := by
      have := hp
      simp only [mapTrial] at this
      rwa [AndersonAC.AgentS78.distanceToCore_map] at this
    exact hω hk hp'

end Local

/-- **Transport (clearing trial bound sub-contract).** -/
theorem trialReindex_proof : AndersonAC.AgentS78.TrialReindexStatement := by
  intro Ω _ ι _ _ _ _ n e core t r g0 order q
  exact ⟨mapTrial e q, rfl, rfl, rfl, rfl, fun _ _ => rfl,
    fun μ d c K Cloc dist collapsed ell h => trialLocalInput_map e q μ d c K Cloc dist collapsed ell h⟩

end AndersonAC.AgentS78.TrialReindex

namespace AndersonAC.AgentS78

/-- **clearing trial bound reduction without the transport hypothesis.** -/
theorem clearingTrialH_of_inputs' {d : ℕ} (hd : 3 ≤ d)
    (hprep : PreparationUniformStatement) (hdrift : LeverageDriftUniformStatement)
    (hconc : AndersonAC.Blueprint.ConcentrationInput)
    (cP CP : ℝ) (qlag : ℝ → ℝ) (hqlag : Tendsto qlag (𝓝[>] 0) (𝓝 0))
    (geo : ∀ {m : ℕ}, ℕ → ℝ → ℕ → Set (RunRecord d m))
    (hgeo : ClearingGeometryStatement d (ClearingGood d cP CP qlag geo) cP CP)
    (hres : ClearingResidualStatement d (ClearingGood d cP CP qlag geo)) :
    ClearingTrialStatementH d (ClearingGood d cP CP qlag geo) :=
  clearingTrialH_of_inputs hd hprep hdrift hconc TrialReindex.trialReindex_proof cP CP qlag hqlag
    geo hgeo hres

end AndersonAC.AgentS78
