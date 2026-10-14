import AndersonAC.AgentS78.Construction.ClearingBlock
import AndersonAC.AgentS78.Construction.ClearingTrialReindex
import AndersonAC.AgentS6Lev2.Proof
import AndersonAC.AgentS6.CapTelescope
import AndersonAC.S6.Ridge

/-!
# Clearing bridge to §6's stopped trial

For a fixed entering record and a stopped trial `q` on its active sites, at every
sample `ω` whose running residuals are the true residuals and whose running pivots pass the
guard, `ω` is a block-local first failure iff the trial fails at `ω`.

The proof compares the two runs step by step (06-clearing.tex, 07-assembly.tex:18–34): the block
state after `k` operations carries the trial state `q.state k ω` (same active set, same real Schur
data, same damped inverse entries, same ridge), so both choose the same pivot (maximal weight,
`siteRank` tie-break = the trial order by `horder`), perform the same Schur update with the same
revealed residual, and stop for the same reason.

**Record hypothesis.** The block reads the committed matrix `rec0.endpoint.M`, while the trial's
initial real matrix is fixed only through `initial_inverse` (its damped inverse is
`trialG0 rec0`). The statement therefore carries the damped identity of the entering record,
`IsDampedEndpoint rec0.endpoint rec0.r (stageScale u j m)`, which ties the two together.
-/

open MeasureTheory Filter
open scoped Topology Matrix ComplexOrder

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78cbridge

open AndersonAC.S6

/-! ## Rows placed along an injection, zero rows elsewhere -/

section RowEmbed

variable {R R' B : Type*} [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']
  [Fintype B] [DecidableEq B]

/-- `C'` is `C` with its rows placed along the injection `f` and zero rows elsewhere. -/
structure RowEmbed (C' : Matrix R' B ℂ) (C : Matrix R B ℂ) (f : R → R') : Prop where
  inj : Function.Injective f
  row : ∀ a b, C' (f a) b = C a b
  zero : ∀ i, i ∉ Set.range f → ∀ b, C' i b = 0

variable {C' : Matrix R' B ℂ} {C : Matrix R B ℂ} {f : R → R'}

theorem RowEmbed.gram_eq (h : RowEmbed C' C f) : gram C' = gram C := by
  ext x y
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  symm
  apply Fintype.sum_of_injective f h.inj
  · intro i hi
    simp [h.zero i hi]
  · intro a
    simp [h.row]

theorem RowEmbed.ridgeGram_eq (h : RowEmbed C' C f) (τ : ℝ) : ridgeGram C' τ = ridgeGram C τ := by
  simp [ridgeGram, h.gram_eq]

theorem RowEmbed.ridgeProjection_apply (h : RowEmbed C' C f) (τ : ℝ) (a b : R) :
    ridgeProjection C' τ (f a) (f b) = ridgeProjection C τ a b := by
  simp only [ridgeProjection, h.ridgeGram_eq, Matrix.mul_apply, Matrix.conjTranspose_apply, h.row]

theorem RowEmbed.ridgeProjection_zero (h : RowEmbed C' C f) (τ : ℝ) (i : R')
    (hi : i ∉ Set.range f) (k : R') : ridgeProjection C' τ i k = 0 := by
  simp [ridgeProjection, Matrix.mul_apply, h.zero i hi]

theorem RowEmbed.leverage_apply (h : RowEmbed C' C f) (τ : ℝ) (a : R) :
    leverage C' τ (f a) = leverage C τ a := by
  unfold leverage
  rw [h.ridgeProjection_apply]

theorem RowEmbed.leverage_zero (h : RowEmbed C' C f) (τ : ℝ) (i : R') (hi : i ∉ Set.range f) :
    leverage C' τ i = 0 := by
  unfold leverage
  rw [h.ridgeProjection_zero τ i hi]
  simp

theorem RowEmbed.rangeProjection_apply (h : RowEmbed C' C f) (a b : R) :
    rangeProjection C' (f a) (f b) = rangeProjection C a b := by
  have h1 : Tendsto (fun τ => ridgeProjection C' τ (f a) (f b)) (𝓝[>] 0)
      (𝓝 (rangeProjection C' (f a) (f b))) :=
    ((continuous_id.matrix_elem (f a) (f b)).tendsto _).comp (AndersonAC.S6.ridge_limit C')
  have h2 : Tendsto (fun τ => ridgeProjection C τ a b) (𝓝[>] 0)
      (𝓝 (rangeProjection C a b)) :=
    ((continuous_id.matrix_elem a b).tendsto _).comp (AndersonAC.S6.ridge_limit C)
  simp_rw [h.ridgeProjection_apply] at h1
  exact tendsto_nhds_unique h1 h2

theorem RowEmbed.rangeProjection_zero (h : RowEmbed C' C f) (i : R') (hi : i ∉ Set.range f) :
    rangeProjection C' i i = 0 := by
  have h1 : Tendsto (fun τ => ridgeProjection C' τ i i) (𝓝[>] 0)
      (𝓝 (rangeProjection C' i i)) :=
    ((continuous_id.matrix_elem i i).tendsto _).comp (AndersonAC.S6.ridge_limit C')
  simp_rw [h.ridgeProjection_zero _ i hi] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

theorem RowEmbed.projectionWeight_apply (h : RowEmbed C' C f) (a : R) :
    projectionWeight C' (f a) = projectionWeight C a := by
  unfold projectionWeight
  rw [h.rangeProjection_apply]

theorem RowEmbed.projectionWeight_zero (h : RowEmbed C' C f) (i : R') (hi : i ∉ Set.range f) :
    projectionWeight C' i = 0 := by
  unfold projectionWeight
  rw [h.rangeProjection_zero i hi]
  simp

end RowEmbed

/-- `maxWeight` of a weight placed along an injection, zero elsewhere. -/
theorem maxWeight_embed {R R' : Type*} [Fintype R] [Fintype R'] (m' : R' → ℝ) (m : R → ℝ)
    (f : R → R') (hrow : ∀ a, m' (f a) = m a) (hzero : ∀ i, i ∉ Set.range f → m' i = 0) :
    maxWeight m' = maxWeight m := by
  unfold maxWeight
  congr 1
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    by_cases hi : i ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hi
      rw [hrow]
      exact Finset.le_sup (f := fun a => Real.toNNReal (m a)) (Finset.mem_univ a)
    · rw [hzero i hi]
      simp
  · apply Finset.sup_le
    intro a _
    rw [← hrow]
    exact Finset.le_sup (f := fun i => Real.toNNReal (m' i)) (Finset.mem_univ (f a))

section Embed

variable {R R' B B' : Type*} [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']

/-- The full comparison: rows along `f`, columns along `g`. -/
theorem embed_facts (C' : Matrix R' B' ℂ) (C : Matrix R B ℂ) (f : R → R') (g : B ≃ B')
    (h : RowEmbed (C'.submatrix id g) C f) :
    (∀ τ a, leverage C' τ (f a) = leverage C τ a) ∧
    (∀ τ i, i ∉ Set.range f → leverage C' τ i = 0) ∧
    (∀ τ, maxWeight (leverage C' τ) = maxWeight (leverage C τ)) ∧
    (∀ l τ, chooseRidge C' l τ = chooseRidge C l τ) ∧
    (∀ a, projectionWeight C' (f a) = projectionWeight C a) ∧
    (∀ i, i ∉ Set.range f → projectionWeight C' i = 0) := by
  have hlev : ∀ τ (i : R'), leverage (C'.submatrix id g) τ i = leverage C' τ i := fun τ i =>
    AndersonAC.AgentS78.TrialReindex.leverage_submatrix C' (Equiv.refl R') g τ i
  have hproj : ∀ i : R', projectionWeight (C'.submatrix id g) i = projectionWeight C' i :=
    fun i => AndersonAC.AgentS78.TrialReindex.projectionWeight_submatrix C' (Equiv.refl R') g i
  have h1 : ∀ τ a, leverage C' τ (f a) = leverage C τ a := fun τ a => by
    rw [← hlev, h.leverage_apply]
  have h2 : ∀ τ i, i ∉ Set.range f → leverage C' τ i = 0 := fun τ i hi => by
    rw [← hlev, h.leverage_zero τ i hi]
  have h3 : ∀ τ, maxWeight (leverage C' τ) = maxWeight (leverage C τ) := fun τ =>
    maxWeight_embed _ _ f (h1 τ) (h2 τ)
  refine ⟨h1, h2, h3, fun l τ => ?_, fun a => ?_, fun i hi => ?_⟩
  · unfold chooseRidge ridgeThreshold
    simp_rw [h3]
  · rw [← hproj, h.projectionWeight_apply]
  · rw [← hproj, h.projectionWeight_zero i hi]

end Embed

/-! ## Leverage against projection weights -/

section Strict

variable {R B : Type*} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]

/-- Strict form of `leverage ≤ projectionWeight` on a row with positive leverage. -/
theorem leverage_lt_projectionWeight (C : Matrix R B ℂ) {τ : ℝ} (hτ : 0 < τ) (i : R)
    (hpos : 0 < leverage C τ i) : leverage C τ i < projectionWeight C i := by
  classical
  let P := rangeProjection C
  let G := ridgeGram C τ
  let H := ridgeGram (Matrix.conjTranspose C) τ
  let Q : Matrix R R ℂ := C * G⁻¹ * Matrix.conjTranspose C
  have hPstar : Matrix.conjTranspose P = P := AndersonAC.AgentS6.rangeProjection_star_eq C
  have hPid : P * P = P := AndersonAC.AgentS6.rangeProjection_idem C
  have hPC : P * C = C := AndersonAC.AgentS6.rangeProjection_mul_eq C
  have hCHP : Matrix.conjTranspose C * P = Matrix.conjTranspose C := by
    have h := congrArg Matrix.conjTranspose hPC
    simpa [hPstar] using h
  have hPQ : P * Q = Q := by
    calc
      P * Q = (P * C) * G⁻¹ * Matrix.conjTranspose C := by
        dsimp [Q]
        simp [Matrix.mul_assoc]
      _ = Q := by rw [hPC]
  have hQP : Q * P = Q := by
    calc
      Q * P = C * G⁻¹ * (Matrix.conjTranspose C * P) := by
        dsimp [Q]
        simp [Matrix.mul_assoc]
      _ = Q := by rw [hCHP]
  have hGunit : IsUnit G.det := AndersonAC.AgentS6.ridgeGram_isUnit C hτ
  have hHunit : IsUnit H.det := AndersonAC.AgentS6.ridgeGram_isUnit (Matrix.conjTranspose C) hτ
  have hcomm : H * C = C * G := by
    dsimp [H, G, AndersonAC.S6.ridgeGram, AndersonAC.S6.gram]
    rw [Matrix.conjTranspose_conjTranspose]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]
    rw [Matrix.mul_assoc]
  have hHF : H * (1 - Q) = (τ : ℂ) • (1 : Matrix R R ℂ) := by
    calc
      H * (1 - Q) = H - (H * C) * G⁻¹ * Matrix.conjTranspose C := by
        dsimp [Q]
        rw [Matrix.mul_sub, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = H - (C * G) * G⁻¹ * Matrix.conjTranspose C := by rw [hcomm]
      _ = H - C * (G * G⁻¹) * Matrix.conjTranspose C := by simp [Matrix.mul_assoc]
      _ = H - C * Matrix.conjTranspose C := by
        rw [Matrix.mul_nonsing_inv G hGunit]
        simp
      _ = (τ : ℂ) • (1 : Matrix R R ℂ) := by
        dsimp [H, AndersonAC.S6.ridgeGram, AndersonAC.S6.gram]
        simp only [Matrix.conjTranspose_conjTranspose]
        abel
  have hF : 1 - Q = (τ : ℂ) • H⁻¹ := by
    calc
      1 - Q = (H⁻¹ * H) * (1 - Q) := by
        rw [Matrix.nonsing_inv_mul H hHunit, Matrix.one_mul]
      _ = H⁻¹ * (H * (1 - Q)) := by simp [Matrix.mul_assoc]
      _ = H⁻¹ * ((τ : ℂ) • (1 : Matrix R R ℂ)) := by rw [hHF]
      _ = (τ : ℂ) • H⁻¹ := by simp [Matrix.mul_smul]
  have hHpd : H.PosDef := by
    dsimp [H]
    unfold ridgeGram gram
    have : (τ : ℂ) • (1 : Matrix R R ℂ) = Matrix.diagonal (fun _ => (τ : ℂ)) := by
      ext a b; simp [Matrix.diagonal, Matrix.one_apply]
    rw [this]
    exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self _)
      (Matrix.PosDef.diagonal (fun _ => Complex.zero_lt_real.mpr hτ))
  have hHinv : (H⁻¹).PosDef := hHpd.inv
  have hEq : P - Q = (τ : ℂ) • (P * H⁻¹ * Matrix.conjTranspose P) := by
    have : Matrix.conjTranspose P * (1 - Q) * P = P - Q := by
      rw [hPstar]
      calc
        P * (1 - Q) * P = P * P - (P * Q) * P := by noncomm_ring
        _ = P - Q := by rw [hPid, hPQ, hQP]
    rw [← this, hF, hPstar]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  -- the row `i` of `P` is nonzero
  have hv : (fun k => star (P i k)) ≠ 0 := by
    intro hv0
    have hrow : ∀ b, C i b = 0 := by
      intro b
      have h1 : (Matrix.conjTranspose C * P) b i = Matrix.conjTranspose C b i := by rw [hCHP]
      have h2 : (Matrix.conjTranspose C * P) b i = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k _
        have hk : P k i = 0 := by
          have := congrFun hv0 k
          simp only [Pi.zero_apply] at this
          have hPki : P k i = star (P i k) := by
            have h' := congrFun (congrFun hPstar k) i
            rw [Matrix.conjTranspose_apply] at h'
            exact h'.symm
          rw [hPki, this]
        rw [hk, mul_zero]
      rw [h2, Matrix.conjTranspose_apply] at h1
      have := congrArg star h1
      simpa using this.symm
    have := AndersonAC.AgentS6.leverage_zero_row C τ i hrow
    linarith
  have hquad : 0 < star (fun k => star (P i k)) ⬝ᵥ (H⁻¹ *ᵥ (fun k => star (P i k))) :=
    hHinv.dotProduct_mulVec_pos hv
  have hdiag : (P - Q) i i = (τ : ℂ) *
      (star (fun k => star (P i k)) ⬝ᵥ (H⁻¹ *ᵥ (fun k => star (P i k)))) := by
    rw [hEq, Matrix.smul_apply, smul_eq_mul, AndersonAC.AgentS6.quad_entry]
  have hre : 0 < ((P - Q) i i).re := by
    rw [hdiag]
    have hq := (Complex.lt_def.mp hquad)
    simp only [Complex.zero_re, Complex.zero_im] at hq
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hτ hq.1
  unfold leverage projectionWeight
  change (Q i i).re < (P i i).re
  simp only [Matrix.sub_apply, Complex.sub_re] at hre
  linarith

/-- If every projection weight is at most `2 l` (projection ready) and `l > 0`, then the
maximal leverage at a positive ridge is `< 2 l`. -/
theorem maxWeight_lt_of_ready (C : Matrix R B ℂ) {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ)
    (hready : ∀ i, projectionWeight C i ≤ 2 * l) :
    maxWeight (leverage C τ) < 2 * l := by
  have hlt : ∀ i, leverage C τ i < 2 * l := by
    intro i
    rcases (AndersonAC.AgentS6.leverage_nonneg C hτ.le i).lt_or_eq with hpos | hzero
    · exact (leverage_lt_projectionWeight C hτ i hpos).trans_le (hready i)
    · rw [← hzero]; linarith
  unfold maxWeight
  have h2l : (0 : ℝ) < 2 * l := by linarith
  have : (Finset.univ.sup (fun i => Real.toNNReal (leverage C τ i))) < Real.toNNReal (2 * l) := by
    rw [Finset.sup_lt_iff (by simpa using h2l)]
    intro i _
    exact (Real.toNNReal_lt_toNNReal_iff h2l).mpr (hlt i)
  have hc := (NNReal.coe_lt_coe.mpr this)
  rwa [Real.coe_toNNReal _ h2l.le] at hc

/-- After the ridge rule on a projection-ready cross block, every leverage is at most `2 l`. -/
theorem leverage_chooseRidge_le_of_ready (C : Matrix R B ℂ) {l τ : ℝ} (hτ : 0 < τ)
    (hready : ∀ i, projectionWeight C i ≤ 2 * l) (i : R) :
    leverage C (chooseRidge C l τ) i ≤ 2 * l := by
  rcases lt_or_ge 0 (chooseRidge C l τ) with hpos | hnpos
  · exact (AndersonAC.AgentS6.leverage_le_projectionWeight C hpos i).trans (hready i)
  · -- transport to `Fin n` rows
    let e := Fintype.equivFin R
    let C₀ : Matrix (Fin (Fintype.card R)) B ℂ := C.submatrix e.symm id
    have hC₀ : C₀ = C.submatrix e.symm (Equiv.refl B) := rfl
    have hch : chooseRidge C₀ l τ = chooseRidge C l τ := by
      rw [hC₀]; exact AndersonAC.AgentS78.TrialReindex.chooseRidge_submatrix C e.symm _ l τ
    have hlev : ∀ σ, leverage C₀ σ (e i) = leverage C σ i := by
      intro σ
      rw [hC₀, AndersonAC.AgentS78.TrialReindex.leverage_submatrix]
      simp
    have := AndersonAC.AgentS6.chooseRidge_nonpos_cap C₀ hτ (by rw [hch]; exact hnpos) (e i)
    rwa [hch, hlev] at this

/-- The maximal leverage after the ridge rule on a projection-ready cross block. -/
theorem maxWeight_chooseRidge_le_of_ready (C : Matrix R B ℂ) {l τ : ℝ} (hl : 0 ≤ l) (hτ : 0 < τ)
    (hready : ∀ i, projectionWeight C i ≤ 2 * l) :
    maxWeight (leverage C (chooseRidge C l τ)) ≤ 2 * l := by
  unfold maxWeight
  have h2l : (0 : ℝ) ≤ 2 * l := by linarith
  have : (Finset.univ.sup (fun i => Real.toNNReal (leverage C (chooseRidge C l τ) i))) ≤
      Real.toNNReal (2 * l) := by
    apply Finset.sup_le
    intro i _
    exact Real.toNNReal_le_toNNReal (leverage_chooseRidge_le_of_ready C hτ hready i)
  have hc := (NNReal.coe_le_coe.mpr this)
  rwa [Real.coe_toNNReal _ h2l] at hc

end Strict

/-! ## Scalars -/

theorem heatLimit_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : heatLimit t = 0 := by
  unfold heatLimit
  apply Nat.floor_eq_zero.mpr
  have heh : eh = 46 / 10000 := by norm_num [eh, delta]
  rcases ht.lt_or_eq with hneg | hzero
  · rw [Real.rpow_def_of_neg hneg]
    have hcos : Real.cos ((-1 - eh) * Real.pi) < 0 := by
      have h1 : (-1 - eh) * Real.pi = -(eh * Real.pi + Real.pi) := by ring
      rw [h1, Real.cos_neg, Real.cos_add_pi]
      have : 0 < Real.cos (eh * Real.pi) := by
        apply Real.cos_pos_of_mem_Ioo
        rw [heh]
        constructor <;> nlinarith [Real.pi_pos]
      linarith
    have hexp := Real.exp_pos (Real.log t * (-1 - eh))
    have := mul_neg_of_pos_of_neg hexp hcos
    linarith
  · rw [hzero, Real.zero_rpow (by rw [heh]; norm_num)]
    norm_num

theorem leverageScale_pos {t : ℝ} (ht : 0 < t) : 0 < leverageScale t := by
  unfold leverageScale
  exact Real.rpow_pos_of_pos ht _

/-! ## Scattering entries -/

theorem scatteringOfDamping_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (p : ι → ℝ)
    (g : Matrix ι ι ℂ) (i k : ι) :
    scatteringOfDamping t p g i k = (1 : Matrix ι ι ℂ) i k +
      (2 * Complex.I * (t : ℂ)) * ((Real.sqrt (p i) : ℂ) * g i k * (Real.sqrt (p k) : ℂ)) := by
  simp [scatteringOfDamping, sqrtDamping, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-! ## The block scratch carrying a trial state -/

section Corr

open AndersonAC.S78 AndersonAC.AgentS78
open Classical

variable {d m : ℕ}

/-- Columns: the core as active sites and as torus sites. -/
def colEquiv {rec0 : RunRecord d m} (B : Finset (ActiveSite rec0)) (Bt : Finset (Torus d m))
    (hBt : Bt = B.map (Function.Embedding.subtype _)) : {b // b ∈ B} ≃ {b // b ∈ Bt} where
  toFun b := ⟨b.val.val, by rw [hBt]; exact Finset.mem_map_of_mem _ b.property⟩
  invFun b := ⟨⟨b.val, by
      have h : b.val ∈ B.map (Function.Embedding.subtype _) := hBt ▸ b.property
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
      rw [← ha]
      exact a.property⟩, by
      have h : b.val ∈ B.map (Function.Embedding.subtype _) := hBt ▸ b.property
      obtain ⟨a, haB, ha⟩ := Finset.mem_map.mp h
      have : a = ⟨b.val, by rw [← ha]; exact a.property⟩ := Subtype.ext ha
      rw [← this]
      exact haB⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem colEquiv_val {rec0 : RunRecord d m} (B : Finset (ActiveSite rec0))
    (Bt : Finset (Torus d m)) (hBt : Bt = B.map (Function.Embedding.subtype _))
    (b : {b // b ∈ B}) : (colEquiv B Bt hBt b).val = b.val.val := rfl

/-- The block scratch `sc` carries the trial state `s` (on the active sites of `rec0`). -/
structure Corr (rec0 : RunRecord d m) (B : Finset (ActiveSite rec0))
    (s : AndersonAC.S6.TrialState B) (sc : ClearScratch d m) : Prop where
  active : sc.active = s.active.map (Function.Embedding.subtype _)
  M : ∀ (a b : ActiveSite rec0) (ha : a ∈ s.active) (hb : b ∈ s.active),
    sc.Mnum a.val b.val = s.M ⟨a, ha⟩ ⟨b, hb⟩
  hatG : ∀ a b : ActiveSite rec0, sc.hatG a.val b.val = s.hatG a b
  hatG_out : ∀ i k : Torus d m, (i ∉ rec0.endpoint.active ∨ k ∉ rec0.endpoint.active) →
    sc.hatG i k = rec0.endpoint.g i k
  g0 : sc.g0 = rec0.endpoint.g
  core : sc.core = B.map (Function.Embedding.subtype _)

variable {rec0 : RunRecord d m} {B : Finset (ActiveSite rec0)}
  {s : AndersonAC.S6.TrialState B} {sc : ClearScratch d m}

theorem Corr.mem_active (hc : Corr rec0 B s sc) (a : ActiveSite rec0) :
    a.val ∈ sc.active ↔ a ∈ s.active := by
  rw [hc.active]
  exact Finset.mem_map' _

theorem Corr.mem_core (hc : Corr rec0 B s sc) (a : ActiveSite rec0) :
    a.val ∈ sc.core ↔ a ∈ B := by
  rw [hc.core]
  exact Finset.mem_map' _

theorem Corr.active_sub (hc : Corr rec0 B s sc) : sc.active ⊆ rec0.endpoint.active := by
  intro i hi
  rw [hc.active] at hi
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
  exact a.property

theorem Corr.image (hc : Corr rec0 B s sc) : s.active.image Subtype.val = sc.active := by
  rw [hc.active, Finset.map_eq_image]
  rfl

theorem Corr.core_sub (hc : Corr rec0 B s sc) : sc.core ⊆ sc.active := by
  intro i hi
  rw [hc.core] at hi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
  exact (hc.mem_active a).mpr (s.core_active ha)

/-- Damped inverses of the scratch and of the trial state agree on active pairs. -/
theorem Corr.inv (hc : Corr rec0 B s sc) (t : ℝ) (a b : ActiveSite rec0) (ha : a ∈ s.active)
    (hb : b ∈ s.active) :
    AndersonAC.S6.activeInverse (restrictM sc.active sc.Mnum) t
        (fun i : {i // i ∈ sc.active} => rec0.r i.val)
        ⟨a.val, (hc.mem_active a).mpr ha⟩ ⟨b.val, (hc.mem_active b).mpr hb⟩ =
      AndersonAC.S6.trialInverse t (fun i : ActiveSite rec0 => rec0.r i.val) s ⟨a, ha⟩ ⟨b, hb⟩ := by
  unfold AndersonAC.S6.trialInverse
  refine activeInverse_corr (rec0 := rec0) sc.active s.active hc.active_sub hc.image
    (restrictM sc.active sc.Mnum) s.M _ _ t ?_ ?_ a.val _ a ha rfl b.val _ b hb rfl
  · intro i hi x hx hxi k hk y hy hyk
    subst hxi hyk
    exact hc.M x y hx hy
  · intro i hi x hx hxi
    subst hxi
    rfl

/-- The block's cross matrix is the trial's, rows placed along `Subtype.val`. -/
theorem Corr.cross (hc : Corr rec0 B s sc) (t : ℝ) :
    RowEmbed ((xCross t rec0.r sc.active (restrictM sc.active sc.Mnum) sc.core).submatrix id
        (colEquiv B sc.core hc.core))
      (AndersonAC.S6.trialCross t (fun i : ActiveSite rec0 => rec0.r i.val) s) Subtype.val := by
  refine ⟨Subtype.val_injective, fun a b => ?_, fun i hi b => ?_⟩
  · simp only [Matrix.submatrix_apply, id]
    unfold xCross AndersonAC.S6.trialCross
    simp only [colEquiv_val]
    by_cases ha : a ∈ s.active
    · have ha' : a.val ∈ sc.active := (hc.mem_active a).mpr ha
      rw [dif_pos ha', dif_pos ha]
      by_cases haB : a ∈ B
      · have haB' : a.val ∈ sc.core := (hc.mem_core a).mpr haB
        rw [if_pos haB', if_pos haB]
      · have haB' : a.val ∉ sc.core := fun h => haB ((hc.mem_core a).mp h)
        rw [if_neg haB', if_neg haB]
        have hb : b.val ∈ s.active := s.core_active b.property
        have hb' : b.val.val ∈ sc.active := (hc.mem_active b.val).mpr hb
        simp only [hb', ↓reduceDIte]
        unfold AndersonAC.S6.scattering
        rw [scatteringOfDamping_apply, scatteringOfDamping_apply]
        have hne : a ≠ b.val := fun h => haB (h ▸ b.property)
        have hne1 : (⟨a.val, ha'⟩ : {i // i ∈ sc.active}) ≠ ⟨b.val.val, hb'⟩ := by
          intro h
          have h' := congrArg Subtype.val h
          exact hne (Subtype.ext h')
        have hne2 : (⟨a, ha⟩ : {i // i ∈ s.active}) ≠ ⟨b.val, s.core_active b.property⟩ := by
          intro h
          exact hne (congrArg Subtype.val h)
        rw [Matrix.one_apply_ne hne1, Matrix.one_apply_ne hne2]
        rw [hc.inv t a b.val ha hb]
        rfl
    · have ha' : a.val ∉ sc.active := fun h => ha ((hc.mem_active a).mp h)
      rw [dif_neg ha', dif_neg ha]
  · simp only [Matrix.submatrix_apply, id]
    unfold xCross
    have hi' : i ∉ sc.active := by
      intro h
      exact hi ⟨⟨i, hc.active_sub h⟩, rfl⟩
    rw [dif_neg hi']

/-- Budgets of the scratch and of the trial state agree. -/
theorem Corr.budgets (hc : Corr rec0 B s sc) {t : ℝ} (ht : 0 < t) :
    AndersonAC.S6.BudgetsHold t sc.g0 sc.hatG ↔ AndersonAC.S6.BudgetsHold t (trialG0 rec0) s.hatG := by
  set D' : Matrix (Torus d m) (Torus d m) ℂ := sc.hatG - sc.g0 with hD'
  set D : Matrix (ActiveSite rec0) (ActiveSite rec0) ℂ := s.hatG - trialG0 rec0 with hD
  have hin : ∀ a b : ActiveSite rec0, D' a.val b.val = D a b := by
    intro a b
    simp only [hD', hD, Matrix.sub_apply, hc.hatG, hc.g0, trialG0, Matrix.submatrix_apply]
  have hout : ∀ i k : Torus d m, (i ∉ Set.range (Subtype.val : ActiveSite rec0 → Torus d m) ∨
      k ∉ Set.range (Subtype.val : ActiveSite rec0 → Torus d m)) → D' i k = 0 := by
    intro i k hik
    have : i ∉ rec0.endpoint.active ∨ k ∉ rec0.endpoint.active := by
      rcases hik with h | h
      · exact Or.inl fun hm => h ⟨⟨i, hm⟩, rfl⟩
      · exact Or.inr fun hm => h ⟨⟨k, hm⟩, rfl⟩
    simp only [hD', Matrix.sub_apply, hc.hatG_out i k this, hc.g0, sub_self]
  have hrow : ∀ a : ActiveSite rec0, AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t D') a.val =
      AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t D) a := by
    intro a
    unfold AndersonAC.S6.sqRow AndersonAC.S6.scaledInverse
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro k hk
      simp [hout a.val k (Or.inr hk)]
    · intro b
      simp [hin]
  have hrow0 : ∀ i, i ∉ Set.range (Subtype.val : ActiveSite rec0 → Torus d m) →
      AndersonAC.S6.sqRow (AndersonAC.S6.scaledInverse t D') i = 0 := by
    intro i hi
    unfold AndersonAC.S6.sqRow AndersonAC.S6.scaledInverse
    apply Finset.sum_eq_zero
    intro k _
    simp [hout i k (Or.inl hi)]
  have hhs : AndersonAC.S6.hsSq (AndersonAC.S6.scaledInverse t D') =
      AndersonAC.S6.hsSq (AndersonAC.S6.scaledInverse t D) := by
    unfold AndersonAC.S6.hsSq
    symm
    exact Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ hrow0
      (fun a => (hrow a).symm)
  have hin' : ∀ a b : ActiveSite rec0, sc.hatG a.val b.val - sc.g0 a.val b.val =
      s.hatG a b - trialG0 rec0 a b := by
    intro a b
    rw [hc.hatG, hc.g0]
    rfl
  have hout' : ∀ i k : Torus d m, (i ∉ Set.range (Subtype.val : ActiveSite rec0 → Torus d m) ∨
      k ∉ Set.range (Subtype.val : ActiveSite rec0 → Torus d m)) →
      sc.hatG i k - sc.g0 i k = 0 := fun i k hik => hout i k hik
  have hE : 0 ≤ AndersonAC.S6.entryBudget t := (Real.rpow_pos_of_pos ht _).le
  have hR : 0 ≤ AndersonAC.S6.rowBudget t := (Real.rpow_pos_of_pos ht _).le
  unfold AndersonAC.S6.BudgetsHold
  rw [← hD', ← hD, hhs]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun a b => ?_, fun a => ?_, h3⟩
    · rw [← hin']; exact h1 _ _
    · rw [← hrow]; exact h2 _
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i k => ?_, fun i => ?_, h3⟩
    · by_cases hi : i ∈ Set.range (Subtype.val : ActiveSite rec0 → Torus d m)
      · by_cases hk : k ∈ Set.range (Subtype.val : ActiveSite rec0 → Torus d m)
        · obtain ⟨a, rfl⟩ := hi
          obtain ⟨b, rfl⟩ := hk
          rw [hin']; exact h1 a b
        · rw [hout' i k (Or.inr hk)]; simpa using hE
      · rw [hout' i k (Or.inl hi)]; simpa using hE
    · by_cases hi : i ∈ Set.range (Subtype.val : ActiveSite rec0 → Torus d m)
      · obtain ⟨a, rfl⟩ := hi
        rw [hrow]; exact h2 a
      · rw [hrow0 i hi]; exact hR


/-- Weights, maxima, ridges and readiness of the scratch are those of the trial state. -/
theorem Corr.facts (hc : Corr rec0 B s sc) (t : ℝ) :
    (∀ τ (a : ActiveSite rec0), scratchWeights t rec0.r sc τ a.val =
      AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ a) ∧
    (∀ τ (i : Torus d m), i ∉ rec0.endpoint.active → scratchWeights t rec0.r sc τ i = 0) ∧
    (∀ τ, AndersonAC.S6.maxWeight (scratchWeights t rec0.r sc τ) =
      AndersonAC.S6.maxWeight (AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ)) ∧
    (∀ l τ, AndersonAC.S6.chooseRidge (xCross t rec0.r sc.active (restrictM sc.active sc.Mnum) sc.core) l τ =
      AndersonAC.S6.chooseRidge (AndersonAC.S6.trialCross t (fun i : ActiveSite rec0 => rec0.r i.val) s) l τ) ∧
    (0 ≤ AndersonAC.S6.leverageScale t →
      (xReady t rec0.r sc.active (restrictM sc.active sc.Mnum) sc.core ↔
        AndersonAC.S6.projectionReady t (fun i : ActiveSite rec0 => rec0.r i.val) s)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := embed_facts _ _ Subtype.val (colEquiv B sc.core hc.core)
    (hc.cross t)
  have hrange : ∀ i : Torus d m, i ∉ rec0.endpoint.active →
      i ∉ Set.range (Subtype.val : ActiveSite rec0 → Torus d m) := by
    rintro i hi ⟨a, rfl⟩
    exact hi a.property
  refine ⟨fun τ a => h1 τ a, fun τ i hi => h2 τ i (hrange i hi), fun τ => h3 τ,
    fun l τ => h4 l τ, fun hl => ?_⟩
  unfold xReady AndersonAC.S6.projectionReady
  constructor
  · intro h a
    rw [← h5 a]
    exact h a.val
  · intro h i
    by_cases hi : i ∈ rec0.endpoint.active
    · have := h5 ⟨i, hi⟩
      simp only at this
      rw [this]
      exact h _
    · rw [h6 i (hrange i hi)]
      linarith

/-- The block's candidate pivot is the trial's pivot (same maximal weight; `siteRank`
tie-break = the trial order). -/
theorem Corr.candPivot_eq (hc : Corr rec0 B s sc) {t τ : ℝ}
    (order : ActiveSite rec0 ≃ Fin (Fintype.card (ActiveSite rec0)))
    (horder : ∀ a b : ActiveSite rec0, (order a).val ≤ (order b).val ↔
      (siteRank d m a.val).val ≤ (siteRank d m b.val).val)
    (p : ActiveSite rec0)
    (hpos : 0 < AndersonAC.S6.maxWeight
      (AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ))
    (hmax : AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ p =
      AndersonAC.S6.maxWeight (AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ))
    (htie : ∀ i, AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ i =
      AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ p → order p ≤ order i) :
    candPivot rec0.r sc t τ = some p.val := by
  obtain ⟨hw, hw0, hmw, -, -⟩ := hc.facts t
  unfold candPivot
  rw [leastMaximizer_eq_some]
  refine ⟨by rw [hw, hmw]; exact hmax, fun i hi => ?_⟩
  rw [hmw] at hi
  by_cases hia : i ∈ rec0.endpoint.active
  · have hi' : AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ ⟨i, hia⟩ =
        AndersonAC.S6.trialWeights t (fun i : ActiveSite rec0 => rec0.r i.val) s τ p := by
      rw [← hw τ ⟨i, hia⟩, hi, hmax]
    have := htie _ hi'
    have h2 := (horder p ⟨i, hia⟩).mp this
    exact h2
  · rw [hw0 τ i hia] at hi
    linarith

end Corr

/-! ## The clearing actions -/

section Actions

open AndersonAC.S78 AndersonAC.AgentS78
open AndersonAC.S2 (RandomSources Query Answer)
open Classical

variable {d m : ℕ}

theorem actionOf_heat_eq (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc : ClearScratch d m)
    (hf : sc.failed = false) (hd : sc.done = false) (hne : sc.core ≠ ∅)
    (hcp : sc.corePhase = false) (hsub : sc.core ⊆ sc.active)
    (hb : AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc.hatG)
    (hlim : sc.step < AndersonAC.S6.heatLimit (stageScale u j m))
    (hcap : AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rc.r sc sc.ridge) ≤
      4 * AndersonAC.S6.leverageScale (stageScale u j m))
    (hnr : ¬ xReady (stageScale u j m) rc.r sc.active (restrictM sc.active sc.Mnum) sc.core)
    (p : Torus d m) (hp : candPivot rc.r sc (stageScale u j m) sc.ridge = some p)
    (hg : guardHolds (d := d) (m := m) j sc.core (coupledActive rc) rc.terminal p)
    (hpc : p ∉ sc.core) :
    actionOf (d := d) (m := m) j u rc sc = .heat p hg := by
  unfold actionOf
  simp only [hf, hd, hne, hcp, hsub, hb, hlim, hcap, hnr, hp, hg, hpc, Bool.false_eq_true,
    if_false, if_true, dite_false, dite_true, ↓reduceIte, ↓reduceDIte]

theorem actionOf_ready_eq (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc : ClearScratch d m)
    (hf : sc.failed = false) (hd : sc.done = false) (hne : sc.core ≠ ∅)
    (hcp : sc.corePhase = false) (hsub : sc.core ⊆ sc.active)
    (hb : AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc.hatG)
    (hlim : sc.step < AndersonAC.S6.heatLimit (stageScale u j m))
    (hcap : AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rc.r sc sc.ridge) ≤
      4 * AndersonAC.S6.leverageScale (stageScale u j m))
    (hr : xReady (stageScale u j m) rc.r sc.active (restrictM sc.active sc.Mnum) sc.core) :
    actionOf (d := d) (m := m) j u rc sc = .coreReady := by
  unfold actionOf
  simp only [hf, hd, hne, hcp, hsub, hb, hlim, hcap, hr, Bool.false_eq_true,
    if_false, if_true, dite_false, dite_true, ↓reduceIte, ↓reduceDIte]

theorem actionOf_fail_of (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc : ClearScratch d m)
    (hf : sc.failed = false) (hd : sc.done = false) (hne : sc.core ≠ ∅)
    (hcp : sc.corePhase = false)
    (h : ¬ (sc.core ⊆ sc.active ∧ AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc.hatG ∧
      sc.step < AndersonAC.S6.heatLimit (stageScale u j m) ∧
      AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rc.r sc sc.ridge) ≤
        4 * AndersonAC.S6.leverageScale (stageScale u j m))) :
    ∃ po, actionOf (d := d) (m := m) j u rc sc = .fail po := by
  unfold actionOf
  simp only [hf, hd, hne, hcp, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
  by_cases h1 : sc.core ⊆ sc.active
  · by_cases h2 : AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc.hatG
    · by_cases h3 : sc.step < AndersonAC.S6.heatLimit (stageScale u j m)
      · by_cases h4 : AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rc.r sc sc.ridge) ≤
            4 * AndersonAC.S6.leverageScale (stageScale u j m)
        · exact absurd ⟨h1, h2, h3, h4⟩ h
        · simp only [h1, h2, h3, h4, ↓reduceIte]
          exact ⟨_, rfl⟩
      · simp only [h1, h2, h3, ↓reduceIte]
        exact ⟨_, rfl⟩
    · simp only [h1, h2, ↓reduceIte]
      exact ⟨_, rfl⟩
  · simp only [h1, ↓reduceIte]
    exact ⟨_, rfl⟩

/-- The heat branch's provisional scratch (verbatim from `clearingUpdate`). -/
def heatScratch (n₀ j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc : ClearScratch d m)
    (p : Torus d m) (ans : Answer (Torus d m)) : ClearScratch d m :=
  let lam := clearingLam n₀ u
  let ξ := residOfAnswer (d := d) (m := m) lam p (rc.prefixLength p) ans
  let t := stageScale u j m
  let l := AndersonAC.S6.leverageScale t
  let E := elimStep (d := d) (m := m) t rc.r sc p ξ
  let sc1raw : ClearScratch d m := { sc with Mnum := E.1, hatG := E.2, active := sc.active.erase p, resids := Function.update sc.resids p ξ, inspected := insert p sc.inspected, step := sc.step + 1 }
  let ridge1 : ℝ := AndersonAC.S6.chooseRidge (xCross t rc.r sc1raw.active (restrictM sc1raw.active sc1raw.Mnum) sc1raw.core) l sc.ridge
  { sc1raw with ridge := ridge1 }

/-- The heat branch's checks after the heat (verbatim from `clearingUpdate`). -/
def heatPost (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc sc1 : ClearScratch d m) :
    ClearScratch d m :=
  let t := stageScale u j m
  let l := AndersonAC.S6.leverageScale t
  if ¬ AndersonAC.S6.BudgetsHold t sc.g0 sc1.hatG then { sc1 with failed := true }
  else if sc1.step ≥ AndersonAC.S6.heatLimit t then { sc1 with failed := true }
  else
    let w := scratchWeights (d := d) (m := m) t rc.r sc1 sc1.ridge
    if 4 * l < AndersonAC.S6.maxWeight w then { sc1 with failed := true }
    else if xReady t rc.r sc1.active (restrictM sc1.active sc1.Mnum) sc1.core then
      { sc1 with corePhase := true }
    else sc1

theorem update_heat_eq (n₀ j : ℕ) (u : ℝ) (s : RunRecord d m × ClearScratch d m)
    (ans : Answer (Torus d m)) (hf : s.2.failed = false) (hd : s.2.done = false)
    (p : Torus d m) (hg : guardHolds (d := d) (m := m) j s.2.core (coupledActive s.1) s.1.terminal p)
    (hact : actionOf (d := d) (m := m) j u s.1 s.2 = .heat p hg) :
    clearingUpdate (d := d) (m := m) n₀ j u s ans =
      (s.1, heatPost j u s.1 s.2 (heatScratch n₀ j u s.1 s.2 p ans)) := by
  have hc : ¬ (s.2.failed = true ∨ s.2.done = true) := by simp [hf, hd]
  unfold clearingUpdate
  simp only [hc, ↓reduceIte]
  rw [hact]
  unfold heatPost heatScratch
  dsimp only
  split_ifs <;> rfl

theorem update_fail_eq (n₀ j : ℕ) (u : ℝ) (s : RunRecord d m × ClearScratch d m)
    (ans : Answer (Torus d m)) (hf : s.2.failed = false) (hd : s.2.done = false)
    (po : Option (Torus d m)) (hact : actionOf (d := d) (m := m) j u s.1 s.2 = .fail po) :
    (clearingUpdate (d := d) (m := m) n₀ j u s ans).2.failed = true := by
  unfold clearingUpdate
  simp only [hf, hd, Bool.false_eq_true, or_self, if_false, ↓reduceIte]
  rw [hact]

theorem update_ready_eq (n₀ j : ℕ) (u : ℝ) (s : RunRecord d m × ClearScratch d m)
    (ans : Answer (Torus d m)) (hf : s.2.failed = false) (hd : s.2.done = false)
    (hact : actionOf (d := d) (m := m) j u s.1 s.2 = .coreReady) :
    (clearingUpdate (d := d) (m := m) n₀ j u s ans).2.corePhase = true ∧
      (clearingUpdate (d := d) (m := m) n₀ j u s ans).2.failed = false := by
  unfold clearingUpdate
  simp only [hf, hd, Bool.false_eq_true, or_self, if_false, ↓reduceIte]
  rw [hact]
  exact ⟨rfl, rfl⟩

theorem next_heat_eq (n₀ j : ℕ) (u : ℝ) (s : RunRecord d m × ClearScratch d m)
    (p : Torus d m) (hg : guardHolds (d := d) (m := m) j s.2.core (coupledActive s.1) s.1.terminal p)
    (hact : actionOf (d := d) (m := m) j u s.1 s.2 = .heat p hg) :
    clearingNext (d := d) (m := m) n₀ j u s = Query.trueSuffix p (s.1.prefixLength p) := by
  unfold clearingNext
  rw [hact]

/-- The heat residual read from the answer to its `trueSuffix` query is the true residual. -/
theorem resid_trueSuffix {M : ℕ → ℕ} (lam : ℝ) (p : Torus d m) (h : ℕ)
    (L : List (Query (Torus d m))) (ω : RandomSources (Torus d m) M) :
    residOfAnswer (d := d) (m := m) lam p h (localAnswer (Torus d m) M L (Query.trueSuffix p h) ω) =
      trueResidual lam ω p h := by
  unfold residOfAnswer trueResidual AndersonAC.S2.binarySuffix
  congr 1
  funext k
  have hmem : (Sum.inl (p, h + k) : AndersonAC.S2.SignIndex (Torus d m)) ∈
      AndersonAC.S2.querySigns (Torus d m) (Query.trueSuffix p h) :=
    ⟨h + k, Nat.le_add_right _ _, rfl⟩
  unfold localAnswer
  simp [hmem, trueDigits]

end Actions

/-! ## heatPost outcomes and the heat step on the carried data -/

section Steps

open AndersonAC.S78 AndersonAC.AgentS78
open AndersonAC.S2 (RandomSources Query Answer)
open Classical

variable {d m : ℕ}

theorem heatPost_failed (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc sc1 : ClearScratch d m)
    (h : ¬ AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc1.hatG ∨
      AndersonAC.S6.heatLimit (stageScale u j m) ≤ sc1.step ∨
      4 * AndersonAC.S6.leverageScale (stageScale u j m) <
        AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rc.r sc1 sc1.ridge)) :
    (heatPost j u rc sc sc1).failed = true := by
  unfold heatPost
  dsimp only
  by_cases h1 : AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc1.hatG
  · rw [if_neg (not_not.mpr h1)]
    by_cases h2 : sc1.step ≥ AndersonAC.S6.heatLimit (stageScale u j m)
    · rw [if_pos h2]
    · rw [if_neg h2]
      have h3 : 4 * AndersonAC.S6.leverageScale (stageScale u j m) <
          AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rc.r sc1 sc1.ridge) := by
        rcases h with h | h | h
        · exact absurd h1 h
        · exact absurd h h2
        · exact h
      rw [if_pos h3]
  · rw [if_pos h1]

theorem heatPost_cont (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc sc1 : ClearScratch d m)
    (h1 : AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc1.hatG)
    (h2 : sc1.step < AndersonAC.S6.heatLimit (stageScale u j m))
    (h3 : AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rc.r sc1 sc1.ridge) ≤
      4 * AndersonAC.S6.leverageScale (stageScale u j m))
    (h4 : ¬ xReady (stageScale u j m) rc.r sc1.active (restrictM sc1.active sc1.Mnum) sc1.core) :
    heatPost j u rc sc sc1 = sc1 := by
  unfold heatPost
  dsimp only
  rw [if_neg (not_not.mpr h1), if_neg (not_le.mpr h2), if_neg (not_lt.mpr h3), if_neg h4]

theorem heatPost_ready (j : ℕ) (u : ℝ) (rc : RunRecord d m) (sc sc1 : ClearScratch d m)
    (h1 : AndersonAC.S6.BudgetsHold (stageScale u j m) sc.g0 sc1.hatG)
    (h2 : sc1.step < AndersonAC.S6.heatLimit (stageScale u j m))
    (h3 : AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rc.r sc1 sc1.ridge) ≤
      4 * AndersonAC.S6.leverageScale (stageScale u j m))
    (h4 : xReady (stageScale u j m) rc.r sc1.active (restrictM sc1.active sc1.Mnum) sc1.core) :
    (heatPost j u rc sc sc1).corePhase = true ∧ (heatPost j u rc sc sc1).failed = sc1.failed := by
  unfold heatPost
  dsimp only
  rw [if_neg (not_not.mpr h1), if_neg (not_le.mpr h2), if_neg (not_lt.mpr h3), if_pos h4]
  exact ⟨rfl, rfl⟩

variable {rec0 : RunRecord d m} {B : Finset (ActiveSite rec0)}
  {s : AndersonAC.S6.TrialState B} {sc : ClearScratch d m}

/-- One heat on the carried data: the scratch after `elimStep` carries the successor state. -/
theorem Corr.heat (hc : Corr rec0 B s sc) {t : ℝ} {s' : AndersonAC.S6.TrialState B}
    {p : ActiveSite rec0} {ξ : ℝ}
    (hh : AndersonAC.S6.HeatTransition t (fun i : ActiveSite rec0 => rec0.r i.val) s s' p ξ)
    (sc' : ClearScratch d m)
    (hM : sc'.Mnum = (elimStep (d := d) (m := m) t rec0.r sc p.val ξ).1)
    (hG : sc'.hatG = (elimStep (d := d) (m := m) t rec0.r sc p.val ξ).2)
    (hA : sc'.active = sc.active.erase p.val) (hg0 : sc'.g0 = sc.g0) (hco : sc'.core = sc.core) :
    Corr rec0 B s' sc' := by
  obtain ⟨hx, -, hact', -, hMf, hGf⟩ := hh
  have hactive : sc'.active = s'.active.map (Function.Embedding.subtype _) := by
    rw [hA, hc.active, hact', Finset.map_erase]
    rfl
  have hmem' : ∀ a : ActiveSite rec0, a.val ∈ sc.active.erase p.val ↔ a ∈ s'.active := by
    intro a
    rw [← hA, hactive]
    exact Finset.mem_map' _
  have hold : ∀ a : ActiveSite rec0, a ∈ s'.active → a ∈ s.active := by
    intro a ha
    rw [hact'] at ha
    exact Finset.mem_of_mem_erase ha
  have hne : ∀ a : ActiveSite rec0, a ∈ s'.active → a.val ≠ p.val := by
    intro a ha h
    rw [hact'] at ha
    exact (Finset.mem_erase.mp ha).1 (Subtype.ext h)
  have hMent : ∀ (a b : ActiveSite rec0) (ha : a ∈ s'.active) (hb : b ∈ s'.active),
      sc'.Mnum a.val b.val = s'.M ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b ha hb
    rw [hM, hMf ⟨a, ha⟩ ⟨b, hb⟩ (hold a ha) (hold b hb)]
    simp only [elimStep, schurStepM]
    rw [if_neg (by rintro (h | h); exacts [hne a ha h, hne b hb h])]
    rw [hc.M a b (hold a ha) (hold b hb), hc.M a p (hold a ha) hx, hc.M p b hx (hold b hb),
      hc.M p p hx hx]
  refine ⟨hactive, hMent, fun a b => ?_, fun i k hik => ?_, hg0.trans hc.g0, hco.trans hc.core⟩
  · rw [hG, hGf a b]
    simp only [elimStep]
    by_cases ha : a ∈ s'.active
    · by_cases hb : b ∈ s'.active
      · have ha' := (hmem' a).mpr ha
        have hb' := (hmem' b).mpr hb
        rw [dif_pos ⟨ha', hb'⟩, dif_pos ha, dif_pos hb]
        simp only [add_sub_cancel]
        unfold AndersonAC.S6.trialInverse
        have hsub : sc.active.erase p.val ⊆ rec0.endpoint.active :=
          (Finset.erase_subset _ _).trans hc.active_sub
        have himg : s'.active.image Subtype.val = sc.active.erase p.val := by
          rw [← hA, hactive, Finset.map_eq_image]
          rfl
        refine activeInverse_corr (rec0 := rec0) (sc.active.erase p.val) s'.active hsub himg
          _ s'.M _ _ t ?_ ?_ a.val ha' a ha rfl b.val hb' b hb rfl
        · intro i hi y hy hyi k hk z hz hzk
          subst hyi hzk
          have := hMent y z hy hz
          rw [hM] at this
          exact this
        · intro i hi y hy hyi
          subst hyi
          rfl
      · have hb' : ¬ b.val ∈ sc.active.erase p.val := fun h => hb ((hmem' b).mp h)
        rw [dif_neg (fun h => hb' h.2), dif_pos ha, dif_neg hb, add_zero, hc.hatG]
    · have ha' : ¬ a.val ∈ sc.active.erase p.val := fun h => ha ((hmem' a).mp h)
      rw [dif_neg (fun h => ha' h.1), dif_neg ha, add_zero, hc.hatG]
  · rw [hG]
    simp only [elimStep]
    have : ¬ (i ∈ sc.active.erase p.val ∧ k ∈ sc.active.erase p.val) := by
      rintro ⟨hi, hk⟩
      rcases hik with h | h
      · exact h (hc.active_sub (Finset.mem_of_mem_erase hi))
      · exact h (hc.active_sub (Finset.mem_of_mem_erase hk))
    rw [dif_neg this]
    exact hc.hatG_out i k hik

/-- The damped identity of the entering record pins the trial's initial real matrix. -/
theorem damped_M_eq {t : ℝ} (hdamp : IsDampedEndpoint rec0.endpoint rec0.r t)
    (s : AndersonAC.S6.TrialState B) (hact : s.active = Finset.univ)
    (hinv : ∀ i k : {i // i ∈ s.active},
      AndersonAC.S6.trialInverse t (fun i : ActiveSite rec0 => rec0.r i.val) s i k =
        trialG0 rec0 i k)
    (a b : ActiveSite rec0) (ha : a ∈ s.active) (hb : b ∈ s.active) :
    (rec0.endpoint.M a.val b.val).re = s.M ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨-, -, hBG⟩ := hdamp
  dsimp only at hBG
  let e : {i // i ∈ s.active} ≃ ActiveSite rec0 :=
    Equiv.subtypeUnivEquiv (fun i => by rw [hact]; exact Finset.mem_univ i)
  set D := AndersonAC.S6.dampedMatrix s.M t (fun i : {i // i ∈ s.active} => rec0.r i.val.val)
    with hDdef
  set Bm : Matrix (ActiveSite rec0) (ActiveSite rec0) ℂ :=
    rec0.endpoint.M.submatrix (fun i : rec0.endpoint.active => i.val)
      (fun i : rec0.endpoint.active => i.val) -
    (t : ℂ) • Matrix.diagonal (fun i : rec0.endpoint.active => rec0.r i.val) with hBm
  have hD : D⁻¹ = (trialG0 rec0).submatrix e e := by
    ext i k
    exact hinv i k
  have h1 : D⁻¹ * Bm.submatrix e e = 1 := by
    rw [hD, Matrix.submatrix_mul_equiv]
    unfold trialG0
    rw [hBG.2, Matrix.submatrix_one_equiv]
  have hu : IsUnit D.det :=
    Matrix.isUnit_nonsing_inv_det_iff.mp (Matrix.isUnit_det_of_right_inverse h1)
  have h2 : D = Bm.submatrix e e := by
    calc D = D * (D⁻¹ * Bm.submatrix e e) := by rw [h1, Matrix.mul_one]
      _ = (D * D⁻¹) * Bm.submatrix e e := by rw [Matrix.mul_assoc]
      _ = Bm.submatrix e e := by rw [Matrix.mul_nonsing_inv D hu, Matrix.one_mul]
  have h3 := congrFun (congrFun h2 ⟨a, ha⟩) ⟨b, hb⟩
  have hea : e ⟨a, ha⟩ = a := rfl
  have heb : e ⟨b, hb⟩ = b := rfl
  simp only [hDdef, hBm, AndersonAC.S6.dampedMatrix, Matrix.sub_apply, Matrix.map_apply,
    Matrix.smul_apply, Matrix.submatrix_apply, hea, heb, smul_eq_mul] at h3
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq] at h3
    have h4 : ((s.M ⟨a, ha⟩ ⟨a, hb⟩ : ℝ) : ℂ) = rec0.endpoint.M a.val a.val := by
      have := congrArg (· + (t : ℂ) * rec0.r a.val) h3
      simpa using this
    rw [← h4]
    simp
  · have hne1 : (⟨a, ha⟩ : {i // i ∈ s.active}) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
    rw [Matrix.diagonal_apply_ne _ hne1, Matrix.diagonal_apply_ne _ hab] at h3
    simp only [mul_zero, sub_zero] at h3
    rw [← h3]
    simp

/-- The initial scratch carries the trial's initial state. -/
theorem corr_init (j : ℕ) (u : ℝ) (x : Torus d m)
    (hcore : theCore (d := d) (m := m) j u x rec0 = B.map (Function.Embedding.subtype _))
    {t : ℝ} (hdamp : IsDampedEndpoint rec0.endpoint rec0.r t)
    (s : AndersonAC.S6.TrialState B) (hact : s.active = Finset.univ)
    (hG : s.hatG = trialG0 rec0)
    (hinv : ∀ i k : {i // i ∈ s.active},
      AndersonAC.S6.trialInverse t (fun i : ActiveSite rec0 => rec0.r i.val) s i k =
        trialG0 rec0 i k) :
    Corr rec0 B s (clearInitScratch (d := d) (m := m) j u x rec0) := by
  refine ⟨?_, fun a b ha hb => ?_, fun a b => ?_, fun i k _ => rfl, rfl, hcore⟩
  · show rec0.endpoint.active = _
    rw [hact, Finset.univ_eq_attach, Finset.attach_map_val]
  · show (rec0.endpoint.M a.val b.val).re = _
    exact damped_M_eq hdamp s hact hinv a b ha hb
  · show rec0.endpoint.g a.val b.val = _
    rw [hG]
    rfl

end Steps

end AndersonAC.AgentS78cbridge

/-! ## The bridge -/

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources Query Answer)
open AndersonAC.AgentS78cbridge
open Classical

/-- The sample-by-sample clearing bridge, corresponding to
`ClearingBridgeAtStatement` in `ClearingBound.lean:78`, with the damped identity
of the entering record. -/
def ClearingBridgeAtDStatement (d m : ℕ) : Prop :=
  ∀ (n₀ j : ℕ) (u : ℝ) (x : Torus d m) (M : ℕ → ℕ) (rec0 : RunRecord d m)
    (B : Finset (ActiveSite rec0)),
    theCore (d := d) (m := m) j u x rec0 = B.map (Function.Embedding.subtype _) →
    B.Nonempty → rec0.aborted = false → clearingScheduled j m →
    Disjoint rec0.endpoint.active rec0.terminal →
    IsDampedEndpoint rec0.endpoint rec0.r (stageScale u j m) →
    ∀ (order : ActiveSite rec0 ≃ Fin (Fintype.card (ActiveSite rec0))),
    (∀ a b : ActiveSite rec0, (order a).val ≤ (order b).val ↔
        (siteRank d m a.val).val ≤ (siteRank d m b.val).val) →
    ∀ (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M)
      B (stageScale u j m) (fun _ i => rec0.r i) (fun _ => trialG0 rec0) order),
    (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) →
    ∀ ω : RandomSources (Torus d m) M,
    (∀ k, k < q.stop ω → q.residual k ω = trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω
        (q.pivot k ω) (rec0.prefixLength (q.pivot k ω))) →
    (∀ k, k < q.stop ω → (q.pivot k ω).val ∉ rec0.pending ∧
      ∃ y ∈ B, physicalDistance d m (q.pivot k ω).val y.val ≤ inspectionRadius j / 2) →
    (ω ∈ localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u x) rec0 ↔
      q.outcome ω = AndersonAC.S6.TrialOutcome.fail)

/-- **Bridge to §6, sample by sample**: for a
fixed entering record with an eligible core `B` of active sites, and a stopped trial `q` on the
active sites with fixed data, at every sample `ω` whose running residuals are the true
residuals and whose running pivots pass the guard, `ω` is a block-local first failure iff the
trial fails at `ω`. -/
theorem clearingBlock_bridge {d m : ℕ} (n₀ j : ℕ) (u : ℝ) (x : Torus d m)
    (M : ℕ → ℕ) (rec0 : RunRecord d m)
    (B : Finset (ActiveSite rec0))
    (hcore : theCore (d := d) (m := m) j u x rec0 =
      B.map (Function.Embedding.subtype _))
    (hne : B.Nonempty)
    (hab : rec0.aborted = false)
    (hsch : clearingScheduled j m)
    (hdisj : Disjoint rec0.endpoint.active rec0.terminal)
    (hdamp : IsDampedEndpoint rec0.endpoint rec0.r (stageScale u j m))
    (order : ActiveSite rec0 ≃ Fin (Fintype.card (ActiveSite rec0)))
    (horder : ∀ a b : ActiveSite rec0,
      (order a).val ≤ (order b).val ↔
        (siteRank d m a.val).val ≤ (siteRank d m b.val).val)
    (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M)
      B (stageScale u j m)
      (fun _ i => rec0.r i) (fun _ => trialG0 rec0) order)
    (_hhist : ∀ k, q.history k =
      AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k)
    (ω : RandomSources (Torus d m) M)
    (hres : ∀ k, k < q.stop ω →
      q.residual k ω = trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω
        (q.pivot k ω) (rec0.prefixLength (q.pivot k ω)))
    (hguard : ∀ k, k < q.stop ω →
      (q.pivot k ω).val ∉ rec0.pending ∧
      ∃ y ∈ B, physicalDistance d m (q.pivot k ω).val y.val ≤
        inspectionRadius j / 2) :
    ω ∈ localFirstFail M (clearingBlock (d := d) (m := m) n₀ j u x) rec0 ↔
      q.outcome ω = AndersonAC.S6.TrialOutcome.fail := by
  let st : ℕ → RunRecord d m × ClearScratch d m := fun k =>
    localState M (clearingBlock (d := d) (m := m) n₀ j u x) rec0 k ω
  have hst_succ : ∀ k, ∃ L, st (k + 1) = clearingUpdate (d := d) (m := m) n₀ j u (st k)
      (localAnswer (Torus d m) M L (clearingNext (d := d) (m := m) n₀ j u (st k)) ω) :=
    fun _ => ⟨_, rfl⟩
  have hst0 : st 0 = (rec0, clearInitScratch (d := d) (m := m) j u x rec0) := rfl
  have hfst : ∀ k, (st k).1 = rec0 := fun k =>
    state_fst (n₀ := n₀) (j := j) (u := u) (x := x) (M := M) rec0 k ω
  have hstk : ∀ k, st k = (rec0, (st k).2) := fun k => Prod.ext (hfst k) rfl
  have hcoreB : B.map (Function.Embedding.subtype _) ≠ ∅ := by
    rw [Ne, Finset.map_eq_empty]
    exact hne.ne_empty
  have hcoreK : ∀ k, (st k).2.core ≠ ∅ := fun k => by
    rw [state_core (n₀ := n₀) (j := j) (u := u) (x := x) (M := M) rec0 k ω, hcore]
    exact hcoreB
  have hi_f : (clearInitScratch (d := d) (m := m) j u x rec0).failed = false := rfl
  have hi_d : (clearInitScratch (d := d) (m := m) j u x rec0).done = false := by
    unfold clearInitScratch
    simp [hab, hsch, hcore, hcoreB]
  have hhalt : ∀ k, (clearingBlock (d := d) (m := m) n₀ j u x).halted (st k) =
      ((st k).2.failed || (st k).2.done) := fun _ => rfl
  have hffail : ∀ k, (clearingBlock (d := d) (m := m) n₀ j u x).firstFail (st k) =
      (st k).2.failed := fun _ => rfl
  -- the final characterization from the two run facts
  suffices hfacts : (q.outcome ω = .done → ∀ k, (st k).2.failed = false) ∧
      (q.outcome ω = .fail → ∃ k, (∀ k' < k, (st k').2.failed = false ∧ (st k').2.done = false) ∧
        (st k).2.failed = true) by
    constructor
    · rintro ⟨k, -, hk⟩
      cases ho : q.outcome ω with
      | fail => rfl
      | done =>
        have := hfacts.1 ho k
        rw [hffail, this] at hk
        exact absurd hk Bool.false_ne_true
    · intro ho
      obtain ⟨k, hlt, hk⟩ := hfacts.2 ho
      refine ⟨k, fun k' hk' => ?_, ?_⟩
      · rw [hhalt, (hlt k' hk').1, (hlt k' hk').2]
        rfl
      · rw [hffail]; exact hk
  by_cases hN : AndersonAC.S6.heatLimit (stageScale u j m) = 0
  · -- no heat is allowed: both fail at once
    have hfail1 : (st 1).2.failed = true := by
      obtain ⟨po, hpo⟩ := actionOf_fail_of (d := d) (m := m) j u rec0
        (clearInitScratch (d := d) (m := m) j u x rec0) hi_f hi_d
        (by have := hcoreK 0; rwa [hst0] at this) rfl
        (by rintro ⟨-, -, hlt, -⟩; rw [hN] at hlt; exact Nat.not_lt_zero _ hlt)
      obtain ⟨L, hL⟩ := hst_succ 0
      rw [hL, hst0]
      exact update_fail_eq n₀ j u _ _ hi_f hi_d po hpo
    refine ⟨fun ho => ?_, fun _ => ⟨1, fun k' hk' => ?_, hfail1⟩⟩
    · exfalso
      have := ((q.done_iff ω).mp ho).1
      rw [hN] at this
      exact Nat.not_lt_zero _ this
    · obtain rfl : k' = 0 := by omega
      rw [hst0]
      exact ⟨hi_f, hi_d⟩
  -- positive scale
  have ht : 0 < stageScale u j m := by
    by_contra h
    exact hN (heatLimit_eq_zero_of_nonpos (not_lt.mp h))
  have hl : 0 < AndersonAC.S6.leverageScale (stageScale u j m) := leverageScale_pos ht
  -- the carried trial data at a running time
  have hrun0 : Corr rec0 B (q.state 0 ω) (st 0).2 ∧ (st 0).2.failed = false ∧
      (st 0).2.done = false ∧ (st 0).2.corePhase = false ∧ (st 0).2.step = 0 ∧
      (st 0).2.ridge = q.ridge 0 ω := by
    have hc : Corr rec0 B (q.state 0 ω) (st 0).2 := by
      rw [hst0]
      exact corr_init j u x hcore hdamp (q.state 0 ω) (q.initial_active ω) (q.start_entries ω)
        (q.initial_inverse ω)
    refine ⟨hc, by rw [hst0]; rfl, by rw [hst0]; exact hi_d, by rw [hst0]; rfl, by rw [hst0]; rfl, ?_⟩
    rw [q.start_ridge ω]
    have := (hc.facts (stageScale u j m)).2.2.2.1 (AndersonAC.S6.leverageScale (stageScale u j m))
      (AndersonAC.S6.leverageScale (stageScale u j m) ^ (-2 : ℤ))
    rw [← this, hst0]
    rfl
  -- one heat from a running time
  have hstep : ∀ k, k < q.stop ω →
      (Corr rec0 B (q.state k ω) (st k).2 ∧ (st k).2.failed = false ∧
        (st k).2.done = false ∧ (st k).2.corePhase = false ∧ (st k).2.step = k ∧
        (st k).2.ridge = q.ridge k ω) → ∃ sc1 : ClearScratch d m,
      st (k + 1) = (rec0, heatPost j u rec0 (st k).2 sc1) ∧
      Corr rec0 B (q.state (k + 1) ω) sc1 ∧ sc1.failed = false ∧ sc1.done = false ∧
      sc1.corePhase = false ∧ sc1.step = k + 1 ∧
      sc1.ridge = AndersonAC.S6.chooseRidge
        (AndersonAC.S6.trialCross (stageScale u j m) (fun i : ActiveSite rec0 => rec0.r i.val)
          (q.state (k + 1) ω))
        (AndersonAC.S6.leverageScale (stageScale u j m)) (q.ridge k ω) ∧
      sc1.g0 = (st k).2.g0 := by
    intro k hk ⟨hc, hf, hd, hcp, hstp, hrdg⟩
    have hheat := q.heat k ω hk
    obtain ⟨hw, -, hmw, -, hrd⟩ := hc.facts (stageScale u j m)
    have hbud : AndersonAC.S6.BudgetsHold (stageScale u j m) (st k).2.g0 (st k).2.hatG :=
      (hc.budgets ht).mpr (q.running_budgets k ω hk)
    have hlim : (st k).2.step < AndersonAC.S6.heatLimit (stageScale u j m) := by
      rw [hstp]; exact lt_of_lt_of_le hk (q.finite_stop ω)
    have hcapq := q.running_cap k ω hk
    have hcap : AndersonAC.S6.maxWeight
        (scratchWeights (stageScale u j m) rec0.r (st k).2 (st k).2.ridge) ≤
        4 * AndersonAC.S6.leverageScale (stageScale u j m) := by
      rw [hmw, hrdg]; exact hcapq.2
    have hnr : ¬ xReady (stageScale u j m) rec0.r (st k).2.active
        (restrictM (st k).2.active (st k).2.Mnum) (st k).2.core := by
      intro hready
      have hr' := (hrd hl.le).mp hready
      have := maxWeight_lt_of_ready _ hl (q.running_ridge k ω hk) hr'
      have h2 := hcapq.1
      unfold AndersonAC.S6.trialWeights at h2
      linarith
    have hpos : 0 < AndersonAC.S6.maxWeight
        (AndersonAC.S6.trialWeights (stageScale u j m) (fun i : ActiveSite rec0 => rec0.r i.val)
          (q.state k ω) (q.ridge k ω)) := by linarith [hcapq.1]
    have hcand : candPivot rec0.r (st k).2 (stageScale u j m) (st k).2.ridge =
        some (q.pivot k ω).val := by
      rw [hrdg]
      exact hc.candPivot_eq order horder (q.pivot k ω) hpos (q.pivot_max k ω hk)
        (fun i hi => q.pivot_tie k ω i hk hi)
    have hg : guardHolds (d := d) (m := m) j (st k).2.core (coupledActive rec0) rec0.terminal
        (q.pivot k ω).val := by
      obtain ⟨hpend, y, hyB, hy⟩ := hguard k hk
      refine ⟨?_, ?_, ⟨y.val, (hc.mem_core y).mpr hyB, hy⟩⟩
      · simp only [coupledActive, Finset.mem_sdiff]
        exact ⟨(q.pivot k ω).property, hpend⟩
      · exact Finset.disjoint_left.mp hdisj (q.pivot k ω).property
    have hpc : (q.pivot k ω).val ∉ (st k).2.core := by
      obtain ⟨-, hxc, -⟩ := hheat
      exact fun h => hxc ((hc.mem_core _).mp h)
    have hact := actionOf_heat_eq (d := d) (m := m) j u rec0 (st k).2 hf hd (hcoreK k) hcp
      hc.core_sub hbud hlim hcap hnr (q.pivot k ω).val hcand hg hpc
    obtain ⟨L, hL⟩ := hst_succ k
    rw [hstk k] at hL
    have hnext := next_heat_eq (d := d) (m := m) n₀ j u (rec0, (st k).2) (q.pivot k ω).val hg hact
    rw [hnext] at hL
    rw [update_heat_eq (d := d) (m := m) n₀ j u (rec0, (st k).2) _ hf hd (q.pivot k ω).val hg
      hact] at hL
    have hξ : residOfAnswer (d := d) (m := m) (clearingLam n₀ u) (q.pivot k ω).val
        (rec0.prefixLength (q.pivot k ω).val)
        (localAnswer (Torus d m) M L
          (Query.trueSuffix (q.pivot k ω).val (rec0.prefixLength (q.pivot k ω).val)) ω) =
        q.residual k ω := by
      rw [resid_trueSuffix, hres k hk]
      rfl
    have hc1 : Corr rec0 B (q.state (k + 1) ω) (heatScratch n₀ j u rec0 (st k).2
        (q.pivot k ω).val (localAnswer (Torus d m) M L
          (Query.trueSuffix (q.pivot k ω).val (rec0.prefixLength (q.pivot k ω).val)) ω)) := by
      refine hc.heat hheat _ ?_ ?_ rfl rfl rfl
      · simp only [heatScratch]
        rw [hξ]
      · simp only [heatScratch]
        rw [hξ]
    refine ⟨_, hL, hc1, hf, hd, hcp, by simp [heatScratch, hstp], ?_, rfl⟩
    rw [← hrdg]
    exact (hc1.facts (stageScale u j m)).2.2.2.1 _ _
  -- every running time carries the trial state
  have hrun : ∀ k, (k < q.stop ω ∨ k = 0) →
      (Corr rec0 B (q.state k ω) (st k).2 ∧ (st k).2.failed = false ∧
        (st k).2.done = false ∧ (st k).2.corePhase = false ∧ (st k).2.step = k ∧
        (st k).2.ridge = q.ridge k ω) := by
    intro k
    induction k with
    | zero => intro _; exact hrun0
    | succ k ih =>
      intro hk
      have hk' : k + 1 < q.stop ω := by omega
      obtain ⟨sc1, hst, hc1, hf1, hd1, hcp1, hs1, hr1, hg1⟩ :=
        hstep k (by omega) (ih (Or.inl (by omega)))
      have hb1 : AndersonAC.S6.BudgetsHold (stageScale u j m) (st k).2.g0 sc1.hatG := by
        rw [← hg1]; exact (hc1.budgets ht).mpr (q.running_budgets (k + 1) ω hk')
      have hl1 : sc1.step < AndersonAC.S6.heatLimit (stageScale u j m) := by
        rw [hs1]; exact lt_of_lt_of_le hk' (q.finite_stop ω)
      have hridge1 : sc1.ridge = q.ridge (k + 1) ω := by rw [hr1, q.ridge_rule k ω hk']
      obtain ⟨-, -, hmw1, -, hrd1⟩ := hc1.facts (stageScale u j m)
      have hcapq := q.running_cap (k + 1) ω hk'
      have hc3 : AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rec0.r sc1 sc1.ridge) ≤
          4 * AndersonAC.S6.leverageScale (stageScale u j m) := by
        rw [hmw1, hridge1]; exact hcapq.2
      have hnr1 : ¬ xReady (stageScale u j m) rec0.r sc1.active (restrictM sc1.active sc1.Mnum)
          sc1.core := by
        intro hready
        have hr' := (hrd1 hl.le).mp hready
        have := maxWeight_lt_of_ready _ hl (q.running_ridge (k + 1) ω hk') hr'
        have h2 := hcapq.1
        unfold AndersonAC.S6.trialWeights at h2
        linarith
      rw [heatPost_cont j u rec0 (st k).2 sc1 hb1 hl1 hc3 hnr1] at hst
      rw [hst]
      exact ⟨hc1, hf1, hd1, hcp1, hs1, hridge1⟩
  refine ⟨fun ho => ?_, fun ho => ?_⟩
  · -- the trial is done: the block reaches the core phase without failing
    obtain ⟨hlt, hbS, hrS⟩ := (q.done_iff ω).mp ho
    have hreach : ∃ n, (∀ k ≤ n, (st k).2.failed = false) ∧ (st n).2.corePhase = true := by
      rcases Nat.eq_zero_or_pos (q.stop ω) with h0 | hpos
      · obtain ⟨hc, hf, hd, hcp, hs, hr⟩ := hrun 0 (Or.inr rfl)
        rw [h0] at hlt hbS hrS
        obtain ⟨-, -, hmw, -, hrd⟩ := hc.facts (stageScale u j m)
        have hcap : AndersonAC.S6.maxWeight
            (scratchWeights (stageScale u j m) rec0.r (st 0).2 (st 0).2.ridge) ≤
            4 * AndersonAC.S6.leverageScale (stageScale u j m) := by
          rw [hmw, hr, q.start_ridge ω]
          have := maxWeight_chooseRidge_le_of_ready _ hl.le (zpow_pos hl (-2 : ℤ)) hrS
          unfold AndersonAC.S6.trialWeights
          linarith
        have hact := actionOf_ready_eq (d := d) (m := m) j u rec0 (st 0).2 hf hd (hcoreK 0) hcp
          hc.core_sub ((hc.budgets ht).mpr hbS) (by rw [hs]; exact hlt) hcap
          ((hrd hl.le).mpr hrS)
        obtain ⟨L, hL⟩ := hst_succ 0
        rw [hstk 0] at hL
        have hu := update_ready_eq n₀ j u (rec0, (st 0).2)
          (localAnswer (Torus d m) M L (clearingNext (d := d) (m := m) n₀ j u (rec0, (st 0).2)) ω)
          hf hd hact
        refine ⟨1, fun k hk => ?_, by rw [hL]; exact hu.1⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
        · exact hf
        · rw [hL]; exact hu.2
      · obtain ⟨k, hk⟩ : ∃ k, q.stop ω = k + 1 := ⟨q.stop ω - 1, by omega⟩
        obtain ⟨sc1, hst, hc1, hf1, -, -, hs1, hr1, hg1⟩ :=
          hstep k (by omega) (hrun k (Or.inl (by omega)))
        rw [hk] at hlt hbS hrS
        obtain ⟨-, -, hmw1, -, hrd1⟩ := hc1.facts (stageScale u j m)
        have hb1 : AndersonAC.S6.BudgetsHold (stageScale u j m) (st k).2.g0 sc1.hatG := by
          rw [← hg1]; exact (hc1.budgets ht).mpr hbS
        have hl1 : sc1.step < AndersonAC.S6.heatLimit (stageScale u j m) := by rw [hs1]; exact hlt
        have hc3 : AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rec0.r sc1 sc1.ridge) ≤
            4 * AndersonAC.S6.leverageScale (stageScale u j m) := by
          rw [hmw1, hr1]
          have := maxWeight_chooseRidge_le_of_ready _ hl.le (q.running_ridge k ω (by omega)) hrS
          unfold AndersonAC.S6.trialWeights
          linarith
        have hp := heatPost_ready j u rec0 (st k).2 sc1 hb1 hl1 hc3 ((hrd1 hl.le).mpr hrS)
        refine ⟨k + 1, fun k' hk' => ?_, by rw [hst]; exact hp.1⟩
        rcases Nat.lt_or_ge k' (k + 1) with h | h
        · exact (hrun k' (Or.inl (by omega))).2.1
        · obtain rfl : k' = k + 1 := by omega
          rw [hst]; exact hp.2.trans hf1
    obtain ⟨n, hn, hcpn⟩ := hreach
    intro k
    rcases le_or_gt k n with hkn | hnk
    · exact hn k hkn
    · exact future_no_fail (n₀ := n₀) (j := j) (u := u) (x := x) (M := M) rec0 n ω hcpn
        (hn n le_rfl) k hnk.le
  · -- the trial fails: the block fails at the same step
    have hfr := q.fail_reason ω ho
    rcases Nat.eq_zero_or_pos (q.stop ω) with h0 | hpos
    · obtain ⟨hc, hf, hd, hcp, hs, hr⟩ := hrun 0 (Or.inr rfl)
      rw [h0] at hfr
      obtain ⟨-, -, hmw, -, -⟩ := hc.facts (stageScale u j m)
      have hnot : ¬ ((st 0).2.core ⊆ (st 0).2.active ∧
          AndersonAC.S6.BudgetsHold (stageScale u j m) (st 0).2.g0 (st 0).2.hatG ∧
          (st 0).2.step < AndersonAC.S6.heatLimit (stageScale u j m) ∧
          AndersonAC.S6.maxWeight (scratchWeights (stageScale u j m) rec0.r (st 0).2
            (st 0).2.ridge) ≤ 4 * AndersonAC.S6.leverageScale (stageScale u j m)) := by
        rintro ⟨-, hb, -, hcap⟩
        rcases hfr with h | h | h
        · exact hN h.symm
        · exact h ((hc.budgets ht).mp hb)
        · rw [hmw, hr] at hcap
          unfold AndersonAC.S6.trialWeights at hcap
          simp only [Nat.zero_sub] at h
          unfold AndersonAC.S6.trialWeights at h
          linarith
      obtain ⟨po, hpo⟩ := actionOf_fail_of (d := d) (m := m) j u rec0 (st 0).2 hf hd (hcoreK 0)
        hcp hnot
      obtain ⟨L, hL⟩ := hst_succ 0
      rw [hstk 0] at hL
      refine ⟨1, fun k' hk' => ?_, ?_⟩
      · obtain rfl : k' = 0 := by omega
        exact ⟨hf, hd⟩
      · rw [hL]; exact update_fail_eq n₀ j u _ _ hf hd po hpo
    · obtain ⟨k, hk⟩ : ∃ k, q.stop ω = k + 1 := ⟨q.stop ω - 1, by omega⟩
      obtain ⟨sc1, hst, hc1, -, -, -, hs1, hr1, hg1⟩ :=
        hstep k (by omega) (hrun k (Or.inl (by omega)))
      rw [hk] at hfr
      obtain ⟨-, -, hmw1, -, -⟩ := hc1.facts (stageScale u j m)
      have hpf : (heatPost j u rec0 (st k).2 sc1).failed = true := by
        apply heatPost_failed
        rcases hfr with h | h | h
        · right; left; rw [hs1, h]
        · left
          intro hb
          rw [← hg1] at hb
          exact h ((hc1.budgets ht).mp hb)
        · right; right
          simp only [Nat.add_sub_cancel] at h
          unfold AndersonAC.S6.trialWeights at h
          have hridge : sc1.ridge = q.ridge k ω := by
            rw [hr1]
            unfold AndersonAC.S6.chooseRidge
            rw [if_neg]
            intro hlt2
            linarith
          rw [hmw1, hridge]
          unfold AndersonAC.S6.trialWeights
          exact h
      refine ⟨k + 1, fun k' hk' => ?_, by rw [hst]; exact hpf⟩
      have := hrun k' (Or.inl (by omega))
      exact ⟨this.2.1, this.2.2.1⟩

/-- The bridge statement holds. -/
theorem clearingBridgeAtD_proof (d m : ℕ) : ClearingBridgeAtDStatement d m :=
  fun n₀ j u x M rec0 B hcore hne hab hsch hdisj hdamp order horder q hhist ω hres hguard =>
    clearingBlock_bridge n₀ j u x M rec0 B hcore hne hab hsch hdisj hdamp order horder q hhist ω
      hres hguard

end AndersonAC.AgentS78
