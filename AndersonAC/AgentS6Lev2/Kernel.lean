import AndersonAC.AgentS6Lev2.Discharge
import AndersonAC.AgentS6Row.TrialBridge

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Matrix

namespace AndersonAC.AgentS6Lev2
open AndersonAC.S6 AndersonAC.AgentS6

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]

theorem measurable_damped (t : ℝ) {M : α → Matrix ι ι ℝ} {r : α → ι → ℂ}
    (hM : Measurable M) (hr : Measurable r) :
    Measurable (fun a => AndersonAC.L64.damped (M a) t (r a)) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [AndersonAC.L64.damped, Matrix.sub_apply, Matrix.map_apply,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  exact (Complex.measurable_ofReal.comp hM.eval_matrix).sub
    (measurable_const.mul (by split_ifs <;> first | exact hr.eval | exact measurable_const))

theorem measurable_scat (t : ℝ) {r : α → ι → ℂ} {G : α → Matrix ι ι ℂ}
    (hr : Measurable r) (hG : Measurable G) :
    Measurable (fun a => AndersonAC.L64.scat t (AndersonAC.L64.pim (r a)) (G a)) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [AndersonAC.L64.scat_apply, AndersonAC.L64.pim]
  have hs (i : ι) : Measurable (fun a => (Real.sqrt ((r a i).im) : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (Complex.measurable_im.comp hr.eval))
  exact measurable_const.add (((measurable_const.mul (hs i)).mul (hs j)).mul hG.eval_matrix)

theorem measurable_ridgeLev (B R : Finset ι) (i : ι)
    {S : α → Matrix ι ι ℂ} {τ : α → ℝ} (hS : Measurable S) (hτ : Measurable τ) :
    Measurable (fun a => AndersonAC.L64.ridgeLev (S a) B R (τ a) i) := by
  have hgram : Measurable (fun a => AndersonAC.L64.gram (S a) B R + (τ a : ℂ) • 1) := by
    refine Measurable.of_eval_matrix _ fun b c => ?_
    simp only [AndersonAC.L64.gram, Matrix.add_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, AndersonAC.L64.crossRow,
      Matrix.smul_apply, smul_eq_mul]
    exact (Finset.measurable_sum _ fun j _ => (continuous_star.measurable.comp hS.eval_matrix).mul hS.eval_matrix).add
      ((Complex.measurable_ofReal.comp hτ).mul measurable_const)
  have hH := AndersonAC.AgentS6.measurable_matrix_inv.comp hgram
  simp only [AndersonAC.L64.ridgeLev, dotProduct, Matrix.mulVec,
    AndersonAC.L64.crossRow, Pi.star_apply]
  exact Complex.measurable_re.comp (Finset.measurable_sum _ fun b _ =>
    hS.eval_matrix.mul (Finset.measurable_sum _ fun c _ => hH.eval_matrix.mul (continuous_star.measurable.comp hS.eval_matrix)))

def l64Delta (square : Bool) (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ)
    (B : Finset ι) (x : ι) (τ y : ℝ) : ℝ :=
  if square then AndersonAC.L64.postP M t r B x τ y - AndersonAC.L64.preP M t r B τ
  else AndersonAC.L64.postA M t r B x τ y - AndersonAC.L64.preA M t r B τ

theorem measurable_l64Delta (square : Bool) (t : ℝ) (B : Finset ι) (x : ι)
    {M : α → Matrix ι ι ℝ} {r : α → ι → ℂ} {τ y : α → ℝ}
    (hM : Measurable M) (hr : Measurable r) (hτ : Measurable τ) (hy : Measurable y) :
    Measurable (fun a => l64Delta square (M a) t (r a) B x (τ a) (y a)) := by
  have hD := measurable_damped t hM hr
  have hDpost : Measurable (fun a => AndersonAC.L64.dampedPost (M a) t (r a) x (y a)) := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    simp only [AndersonAC.L64.dampedPost, Matrix.add_apply, Matrix.diagonal_apply,
      Pi.single_apply]
    exact hD.eval_matrix.add (by
      split_ifs <;> first | exact (Complex.measurable_ofReal.comp hy).add (measurable_const.mul hr.eval) | exact measurable_const)
  have hS := measurable_scat t hr (AndersonAC.AgentS6.measurable_matrix_inv.comp hD)
  have hSp := measurable_scat t hr (AndersonAC.AgentS6.measurable_matrix_inv.comp hDpost)
  cases square <;> simp only [l64Delta, Bool.false_eq_true, ↓reduceIte,
    AndersonAC.L64.preA, AndersonAC.L64.postA, AndersonAC.L64.preP, AndersonAC.L64.postP,
    AndersonAC.L64.preLev, AndersonAC.L64.postLev]
  · exact (Finset.measurable_sum _ fun i _ => measurable_ridgeLev B (Bᶜ.erase x) i hSp hτ).sub
      (Finset.measurable_sum _ fun i _ => measurable_ridgeLev B Bᶜ i hS hτ)
  · exact (Finset.measurable_sum _ fun i _ => (measurable_ridgeLev B (Bᶜ.erase x) i hSp hτ).pow_const 2).sub
      (Finset.measurable_sum _ fun i _ => (measurable_ridgeLev B Bᶜ i hS hτ).pow_const 2)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
  {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
  {order : Fin n ≃ Fin (Fintype.card (Fin n))}

/-- Conditional residual law with the history sigma algebra fixed explicitly. -/
def residualLaw (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (ω : Ω) : Measure ℝ :=
  (@ProbabilityTheory.condDistrib Ω Ω ℝ _ _ _ mΩ (q.history k)
    (q.residual k) id μ _) ω

/-- Recover the real prestate matrix from the recorded active inverse. -/
def recoveredM (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ)
    (A : Finset (Fin n)) (ω : Ω) : Matrix A A ℝ :=
  fun i j => (((q.state k ω).hatG.submatrix Subtype.val Subtype.val)⁻¹ i j +
    if i = j then (t : ℂ) * r ω i else 0).re

theorem recoveredM_eq (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (ω : Ω) (hk : k ≤ q.stop ω) (ht : 0 < t)
    (hr : ∀ i, 0 < (r ω i).im) :
    recoveredM q k (q.state k ω).active ω = (q.state k ω).M := by
  have hG : (q.state k ω).hatG.submatrix Subtype.val Subtype.val =
      trialInverse t (r ω) (q.state k ω) := by
    ext i j; exact hatG_eq_trialInverse q k ω hk i j
  have hD := damped_isUnit (q.state k ω).M (q.state k ω).symmetric ht _ (fun i => hr i)
  ext i j
  simp only [recoveredM, hG, trialInverse, activeInverse,
    Matrix.nonsing_inv_nonsing_inv _ hD, damped_apply]
  split_ifs <;> simp

theorem measurable_recoveredM (q : StoppedTrial (Ω := Ω) core t r g0 order)
    (k : ℕ) (A : Finset (Fin n)) : Measurable[q.history k] (recoveredM q k A) := by
  have hG : Measurable[q.history k] (fun ω => (q.state k ω).hatG.submatrix
      (Subtype.val : A → Fin n) Subtype.val) :=
    @Measurable.of_eval_matrix A A ℂ _ Ω (q.history k) _ fun i j =>
      (q.entries_adapted k i.val j.val).measurable
  have hH := AndersonAC.AgentS6.measurable_matrix_inv.comp hG
  have hr : Measurable[q.history k] (r : Ω → Fin n → ℂ) :=
    (q.damping_adapted.mono (q.history.mono (Nat.zero_le k))).measurable
  let f := recoveredM q k A
  change Measurable[q.history k] f
  letI : MeasurableSpace Ω := q.history k
  refine Measurable.of_eval_matrix f fun i j => ?_
  simp only [f, recoveredM]
  exact Complex.measurable_re.comp (hH.eval_matrix.add (by
    split_ifs <;> first | exact measurable_const.mul hr.eval | exact measurable_const))

end AndersonAC.AgentS6Lev2

#print axioms AndersonAC.AgentS6Lev2.recoveredM_eq
#print axioms AndersonAC.AgentS6Lev2.measurable_recoveredM
#print axioms AndersonAC.AgentS6Lev2.measurable_l64Delta
