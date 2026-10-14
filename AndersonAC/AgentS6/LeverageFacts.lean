import AndersonAC.S6Deriv.RidgeDerivative

/-! Ridge-leverage facts used by the heat count of Proposition 6.6 (06-clearing.tex:340–375,
650–684): nonnegativity, total at most `|B|`, joint measurability in `(C, τ)`, invariance under
reindexing the core, and continuity/antitonicity on `τ > 0` (from the proved ridge derivative). -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Filter Set

namespace AndersonAC.AgentS6

open AndersonAC.S6

variable {R B : Type*} [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B]

theorem ridgeGram_posSemidef (C : Matrix R B ℂ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (ridgeGram C τ).PosSemidef := by
  unfold ridgeGram gram
  refine (Matrix.posSemidef_conjTranspose_mul_self C).add ?_
  have h1 : (1 : Matrix B B ℂ).PosSemidef := Matrix.PosSemidef.one
  have : (τ : ℂ) • (1 : Matrix B B ℂ) = Matrix.diagonal (fun _ => (τ : ℂ)) := by
    ext i j; simp [Matrix.diagonal, Matrix.one_apply]
  rw [this]
  exact Matrix.PosSemidef.diagonal (fun _ => Complex.zero_le_real.mpr hτ)

theorem quad_entry (C : Matrix R B ℂ) (H : Matrix B B ℂ) (i : R) :
    (C * H * Cᴴ) i i = star (fun b => star (C i b)) ⬝ᵥ (H *ᵥ (fun b => star (C i b))) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem leverage_nonneg (C : Matrix R B ℂ) {τ : ℝ} (hτ : 0 ≤ τ) (i : R) :
    0 ≤ leverage C τ i := by
  unfold leverage ridgeProjection
  have hH : ((ridgeGram C τ)⁻¹).PosSemidef := (ridgeGram_posSemidef C hτ).inv
  rw [quad_entry]
  exact (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg _)).1

theorem ridgeGram_isUnit (C : Matrix R B ℂ) {τ : ℝ} (hτ : 0 < τ) :
    IsUnit (ridgeGram C τ).det := by
  have hpd : (ridgeGram C τ).PosDef := by
    unfold ridgeGram gram
    have : (τ : ℂ) • (1 : Matrix B B ℂ) = Matrix.diagonal (fun _ => (τ : ℂ)) := by
      ext i j; simp [Matrix.diagonal, Matrix.one_apply]
    rw [this]
    exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self C)
      (Matrix.PosDef.diagonal (fun _ => Complex.zero_lt_real.mpr hτ))
  exact (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit

theorem totalWeight_leverage_le (C : Matrix R B ℂ) {τ : ℝ} (hτ : 0 < τ) :
    totalWeight (leverage C τ) ≤ (Fintype.card B : ℝ) := by
  set G := ridgeGram C τ
  set H := G⁻¹
  have hunit := ridgeGram_isUnit C hτ
  have hHG : H * G = 1 := Matrix.nonsing_inv_mul G hunit
  have htr : (C * H * Cᴴ).trace = (Fintype.card B : ℂ) - (τ : ℂ) * H.trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have hG : Cᴴ * C = G - (τ : ℂ) • 1 := by
      simp only [G, ridgeGram, gram]; abel
    rw [hG, Matrix.mul_sub, hHG, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  have hHpsd : H.PosSemidef := (ridgeGram_posSemidef C hτ.le).inv
  have hHtr : 0 ≤ H.trace.re := (Complex.nonneg_iff.mp hHpsd.trace_nonneg).1
  have hsum : totalWeight (leverage C τ) = (C * H * Cᴴ).trace.re := by
    unfold totalWeight leverage ridgeProjection Matrix.trace
    simp only [Matrix.diag_apply, Complex.re_sum]
    rfl
  rw [hsum, htr]
  simp only [Complex.sub_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith

theorem le_maxWeight (m : R → ℝ) (i : R) : m i ≤ maxWeight m := by
  unfold maxWeight
  have h : Real.toNNReal (m i) ≤ Finset.univ.sup (fun i => Real.toNNReal (m i)) :=
    Finset.le_sup (f := fun i => Real.toNNReal (m i)) (Finset.mem_univ i)
  calc m i ≤ (Real.toNNReal (m i) : ℝ) := Real.le_coe_toNNReal (m i)
    _ ≤ _ := by exact_mod_cast h

theorem maxWeight_le {m : R → ℝ} {a : ℝ} (ha : 0 ≤ a) (h : ∀ i, m i ≤ a) :
    maxWeight m ≤ a := by
  unfold maxWeight
  have : Finset.univ.sup (fun i => Real.toNNReal (m i)) ≤ Real.toNNReal a :=
    Finset.sup_le fun i _ => Real.toNNReal_le_toNNReal (h i)
  calc ((Finset.univ.sup (fun i => Real.toNNReal (m i)) : NNReal) : ℝ) ≤ (Real.toNNReal a : ℝ) := by
        exact_mod_cast this
    _ = a := Real.coe_toNNReal a ha

/-! Measurability. -/

section Meas

variable {α : Type*} [MeasurableSpace α]

theorem measurable_matrix_mul {m n o : Type*} [Fintype n]
    {f : α → Matrix m n ℂ} {g : α → Matrix n o ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x * g x) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => hf.eval_matrix.mul hg.eval_matrix

theorem measurable_matrix_inv {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable (fun A : Matrix n n ℂ => A⁻¹) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  have hdet : Measurable (fun A : Matrix n n ℂ => A.det) :=
    (continuous_id.matrix_det).measurable
  have hadj : Measurable (fun A : Matrix n n ℂ => A.adjugate i j) :=
    ((continuous_id.matrix_adjugate).matrix_elem i j).measurable
  exact (hdet.inv).mul hadj

theorem measurable_leverage (i : R) :
    Measurable (fun p : Matrix R B ℂ × ℝ => leverage p.1 p.2 i) := by
  unfold leverage ridgeProjection ridgeGram gram
  have hC : Measurable (fun p : Matrix R B ℂ × ℝ => p.1) := measurable_fst
  have hCt : Measurable (fun p : Matrix R B ℂ × ℝ => p.1ᴴ) :=
    (continuous_fst.matrix_conjTranspose).measurable
  have hG : Measurable (fun p : Matrix R B ℂ × ℝ => p.1ᴴ * p.1 + ((p.2 : ℂ)) • (1 : Matrix B B ℂ)) :=
    (Continuous.add (continuous_fst.matrix_conjTranspose.matrix_mul continuous_fst)
      ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)).measurable
  have hM := measurable_matrix_mul (measurable_matrix_mul hC (measurable_matrix_inv.comp hG)) hCt
  exact Complex.measurable_re.comp hM.eval_matrix

end Meas

/-! Reindexing the core and the ridge derivative. -/

theorem ridgeProjection_reindex {B' : Type*} [Fintype B'] [DecidableEq B']
    (C : Matrix R B ℂ) (e : B' ≃ B) (τ : ℝ) :
    ridgeProjection (C.submatrix id e) τ = ridgeProjection C τ := by
  unfold ridgeProjection ridgeGram gram
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul Cᴴ C e id e Function.bijective_id]
  have hG : (Cᴴ * C).submatrix e e + ((τ : ℂ) • (1 : Matrix B' B' ℂ)) =
      (Cᴴ * C + (τ : ℂ) • (1 : Matrix B B ℂ)).submatrix e e := by
    ext a b
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [hG, Matrix.inv_submatrix_equiv, ← Matrix.submatrix_mul C _ id e e e.bijective,
    ← Matrix.submatrix_mul _ Cᴴ id e id e.bijective]
  rfl

theorem leverage_reindex {B' : Type*} [Fintype B'] [DecidableEq B']
    (C : Matrix R B ℂ) (e : B' ≃ B) (τ : ℝ) (i : R) :
    leverage (C.submatrix id e) τ i = leverage C τ i := by
  unfold leverage; rw [ridgeProjection_reindex]

theorem leverage_hasDerivAt {n : ℕ} (C : Matrix (Fin n) B ℂ) (i : Fin n) {τ : ℝ} (hτ : 0 < τ) :
    ∃ D : ℝ, D ≤ 0 ∧ HasDerivAt (fun s => leverage C s i) D τ := by
  set e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  obtain ⟨h1, h2⟩ := AndersonAC.SolS6.ridgeDerivative_proof (Fintype.card B) n
    (C.submatrix id e) i τ hτ
  have hfun : (fun s => leverage (C.submatrix id e) s i) = (fun s => leverage C s i) := by
    funext s; exact leverage_reindex C e s i
  rw [hfun] at h1
  exact ⟨_, neg_nonpos.mpr h2, h1⟩

theorem leverage_continuousOn {n : ℕ} (C : Matrix (Fin n) B ℂ) (i : Fin n) :
    ContinuousOn (fun s => leverage C s i) (Ioi 0) := fun τ hτ =>
  (leverage_hasDerivAt C i hτ).choose_spec.2.continuousAt.continuousWithinAt

theorem leverage_antitoneOn {n : ℕ} (C : Matrix (Fin n) B ℂ) (i : Fin n) :
    AntitoneOn (fun s => leverage C s i) (Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) (leverage_continuousOn C i) ?_ ?_
  · rw [interior_Ioi]
    exact fun τ hτ => (leverage_hasDerivAt C i hτ).choose_spec.2.differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro τ hτ
    obtain ⟨D, hD, hd⟩ := leverage_hasDerivAt C i hτ
    rw [hd.deriv]; exact hD

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.leverage_nonneg
#print axioms AndersonAC.AgentS6.totalWeight_leverage_le
#print axioms AndersonAC.AgentS6.measurable_leverage
#print axioms AndersonAC.AgentS6.leverage_antitoneOn
#print axioms AndersonAC.AgentS6.leverage_continuousOn
