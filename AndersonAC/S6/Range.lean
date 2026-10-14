import AndersonAC.S6.Commutator
import AndersonAC.S6.Localization
import AndersonAC.S6.Normalization
import AndersonAC.S6.Statements

/-! Full scattering-range localization with the explicit §2 Ward input. -/
noncomputable section
open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace AndersonAC.SolS6

def localizationRate (d : ℕ) (c : ℝ) : ℝ :=
  Real.log (1 + c / (4 * (1 + 2 * (d : ℝ))))

theorem localization_rate_bound (d : ℕ) (c : ℝ) (hc : 0 < c) :
    0 < localizationRate d c ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (2 * d) * (Real.exp (localizationRate d c * t) - 1) ≤ c * t / 4 := by
  have hden : 0 < (4 * (1 + 2 * (d : ℝ))) := by positivity
  have hfracpos : 0 < c / (4 * (1 + 2 * (d : ℝ))) := div_pos hc hden
  have ha : 0 < localizationRate d c := Real.log_pos (by linarith)
  have he : Real.exp (localizationRate d c) - 1 = c / (4 * (1 + 2 * (d : ℝ))) := by
    rw [localizationRate, Real.exp_log (by linarith : 0 < 1 + c / (4 * (1 + 2 * (d : ℝ))))]
    ring
  refine ⟨ha, ?_⟩
  intro t ht ht1
  have hf : (2 * d : ℝ) * (c / (4 * (1 + 2 * (d : ℝ)))) ≤ c / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hden (by norm_num : 0 < (4 : ℝ))).mpr
    nlinarith
  calc
    _ ≤ (2 * d) * ((Real.exp (localizationRate d c) - 1) * t) :=
      mul_le_mul_of_nonneg_left (exp_scaled_bound _ t ht ht1) (by positivity)
    _ = ((2 * d) * (c / (4 * (1 + 2 * (d : ℝ))))) * t := by rw [he]; ring
    _ ≤ (c / 4) * t := mul_le_mul_of_nonneg_right hf ht
    _ = _ := by ring

theorem inverse_bound_of_geometry (hWard : AndersonAC.Blueprint.WardInput)
    (d b n : ℕ) (t c K : ℝ) (r : Fin n → ℂ) (ρ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin b) ℂ)
    (ht : 0 < t) (hc : 0 < c) (hb : AndersonAC.S6.BroadBounds c K r)
    (hgeo : AndersonAC.S6.ExteriorGeometry d ρ H C t r) :
    IsUnit H.det ∧ ‖H⁻¹‖ ≤ (t * c)⁻¹ := by
  obtain ⟨J, T, hJ, hT, hH, _, _, _, _⟩ := hgeo.decomposition
  let M := (J + T).map Complex.ofReal
  have hMt : Mᵀ = M := by
    ext i j
    change ((J j i + T j i : ℝ) : ℂ) = ((J i j + T i j : ℝ) : ℂ)
    rw [hJ.apply i j, hT.apply i j]
  have hreal : ∀ i j, (M i j).im = 0 := by intro i j; simp [M]
  obtain ⟨G, hInv, _, hnorm, _⟩ := hWard n M hMt hreal t ht r c hc (fun i => (hb.2 i).2.1)
  have hInvH : AndersonAC.Blueprint.twoSidedInverse H G := by
    rw [hH]
    exact hInv
  have hunit : IsUnit H.det := Matrix.isUnit_det_of_left_inverse hInvH.2
  have hG : G = H⁻¹ := by
    calc
      G = G * (H * H⁻¹) := by rw [Matrix.mul_nonsing_inv H hunit, Matrix.mul_one]
      _ = (G * H) * H⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = H⁻¹ := by rw [hInvH.2, Matrix.one_mul]
  rw [hG] at hnorm
  exact ⟨hunit, hnorm⟩

theorem sqrtDamping_unit {R : Type*} [Fintype R] [DecidableEq R]
    (p : R → ℝ) (hp : ∀ i, 0 < p i) : IsUnit (AndersonAC.S6.sqrtDamping p).det := by
  rw [AndersonAC.S6.sqrtDamping, Matrix.det_diagonal]
  apply (isUnit_iff_ne_zero).mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hp i)))

theorem range_localization_of_ward (hWard : AndersonAC.Blueprint.WardInput)
    (d : ℕ) (c K : ℝ) (hc : 0 < c) (hK : c ≤ K) :
    AndersonAC.S6.Planned.range_localization d c K hc hK := by
  let a := localizationRate d c
  let L := 2 * Real.sqrt (K / c)
  obtain ⟨ha, hrate⟩ := localization_rate_bound d c hc
  have hKpos : 0 < K := hc.trans_le hK
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨a, L, ha, hL, ?_⟩
  intro b n t r ρ H C ht ht1 hb hgeo
  obtain ⟨hHunit, hHnorm⟩ := inverse_bound_of_geometry hWard d b n t c K r ρ H C ht hc hb hgeo
  let E := AndersonAC.S6.exponentialWeight a t ρ
  let En := AndersonAC.S6.exponentialWeight (-a) t ρ
  let Err := E * H * En - H
  obtain ⟨hEEn, hEnE⟩ := exponential_weight_inverse a t ρ
  have hcomm : E * H = (H + Err) * E := by
    symm
    calc
      (H + Err) * E = (E * H * En) * E := by dsimp [Err]; noncomm_ring
      _ = E * H * (En * E) := by simp only [Matrix.mul_assoc]
      _ = E * H := by rw [hEnE, Matrix.mul_one]
  have herr : ‖Err‖ ≤ c * t / 4 := by
    obtain ⟨J, T, hJ, _, hH, hentry, hdegree, hJρ, hTρ⟩ := hgeo.decomposition
    have hnorm := weighted_commutator_bound d n a t ρ J T r ha.le ht.le hJ hentry hdegree hJρ hTρ
    change ‖E * H * En - H‖ ≤ _
    rw [hH]
    exact hnorm.trans (hrate t ht.le ht1)
  have hsmall : ‖H⁻¹ * Err‖ ≤ 1 / 2 := by
    calc
      _ ≤ ‖H⁻¹‖ * ‖Err‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (t * c)⁻¹ * (c * t / 4) :=
        mul_le_mul hHnorm herr (norm_nonneg _) (by positivity)
      _ = 1 / 4 := by field_simp
      _ ≤ _ := by norm_num
  let p := AndersonAC.S6.imagDamping r
  let D := AndersonAC.S6.sqrtDamping p
  have hp : ∀ i, c ≤ p i := fun i => (hb.2 i).2.1
  have hpupper : ∀ i, p i ≤ K := fun i => (hb.2 i).2.2
  have hDunit : IsUnit D.det := sqrtDamping_unit p (fun i => hc.trans_le (hp i))
  have hweighted : ∀ v ∈ AndersonAC.S6.matrixRange C, ‖Matrix.toEuclideanLin E v‖ ≤ L * ‖v‖ := by
    intro v hv
    let w := Matrix.toEuclideanLin D⁻¹ v
    have hvw : v = Matrix.toEuclideanLin D w := by
      change v = Matrix.toEuclideanLin D (Matrix.toEuclideanLin D⁻¹ v)
      have h := congrArg (fun A => Matrix.toEuclideanLin A v) (Matrix.mul_nonsing_inv D hDunit)
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        Matrix.toLpLin_one, LinearMap.comp_apply, LinearMap.id_apply] using h.symm
    have hsrc : ∀ i, 0 < ρ i → (Matrix.toEuclideanLin H w) i = 0 := by
      intro i hi
      have h := hgeo.exterior_source v hv i hi
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h
    have hsource : Matrix.toEuclideanLin E (Matrix.toEuclideanLin H w) = Matrix.toEuclideanLin H w := by
      ext i
      change (E *ᵥ (fun j => (Matrix.toEuclideanLin H w) j)) i = (Matrix.toEuclideanLin H w) i
      change ((AndersonAC.S6.exponentialWeight a t ρ) *ᵥ _) i = _
      simp only [AndersonAC.S6.exponentialWeight, Matrix.mulVec_diagonal]
      by_cases hi : 0 < ρ i
      · rw [hsrc i hi]; simp
      · have hz : ρ i = 0 := le_antisymm (le_of_not_gt hi) (hgeo.radius_nonneg i)
        simp [hz]
    have hw := weighted_range_absorption H E Err w hHunit hcomm hsource hsmall
    exact damping_weight_transfer a t c K p ρ v w hc hK hp hpupper hvw hw
  refine ⟨hweighted, ?_⟩
  exact projection_decay_of_weighted_range C a t L ρ hL.le hweighted

end AndersonAC.SolS6

namespace AndersonAC.S6

/-- Lemma 6.2 with its named §2 Ward/dissipativity dependency supplied explicitly. -/
theorem range_localization (hWard : AndersonAC.Blueprint.WardInput)
    (d : ℕ) (c K : ℝ) (hc : 0 < c) (hK : c ≤ K) :
    Planned.range_localization d c K hc hK :=
  AndersonAC.SolS6.range_localization_of_ward hWard d c K hc hK

end AndersonAC.S6

#print axioms AndersonAC.SolS6.localization_rate_bound
#print axioms AndersonAC.SolS6.inverse_bound_of_geometry
#print axioms AndersonAC.SolS6.range_localization_of_ward
#print axioms AndersonAC.S6.range_localization
