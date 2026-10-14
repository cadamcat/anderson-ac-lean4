import AndersonAC.S45.Definitions
import AndersonAC.S45.GammaProof
import AndersonAC.S45.SweepEndpointProof
import AndersonAC.S45.PrestateProof

/-!
Conditional support for the §4.4 and §4.7 estimates. This module imports
only the definition layer. The analytic prestate proposition is restated
locally so that a later proof can use it without importing the sorry-bearing
statement module.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators

namespace AndersonAC.AgentS45

/-- Exact local copy of `AndersonAC.S45.analytic_prestate`'s proposition.
The check module verifies that this remains definitionally the same type. -/
def analyticPrestateHypothesis : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n : ℕ) (t : ℝ) (s : AndersonAC.S45.State (Fin n))
      (Λplus Wstar : AndersonAC.S45.Form (Fin n)),
    t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
    (∀ i, ‖s.rawLag i‖ ≤ C' * AndersonAC.S45.power t AndersonAC.S45.beta ∧
      |s.q i - s.p i| ≤ C' * AndersonAC.S45.power t AndersonAC.S45.beta ∧
      (∑ j, s.F t i j) ≤ C' ∧ ‖s.h t i i‖ ≤ C' * Real.sqrt t) ∧
    (∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤
      C' * AndersonAC.S45.power t (AndersonAC.S45.delta / 2)) ∧
    (∀ i, (s.F t ^ 3) i i ≤
      C' * AndersonAC.S45.power t AndersonAC.S45.kappa *
        AndersonAC.S45.rowCap t)

/-- The scalar deletion parameter stays uniformly bounded on a small-scale
prestate, conditional on the analytic estimates used in the sweep lemmas. -/
theorem gamma_norm_bound_of_analyticPrestate
    (hAnalytic : analyticPrestateHypothesis) (C : ℝ) (hC : 1 ≤ C) :
    ∃ G > 0, ∃ t0 > 0,
      ∀ (n : ℕ) (t : ℝ) (s : AndersonAC.S45.State (Fin n))
        (Λplus Wstar : AndersonAC.S45.Form (Fin n)) (i : Fin n) (ξ : ℝ),
        t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
        |ξ| ≤ C * Real.sqrt t → ‖AndersonAC.S45.gamma t s i ξ‖ ≤ G := by
  obtain ⟨A, hApos, tA, htA, hFacts⟩ := hAnalytic C hC
  let L : ℝ := 4 * C * (C + A)
  refine ⟨4 * C, by positivity, min tA ((1 / L) ^ 2), ?_, ?_⟩
  · exact lt_min htA (by positivity)
  · intro n t s Λplus Wstar i ξ htt hPre hξ
    have ht : 0 < t := hPre.scale.1
    have ht1 : t ≤ 1 := hPre.scale.2.le
    have hCnonneg : 0 ≤ C := le_trans (by norm_num) hC
    have httA : t < tA :=
      lt_of_lt_of_le htt (min_le_left tA ((1 / L) ^ 2))
    have httSmall : t < (1 / L) ^ 2 := by
      exact lt_of_lt_of_le htt (min_le_right tA ((1 / L) ^ 2))
    have hβ : 0 ≤ AndersonAC.S45.beta := by
      norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta]
    have hpow : AndersonAC.S45.power t AndersonAC.S45.beta ≤ 1 := by
      exact Real.rpow_le_one ht.le ht1 hβ
    have hLpos : 0 < L := by
      dsimp [L]
      positivity
    have hsqrtSmall : Real.sqrt t < 1 / L :=
      (Real.sqrt_lt ht.le (by positivity)).2 (by simpa using httSmall)
    have hsmallProduct : 2 * C * (C + A) * Real.sqrt t < 1 / 2 := by
      have hmul := mul_lt_mul_of_pos_left hsqrtSmall (by positivity : 0 < 2 * C * (C + A))
      have heq : 2 * C * (C + A) * (1 / L) = 1 / 2 := by
        dsimp [L]
        field_simp
        <;> ring
      linarith
    have hArow := hFacts n t s Λplus Wstar httA hPre
    have hraw : ‖s.rawLag i‖ ≤ A * AndersonAC.S45.power t AndersonAC.S45.beta :=
      (hArow.1 i).1
    have hr : ‖s.r i‖ ≤ C := (hPre.broad i).1
    have hg : ‖s.g i i‖ ≤ C + A := by
      have hpowA := mul_le_mul_of_nonneg_left hpow hApos.le
      calc
        ‖s.g i i‖ = ‖s.r i + s.rawLag i‖ := by
          congr 1
          simp [AndersonAC.S45.State.rawLag]
        _ ≤ ‖s.r i‖ + ‖s.rawLag i‖ := norm_add_le _ _
        _ ≤ C + A * AndersonAC.S45.power t AndersonAC.S45.beta :=
          add_le_add hr hraw
        _ ≤ C + A := by linarith
    have ht_le_sqrt : t ≤ Real.sqrt t := by
      have hsqrt_le_one : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
      calc
        t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
        _ = Real.sqrt t * Real.sqrt t := by ring
        _ ≤ Real.sqrt t * 1 := mul_le_mul_of_nonneg_left hsqrt_le_one
          (Real.sqrt_nonneg _)
        _ = Real.sqrt t := by ring
    have hnum : ‖(ξ : ℂ) + (t : ℂ) * s.r i‖ ≤ 2 * C * Real.sqrt t := by
      calc
        ‖(ξ : ℂ) + (t : ℂ) * s.r i‖ ≤
            ‖(ξ : ℂ)‖ + ‖(t : ℂ) * s.r i‖ := norm_add_le _ _
        _ = |ξ| + t * ‖s.r i‖ := by
          simp [Complex.norm_real, abs_of_pos ht]
        _ ≤ C * Real.sqrt t + t * C := by
          exact add_le_add hξ (mul_le_mul_of_nonneg_left hr ht.le)
        _ ≤ 2 * C * Real.sqrt t := by
          nlinarith [mul_le_mul_of_nonneg_right ht_le_sqrt hCnonneg]
    let q : ℂ := ((ξ : ℂ) + (t : ℂ) * s.r i) * s.g i i
    have hq : ‖q‖ ≤ 2 * C * (C + A) * Real.sqrt t := by
      calc
        ‖q‖ ≤ ‖(ξ : ℂ) + (t : ℂ) * s.r i‖ * ‖s.g i i‖ := by
          dsimp [q]
          exact norm_mul_le _ _
        _ ≤ (2 * C * Real.sqrt t) * (C + A) :=
          mul_le_mul hnum hg (norm_nonneg _) (by positivity)
        _ = 2 * C * (C + A) * Real.sqrt t := by ring
    have hqsmall : ‖q‖ < 1 / 2 := lt_of_le_of_lt hq hsmallProduct
    have hden : 1 / 2 ≤ ‖(1 : ℂ) + q‖ := by
      have htri : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) + q‖ + ‖q‖ := by
        calc
          ‖(1 : ℂ)‖ = ‖((1 : ℂ) + q) - q‖ := by congr 1 <;> ring
          _ ≤ ‖(1 : ℂ) + q‖ + ‖q‖ := norm_sub_le _ _
      simp only [norm_one] at htri
      linarith
    let d : ℂ := (Real.sqrt t : ℂ) * ((1 : ℂ) + q)
    have hd : Real.sqrt t / 2 ≤ ‖d‖ := by
      have hmul := mul_le_mul_of_nonneg_left hden (Real.sqrt_nonneg t)
      calc
        Real.sqrt t / 2 = Real.sqrt t * (1 / 2) := by ring
        _ ≤ Real.sqrt t * ‖(1 : ℂ) + q‖ := by nlinarith [hmul]
        _ = ‖d‖ := by
          dsimp [d]
          rw [norm_mul]
          simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg t)]
    have hdpos : 0 < ‖d‖ := lt_of_lt_of_le (by positivity) hd
    have hratio : ‖(ξ : ℂ) + (t : ℂ) * s.r i‖ / ‖d‖ ≤ 4 * C := by
      rw [div_le_iff₀ hdpos]
      have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4 * C)
      nlinarith [hnum, hm]
    dsimp [AndersonAC.S45.gamma]
    rw [norm_div]
    simpa [q, d] using hratio

/-- The analytic lag estimate and the gamma moment expansion give the
small scalar mean needed in the signed sweep estimates. -/
theorem gamma_mean_bound_of_analyticPrestate
    (hAnalytic : analyticPrestateHypothesis) (C : ℝ) (hC : 1 ≤ C) :
    ∃ M > 0, ∃ t0 > 0,
      ∀ (n : ℕ) (Ω : Type) [mΩ : MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ)
        (s : AndersonAC.S45.State (Fin n))
        (Λplus Wstar : AndersonAC.S45.Form (Fin n)) (x : Fin n)
        (ξ : Ω → ℝ),
        t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
        AndersonAC.S45.MomentLaw μ t C ξ →
        ‖(∫ ω, AndersonAC.S45.gamma t s x (ξ ω) ∂μ)‖ ≤
          M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by
  obtain ⟨A, hApos, tA, htA, hFacts⟩ := hAnalytic C hC
  let C₁ : ℝ := 2 * C + A
  have hC₁ : 1 ≤ C₁ := by
    dsimp [C₁]
    linarith
  have hC_le : C ≤ C₁ := by
    dsimp [C₁]
    linarith
  obtain ⟨G, hGpos, tG, htG, hGamma⟩ :=
    AndersonAC.AgentS45.gamma_moments_proof C₁ hC₁
  let M : ℝ := G + A
  refine ⟨M, ?_, min tA tG, lt_min htA htG, ?_⟩
  · dsimp [M]
    positivity
  · intro n Ω mΩ μ hμ t s Λplus Wstar x ξ htt hPre hLaw
    have ht : 0 < t := hPre.scale.1
    have ht1 : t ≤ 1 := hPre.scale.2.le
    have httA : t < tA := lt_of_lt_of_le htt (min_le_left _ _)
    have httG : t < tG := lt_of_lt_of_le htt (min_le_right _ _)
    have hβpos : 0 ≤ AndersonAC.S45.beta := by
      norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta]
    have hpow : AndersonAC.S45.power t AndersonAC.S45.beta ≤ 1 :=
      Real.rpow_le_one ht.le ht1 hβpos
    have ha := hFacts n t s Λplus Wstar httA hPre
    have hraw : ‖s.rawLag x‖ ≤ A * AndersonAC.S45.power t AndersonAC.S45.beta :=
      (ha.1 x).1
    have hr : ‖s.r x‖ ≤ C := (hPre.broad x).1
    have hg : ‖s.g x x‖ ≤ C + A := by
      have hAterm := mul_le_mul_of_nonneg_left hpow hApos.le
      calc
        ‖s.g x x‖ = ‖s.r x + s.rawLag x‖ := by
          congr 1
          simp [AndersonAC.S45.State.rawLag]
        _ ≤ ‖s.r x‖ + ‖s.rawLag x‖ := norm_add_le _ _
        _ ≤ C + A * AndersonAC.S45.power t AndersonAC.S45.beta :=
          add_le_add hr hraw
        _ ≤ C + A := by linarith
    have hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ C₁ := by
      dsimp [C₁]
      linarith
    let law₁ : AndersonAC.S45.MomentLaw μ t C₁ ξ := {
      measurable := hLaw.measurable
      mean := hLaw.mean
      variance := hLaw.variance
      bounded := hLaw.bounded.mono fun ω hω =>
        hω.trans (mul_le_mul_of_nonneg_right hC_le (Real.sqrt_nonneg t))
    }
    have hGm := hGamma (Fin n) Ω μ t s x ξ ht httG hstate law₁
    have hmean := hGm.2.1
    have hz : ‖s.z t x‖ ≤ Real.sqrt t *
        (A * AndersonAC.S45.power t AndersonAC.S45.beta) := by
      change ‖(Real.sqrt t : ℂ) * s.rawLag x‖ ≤ _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg t)]
      exact mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg t)
    have hpowOrder : AndersonAC.S45.beta ≤ 1 / 2 := by
      norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta]
    have hsqrtLe : Real.sqrt t ≤ AndersonAC.S45.power t AndersonAC.S45.beta := by
      dsimp [AndersonAC.S45.power]
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 hpowOrder
    have htLe : t ≤ Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by
      calc
        t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
        _ = Real.sqrt t * Real.sqrt t := by ring
        _ ≤ Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta :=
          mul_le_mul_of_nonneg_left hsqrtLe (Real.sqrt_nonneg t)
    calc
      ‖(∫ ω, AndersonAC.S45.gamma t s x (ξ ω) ∂μ)‖ =
          ‖((∫ ω, AndersonAC.S45.gamma t s x (ξ ω) ∂μ) + s.z t x) - s.z t x‖ := by
            congr 1
            abel
      _ ≤ ‖(∫ ω, AndersonAC.S45.gamma t s x (ξ ω) ∂μ) + s.z t x‖ +
          ‖s.z t x‖ := norm_sub_le _ _
      _ ≤ G * t + Real.sqrt t *
          (A * AndersonAC.S45.power t AndersonAC.S45.beta) := add_le_add hmean hz
      _ ≤ (G + A) * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by
          have hGterm := mul_le_mul_of_nonneg_left htLe hGpos.le
          nlinarith [hGterm]

theorem gamma_reindex {P Q : Type*} (e : Q ≃ P)
    (s : AndersonAC.S45.State P) (t : ℝ) (x : P) (ξ : ℝ) :
    AndersonAC.S45.gamma t (State.reindex e s) (e.symm x) ξ =
      AndersonAC.S45.gamma t s x ξ := by
  simp [State.reindex, AndersonAC.S45.gamma, Equiv.apply_symm_apply]

/-- Ward and the positive lower bound on the diagonal imaginary part control
the operator norm of the scaled Green matrix. -/
theorem ward_h_operator_bound {P : Type*} [Fintype P] [DecidableEq P]
    (s : AndersonAC.S45.State P) (t C : ℝ) (ht : 0 < t) (hC : 0 < C)
    (hsym : s.g.IsSymm) (hward : s.ward t)
    (hp : ∀ i, 1 / C ≤ s.p i) :
    ‖s.h t‖ ≤ C / Real.sqrt t := by
  classical
  let d : Matrix P P ℂ := diagonal (fun i => (Real.sqrt (s.p i) : ℂ))
  let dInv : Matrix P P ℂ := diagonal (fun i => ((Real.sqrt (s.p i) : ℂ)⁻¹))
  let a : Matrix P P ℂ := s.h t * d
  have hpPos : ∀ i, 0 < s.p i := by
    intro i
    have hle := hp i
    have hCinv : 0 < 1 / C := by positivity
    exact lt_of_lt_of_le hCinv hle
  have hdstar : dᴴ = d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, Matrix.diagonal_apply]
    · simp [d, Matrix.diagonal_apply, hij, Ne.symm hij]
  have hdd : d * dᴴ = diagonal (fun i => (s.p i : ℂ)) := by
    rw [hdstar]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, Matrix.mul_apply, Matrix.diagonal_apply]
      calc
        (Real.sqrt (s.p i) : ℂ) * (Real.sqrt (s.p i) : ℂ) =
            ((Real.sqrt (s.p i)) * (Real.sqrt (s.p i)) : ℝ) := by simp
        _ = (s.p i : ℂ) := by
          have hsqrtSq : Real.sqrt (s.p i) * Real.sqrt (s.p i) = s.p i := by
            simpa [pow_two] using Real.sq_sqrt (le_of_lt (hpPos i))
          exact congrArg (fun x : ℝ => (x : ℂ)) hsqrtSq
    · simp [d, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  have hdinv : d * dInv = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, dInv, Matrix.mul_apply, Matrix.diagonal_apply,
        Real.sqrt_ne_zero'.2 (hpPos i)]
    · simp [d, dInv, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  have hAeq : a * aᴴ = s.h t * diagonal (fun i => (s.p i : ℂ)) * (s.h t)ᴴ := by
    calc
      a * aᴴ = s.h t * (d * dᴴ) * (s.h t)ᴴ := by
        simp [a, Matrix.conjTranspose_mul, mul_assoc]
      _ = s.h t * diagonal (fun i => (s.p i : ℂ)) * (s.h t)ᴴ := by rw [hdd]
  have hAward : a * aᴴ = AndersonAC.S45.matrixIm s.g := by
    rw [hAeq]
    exact hward
  have hNormA : ‖a‖ ^ 2 = ‖AndersonAC.S45.matrixIm s.g‖ := by
    calc
      ‖a‖ ^ 2 = ‖a * aᴴ‖ := by
        rw [pow_two, ← CStarRing.norm_self_mul_star]
        simpa [Matrix.star_eq_conjTranspose]
      _ = ‖AndersonAC.S45.matrixIm s.g‖ := congrArg norm hAward
  let c : ℂ := (2 * Complex.I * (Real.sqrt t : ℂ))⁻¹
  have hImFormula : AndersonAC.S45.matrixIm s.g =
      c • (s.h t - (s.h t)ᴴ) := by
    ext i j
    have hsij : s.g j i = s.g i j := hsym.apply i j
    have hentry : s.h t i j - star (s.h t j i) =
        (2 * Complex.I * (Real.sqrt t : ℂ)) * (s.g i j).im := by
      have hsub : s.g i j - star (s.g i j) =
          2 * (s.g i j).im * Complex.I := by
        rw [RCLike.star_def]
        exact RCLike.sub_conj _
      calc
        s.h t i j - star (s.h t j i) =
            (Real.sqrt t : ℂ) * s.g i j -
              (Real.sqrt t : ℂ) * star (s.g i j) := by
                simp [AndersonAC.S45.State.h, Matrix.smul_apply,
                  hsij, RCLike.star_def]
        _ = (Real.sqrt t : ℂ) * (s.g i j - star (s.g i j)) := by ring
        _ = (Real.sqrt t : ℂ) * (2 * (s.g i j).im * Complex.I) := by rw [hsub]
        _ = (2 * Complex.I * (Real.sqrt t : ℂ)) * (s.g i j).im := by ring
    change ((s.g i j).im : ℂ) = c * (s.h t i j - star (s.h t j i))
    rw [hentry]
    dsimp [c]
    field_simp [ne_of_gt ht] <;> ring
  have hc : ‖c‖ = 1 / (2 * Real.sqrt t) := by
    dsimp [c]
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real]
    norm_num [Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 ht)]
  have hdiff : ‖s.h t - (s.h t)ᴴ‖ ≤ 2 * ‖s.h t‖ := by
    calc
      ‖s.h t - (s.h t)ᴴ‖ ≤ ‖s.h t‖ + ‖(s.h t)ᴴ‖ := norm_sub_le _ _
      _ = 2 * ‖s.h t‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring
  have hImNorm : ‖AndersonAC.S45.matrixIm s.g‖ ≤ ‖s.h t‖ / Real.sqrt t := by
    rw [hImFormula, norm_smul, hc]
    calc
      (1 / (2 * Real.sqrt t)) * ‖s.h t - (s.h t)ᴴ‖ ≤
          (1 / (2 * Real.sqrt t)) * (2 * ‖s.h t‖) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = ‖s.h t‖ / Real.sqrt t := by field_simp <;> ring
  have hInvSqrt : ∀ i, (Real.sqrt (s.p i))⁻¹ ≤ Real.sqrt C := by
    intro i
    have hCp : 1 ≤ C * s.p i := by
      have hm := mul_le_mul_of_nonneg_left (hp i) hC.le
      simpa [hC.ne'] using hm
    have hprod : 1 ≤ Real.sqrt C * Real.sqrt (s.p i) := by
      rw [← Real.sqrt_mul hC.le]
      exact Real.one_le_sqrt.mpr hCp
    have hdiv : 1 / Real.sqrt (s.p i) ≤ Real.sqrt C :=
      (div_le_iff₀ (Real.sqrt_pos.2 (hpPos i))).2 hprod
    simpa only [one_div] using hdiv
  have hDInv : ‖dInv‖ ≤ Real.sqrt C := by
    rw [Matrix.l2_opNorm_diagonal]
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg C)]
    intro i
    have hh := hInvSqrt i
    simpa [dInv, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (s.p i))] using hh
  have hFactor : s.h t = a * dInv := by
    calc
      s.h t = s.h t * 1 := by simp
      _ = s.h t * (d * dInv) := by rw [hdinv]
      _ = a * dInv := by simp [a, mul_assoc]
  have hAControl : ‖s.h t‖ ≤ ‖a‖ * Real.sqrt C := by
    rw [hFactor]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hDInv (norm_nonneg _))
  have hSquare : ‖s.h t‖ ^ 2 ≤ C * ‖a‖ ^ 2 := by
    calc
      ‖s.h t‖ ^ 2 ≤ (‖a‖ * Real.sqrt C) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hAControl
      _ = C * ‖a‖ ^ 2 := by
        calc
          (‖a‖ * Real.sqrt C) ^ 2 = ‖a‖ ^ 2 * (Real.sqrt C) ^ 2 := by ring
          _ = C * ‖a‖ ^ 2 := by rw [Real.sq_sqrt hC.le]; ring
  have hMain : ‖s.h t‖ ^ 2 ≤ C * (‖s.h t‖ / Real.sqrt t) := by
    calc
      ‖s.h t‖ ^ 2 ≤ C * ‖a‖ ^ 2 := hSquare
      _ = C * ‖AndersonAC.S45.matrixIm s.g‖ := by rw [hNormA]
      _ ≤ C * (‖s.h t‖ / Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hImNorm hC.le
  by_cases hzero : ‖s.h t‖ = 0
  · simpa [hzero] using (div_nonneg hC.le (Real.sqrt_nonneg t))
  · have hpos : 0 < ‖s.h t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hmul : ‖s.h t‖ * ‖s.h t‖ ≤ (C / Real.sqrt t) * ‖s.h t‖ := by
      calc
        ‖s.h t‖ * ‖s.h t‖ = ‖s.h t‖ ^ 2 := by ring
        _ ≤ C * (‖s.h t‖ / Real.sqrt t) := hMain
        _ = (C / Real.sqrt t) * ‖s.h t‖ := by ring
    exact le_of_mul_le_mul_right hmul hpos

/-- A scalar fourth-power perturbation bound used in the proxy expansion. -/
theorem fourth_increment_abs_bound (a b : ℂ) :
    |‖a - b‖ ^ 4 - ‖a‖ ^ 4| ≤
      4 * ‖a‖ ^ 3 * ‖b‖ + 6 * ‖a‖ ^ 2 * ‖b‖ ^ 2 +
        4 * ‖a‖ * ‖b‖ ^ 3 + ‖b‖ ^ 4 := by
  let x : ℝ := ‖a - b‖
  let y : ℝ := ‖a‖
  let z : ℝ := ‖b‖
  have hx : 0 ≤ x := by simp [x]
  have hy : 0 ≤ y := by simp [y]
  have hz : 0 ≤ z := by simp [z]
  have hxy : |x - y| ≤ z := by
    apply abs_le.mpr
    constructor
    · have h := norm_add_le (a - b) b
      have heq : (a - b) + b = a := by abel
      rw [heq] at h
      change y ≤ x + z at h
      dsimp only [x, y, z]
      linarith
    · have h := norm_sub_le a b
      change x ≤ y + z at h
      dsimp only [x, y, z]
      linarith
  have hxy' : x ≤ y + z := by
    have h := abs_le.mp hxy
    linarith
  have hx3 : x ^ 3 ≤ (y + z) ^ 3 := by gcongr
  have hx2y : x ^ 2 * y ≤ (y + z) ^ 2 * y := by gcongr
  have hxy2 : x * y ^ 2 ≤ (y + z) * y ^ 2 := by gcongr
  have hpoly :
      x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 ≤
        (y + z) ^ 3 + (y + z) ^ 2 * y + (y + z) * y ^ 2 + y ^ 3 := by
    linarith
  have hfac : x ^ 4 - y ^ 4 =
      (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) := by ring
  have hpoly_nonneg : 0 ≤ x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 := by positivity
  calc
    |x ^ 4 - y ^ 4| = |x - y| *
        (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) := by
          rw [hfac, abs_mul, abs_of_nonneg hpoly_nonneg]
    _ ≤ z * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) :=
          mul_le_mul_of_nonneg_right hxy hpoly_nonneg
    _ ≤ z * ((y + z) ^ 3 + (y + z) ^ 2 * y +
          (y + z) * y ^ 2 + y ^ 3) := by gcongr
    _ = 4 * y ^ 3 * z + 6 * y ^ 2 * z ^ 2 +
          4 * y * z ^ 3 + z ^ 4 := by ring
    _ = 4 * ‖a‖ ^ 3 * ‖b‖ + 6 * ‖a‖ ^ 2 * ‖b‖ ^ 2 +
          4 * ‖a‖ * ‖b‖ ^ 3 + ‖b‖ ^ 4 := by rfl

/-- The first-order term in the fourth-power expansion has a quadratic
remainder. -/
theorem fourth_increment_remainder_bound (a b : ℂ) :
    |‖a - b‖ ^ 4 - ‖a‖ ^ 4 +
        4 * ‖a‖ ^ 2 * (a * star b).re| ≤
      8 * ‖a‖ ^ 2 * ‖b‖ ^ 2 + 3 * ‖b‖ ^ 4 := by
  let A : ℝ := ‖a‖
  let B : ℝ := ‖b‖
  let c : ℝ := (a * star b).re
  have hA : 0 ≤ A := by simp [A]
  have hB : 0 ≤ B := by simp [B]
  have hc : |c| ≤ A * B := by
    dsimp [c, A, B]
    calc
      |(a * star b).re| ≤ ‖a * star b‖ :=
        RCLike.abs_re_le_norm (K := ℂ) (a * star b)
      _ = ‖a‖ * ‖b‖ := by simp [norm_mul]
  have hnormSq : ‖a - b‖ ^ 2 = A ^ 2 + B ^ 2 - 2 * c := by
    dsimp [A, B, c]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hid : ‖a - b‖ ^ 4 - A ^ 4 + 4 * A ^ 2 * c =
      2 * A ^ 2 * B ^ 2 + B ^ 4 - 4 * B ^ 2 * c + 4 * c ^ 2 := by
    calc
      ‖a - b‖ ^ 4 - A ^ 4 + 4 * A ^ 2 * c =
          (‖a - b‖ ^ 2) ^ 2 - A ^ 4 + 4 * A ^ 2 * c := by ring
      _ = (A ^ 2 + B ^ 2 - 2 * c) ^ 2 - A ^ 4 + 4 * A ^ 2 * c := by
          rw [hnormSq]
      _ = 2 * A ^ 2 * B ^ 2 + B ^ 4 - 4 * B ^ 2 * c + 4 * c ^ 2 := by ring
  have hab : 2 * A * B ^ 3 ≤ A ^ 2 * B ^ 2 + B ^ 4 := by
    nlinarith [sq_nonneg (A * B - B ^ 2)]
  have hupper : ‖a - b‖ ^ 4 - A ^ 4 + 4 * A ^ 2 * c ≤
      8 * A ^ 2 * B ^ 2 + 3 * B ^ 4 := by
    rw [hid]
    have hcLower : -(A * B) ≤ c := (abs_le.mp hc).1
    have hterm : -(B ^ 2 * c) ≤ A * B ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_left hcLower (sq_nonneg B)
      nlinarith [hmul]
    have hcc : c ^ 2 ≤ A ^ 2 * B ^ 2 := by
      have hAB : 0 ≤ A * B := mul_nonneg hA hB
      have hsquare : |c| ^ 2 ≤ (A * B) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg c) hAB).2 hc
      calc
        c ^ 2 = |c| ^ 2 := by rw [sq_abs]
        _ ≤ (A * B) ^ 2 := hsquare
        _ = A ^ 2 * B ^ 2 := by ring
    nlinarith [hab, hterm, hcc]
  have hlower : -(8 * A ^ 2 * B ^ 2 + 3 * B ^ 4) ≤
      ‖a - b‖ ^ 4 - A ^ 4 + 4 * A ^ 2 * c := by
    rw [hid]
    have hcUpper : c ≤ A * B := (abs_le.mp hc).2
    have hterm' : B ^ 2 * c ≤ A * B ^ 3 := by
      calc
        B ^ 2 * c ≤ B ^ 2 * (A * B) :=
          mul_le_mul_of_nonneg_left hcUpper (sq_nonneg B)
        _ = A * B ^ 3 := by ring
    nlinarith [hab, hterm', sq_nonneg c]
  have habs : |‖a - b‖ ^ 4 - A ^ 4 + 4 * A ^ 2 * c| ≤
      8 * A ^ 2 * B ^ 2 + 3 * B ^ 4 := abs_le.mpr ⟨hlower, hupper⟩
  simpa [A, B, c] using habs

/-- Pointwise absolute proxy increments reduce to the scalar expansion bound. -/
theorem fourthProxy_abs_le {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P)
    (C : Finset P) (i x : P) (ξ : ℝ) (hix : i ≠ x) :
    |AndersonAC.S45.fourthProxy t s C i x ξ| ≤
      Finset.sum (C.erase x) (fun j : P =>
        4 * ‖s.h t i j‖ ^ 3 *
            ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ +
          6 * ‖s.h t i j‖ ^ 2 *
            ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 2 +
          4 * ‖s.h t i j‖ *
            ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 3 +
          ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 4) := by
  unfold AndersonAC.S45.fourthProxy
  rw [if_neg hix]
  calc
    |Finset.sum (C.erase x) (fun j : P =>
        (‖s.h t i j - AndersonAC.S45.gamma t s x ξ *
            s.h t i x * s.h t x j‖ ^ 4 - ‖s.h t i j‖ ^ 4))| ≤
        Finset.sum (C.erase x) (fun j : P =>
          |‖s.h t i j - AndersonAC.S45.gamma t s x ξ *
              s.h t i x * s.h t x j‖ ^ 4 - ‖s.h t i j‖ ^ 4|) := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (C.erase x) (fun j : P =>
          (4 * ‖s.h t i j‖ ^ 3 *
                ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ +
            6 * ‖s.h t i j‖ ^ 2 *
                ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 2 +
            4 * ‖s.h t i j‖ *
                ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 3 +
            ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 4)) := by
            apply Finset.sum_le_sum
            intro j hj
            exact fourth_increment_abs_bound (s.h t i j)
              (AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j)

/-- The weighted row correlation in the linear proxy stack is the diagonal
entry of the matrix cube. -/
theorem row_correlation_eq_cube {P : Type*} [Fintype P] [DecidableEq P]
    (F : Matrix P P ℝ) (hF : F.IsSymm) (i : P) :
    (∑ x, F i x * ∑ j, F i j * F x j) = (F ^ 3) i i := by
  classical
  have hsym : ∀ x y, F x y = F y x := by
    intro x y
    have h := congrFun (congrFun hF y) x
    simpa using h
  rw [pow_succ, pow_succ]
  simp only [Matrix.mul_apply, pow_one]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsym x j, hsym x i]
  ac_rfl

/-- The analytic prestate hypothesis directly supplies the row-cube estimate
needed after the preceding correlation identity. -/
theorem analytic_row_correlation_bound
    (hAnalytic : analyticPrestateHypothesis) (C : ℝ) (hC : 1 ≤ C) :
    ∃ A > 0, ∃ t0 > 0,
      ∀ (n : ℕ) (t : ℝ) (s : AndersonAC.S45.State (Fin n))
        (Λplus Wstar : AndersonAC.S45.Form (Fin n)) (i : Fin n),
        t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
        (∑ x, s.F t i x * ∑ j, s.F t i j * s.F t x j) ≤
          A * AndersonAC.S45.power t AndersonAC.S45.kappa *
            AndersonAC.S45.rowCap t := by
  obtain ⟨A, hApos, t0, ht0, hFacts⟩ := hAnalytic C hC
  refine ⟨A, hApos, t0, ht0, ?_⟩
  intro n t s Λplus Wstar i htt hPre
  have hFsym : (s.F t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro x y
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare,
      AndersonAC.S45.State.h, Matrix.IsSymm.apply hPre.symmetric y x]
  rw [row_correlation_eq_cube (s.F t) hFsym i]
  exact (hFacts n t s Λplus Wstar htt hPre).2.2 i

/-- Cauchy--Schwarz turns the linear fourth-proxy envelope into the same
row-correlation controlled by `F³`. -/
theorem fourth_linear_envelope_stack_bound {P : Type*} [Fintype P] [DecidableEq P]
    (F : Matrix P P ℝ) (hFsym : F.IsSymm) (hFnonneg : ∀ i j, 0 ≤ F i j)
    (i : P) (S : Finset P) (G H K : ℝ)
    (hH : 0 ≤ H)
    (hrow : (∑ j, F i j ^ 2) ≤ H)
    (hcube : (F ^ 3) i i ≤ K) :
    (∑ x ∈ S,
      (4 * G * Real.sqrt (F i x) *
        (∑ j, F i j * Real.sqrt (F i j * F x j))) ^ 2) ≤
      16 * G ^ 2 * H * K := by
  classical
  let corr : P → ℝ := fun x => ∑ j, F i j * F x j
  let lin : P → ℝ := fun x =>
    4 * G * Real.sqrt (F i x) *
      (∑ j, F i j * Real.sqrt (F i j * F x j))
  have hcorr_nonneg : ∀ x, 0 ≤ corr x := by
    intro x
    dsimp [corr]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hFnonneg i j) (hFnonneg x j)
  have hsum_cauchy : ∀ x,
      (∑ j, F i j * Real.sqrt (F i j * F x j)) ^ 2 ≤
        (∑ j, F i j ^ 2) * corr x := by
    intro x
    dsimp [corr]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun j _ => sq_nonneg (F i j))
      (fun j _ => mul_nonneg (hFnonneg i j) (hFnonneg x j))
    intro j _
    have hprod : 0 ≤ F i j * F x j := mul_nonneg (hFnonneg i j) (hFnonneg x j)
    rw [mul_pow, Real.sq_sqrt hprod]
  have hlin_sq : ∀ x,
      lin x ^ 2 ≤ 16 * G ^ 2 * H * (F i x * corr x) := by
    intro x
    dsimp [lin]
    have hcs := hsum_cauchy x
    have hsqrt : (Real.sqrt (F i x)) ^ 2 = F i x :=
      Real.sq_sqrt (hFnonneg i x)
    have hcoef : 0 ≤ 16 * G ^ 2 * F i x :=
      mul_nonneg (by positivity) (hFnonneg i x)
    have hm := mul_le_mul_of_nonneg_left hcs hcoef
    have hrowCorr := mul_le_mul_of_nonneg_right hrow (hcorr_nonneg x)
    have hm2 := mul_le_mul_of_nonneg_left hrowCorr hcoef
    calc
      lin x ^ 2 = (4 * G) ^ 2 * (Real.sqrt (F i x)) ^ 2 *
          (∑ j, F i j * Real.sqrt (F i j * F x j)) ^ 2 := by
            dsimp [lin]
            ring
      _ = 16 * G ^ 2 * F i x *
          (∑ j, F i j * Real.sqrt (F i j * F x j)) ^ 2 := by
            rw [hsqrt]
            ring
      _ ≤ 16 * G ^ 2 * F i x *
          ((∑ j, F i j ^ 2) * corr x) := hm
      _ ≤ 16 * G ^ 2 * F i x * (H * corr x) := hm2
      _ = 16 * G ^ 2 * H * (F i x * corr x) := by ring
  calc
    (∑ x ∈ S, lin x ^ 2) ≤
        ∑ x ∈ S, 16 * G ^ 2 * H * (F i x * corr x) := by
          apply Finset.sum_le_sum
          intro x hx
          exact hlin_sq x
    _ ≤ ∑ x, 16 * G ^ 2 * H * (F i x * corr x) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          intro x hx _
          exact mul_nonneg (by positivity)
            (mul_nonneg (hFnonneg i x) (hcorr_nonneg x))
    _ = 16 * G ^ 2 * H * (F ^ 3) i i := by
          dsimp [corr]
          rw [← row_correlation_eq_cube F hFsym i]
          rw [← Finset.mul_sum]
    _ ≤ 16 * G ^ 2 * H * K := by
          exact mul_le_mul_of_nonneg_left hcube (by positivity)

/-- The linear term in the scalar fourth-power expansion, before summing its
remaining column, for a fixed row and candidate pivot. -/
def fourthLinearEnvelope {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (cols : Finset P)
    (i x : P) (ξ : ℝ) : ℝ :=
  ∑ j ∈ cols.erase x,
    4 * ‖s.h t i j‖ ^ 3 *
      ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖

/-- The actual linear fourth-proxy envelope has the square-stack bound from
the row fourth-power cap and the `F³` diagonal bound. -/
theorem fourth_linear_proxy_stack_bound {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (cols S : Finset P) (i : P)
    (z : P → ℝ) (G H K : ℝ) (hsym : s.g.IsSymm) (hG : 0 ≤ G)
    (hgamma : ∀ x ∈ S, ‖AndersonAC.S45.gamma t s x (z x)‖ ≤ G)
    (hrow : (∑ j, s.F t i j ^ 2) ≤ H)
    (hcube : (s.F t ^ 3) i i ≤ K) :
    (∑ x ∈ S,
      (fourthLinearEnvelope t s cols i x (z x)) ^ 2) ≤
      16 * G ^ 2 * H * K := by
  have hFsym : (s.F t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare,
      AndersonAC.S45.State.h, Matrix.IsSymm.apply hsym a b]
  have hFnonneg : ∀ a b, 0 ≤ s.F t a b := by
    intro a b
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare]
  have hroot : ∀ a b, Real.sqrt (s.F t a b) = ‖s.h t a b‖ := by
    intro a b
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare]
  let lin : P → ℝ := fun x =>
    4 * G * Real.sqrt (s.F t i x) *
      (∑ j, s.F t i j * Real.sqrt (s.F t i j * s.F t x j))
  have hlin_nonneg : ∀ x, 0 ≤ lin x := by
    intro x
    dsimp [lin]
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (Finset.sum_nonneg fun j _ =>
        mul_nonneg (hFnonneg i j) (Real.sqrt_nonneg _))
  have hEnvelope_le : ∀ x ∈ S, fourthLinearEnvelope t s cols i x (z x) ≤ lin x := by
    intro x hx
    unfold fourthLinearEnvelope
    let q : P → ℝ := fun j =>
      4 * G * Real.sqrt (s.F t i x) *
        (s.F t i j * Real.sqrt (s.F t i j * s.F t x j))
    have hterm : ∀ j,
        4 * ‖s.h t i j‖ ^ 3 *
            ‖AndersonAC.S45.gamma t s x (z x) * s.h t i x * s.h t x j‖ ≤ q j := by
      intro j
      have hg : ‖AndersonAC.S45.gamma t s x (z x) * s.h t i x * s.h t x j‖ ≤
          G * ‖s.h t i x‖ * ‖s.h t x j‖ := by
        rw [norm_mul, norm_mul]
        have := hgamma x hx
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right this (norm_nonneg _)) (norm_nonneg _)
      have hmulroot :
          Real.sqrt (s.F t i j * s.F t x j) =
            ‖s.h t i j‖ * ‖s.h t x j‖ := by
        rw [Real.sqrt_mul (hFnonneg i j), hroot, hroot]
      have hrooti := hroot i x
      have hrootj := hroot i j
      have hrootxj := hroot x j
      have hFij : s.F t i j = ‖s.h t i j‖ ^ 2 := by
        rfl
      have hcubeNorm : ‖s.h t i j‖ ^ 3 = s.F t i j * ‖s.h t i j‖ := by
        calc
          ‖s.h t i j‖ ^ 3 = ‖s.h t i j‖ ^ 2 * ‖s.h t i j‖ := by ring
          _ = s.F t i j * ‖s.h t i j‖ := by rw [← hFij]
      calc
        4 * ‖s.h t i j‖ ^ 3 *
            ‖AndersonAC.S45.gamma t s x (z x) * s.h t i x * s.h t x j‖ ≤
          4 * ‖s.h t i j‖ ^ 3 *
            (G * ‖s.h t i x‖ * ‖s.h t x j‖) := by
              gcongr
        _ = q j := by
          dsimp [q]
          calc
            4 * ‖s.h t i j‖ ^ 3 *
                (G * ‖s.h t i x‖ * ‖s.h t x j‖) =
              4 * G * Real.sqrt (s.F t i x) *
                (‖s.h t i j‖ ^ 3 * ‖s.h t x j‖) := by
                  rw [← hrooti]
                  ring
            _ = 4 * G * Real.sqrt (s.F t i x) *
                (s.F t i j * ‖s.h t i j‖ * ‖s.h t x j‖) := by
                  rw [hcubeNorm]
            _ = 4 * G * Real.sqrt (s.F t i x) *
                (s.F t i j * Real.sqrt (s.F t i j * s.F t x j)) := by
                  rw [hmulroot]
                  ring
    have hsumle :
        (∑ j ∈ cols.erase x,
          4 * ‖s.h t i j‖ ^ 3 *
            ‖AndersonAC.S45.gamma t s x (z x) * s.h t i x * s.h t x j‖) ≤
          ∑ j ∈ cols.erase x, q j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hterm j
    have hqnonneg : ∀ j, 0 ≤ q j := by
      intro j
      dsimp [q]
      exact mul_nonneg
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (mul_nonneg (hFnonneg i j) (Real.sqrt_nonneg _))
    have hsum_subset : (∑ j ∈ cols.erase x, q j) ≤ ∑ j, q j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (cols.erase x))
      intro j hj _
      exact hqnonneg j
    calc
      (∑ j ∈ cols.erase x,
        4 * ‖s.h t i j‖ ^ 3 *
          ‖AndersonAC.S45.gamma t s x (z x) * s.h t i x * s.h t x j‖)
          ≤ ∑ j ∈ cols.erase x, q j := hsumle
      _ ≤ ∑ j, q j := hsum_subset
      _ = lin x := by simp [q, lin, Finset.mul_sum]
  have hH : 0 ≤ H :=
    le_trans (Finset.sum_nonneg fun j _ => sq_nonneg (s.F t i j)) hrow
  have hlinStack : (∑ x ∈ S, lin x ^ 2) ≤ 16 * G ^ 2 * H * K :=
    fourth_linear_envelope_stack_bound
      (s.F t) hFsym hFnonneg i S G H K hH hrow hcube
  have hEnvelope_nonneg : ∀ x, 0 ≤ fourthLinearEnvelope t s cols i x (z x) := by
    intro x
    unfold fourthLinearEnvelope
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (norm_nonneg _)
  calc
    (∑ x ∈ S, (fourthLinearEnvelope t s cols i x (z x)) ^ 2) ≤
        ∑ x ∈ S, (lin x) ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          exact (sq_le_sq₀ (hEnvelope_nonneg x) (hlin_nonneg x)).2 (hEnvelope_le x hx)
    _ ≤ 16 * G ^ 2 * H * K := hlinStack

/-- The quadratic term in the fourth-power expansion is smaller by one
additional row-cap factor. -/
theorem fourth_quadratic_envelope_stack_bound {P : Type*} [Fintype P]
    (F : Matrix P P ℝ) (i : P) (S : Finset P) (G H : ℝ)
    (hH : 0 ≤ H) (hrowsq : ∀ x, (∑ j, F x j ^ 2) ≤ H) :
    (∑ x ∈ S, (6 * G ^ 2 * F i x * (∑ j, F i j * F x j)) ^ 2) ≤
      36 * G ^ 4 * H ^ 3 := by
  classical
  let corr : P → ℝ := fun x => ∑ j, F i j * F x j
  have hrow_nonneg : ∀ x, 0 ≤ ∑ j, F x j ^ 2 := by
    intro x
    exact Finset.sum_nonneg fun j _ => sq_nonneg (F x j)
  have hcorr_sq : ∀ x, (corr x) ^ 2 ≤ H ^ 2 := by
    intro x
    have hcs : (corr x) ^ 2 ≤ (∑ j, F i j ^ 2) * ∑ j, F x j ^ 2 := by
      dsimp [corr]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hprod : (∑ j, F i j ^ 2) * (∑ j, F x j ^ 2) ≤ H * H := by
      calc
        (∑ j, F i j ^ 2) * (∑ j, F x j ^ 2) ≤
            H * (∑ j, F x j ^ 2) :=
              mul_le_mul_of_nonneg_right (hrowsq i) (hrow_nonneg x)
        _ ≤ H * H := mul_le_mul_of_nonneg_left (hrowsq x) hH
    have hHpow : H * H = H ^ 2 := by ring
    exact hcs.trans (hprod.trans_eq hHpow)
  have hsumSq : (∑ x, (F i x) ^ 2) ≤ H := hrowsq i
  calc
    (∑ x ∈ S, (6 * G ^ 2 * F i x * corr x) ^ 2) ≤
        ∑ x ∈ S, 36 * G ^ 4 * (F i x) ^ 2 * H ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          have hcoef : 0 ≤ 36 * G ^ 4 * (F i x) ^ 2 := by positivity
          have hm := mul_le_mul_of_nonneg_left (hcorr_sq x) hcoef
          calc
            (6 * G ^ 2 * F i x * corr x) ^ 2 =
                (36 * G ^ 4 * (F i x) ^ 2) * corr x ^ 2 := by ring
            _ ≤ (36 * G ^ 4 * (F i x) ^ 2) * H ^ 2 := hm
    _ ≤ ∑ x, 36 * G ^ 4 * (F i x) ^ 2 * H ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          intro x hx _
          positivity
    _ = 36 * G ^ 4 * H ^ 2 * ∑ x, (F i x) ^ 2 := by
          calc
            _ = ∑ x, (36 * G ^ 4 * H ^ 2) * (F i x) ^ 2 := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = 36 * G ^ 4 * H ^ 2 * ∑ x, (F i x) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 36 * G ^ 4 * H ^ 2 * H :=
          mul_le_mul_of_nonneg_left hsumSq (by positivity)
    _ = 36 * G ^ 4 * H ^ 3 := by ring

/-- The cubic envelope is controlled by the bounded row sums and the row
fourth-power cap. -/
theorem fourth_cubic_envelope_stack_bound {P : Type*} [Fintype P]
    (F : Matrix P P ℝ) (i : P) (S : Finset P) (G H A : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hrowsq : ∀ x, (∑ j, F x j ^ 2) ≤ H)
    (hrowsum : ∀ x, (∑ j, F x j) ≤ A)
    (hFnonneg : ∀ x j, 0 ≤ F x j) :
    (∑ x ∈ S,
      (4 * G ^ 3 * F i x * Real.sqrt (F i x) *
        (∑ j, Real.sqrt (F i j) * (F x j * Real.sqrt (F x j)))) ^ 2) ≤
      16 * G ^ 6 * A * H ^ 3 := by
  classical
  let cub x : ℝ := ∑ j, F x j ^ 3
  let third x : ℝ :=
    ∑ j, Real.sqrt (F i j) * (F x j * Real.sqrt (F x j))
  have hentrySq : ∀ x j, F x j ^ 2 ≤ H := by
    intro x j
    calc
      F x j ^ 2 ≤ ∑ k, F x k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (F x k)) (Finset.mem_univ j)
      _ ≤ H := hrowsq x
  have hentryRoot : ∀ x j, F x j ≤ Real.sqrt H := by
    intro x j
    exact Real.le_sqrt_of_sq_le (hentrySq x j)
  have hcub : ∀ x, cub x ≤ Real.sqrt H * H := by
    intro x
    dsimp [cub]
    calc
      ∑ j, F x j ^ 3 ≤ ∑ j, Real.sqrt H * F x j ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hmul := mul_le_mul_of_nonneg_right (hentryRoot x j)
          (sq_nonneg (F x j))
        nlinarith [hmul]
      _ = Real.sqrt H * ∑ j, F x j ^ 2 := by rw [← Finset.mul_sum]
      _ ≤ Real.sqrt H * H := mul_le_mul_of_nonneg_left (hrowsq x)
        (Real.sqrt_nonneg H)
  have hthirdSq : ∀ x, third x ^ 2 ≤ A * (Real.sqrt H * H) := by
    intro x
    dsimp [third]
    have hcs :
        (∑ j, Real.sqrt (F i j) * (F x j * Real.sqrt (F x j))) ^ 2 ≤
          (∑ j, F i j) * cub x := by
      calc
        (∑ j, Real.sqrt (F i j) * (F x j * Real.sqrt (F x j))) ^ 2 ≤
            (∑ j, (Real.sqrt (F i j)) ^ 2) *
              ∑ j, (F x j * Real.sqrt (F x j)) ^ 2 :=
                Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = (∑ j, F i j) * cub x := by
          congr 1
          · apply Finset.sum_congr rfl
            intro j hj
            rw [Real.sq_sqrt (hFnonneg i j)]
          · apply Finset.sum_congr rfl
            intro j hj
            rw [mul_pow, Real.sq_sqrt (hFnonneg x j)]
            ring
    have hrowSumNonneg : 0 ≤ ∑ j, F i j :=
      Finset.sum_nonneg fun j _ => hFnonneg i j
    have hcubNonneg : 0 ≤ cub x := by
      dsimp [cub]
      exact Finset.sum_nonneg fun j _ => pow_nonneg (hFnonneg x j) 3
    have hfirst := mul_le_mul_of_nonneg_right (hrowsum i) hcubNonneg
    have hsecond := mul_le_mul_of_nonneg_left (hcub x) hA
    exact hcs.trans (hfirst.trans hsecond)
  have hrowCube : cub i ≤ Real.sqrt H * H := hcub i
  calc
    (∑ x ∈ S,
      (4 * G ^ 3 * F i x * Real.sqrt (F i x) * third x) ^ 2) ≤
        ∑ x ∈ S, 16 * G ^ 6 * (F i x) ^ 3 *
          (A * (Real.sqrt H * H)) := by
            apply Finset.sum_le_sum
            intro x hx
            have hsqrt : (Real.sqrt (F i x)) ^ 2 = F i x :=
              Real.sq_sqrt (hFnonneg i x)
            have hcoef : 0 ≤ 16 * G ^ 6 * (F i x) ^ 3 :=
              mul_nonneg (by positivity) (pow_nonneg (hFnonneg i x) 3)
            have hm := mul_le_mul_of_nonneg_left (hthirdSq x) hcoef
            calc
              (4 * G ^ 3 * F i x * Real.sqrt (F i x) * third x) ^ 2 =
                  (16 * G ^ 6 * (F i x) ^ 3) * third x ^ 2 := by
                    calc
                      _ = (4 * G ^ 3) ^ 2 * (F i x) ^ 2 *
                          (Real.sqrt (F i x)) ^ 2 * third x ^ 2 := by ring
                      _ = (16 * G ^ 6 * (F i x) ^ 3) * third x ^ 2 := by
                        rw [hsqrt]
                        ring
              _ ≤ 16 * G ^ 6 * (F i x) ^ 3 *
                  (A * (Real.sqrt H * H)) := hm
    _ ≤ ∑ x, 16 * G ^ 6 * (F i x) ^ 3 *
          (A * (Real.sqrt H * H)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            intro x hx _
            exact mul_nonneg
              (mul_nonneg (by positivity) (pow_nonneg (hFnonneg i x) 3))
              (mul_nonneg hA (mul_nonneg (Real.sqrt_nonneg H) hH))
    _ = 16 * G ^ 6 * (A * (Real.sqrt H * H)) * cub i := by
          calc
            _ = ∑ x, (16 * G ^ 6 * (A * (Real.sqrt H * H))) * (F i x) ^ 3 := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = 16 * G ^ 6 * (A * (Real.sqrt H * H)) * cub i := by
              simp [cub, Finset.mul_sum]
    _ ≤ 16 * G ^ 6 * (A * (Real.sqrt H * H)) * (Real.sqrt H * H) :=
          mul_le_mul_of_nonneg_left hrowCube (by positivity)
    _ = 16 * G ^ 6 * A * H ^ 3 := by
          have hrootSq : (Real.sqrt H) ^ 2 = H := Real.sq_sqrt hH
          calc
            16 * G ^ 6 * (A * (Real.sqrt H * H)) * (Real.sqrt H * H) =
              16 * G ^ 6 * A * ((Real.sqrt H) ^ 2 * H ^ 2) := by ring
            _ = 16 * G ^ 6 * A * (H * H ^ 2) := by rw [hrootSq]
            _ = 16 * G ^ 6 * A * H ^ 3 := by ring

/-- The quartic remainder envelope is smaller still, using only the row
fourth-power cap. -/
theorem fourth_quartic_envelope_stack_bound {P : Type*} [Fintype P]
    (F : Matrix P P ℝ) (i : P) (S : Finset P) (G H : ℝ)
    (hH : 0 ≤ H) (hrowsq : ∀ x, (∑ j, F x j ^ 2) ≤ H) :
    (∑ x ∈ S,
      (G ^ 4 * (F i x) ^ 2 * (∑ j, F x j ^ 2)) ^ 2) ≤
      G ^ 8 * H ^ 4 := by
  classical
  have hrow_nonneg : ∀ x, 0 ≤ ∑ j, F x j ^ 2 := by
    intro x
    exact Finset.sum_nonneg fun j _ => sq_nonneg (F x j)
  have hentrySq : ∀ x, (F i x) ^ 2 ≤ H := by
    intro x
    calc
      (F i x) ^ 2 ≤ ∑ j, F i j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (F i j)) (Finset.mem_univ x)
      _ ≤ H := hrowsq i
  have hrowFourth : (∑ x, (F i x) ^ 4) ≤ H ^ 2 := by
    calc
      ∑ x, (F i x) ^ 4 ≤ ∑ x, H * (F i x) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        have hm := mul_le_mul_of_nonneg_right (hentrySq x) (sq_nonneg (F i x))
        nlinarith [hm]
      _ = H * ∑ x, (F i x) ^ 2 := by rw [← Finset.mul_sum]
      _ ≤ H * H := mul_le_mul_of_nonneg_left (hrowsq i) hH
      _ = H ^ 2 := by ring
  calc
    (∑ x ∈ S,
      (G ^ 4 * (F i x) ^ 2 * (∑ j, F x j ^ 2)) ^ 2) ≤
        ∑ x ∈ S, G ^ 8 * (F i x) ^ 4 * H ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          have hsquare : (∑ j, F x j ^ 2) ^ 2 ≤ H ^ 2 :=
            (sq_le_sq₀ (hrow_nonneg x) hH).2 (hrowsq x)
          have hcoef : 0 ≤ G ^ 8 * (F i x) ^ 4 := by positivity
          have hm := mul_le_mul_of_nonneg_left hsquare hcoef
          calc
            (G ^ 4 * (F i x) ^ 2 * (∑ j, F x j ^ 2)) ^ 2 =
                (G ^ 8 * (F i x) ^ 4) * (∑ j, F x j ^ 2) ^ 2 := by ring
            _ ≤ G ^ 8 * (F i x) ^ 4 * H ^ 2 := hm
    _ ≤ ∑ x, G ^ 8 * (F i x) ^ 4 * H ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          intro x hx _
          positivity
    _ = G ^ 8 * H ^ 2 * ∑ x, (F i x) ^ 4 := by
          calc
            _ = ∑ x, (G ^ 8 * H ^ 2) * (F i x) ^ 4 := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = G ^ 8 * H ^ 2 * ∑ x, (F i x) ^ 4 := by rw [Finset.mul_sum]
    _ ≤ G ^ 8 * H ^ 2 * H ^ 2 :=
          mul_le_mul_of_nonneg_left hrowFourth (by positivity)
    _ = G ^ 8 * H ^ 4 := by ring

/-- Combining the four scalar expansion envelopes costs only a factor four in
the sum of their separate square-stack bounds. -/
theorem fourth_all_envelopes_stack_bound {P : Type*} [Fintype P] [DecidableEq P]
    (F : Matrix P P ℝ) (hFsym : F.IsSymm) (hFnonneg : ∀ x j, 0 ≤ F x j)
    (i : P) (S : Finset P) (G H A K : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hrowsq : ∀ x, (∑ j, F x j ^ 2) ≤ H)
    (hrowsum : ∀ x, (∑ j, F x j) ≤ A)
    (hcube : (F ^ 3) i i ≤ K) :
    (∑ x ∈ S,
      (4 * G * Real.sqrt (F i x) *
          (∑ j, F i j * Real.sqrt (F i j * F x j)) +
        6 * G ^ 2 * F i x * (∑ j, F i j * F x j) +
        4 * G ^ 3 * F i x * Real.sqrt (F i x) *
          (∑ j, Real.sqrt (F i j) * (F x j * Real.sqrt (F x j))) +
        G ^ 4 * (F i x) ^ 2 * (∑ j, F x j ^ 2)) ^ 2) ≤
      4 * (16 * G ^ 2 * H * K + 36 * G ^ 4 * H ^ 3 +
        16 * G ^ 6 * A * H ^ 3 + G ^ 8 * H ^ 4) := by
  let lin : P → ℝ := fun x => 4 * G * Real.sqrt (F i x) *
    (∑ j, F i j * Real.sqrt (F i j * F x j))
  let quad : P → ℝ := fun x => 6 * G ^ 2 * F i x * (∑ j, F i j * F x j)
  let cubic : P → ℝ := fun x => 4 * G ^ 3 * F i x * Real.sqrt (F i x) *
    (∑ j, Real.sqrt (F i j) * (F x j * Real.sqrt (F x j)))
  let quartic : P → ℝ := fun x => G ^ 4 * (F i x) ^ 2 * (∑ j, F x j ^ 2)
  have hlin := fourth_linear_envelope_stack_bound F hFsym hFnonneg i S G H K hH
    (hrowsq i) hcube
  have hquad := fourth_quadratic_envelope_stack_bound F i S G H hH hrowsq
  have hcubic := fourth_cubic_envelope_stack_bound F i S G H A hH hA
    hrowsq hrowsum hFnonneg
  have hquartic := fourth_quartic_envelope_stack_bound F i S G H hH hrowsq
  have hfour (x : P) :
      (lin x + quad x + cubic x + quartic x) ^ 2 ≤
        4 * (lin x ^ 2 + quad x ^ 2 + cubic x ^ 2 + quartic x ^ 2) := by
    nlinarith [sq_nonneg (lin x - quad x), sq_nonneg (lin x - cubic x),
      sq_nonneg (lin x - quartic x), sq_nonneg (quad x - cubic x),
      sq_nonneg (quad x - quartic x), sq_nonneg (cubic x - quartic x)]
  calc
    (∑ x ∈ S, (lin x + quad x + cubic x + quartic x) ^ 2) ≤
        ∑ x ∈ S, 4 * (lin x ^ 2 + quad x ^ 2 + cubic x ^ 2 + quartic x ^ 2) := by
          apply Finset.sum_le_sum
          intro x hx
          exact hfour x
    _ = 4 * ((∑ x ∈ S, lin x ^ 2) + (∑ x ∈ S, quad x ^ 2) +
        (∑ x ∈ S, cubic x ^ 2) + (∑ x ∈ S, quartic x ^ 2)) := by
          calc
            _ = 4 * ∑ x ∈ S,
                (lin x ^ 2 + quad x ^ 2 + cubic x ^ 2 + quartic x ^ 2) := by
                  rw [← Finset.mul_sum]
            _ = 4 * ((∑ x ∈ S, lin x ^ 2) + (∑ x ∈ S, quad x ^ 2) +
                (∑ x ∈ S, cubic x ^ 2) + (∑ x ∈ S, quartic x ^ 2)) := by
                  simp_rw [Finset.sum_add_distrib]
    _ ≤ 4 * (16 * G ^ 2 * H * K + 36 * G ^ 4 * H ^ 3 +
        16 * G ^ 6 * A * H ^ 3 + G ^ 8 * H ^ 4) := by
          gcongr

/-- Pointwise fourth-proxy increments are bounded by the four matrix
envelopes used in `fourth_all_envelopes_stack_bound`. -/
theorem fourthProxy_abs_le_F_envelopes {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : AndersonAC.S45.State P) (cols : Finset P)
    (i x : P) (ξ G : ℝ) (hG : 0 ≤ G)
    (hgamma : ‖AndersonAC.S45.gamma t s x ξ‖ ≤ G) :
    |AndersonAC.S45.fourthProxy t s cols i x ξ| ≤
      4 * G * Real.sqrt (s.F t i x) *
          (∑ j, s.F t i j * Real.sqrt (s.F t i j * s.F t x j)) +
      6 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
      4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) *
          (∑ j, Real.sqrt (s.F t i j) * (s.F t x j * Real.sqrt (s.F t x j))) +
      G ^ 4 * (s.F t i x) ^ 2 * (∑ j, s.F t x j ^ 2) := by
  have hFnonneg : ∀ a b, 0 ≤ s.F t a b := by
    intro a b
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare]
  have hroot : ∀ a b, Real.sqrt (s.F t a b) = ‖s.h t a b‖ := by
    intro a b
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare]
  have hprod : ∀ j,
      ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ≤
        G * ‖s.h t i x‖ * ‖s.h t x j‖ := by
    intro j
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hgamma (norm_nonneg _)) (norm_nonneg _)
  let e₁ : P → ℝ := fun j =>
    4 * ‖s.h t i j‖ ^ 3 *
      ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖
  let e₂ : P → ℝ := fun j =>
    6 * ‖s.h t i j‖ ^ 2 *
      ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 2
  let e₃ : P → ℝ := fun j =>
    4 * ‖s.h t i j‖ *
      ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 3
  let e₄ : P → ℝ := fun j =>
      ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 4
  let u₁ : P → ℝ := fun j =>
    4 * G * Real.sqrt (s.F t i x) *
      (s.F t i j * Real.sqrt (s.F t i j * s.F t x j))
  let u₂ : P → ℝ := fun j =>
    6 * G ^ 2 * s.F t i x * (s.F t i j * s.F t x j)
  let u₃ : P → ℝ := fun j =>
    4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) *
      (Real.sqrt (s.F t i j) * (s.F t x j * Real.sqrt (s.F t x j)))
  let u₄ : P → ℝ := fun j => G ^ 4 * (s.F t i x) ^ 2 * (s.F t x j) ^ 2
  have hFij : ∀ a b, s.F t a b = ‖s.h t a b‖ ^ 2 := by
    intro a b
    rfl
  have hcubeNorm : ∀ a b, ‖s.h t a b‖ ^ 3 = s.F t a b * ‖s.h t a b‖ := by
    intro a b
    calc
      ‖s.h t a b‖ ^ 3 = ‖s.h t a b‖ ^ 2 * ‖s.h t a b‖ := by ring
      _ = s.F t a b * ‖s.h t a b‖ := by rw [← hFij a b]
  have hterm₁ : ∀ j, e₁ j ≤ u₁ j := by
    intro j
    dsimp [e₁, u₁]
    have hmulroot :
        Real.sqrt (s.F t i j * s.F t x j) = ‖s.h t i j‖ * ‖s.h t x j‖ := by
      rw [Real.sqrt_mul (hFnonneg i j), hroot, hroot]
    calc
      4 * ‖s.h t i j‖ ^ 3 *
          ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ≤
        4 * ‖s.h t i j‖ ^ 3 * (G * ‖s.h t i x‖ * ‖s.h t x j‖) := by
          exact mul_le_mul_of_nonneg_left (hprod j) (by positivity)
      _ = 4 * G * ‖s.h t i x‖ *
          (‖s.h t i j‖ ^ 3 * ‖s.h t x j‖) := by ring
      _ = 4 * G * Real.sqrt (s.F t i x) *
          (‖s.h t i j‖ ^ 3 * ‖s.h t x j‖) := by rw [← hroot i x]
      _ = 4 * G * Real.sqrt (s.F t i x) *
          (s.F t i j * ‖s.h t i j‖ * ‖s.h t x j‖) := by rw [hcubeNorm i j]
      _ = 4 * G * Real.sqrt (s.F t i x) *
          (s.F t i j * Real.sqrt (s.F t i j * s.F t x j)) := by
            rw [hmulroot]
            ring
  have hterm₂ : ∀ j, e₂ j ≤ u₂ j := by
    intro j
    dsimp [e₂, u₂]
    have hpow :
        ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 2 ≤
          (G * ‖s.h t i x‖ * ‖s.h t x j‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hprod j)
    calc
      6 * ‖s.h t i j‖ ^ 2 *
          ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 2 ≤
        6 * ‖s.h t i j‖ ^ 2 *
          (G * ‖s.h t i x‖ * ‖s.h t x j‖) ^ 2 := by gcongr
      _ = 6 * G ^ 2 * s.F t i x * (s.F t i j * s.F t x j) := by
          calc
            _ = 6 * G ^ 2 * (‖s.h t i x‖ ^ 2) *
                ((‖s.h t i j‖ ^ 2) * (‖s.h t x j‖ ^ 2)) := by ring
            _ = 6 * G ^ 2 * s.F t i x * (s.F t i j * s.F t x j) := by
                rw [← hFij i x, ← hFij i j, ← hFij x j]
  have hterm₃ : ∀ j, e₃ j ≤ u₃ j := by
    intro j
    dsimp [e₃, u₃]
    have hpow :
        ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 3 ≤
          (G * ‖s.h t i x‖ * ‖s.h t x j‖) ^ 3 := by
      exact (pow_le_pow_left₀ (norm_nonneg _) (hprod j) 3)
    calc
      4 * ‖s.h t i j‖ *
          ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 3 ≤
        4 * ‖s.h t i j‖ *
          (G * ‖s.h t i x‖ * ‖s.h t x j‖) ^ 3 := by gcongr
      _ = 4 * G ^ 3 * ‖s.h t i x‖ ^ 3 * ‖s.h t i j‖ * ‖s.h t x j‖ ^ 3 := by ring
      _ = 4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) *
          (Real.sqrt (s.F t i j) * (s.F t x j * Real.sqrt (s.F t x j))) := by
          rw [hcubeNorm i x, hcubeNorm x j, ← hroot i x, ← hroot i j,
            ← hroot x j]
          ring
  have hterm₄ : ∀ j, e₄ j ≤ u₄ j := by
    intro j
    dsimp [e₄, u₄]
    have hpow :
        ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 4 ≤
          (G * ‖s.h t i x‖ * ‖s.h t x j‖) ^ 4 := by
      exact (pow_le_pow_left₀ (norm_nonneg _) (hprod j) 4)
    calc
      ‖AndersonAC.S45.gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 4 ≤
          (G * ‖s.h t i x‖ * ‖s.h t x j‖) ^ 4 := hpow
      _ = G ^ 4 * (s.F t i x) ^ 2 * (s.F t x j) ^ 2 := by
          calc
            _ = G ^ 4 * (‖s.h t i x‖ ^ 2) ^ 2 * (‖s.h t x j‖ ^ 2) ^ 2 := by ring
            _ = G ^ 4 * (s.F t i x) ^ 2 * (s.F t x j) ^ 2 := by
              rw [← hFij i x, ← hFij x j]
  have hsumBase :
      |AndersonAC.S45.fourthProxy t s cols i x ξ| ≤
        (∑ j ∈ cols.erase x, e₁ j) + (∑ j ∈ cols.erase x, e₂ j) +
          (∑ j ∈ cols.erase x, e₃ j) + (∑ j ∈ cols.erase x, e₄ j) := by
    by_cases hix : i = x
    · subst x
      simp [AndersonAC.S45.fourthProxy]
      positivity
    · have hbase := fourthProxy_abs_le t s cols i x ξ hix
      simpa [e₁, e₂, e₃, e₄, Finset.sum_add_distrib] using hbase
  have hE₁ : ∑ j ∈ cols.erase x, e₁ j ≤ ∑ j, u₁ j := by
    calc
      ∑ j ∈ cols.erase x, e₁ j ≤ ∑ j ∈ cols.erase x, u₁ j :=
        Finset.sum_le_sum fun j _ => hterm₁ j
      _ ≤ ∑ j, u₁ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (cols.erase x))
        intro j hj _
        dsimp [u₁]
        exact mul_nonneg
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
          (mul_nonneg (hFnonneg i j) (Real.sqrt_nonneg _))
  have hE₂ : ∑ j ∈ cols.erase x, e₂ j ≤ ∑ j, u₂ j := by
    calc
      ∑ j ∈ cols.erase x, e₂ j ≤ ∑ j ∈ cols.erase x, u₂ j :=
        Finset.sum_le_sum fun j _ => hterm₂ j
      _ ≤ ∑ j, u₂ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (cols.erase x))
        intro j hj _
        dsimp [u₂]
        exact mul_nonneg
          (mul_nonneg (by positivity) (hFnonneg i x))
          (mul_nonneg (hFnonneg i j) (hFnonneg x j))
  have hE₃ : ∑ j ∈ cols.erase x, e₃ j ≤ ∑ j, u₃ j := by
    calc
      ∑ j ∈ cols.erase x, e₃ j ≤ ∑ j ∈ cols.erase x, u₃ j :=
        Finset.sum_le_sum fun j _ => hterm₃ j
      _ ≤ ∑ j, u₃ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (cols.erase x))
        intro j hj _
        dsimp [u₃]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) (hFnonneg i x))
            (Real.sqrt_nonneg _))
          (mul_nonneg (Real.sqrt_nonneg _)
            (mul_nonneg (hFnonneg x j) (Real.sqrt_nonneg _)))
  have hE₄ : ∑ j ∈ cols.erase x, e₄ j ≤ ∑ j, u₄ j := by
    calc
      ∑ j ∈ cols.erase x, e₄ j ≤ ∑ j ∈ cols.erase x, u₄ j :=
        Finset.sum_le_sum fun j _ => hterm₄ j
      _ ≤ ∑ j, u₄ j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (cols.erase x))
        intro j hj _
        dsimp [u₄]
        exact mul_nonneg
          (mul_nonneg (by positivity) (sq_nonneg (s.F t i x)))
          (sq_nonneg (s.F t x j))
  calc
    |AndersonAC.S45.fourthProxy t s cols i x ξ| ≤
        (∑ j ∈ cols.erase x, e₁ j) + (∑ j ∈ cols.erase x, e₂ j) +
          (∑ j ∈ cols.erase x, e₃ j) + (∑ j ∈ cols.erase x, e₄ j) := hsumBase
    _ ≤ (∑ j, u₁ j) + (∑ j, u₂ j) + (∑ j, u₃ j) + (∑ j, u₄ j) := by
          linarith
    _ = 4 * G * Real.sqrt (s.F t i x) *
          (∑ j, s.F t i j * Real.sqrt (s.F t i j * s.F t x j)) +
        6 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
        4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) *
          (∑ j, Real.sqrt (s.F t i j) * (s.F t x j * Real.sqrt (s.F t x j))) +
        G ^ 4 * (s.F t i x) ^ 2 * (∑ j, s.F t x j ^ 2) := by
          simp [u₁, u₂, u₃, u₄, Finset.mul_sum]

/-- The deterministic square-stack estimate follows from row data and a
uniform pointwise bound on the scalar pivot parameter. -/
theorem fourthProxy_square_stack_of_matrix_bounds {P : Type*} [Fintype P]
    [DecidableEq P] (t : ℝ) (s : AndersonAC.S45.State P)
    (cols S : Finset P) (i : P) (z : P → ℝ) (G H A K : ℝ)
    (hG : 0 ≤ G) (hsym : s.g.IsSymm)
    (hgamma : ∀ x ∈ S, ‖AndersonAC.S45.gamma t s x (z x)‖ ≤ G)
    (hrowsq : ∀ r, (∑ j, s.F t r j ^ 2) ≤ H)
    (hrowsum : ∀ r, (∑ j, s.F t r j) ≤ A)
    (hcube : (s.F t ^ 3) i i ≤ K) :
    (∑ x ∈ S,
      |AndersonAC.S45.fourthProxy t s cols i x (z x)| ^ 2) ≤
      4 * (16 * G ^ 2 * H * K + 36 * G ^ 4 * H ^ 3 +
        16 * G ^ 6 * A * H ^ 3 + G ^ 8 * H ^ 4) := by
  have hFsym : (s.F t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro a b
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare,
      AndersonAC.S45.State.h, Matrix.IsSymm.apply hsym a b]
  have hFnonneg : ∀ a b, 0 ≤ s.F t a b := by
    intro a b
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare]
  have hpoint : ∀ x ∈ S,
      |AndersonAC.S45.fourthProxy t s cols i x (z x)| ^ 2 ≤
        (4 * G * Real.sqrt (s.F t i x) *
            (∑ j, s.F t i j * Real.sqrt (s.F t i j * s.F t x j)) +
          6 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
          4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) *
            (∑ j, Real.sqrt (s.F t i j) *
              (s.F t x j * Real.sqrt (s.F t x j))) +
          G ^ 4 * (s.F t i x) ^ 2 * (∑ j, s.F t x j ^ 2)) ^ 2 := by
    intro x hx
    have hp := fourthProxy_abs_le_F_envelopes t s cols i x (z x) G hG
      (hgamma x hx)
    have hnonneg : 0 ≤
        4 * G * Real.sqrt (s.F t i x) *
            (∑ j, s.F t i j * Real.sqrt (s.F t i j * s.F t x j)) +
          6 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
          4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) *
            (∑ j, Real.sqrt (s.F t i j) *
              (s.F t x j * Real.sqrt (s.F t x j))) +
          G ^ 4 * (s.F t i x) ^ 2 * (∑ j, s.F t x j ^ 2) := by
      have h1 : 0 ≤ 4 * G * Real.sqrt (s.F t i x) *
          (∑ j, s.F t i j * Real.sqrt (s.F t i j * s.F t x j)) :=
        mul_nonneg
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
          (Finset.sum_nonneg fun j _ =>
            mul_nonneg (hFnonneg i j) (Real.sqrt_nonneg _))
      have h2 : 0 ≤ 6 * G ^ 2 * s.F t i x *
          (∑ j, s.F t i j * s.F t x j) :=
        mul_nonneg
          (mul_nonneg (by positivity) (hFnonneg i x))
          (Finset.sum_nonneg fun j _ => mul_nonneg (hFnonneg i j) (hFnonneg x j))
      have h3 : 0 ≤ 4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) *
          (∑ j, Real.sqrt (s.F t i j) * (s.F t x j * Real.sqrt (s.F t x j))) := by
        have hcoeff : 0 ≤ 4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) :=
          mul_nonneg
            (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hG 3))
              (hFnonneg i x))
            (Real.sqrt_nonneg _)
        have hsum : 0 ≤ ∑ j, Real.sqrt (s.F t i j) *
            (s.F t x j * Real.sqrt (s.F t x j)) :=
          Finset.sum_nonneg fun j _ =>
            mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (hFnonneg x j)
              (Real.sqrt_nonneg _))
        exact mul_nonneg hcoeff hsum
      have h4 : 0 ≤ G ^ 4 * (s.F t i x) ^ 2 *
          (∑ j, s.F t x j ^ 2) :=
        mul_nonneg
          (mul_nonneg (pow_nonneg hG 4) (sq_nonneg (s.F t i x)))
          (Finset.sum_nonneg fun j _ => sq_nonneg (s.F t x j))
      linarith
    exact (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hp
  calc
    (∑ x ∈ S,
      |AndersonAC.S45.fourthProxy t s cols i x (z x)| ^ 2) ≤
        ∑ x ∈ S,
          (4 * G * Real.sqrt (s.F t i x) *
              (∑ j, s.F t i j * Real.sqrt (s.F t i j * s.F t x j)) +
            6 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
            4 * G ^ 3 * s.F t i x * Real.sqrt (s.F t i x) *
              (∑ j, Real.sqrt (s.F t i j) *
                (s.F t x j * Real.sqrt (s.F t x j))) +
            G ^ 4 * (s.F t i x) ^ 2 * (∑ j, s.F t x j ^ 2)) ^ 2 := by
              apply Finset.sum_le_sum
              intro x hx
              exact hpoint x hx
    _ ≤ 4 * (16 * G ^ 2 * H * K + 36 * G ^ 4 * H ^ 3 +
          16 * G ^ 6 * A * H ^ 3 + G ^ 8 * H ^ 4) :=
            fourth_all_envelopes_stack_bound
              (s.F t) hFsym hFnonneg i S G H A K
              (le_trans (Finset.sum_nonneg fun j _ => sq_nonneg (s.F t i j))
                (hrowsq i))
              (le_trans (Finset.sum_nonneg fun j _ => hFnonneg i j) (hrowsum i))
              hrowsq hrowsum hcube

/-- Conditional deterministic square-stack half of Lemma 4.7 for the
canonical finite index type. -/
theorem fourth_bounds_stack_fin_of_analyticPrestate
    (hAnalytic : analyticPrestateHypothesis) (C : ℝ) (hC : 1 ≤ C) :
    ∃ C' > 0, ∃ t0 > 0,
      ∀ (n : ℕ) (Ω : Type) [mΩ : MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ)
        (s : AndersonAC.S45.State (Fin n))
        (Λplus Wstar : AndersonAC.S45.Form (Fin n))
        (S cols : Finset (Fin n)) (ξ : Fin n → Ω → ℝ),
        t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
        (∀ x ∈ S, AndersonAC.S45.MomentLaw μ t C (ξ x)) →
        (∀ z : Fin n → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ i,
          (∑ x ∈ S,
            |AndersonAC.S45.fourthProxy t s cols i x (z x)| ^ 2) ≤
            C' * AndersonAC.S45.power t AndersonAC.S45.kappa *
              AndersonAC.S45.rowCap t ^ 2) := by
  obtain ⟨A, hApos, tA, htA, hFacts⟩ := hAnalytic C hC
  obtain ⟨G, hGpos, tG, htG, hGamma⟩ :=
    gamma_norm_bound_of_analyticPrestate hAnalytic C hC
  let C' : ℝ := 4 * (16 * G ^ 2 * A + 36 * G ^ 4 + 16 * G ^ 6 * A + G ^ 8)
  let t0 : ℝ := min tA tG
  refine ⟨C', ?_, t0, lt_min htA htG, ?_⟩
  · dsimp [C']
    positivity
  · intro n Ω mΩ μ hμ t s Λplus Wstar S cols ξ htt hPre _hLaw
    intro z hz i
    have ht : 0 < t := hPre.scale.1
    have ht1 : t ≤ 1 := hPre.scale.2.le
    have httA : t < tA := lt_of_lt_of_le htt (min_le_left _ _)
    have httG : t < tG := lt_of_lt_of_le htt (min_le_right _ _)
    have ha := hFacts n t s Λplus Wstar httA hPre
    have hrowsum : ∀ r, (∑ j, s.F t r j) ≤ A := fun r => (ha.1 r).2.2.1
    have hcube : ∀ r, (s.F t ^ 3) r r ≤
        A * AndersonAC.S45.power t AndersonAC.S45.kappa *
          AndersonAC.S45.rowCap t := fun r => ha.2.2 r
    have hrowsq : ∀ r, (∑ j, s.F t r j ^ 2) ≤ AndersonAC.S45.rowCap t := by
      intro r
      have hcap := hPre.row_cap r
      calc
        (∑ j, s.F t r j ^ 2) = ∑ j, ‖s.h t r j‖ ^ 4 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare]
          ring
        _ = s.fourthRow t Finset.univ r := by
          simp [AndersonAC.S45.State.fourthRow]
        _ ≤ AndersonAC.S45.rowCap t := hcap
    have hFnonneg : ∀ a b, 0 ≤ s.F t a b := by
      intro a b
      simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare]
    have hFsym : (s.F t).IsSymm := by
      apply Matrix.IsSymm.ext
      intro a b
      simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare,
        AndersonAC.S45.State.h, Matrix.IsSymm.apply hPre.symmetric a b]
    have hH : 0 ≤ AndersonAC.S45.rowCap t := by
      dsimp [AndersonAC.S45.rowCap, AndersonAC.S45.power]
      exact le_of_lt (Real.rpow_pos_of_pos ht _)
    have hκle1 : AndersonAC.S45.power t AndersonAC.S45.kappa ≤ 1 := by
      exact Real.rpow_le_one ht.le ht1
        (by norm_num [AndersonAC.S45.kappa, AndersonAC.S45.delta])
    have hHleκ : AndersonAC.S45.rowCap t ≤
        AndersonAC.S45.power t AndersonAC.S45.kappa := by
      dsimp [AndersonAC.S45.rowCap, AndersonAC.S45.power]
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by
        norm_num [AndersonAC.S45.kappa, AndersonAC.S45.delta])
    have hH2leκ : (AndersonAC.S45.rowCap t) ^ 2 ≤
        AndersonAC.S45.power t AndersonAC.S45.kappa := by
      have hHle1 : AndersonAC.S45.rowCap t ≤ 1 := hHleκ.trans hκle1
      have hκpos : 0 ≤ AndersonAC.S45.power t AndersonAC.S45.kappa :=
        le_of_lt (Real.rpow_pos_of_pos ht _)
      calc
        (AndersonAC.S45.rowCap t) ^ 2 =
            AndersonAC.S45.rowCap t * AndersonAC.S45.rowCap t := by ring
        _ ≤ AndersonAC.S45.power t AndersonAC.S45.kappa *
            AndersonAC.S45.rowCap t :=
              mul_le_mul_of_nonneg_right hHleκ hH
        _ ≤ AndersonAC.S45.power t AndersonAC.S45.kappa * 1 :=
              mul_le_mul_of_nonneg_left hHle1 hκpos
        _ = AndersonAC.S45.power t AndersonAC.S45.kappa := by ring
    have hH3le : (AndersonAC.S45.rowCap t) ^ 3 ≤
        AndersonAC.S45.power t AndersonAC.S45.kappa *
          (AndersonAC.S45.rowCap t) ^ 2 := by
      calc
        (AndersonAC.S45.rowCap t) ^ 3 =
            AndersonAC.S45.rowCap t * (AndersonAC.S45.rowCap t) ^ 2 := by ring
        _ ≤ AndersonAC.S45.power t AndersonAC.S45.kappa *
            (AndersonAC.S45.rowCap t) ^ 2 :=
              mul_le_mul_of_nonneg_right hHleκ (sq_nonneg _)
    have hH4le : (AndersonAC.S45.rowCap t) ^ 4 ≤
        AndersonAC.S45.power t AndersonAC.S45.kappa *
          (AndersonAC.S45.rowCap t) ^ 2 := by
      calc
        (AndersonAC.S45.rowCap t) ^ 4 =
            (AndersonAC.S45.rowCap t) ^ 2 *
              (AndersonAC.S45.rowCap t) ^ 2 := by ring
        _ ≤ AndersonAC.S45.power t AndersonAC.S45.kappa *
            (AndersonAC.S45.rowCap t) ^ 2 :=
              mul_le_mul_of_nonneg_right hH2leκ (sq_nonneg _)
    have hGammaZ : ∀ x ∈ S, ‖AndersonAC.S45.gamma t s x (z x)‖ ≤ G := by
      intro x hx
      exact hGamma n t s Λplus Wstar x (z x) httG hPre (hz x hx)
    have hstack := fourthProxy_square_stack_of_matrix_bounds t s cols S i z G
      (AndersonAC.S45.rowCap t) A
      (A * AndersonAC.S45.power t AndersonAC.S45.kappa *
        AndersonAC.S45.rowCap t) hGpos.le hPre.symmetric hGammaZ hrowsq hrowsum
      (hcube i)
    calc
      (∑ x ∈ S,
        |AndersonAC.S45.fourthProxy t s cols i x (z x)| ^ 2) ≤
          4 * (16 * G ^ 2 * AndersonAC.S45.rowCap t *
                (A * AndersonAC.S45.power t AndersonAC.S45.kappa *
                  AndersonAC.S45.rowCap t) +
              36 * G ^ 4 * (AndersonAC.S45.rowCap t) ^ 3 +
              16 * G ^ 6 * A * (AndersonAC.S45.rowCap t) ^ 3 +
              G ^ 8 * (AndersonAC.S45.rowCap t) ^ 4) := hstack
      _ ≤ C' * AndersonAC.S45.power t AndersonAC.S45.kappa *
            AndersonAC.S45.rowCap t ^ 2 := by
          dsimp [C']
          have hterm2 := mul_le_mul_of_nonneg_left hH3le (by positivity :
            0 ≤ 36 * G ^ 4)
          have hterm3 := mul_le_mul_of_nonneg_left hH3le (by positivity :
            0 ≤ 16 * G ^ 6 * A)
          have hterm4 := mul_le_mul_of_nonneg_left hH4le (by positivity :
            0 ≤ G ^ 8)
          have hsum :
              16 * G ^ 2 * A * AndersonAC.S45.power t AndersonAC.S45.kappa *
                  (AndersonAC.S45.rowCap t) ^ 2 +
                36 * G ^ 4 * (AndersonAC.S45.rowCap t) ^ 3 +
                16 * G ^ 6 * A * (AndersonAC.S45.rowCap t) ^ 3 +
                G ^ 8 * (AndersonAC.S45.rowCap t) ^ 4 ≤
              16 * G ^ 2 * A * AndersonAC.S45.power t AndersonAC.S45.kappa *
                  (AndersonAC.S45.rowCap t) ^ 2 +
                36 * G ^ 4 * (AndersonAC.S45.power t AndersonAC.S45.kappa *
                  (AndersonAC.S45.rowCap t) ^ 2) +
                16 * G ^ 6 * A * (AndersonAC.S45.power t AndersonAC.S45.kappa *
                  (AndersonAC.S45.rowCap t) ^ 2) +
                G ^ 8 * (AndersonAC.S45.power t AndersonAC.S45.kappa *
                  (AndersonAC.S45.rowCap t) ^ 2) := by
            linarith [hterm2, hterm3, hterm4]
          calc
            _ = 4 * (16 * G ^ 2 * A * AndersonAC.S45.power t
                  AndersonAC.S45.kappa * (AndersonAC.S45.rowCap t) ^ 2 +
                36 * G ^ 4 * (AndersonAC.S45.rowCap t) ^ 3 +
                16 * G ^ 6 * A * (AndersonAC.S45.rowCap t) ^ 3 +
                G ^ 8 * (AndersonAC.S45.rowCap t) ^ 4) := by ring
            _ ≤ 4 * (16 * G ^ 2 * A * AndersonAC.S45.power t
                  AndersonAC.S45.kappa * (AndersonAC.S45.rowCap t) ^ 2 +
                36 * G ^ 4 * (AndersonAC.S45.power t AndersonAC.S45.kappa *
                  (AndersonAC.S45.rowCap t) ^ 2) +
                16 * G ^ 6 * A * (AndersonAC.S45.power t AndersonAC.S45.kappa *
                  (AndersonAC.S45.rowCap t) ^ 2) +
                G ^ 8 * (AndersonAC.S45.power t AndersonAC.S45.kappa *
                  (AndersonAC.S45.rowCap t) ^ 2)) := by
                    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
            _ = C' * AndersonAC.S45.power t AndersonAC.S45.kappa *
                AndersonAC.S45.rowCap t ^ 2 := by ring

/-- Pull a form on `P` back to a finite equivalent index type. -/
def formReindex {P Q : Type*} (e : Q ≃ P)
    (Λ : AndersonAC.S45.Form P) : AndersonAC.S45.Form Q :=
  fun y => Λ (y ∘ e.symm)

theorem l1_reindex {P Q : Type*} [Fintype P] [Fintype Q]
    (e : Q ≃ P) (y : Q → ℝ) :
    AndersonAC.S45.l1 (y ∘ e.symm) = AndersonAC.S45.l1 y := by
  unfold AndersonAC.S45.l1
  exact Fintype.sum_equiv e.symm _ _ (fun i => by simp)

theorem l2sq_reindex {P Q : Type*} [Fintype P] [Fintype Q]
    (e : Q ≃ P) (y : Q → ℝ) :
    AndersonAC.S45.l2sq (y ∘ e.symm) = AndersonAC.S45.l2sq y := by
  unfold AndersonAC.S45.l2sq
  exact Fintype.sum_equiv e.symm _ _ (fun i => by simp)

theorem neutral_reindex {P Q : Type*} [Fintype P] [Fintype Q]
    (e : Q ≃ P) (y : Q → ℝ) (hy : AndersonAC.S45.neutral y) :
    AndersonAC.S45.neutral (y ∘ e.symm) := by
  unfold AndersonAC.S45.neutral at *
  calc
    (∑ i : P, (y ∘ e.symm) i) = ∑ i : Q, y i := by
      exact Fintype.sum_equiv e.symm _ _ (fun i => by simp)
    _ = 0 := hy

theorem State.reindex_lag {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (e : Q ≃ P) (s : AndersonAC.S45.State P)
    (t : ℝ) (i : Q) :
    (State.reindex e s).lag t i = s.lag t (e i) := by
  change (((1 - (State.reindex e s).K t)⁻¹) *ᵥ
      (State.reindex e s).rawLag) i =
    (((1 - s.K t)⁻¹) *ᵥ s.rawLag) (e i)
  rw [State.reindex_K]
  have hmat : 1 - (s.K t).submatrix e e = (1 - s.K t).submatrix e e := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [Matrix.submatrix_apply]
    · simp [Matrix.submatrix_apply, hab]
  rw [hmat, Matrix.inv_submatrix_equiv]
  change
    (∑ j : Q, ((1 - s.K t)⁻¹) (e i) (e j) * s.rawLag (e j)) =
      (∑ j : P, ((1 - s.K t)⁻¹) (e i) j * s.rawLag j)
  exact Fintype.sum_equiv e _ _ (fun j => rfl)

theorem State.reindex_F {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (e : Q ≃ P)
    (s : AndersonAC.S45.State P) (t : ℝ) :
    (State.reindex e s).F t = (s.F t).submatrix e e := by
  ext i j
  simp [AndersonAC.S45.State.F, State.reindex_h,
    AndersonAC.S45.entryAbsSquare, Matrix.submatrix_apply]

theorem State.reindex_diagonal_h {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (e : Q ≃ P)
    (s : AndersonAC.S45.State P) (t : ℝ) (i : Q) :
    diagonal ((State.reindex e s).h t i) * (State.reindex e s).h t =
      (diagonal (s.h t (e i)) * s.h t).submatrix e e := by
  have hrow : (State.reindex e s).h t i = (s.h t (e i)) ∘ e := by
    funext j
    rw [State.reindex_h]
    rfl
  rw [hrow, State.reindex_h]
  ext a b
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.diagonal_apply]

theorem fourthProxy_reindex {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (e : Q ≃ P)
    (s : AndersonAC.S45.State P) (t : ℝ) (cols : Finset P)
    (i x : P) (ξ : ℝ) :
    AndersonAC.S45.fourthProxy t (State.reindex e s) (cols.image e.symm)
      (e.symm i) (e.symm x) ξ =
    AndersonAC.S45.fourthProxy t s cols i x ξ := by
  by_cases hix : i = x
  · subst x
    simp [AndersonAC.S45.fourthProxy]
  · have hix' : e.symm i ≠ e.symm x := by
      intro h
      apply hix
      exact e.symm.injective h
    have hentry (a b : Q) :
        (State.reindex e s).h t a b =
          (Real.sqrt t : ℂ) * s.g (e a) (e b) := by
      change (Real.sqrt t : ℂ) • s.g (e a) (e b) = _
      simp [smul_eq_mul]
    have hentryOld (a b : P) :
        s.h t a b = (Real.sqrt t : ℂ) * s.g a b := by
      simp [AndersonAC.S45.State.h, Matrix.smul_apply, smul_eq_mul]
    have hgammaReindex :
        AndersonAC.S45.gamma t (State.reindex e s) (e.symm x) ξ =
          AndersonAC.S45.gamma t s x ξ := by
      simp [State.reindex, AndersonAC.S45.gamma, Equiv.apply_symm_apply]
    unfold AndersonAC.S45.fourthProxy
    rw [if_neg hix, if_neg hix']
    rw [← Finset.image_erase e.symm.injective cols x]
    rw [Finset.sum_image e.symm.injective.injOn]
    apply Finset.sum_congr rfl
    intro j hj
    simp [hentry, hentryOld, hgammaReindex, Equiv.apply_symm_apply,
      Complex.norm_real, Real.norm_eq_abs, smul_eq_mul]

/-- Prestate data is invariant under an equivalence of finite index types. -/
theorem prestate_reindex {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (e : Q ≃ P) (t C : ℝ)
    (Λplus Wstar : AndersonAC.S45.Form P) (s : AndersonAC.S45.State P)
    (hPre : AndersonAC.S45.Prestate t C Λplus Wstar s) :
    AndersonAC.S45.Prestate t C (formReindex e Λplus) (formReindex e Wstar)
      (State.reindex e s) := by
  refine {
    scale := hPre.scale
    broad := ?_
    symmetric := ?_
    ward := ?_
    K_cap := ?_
    invertible := ?_
    kernel := ?_
    row_cap := ?_
    lag_cap := ?_
    sharp := ?_
    fourier := ?_
    dual_fourier := ?_
    volume := ?_ }
  · intro i
    simpa [State.reindex, AndersonAC.S45.State.p] using hPre.broad (e i)
  · apply Matrix.IsSymm.ext
    intro i j
    simpa [State.reindex] using hPre.symmetric.apply (e i) (e j)
  · have hWardEq : s.h t *
        diagonal (fun i => (s.p i : ℂ)) * (s.h t)ᴴ =
          AndersonAC.S45.matrixIm s.g := hPre.ward
    have hw := congrArg (Matrix.reindexRingEquiv ℂ e.symm) hWardEq
    simp only [map_mul] at hw
    simp only [Matrix.coe_reindexRingEquiv, reindex_apply] at hw
    simp only [Equiv.symm_symm] at hw
    have hdiag :
        (diagonal (fun i : P => (s.p i : ℂ))).submatrix e e =
          diagonal (fun i : Q => (s.p (e i) : ℂ)) := by
      exact Matrix.submatrix_diagonal_equiv _ _
    have him :
        (AndersonAC.S45.matrixIm s.g).submatrix e e =
          AndersonAC.S45.matrixIm (State.reindex e s).g := by
      ext i j
      rfl
    rw [hdiag, him] at hw
    change (State.reindex e s).h t *
        diagonal (fun i => ((State.reindex e s).p i : ℂ)) *
          ((State.reindex e s).h t)ᴴ =
      AndersonAC.S45.matrixIm (State.reindex e s).g
    rw [State.reindex_h]
    rw [← Matrix.conjTranspose_submatrix] at hw
    exact hw
  · calc
      ‖(State.reindex e s).K t‖ = ‖(s.K t).submatrix e e‖ := by rw [State.reindex_K]
      _ = ‖s.K t‖ := norm_submatrix_equiv e (s.K t)
      _ ≤ 1 / 2 := hPre.K_cap
  · have hunit : IsUnit ((1 - s.K t).submatrix e e) :=
      (Matrix.isUnit_submatrix_equiv e e).2 hPre.invertible
    have hmatrix : 1 - (State.reindex e s).K t = (1 - s.K t).submatrix e e := by
      rw [State.reindex_K]
      ext i j
      simp [Matrix.submatrix_apply, Matrix.one_apply]
    rw [hmatrix]
    exact hunit
  · refine ⟨?_, ?_, ?_⟩
    · rw [State.reindex_D]
      apply Matrix.IsSymm.ext
      intro i j
      exact hPre.kernel.1.apply (e i) (e j)
    · intro f
      rw [State.reindex_D, qform_submatrix]
      exact hPre.kernel.2.1 (f ∘ e.symm)
    · intro f
      rw [State.reindex_D, qform_submatrix]
      constructor
      · intro hf
        obtain ⟨a, ha⟩ := (hPre.kernel.2.2 (f ∘ e.symm)).1 hf
        refine ⟨a, ?_⟩
        intro i
        simpa using ha (e i)
      · rintro ⟨a, ha⟩
        apply (hPre.kernel.2.2 (f ∘ e.symm)).2
        refine ⟨a, ?_⟩
        intro p
        simpa using ha (e.symm p)
  · intro i
    rw [State.reindex_fourthRow]
    exact hPre.row_cap (e i)
  · intro i
    rw [State.reindex_lag]
    exact hPre.lag_cap (e i)
  · intro y hy
    have hneutral := neutral_reindex e y hy
    have hX : (State.reindex e s).X t y = s.X t (y ∘ e.symm) := by
      unfold AndersonAC.S45.State.X
      rw [State.reindex_D]
      exact dualForm_submatrix e (s.D t) y
    have hsum :
        (∑ i, y i ^ 2 / (State.reindex e s).p i ^ 2) =
          ∑ i, (y ∘ e.symm) i ^ 2 / s.p i ^ 2 := by
      exact Fintype.sum_equiv e _ _ (fun i => by simp [State.reindex,
        AndersonAC.S45.State.p])
    have hsharp := hPre.sharp (y ∘ e.symm) hneutral
    simpa [formReindex, hX, hsum] using hsharp
  · intro y hy
    have hneutral := neutral_reindex e y hy
    simpa [formReindex, l1_reindex e y, l2sq_reindex e y] using
      hPre.fourier (y ∘ e.symm) hneutral
  · intro y hy
    have hneutral := neutral_reindex e y hy
    simpa [formReindex, l1_reindex e y, l2sq_reindex e y] using
      hPre.dual_fourier (y ∘ e.symm) hneutral
  · simpa [Fintype.card_congr e] using hPre.volume

/-- The gamma pointwise bound transfers from `Fin n` to any finite index
type. -/
theorem gamma_norm_bound_any_of_analyticPrestate
    (hAnalytic : analyticPrestateHypothesis) (C : ℝ) (hC : 1 ≤ C) :
    ∃ G > 0, ∃ t0 > 0,
      ∀ (P : Type) [Fintype P] [DecidableEq P] (t : ℝ)
        (s : AndersonAC.S45.State P) (Λplus Wstar : AndersonAC.S45.Form P)
        (x : P) (ξ : ℝ),
        t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
        |ξ| ≤ C * Real.sqrt t → ‖AndersonAC.S45.gamma t s x ξ‖ ≤ G := by
  obtain ⟨G, hGpos, t0, ht0, hFin⟩ :=
    gamma_norm_bound_of_analyticPrestate hAnalytic C hC
  refine ⟨G, hGpos, t0, ht0, ?_⟩
  intro P instFintype instDecEq t s Λplus Wstar x ξ htt hPre hξ
  let n : ℕ := Fintype.card P
  let e : Fin n ≃ P := (Fintype.equivFin P).symm
  let sFin : AndersonAC.S45.State (Fin n) := State.reindex e s
  let ΛFin : AndersonAC.S45.Form (Fin n) := formReindex e Λplus
  let WFin : AndersonAC.S45.Form (Fin n) := formReindex e Wstar
  have hPreFin : AndersonAC.S45.Prestate t C ΛFin WFin sFin := by
    simpa [sFin, ΛFin, WFin] using prestate_reindex e t C Λplus Wstar s hPre
  have hBound := hFin n t sFin ΛFin WFin (e.symm x) ξ htt hPreFin hξ
  simpa [sFin, gamma_reindex] using hBound

/-- The small scalar gamma mean bound also transfers to arbitrary finite
index types. -/
theorem gamma_mean_bound_any_of_analyticPrestate
    (hAnalytic : analyticPrestateHypothesis) (C : ℝ) (hC : 1 ≤ C) :
    ∃ M > 0, ∃ t0 > 0,
      ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ)
        (s : AndersonAC.S45.State P) (Λplus Wstar : AndersonAC.S45.Form P)
        (x : P) (ξ : Ω → ℝ),
        t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
        AndersonAC.S45.MomentLaw μ t C ξ →
        ‖(∫ ω, AndersonAC.S45.gamma t s x (ξ ω) ∂μ)‖ ≤
          M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by
  obtain ⟨A, hApos, tA, htA, hFacts⟩ := hAnalytic C hC
  let C₁ : ℝ := 2 * C + A
  have hC₁ : 1 ≤ C₁ := by dsimp [C₁]; linarith
  have hC_le : C ≤ C₁ := by dsimp [C₁]; linarith
  obtain ⟨G, hGpos, tG, htG, hGamma⟩ :=
    AndersonAC.AgentS45.gamma_moments_proof C₁ hC₁
  let M : ℝ := G + A
  refine ⟨M, ?_, min tA tG, lt_min htA htG, ?_⟩
  · dsimp [M]
    positivity
  · intro P Ω instFintype instDecEq mΩ μ instProb t s Λplus Wstar x ξ
      htt hPre hLaw
    have ht : 0 < t := hPre.scale.1
    have ht1 : t ≤ 1 := hPre.scale.2.le
    have httA : t < tA := lt_of_lt_of_le htt (min_le_left _ _)
    have httG : t < tG := lt_of_lt_of_le htt (min_le_right _ _)
    let n : ℕ := Fintype.card P
    let e : Fin n ≃ P := (Fintype.equivFin P).symm
    let sFin : AndersonAC.S45.State (Fin n) := State.reindex e s
    let ΛFin : AndersonAC.S45.Form (Fin n) := formReindex e Λplus
    let WFin : AndersonAC.S45.Form (Fin n) := formReindex e Wstar
    have hPreFin : AndersonAC.S45.Prestate t C ΛFin WFin sFin := by
      simpa [sFin, ΛFin, WFin] using prestate_reindex e t C Λplus Wstar s hPre
    have hFactsFin := hFacts n t sFin ΛFin WFin httA hPreFin
    have hrawFin : ‖sFin.rawLag (e.symm x)‖ ≤
        A * AndersonAC.S45.power t AndersonAC.S45.beta :=
      (hFactsFin.1 (e.symm x)).1
    have hraw : ‖s.rawLag x‖ ≤ A * AndersonAC.S45.power t AndersonAC.S45.beta := by
      have hrawEq : sFin.rawLag (e.symm x) = s.rawLag x := by
        simp [sFin, State.reindex, AndersonAC.S45.State.rawLag,
          Equiv.apply_symm_apply]
      rw [hrawEq] at hrawFin
      exact hrawFin
    have hr : ‖s.r x‖ ≤ C := (hPre.broad x).1
    have hg : ‖s.g x x‖ ≤ C + A := by
      have hpow : AndersonAC.S45.power t AndersonAC.S45.beta ≤ 1 := by
        exact Real.rpow_le_one ht.le ht1
          (by norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta])
      have hAterm := mul_le_mul_of_nonneg_left hpow hApos.le
      calc
        ‖s.g x x‖ = ‖s.r x + s.rawLag x‖ := by
          congr 1
          simp [AndersonAC.S45.State.rawLag]
        _ ≤ ‖s.r x‖ + ‖s.rawLag x‖ := norm_add_le _ _
        _ ≤ C + A * AndersonAC.S45.power t AndersonAC.S45.beta :=
          add_le_add hr hraw
        _ ≤ C + A := by linarith
    have hstate : ‖s.g x x‖ + ‖s.r x‖ ≤ C₁ := by
      dsimp [C₁]
      linarith
    let law₁ : AndersonAC.S45.MomentLaw μ t C₁ ξ := {
      measurable := hLaw.measurable
      mean := hLaw.mean
      variance := hLaw.variance
      bounded := hLaw.bounded.mono fun ω hω =>
        hω.trans (mul_le_mul_of_nonneg_right hC_le (Real.sqrt_nonneg t))
    }
    have hGm := hGamma P Ω μ t s x ξ ht httG hstate law₁
    have hmean := hGm.2.1
    have hz : ‖s.z t x‖ ≤ Real.sqrt t *
        (A * AndersonAC.S45.power t AndersonAC.S45.beta) := by
      change ‖(Real.sqrt t : ℂ) * s.rawLag x‖ ≤ _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg t)]
      exact mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg t)
    have hpowOrder : AndersonAC.S45.beta ≤ 1 / 2 := by
      norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta]
    have hsqrtLe : Real.sqrt t ≤ AndersonAC.S45.power t AndersonAC.S45.beta := by
      dsimp [AndersonAC.S45.power]
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 hpowOrder
    have htLe : t ≤ Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by
      calc
        t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
        _ = Real.sqrt t * Real.sqrt t := by ring
        _ ≤ Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta :=
          mul_le_mul_of_nonneg_left hsqrtLe (Real.sqrt_nonneg t)
    calc
      ‖(∫ ω, AndersonAC.S45.gamma t s x (ξ ω) ∂μ)‖ =
          ‖((∫ ω, AndersonAC.S45.gamma t s x (ξ ω) ∂μ) + s.z t x) - s.z t x‖ := by
            congr 1
            abel
      _ ≤ ‖(∫ ω, AndersonAC.S45.gamma t s x (ξ ω) ∂μ) + s.z t x‖ +
          ‖s.z t x‖ := norm_sub_le _ _
      _ ≤ G * t + Real.sqrt t *
          (A * AndersonAC.S45.power t AndersonAC.S45.beta) := add_le_add hmean hz
      _ ≤ (G + A) * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by
          have hGterm := mul_le_mul_of_nonneg_left htLe hGpos.le
          nlinarith [hGterm]

/-- Arbitrary finite index types reduce to the canonical finite type for the
conditional deterministic square-stack result. -/
theorem fourth_bounds_square_stack_of_analyticPrestate
    (hAnalytic : analyticPrestateHypothesis) :
    ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
      ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : AndersonAC.S45.State P)
        (Λplus Wstar : AndersonAC.S45.Form P) (S cols : Finset P)
        (ξ : P → Ω → ℝ),
        t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
        (∀ x ∈ S, AndersonAC.S45.MomentLaw μ t C (ξ x)) →
        (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ i,
          (∑ x ∈ S,
            |AndersonAC.S45.fourthProxy t s cols i x (z x)| ^ 2) ≤
            C' * AndersonAC.S45.power t AndersonAC.S45.kappa *
              AndersonAC.S45.rowCap t ^ 2) := by
  intro C hC
  obtain ⟨C', hC'pos, t0, ht0, hFin⟩ :=
    fourth_bounds_stack_fin_of_analyticPrestate hAnalytic C hC
  refine ⟨C', hC'pos, t0, ht0, ?_⟩
  intro P Ω instFintype instDecidable mΩ μ instProb t s Λplus Wstar S cols ξ
    htt hPre hLaw z hz i
  let n : ℕ := Fintype.card P
  let e : Fin n ≃ P := (Fintype.equivFin P).symm
  let sFin : AndersonAC.S45.State (Fin n) := State.reindex e s
  let ΛFin : AndersonAC.S45.Form (Fin n) := formReindex e Λplus
  let WFin : AndersonAC.S45.Form (Fin n) := formReindex e Wstar
  let SFin : Finset (Fin n) := S.image e.symm
  let colsFin : Finset (Fin n) := cols.image e.symm
  let ξFin : Fin n → Ω → ℝ := fun j => ξ (e j)
  let zFin : Fin n → ℝ := fun j => z (e j)
  have hPreFin : AndersonAC.S45.Prestate t C ΛFin WFin sFin := by
    simpa [sFin, ΛFin, WFin] using prestate_reindex e t C Λplus Wstar s hPre
  have hLawFin : ∀ j ∈ SFin, AndersonAC.S45.MomentLaw μ t C (ξFin j) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨x, hx, hxe⟩
    subst j
    simpa [ξFin] using hLaw x hx
  have hzFin : ∀ j ∈ SFin, |zFin j| ≤ C * Real.sqrt t := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨x, hx, hxe⟩
    subst j
    simpa [zFin] using hz x hx
  have hFinBound :=
    hFin n Ω μ t sFin ΛFin WFin SFin colsFin ξFin htt hPreFin hLawFin zFin hzFin (e.symm i)
  have hsum :
      (∑ x ∈ S,
        |AndersonAC.S45.fourthProxy t s cols i x (z x)| ^ 2) =
      ∑ j ∈ SFin,
        |AndersonAC.S45.fourthProxy t sFin colsFin (e.symm i) j (zFin j)| ^ 2 := by
    calc
      _ = ∑ x ∈ S,
          |AndersonAC.S45.fourthProxy t sFin colsFin (e.symm i)
            (e.symm x) (zFin (e.symm x))| ^ 2 := by
              apply Finset.sum_congr rfl
              intro x hx
              have hp := fourthProxy_reindex e s t cols i x (z x)
              simpa [sFin, colsFin, zFin] using
                congrArg (fun a : ℝ => a ^ 2) hp.symm
      _ = ∑ j ∈ SFin,
          |AndersonAC.S45.fourthProxy t sFin colsFin (e.symm i) j (zFin j)| ^ 2 := by
              dsimp [SFin]
              rw [Finset.sum_image e.symm.injective.injOn]
  calc
    (∑ x ∈ S,
      |AndersonAC.S45.fourthProxy t s cols i x (z x)| ^ 2) =
        ∑ j ∈ SFin,
          |AndersonAC.S45.fourthProxy t sFin colsFin (e.symm i) j (zFin j)| ^ 2 := hsum
    _ ≤ C' * AndersonAC.S45.power t AndersonAC.S45.kappa *
          AndersonAC.S45.rowCap t ^ 2 := hFinBound

/-- The checked analytic-prestate endpoint extends from `Fin n` to every
finite index type by the state equivalence already used for the proxy stack. -/
theorem analyticPrestate_any :
    ∀ (C : ℝ), 1 ≤ C → ∃ A > 0, ∃ t0 > 0,
      ∀ (P : Type) [Fintype P] [DecidableEq P] (t : ℝ)
        (s : AndersonAC.S45.State P) (Λplus Wstar : AndersonAC.S45.Form P),
        t < t0 → AndersonAC.S45.Prestate t C Λplus Wstar s →
        (∀ i, ‖s.rawLag i‖ ≤ A * AndersonAC.S45.power t AndersonAC.S45.beta ∧
          |s.q i - s.p i| ≤ A * AndersonAC.S45.power t AndersonAC.S45.beta ∧
          (∑ j, s.F t i j) ≤ A ∧ ‖s.h t i i‖ ≤ A * Real.sqrt t) ∧
        (∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤
          A * AndersonAC.S45.power t (AndersonAC.S45.delta / 2)) ∧
        (∀ i, (s.F t ^ 3) i i ≤
          A * AndersonAC.S45.power t AndersonAC.S45.kappa *
            AndersonAC.S45.rowCap t) := by
  intro C hC
  obtain ⟨A, hApos, t0, ht0, hFin⟩ :=
    AndersonAC.AgentS45.analytic_prestate_proof C hC
  refine ⟨A, hApos, t0, ht0, ?_⟩
  intro P instFintype instDecidable t s Λplus Wstar htt hPre
  let n : ℕ := Fintype.card P
  let e : Fin n ≃ P := (Fintype.equivFin P).symm
  let sFin : AndersonAC.S45.State (Fin n) := State.reindex e s
  let ΛFin : AndersonAC.S45.Form (Fin n) := formReindex e Λplus
  let WFin : AndersonAC.S45.Form (Fin n) := formReindex e Wstar
  have hPreFin : AndersonAC.S45.Prestate t C ΛFin WFin sFin := by
    simpa [sFin, ΛFin, WFin] using prestate_reindex e t C Λplus Wstar s hPre
  have hfacts := hFin n t sFin ΛFin WFin htt hPreFin
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := hfacts.1 (e.symm i)
    have hFfin : sFin.F t = (s.F t).submatrix e e := by
      simpa [sFin] using State.reindex_F e s t
    have hrowsum : (∑ j : Fin n, sFin.F t (e.symm i) j) =
        ∑ j : P, s.F t i j := by
      rw [hFfin]
      exact Fintype.sum_equiv e _ _ (fun j => by simp [Matrix.submatrix_apply])
    rcases hi with ⟨hraw, hqp, hrow, hdiag⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [sFin, State.reindex, AndersonAC.S45.State.rawLag] using hraw
    · simpa [sFin, State.reindex, AndersonAC.S45.State.q,
        AndersonAC.S45.State.p] using hqp
    · rw [← hrowsum]
      exact hrow
    · simpa [sFin, State.reindex_h] using hdiag
  · intro i
    have hi := hfacts.2.1 (e.symm i)
    have hmat : diagonal ((State.reindex e s).h t (e.symm i)) *
        (State.reindex e s).h t =
        (diagonal (s.h t i) * s.h t).submatrix e e := by
      simpa using State.reindex_diagonal_h e s t (e.symm i)
    rw [hmat] at hi
    rw [norm_submatrix_equiv e] at hi
    simpa [sFin] using hi
  · intro i
    have hi := hfacts.2.2 (e.symm i)
    have hpow : (sFin.F t) ^ 3 = (s.F t ^ 3).submatrix e e := by
      let φ := Matrix.reindexRingEquiv ℝ e.symm
      have hbase : φ (s.F t) = sFin.F t := by
        change (s.F t).submatrix e e = (State.reindex e s).F t
        exact (State.reindex_F e s t).symm
      calc
        (sFin.F t) ^ 3 = (φ (s.F t)) ^ 3 := by rw [hbase]
        _ = φ ((s.F t) ^ 3) := (map_pow φ (s.F t) 3).symm
        _ = (s.F t ^ 3).submatrix e e := by
          change (s.F t ^ 3).submatrix e e = _
          rfl
    rw [hpow] at hi
    simpa [sFin, Matrix.submatrix_apply] using hi

private theorem l2sq_mulVec_le_opNorm_sq {P : Type*} [Fintype P] [DecidableEq P]
    (A : AndersonAC.S45.CMat P) (u : P → ℂ) :
    AndersonAC.S45.l2sq (A *ᵥ u) ≤ ‖A‖ ^ 2 * AndersonAC.S45.l2sq u := by
  have hnormSq (x : P → ℂ) : ‖WithLp.toLp 2 x‖ ^ 2 = AndersonAC.S45.l2sq x := by
    rw [PiLp.norm_eq_of_L2]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (‖x i‖))]
    rfl
  have hnorm : ‖WithLp.toLp 2 (A *ᵥ u)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 u‖ := by
    have h :=
      (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 u)
    simpa [Matrix.toEuclideanCLM_toLp, Matrix.l2_opNorm_toEuclideanCLM] using h
  calc
    AndersonAC.S45.l2sq (A *ᵥ u) = ‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 := (hnormSq _).symm
    _ ≤ (‖A‖ * ‖WithLp.toLp 2 u‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    _ = ‖A‖ ^ 2 * AndersonAC.S45.l2sq u := by rw [mul_pow, hnormSq]

open AndersonAC.S45

/-- Two Cauchy--Schwarz estimates give the fourth-power version of the
row Hölder estimate, without taking roots. -/
theorem fourth_weighted_sum_bound {P : Type*} [Fintype P]
    (a b : P → ℝ) (H B L : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hrow : (∑ j, a j ^ 4) ≤ H)
    (hmax : ∀ j, b j ≤ B) (hl2 : (∑ j, b j ^ 2) ≤ L) :
    (∑ j, a j ^ 3 * b j) ^ 4 ≤ H ^ 3 * B ^ 2 * L := by
  classical
  let T := ∑ j, a j ^ 2 * b j ^ 2
  have hT : 0 ≤ T := Finset.sum_nonneg fun j _ => by positivity
  have hcs₁ : (∑ j, a j ^ 3 * b j) ^ 2 ≤ H * T := by
    calc
      _ = (∑ j, (a j ^ 2) * (a j * b j)) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (∑ j, (a j ^ 2) ^ 2) * (∑ j, (a j * b j) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, a j ^ 4) * T := by simp [T, mul_pow, ← pow_mul]
      _ ≤ H * T := mul_le_mul_of_nonneg_right hrow hT
  have hb4 : (∑ j, b j ^ 4) ≤ B ^ 2 * L := by
    calc
      _ ≤ ∑ j, B ^ 2 * b j ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hs := (sq_le_sq₀ (hb j) hB).2 (hmax j)
        nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (b j))]
      _ = B ^ 2 * ∑ j, b j ^ 2 := by rw [Finset.mul_sum]
      _ ≤ B ^ 2 * L := mul_le_mul_of_nonneg_left hl2 (sq_nonneg B)
  have hcs₂ : T ^ 2 ≤ H * (B ^ 2 * L) := by
    calc
      T ^ 2 ≤ (∑ j, (a j ^ 2) ^ 2) * (∑ j, (b j ^ 2) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, a j ^ 4) * (∑ j, b j ^ 4) := by simp [← pow_mul]
      _ ≤ H * (B ^ 2 * L) := mul_le_mul hrow hb4
        (Finset.sum_nonneg fun j _ => by positivity) hH
  calc
    _ = ((∑ j, a j ^ 3 * b j) ^ 2) ^ 2 := by ring
    _ ≤ (H * T) ^ 2 := by gcongr
    _ = H ^ 2 * T ^ 2 := by ring
    _ ≤ H ^ 2 * (H * (B ^ 2 * L)) :=
      mul_le_mul_of_nonneg_left hcs₂ (sq_nonneg H)
    _ = H ^ 3 * B ^ 2 * L := by ring

/-- The restored signed contraction has both an entrywise and an L² row
bound. The latter retains the operator cancellation of the Green matrix. -/
theorem mean_contraction_row_bounds {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (μ : P → ℂ) (i : P) (A m : ℝ)
    (hsym : s.g.IsSymm) (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hrow : ∀ r, (∑ j, s.F t r j) ≤ A) (hμ : ∀ x, ‖μ x‖ ≤ m) :
    let B := fun j => ∑ x, μ x * s.h t i x * s.h t x j
    (∀ j, ‖B j‖ ≤ m * A) ∧ l2sq B ≤ ‖s.h t‖ ^ 2 * m ^ 2 * A := by
  classical
  dsimp only
  have hsymh : ∀ x j, s.h t x j = s.h t j x := by
    intro x j
    simp [AndersonAC.S45.State.h, hsym.apply x j]
  constructor
  · intro j
    have hcs : (∑ x, ‖s.h t i x‖ * ‖s.h t x j‖) ^ 2 ≤ A ^ 2 := by
      calc
        _ ≤ (∑ x, ‖s.h t i x‖ ^ 2) * (∑ x, ‖s.h t x j‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = (∑ x, s.F t i x) * (∑ x, s.F t j x) := by
          simp only [hsymh, AndersonAC.S45.State.F, entryAbsSquare]
        _ ≤ A * A := mul_le_mul (hrow i) (hrow j)
          (Finset.sum_nonneg fun x _ => by simp [AndersonAC.S45.State.F, entryAbsSquare]) hA
        _ = A ^ 2 := by ring
    have hsum : (∑ x, ‖s.h t i x‖ * ‖s.h t x j‖) ≤ A := by
      exact (sq_le_sq₀ (Finset.sum_nonneg fun x _ => by positivity) hA).1 hcs
    calc
      _ ≤ ∑ x, ‖μ x * s.h t i x * s.h t x j‖ := norm_sum_le _ _
      _ ≤ ∑ x, m * (‖s.h t i x‖ * ‖s.h t x j‖) := by
        apply Finset.sum_le_sum
        intro x _
        simp only [norm_mul]
        calc
          _ ≤ m * ‖s.h t i x‖ * ‖s.h t x j‖ := by gcongr; exact hμ x
          _ = _ := by ring
      _ = m * ∑ x, ‖s.h t i x‖ * ‖s.h t x j‖ := by rw [Finset.mul_sum]
      _ ≤ m * A := mul_le_mul_of_nonneg_left hsum hm
  · have hvec : (fun j => ∑ x, μ x * s.h t i x * s.h t x j) =
        s.h t *ᵥ (fun x => μ x * s.h t i x) := by
      funext j
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro x _
      rw [hsymh x j]
      ring
    have hv : l2sq (fun x => μ x * s.h t i x) ≤ m ^ 2 * A := by
      calc
        _ ≤ ∑ x, m ^ 2 * s.F t i x := by
          unfold l2sq
          apply Finset.sum_le_sum
          intro x _
          change ‖μ x * s.h t i x‖ ^ 2 ≤ m ^ 2 * ‖s.h t i x‖ ^ 2
          rw [norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_right
            ((sq_le_sq₀ (norm_nonneg _) hm).2 (hμ x)) (sq_nonneg _)
        _ = m ^ 2 * ∑ x, s.F t i x := by rw [Finset.mul_sum]
        _ ≤ m ^ 2 * A := mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg m)
    rw [hvec]
    calc
      _ ≤ ‖s.h t‖ ^ 2 * l2sq (fun x => μ x * s.h t i x) :=
        l2sq_mulVec_le_opNorm_sq _ _
      _ ≤ ‖s.h t‖ ^ 2 * (m ^ 2 * A) :=
        mul_le_mul_of_nonneg_left hv (sq_nonneg _)
      _ = _ := by ring

/-- The exponents leave enough room for the signed fourth-order mean. -/
theorem fourth_mean_power_budget {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    rowCap t ^ 3 * t * power t AndersonAC.S45.beta ^ 4 ≤
      rowCap t ^ 4 * power t kappa ^ 4 := by
  have hleft : rowCap t ^ 3 * t * power t AndersonAC.S45.beta ^ 4 =
      power t (3 * (1 + delta) + 1 + 4 * AndersonAC.S45.beta) := by
    change (t ^ (1 + delta)) ^ 3 * t * (t ^ AndersonAC.S45.beta) ^ 4 =
      t ^ (3 * (1 + delta) + 1 + 4 * AndersonAC.S45.beta)
    calc
      _ = t ^ ((1 + delta) * (3 : ℕ)) * t ^ (1 : ℝ) *
          t ^ (AndersonAC.S45.beta * (4 : ℕ)) := by
        rw [Real.rpow_mul_natCast ht.le, Real.rpow_mul_natCast ht.le, Real.rpow_one]
      _ = t ^ (((1 + delta) * 3 + 1) + AndersonAC.S45.beta * 4) := by
        rw [← Real.rpow_add ht, ← Real.rpow_add ht]
        norm_num
      _ = _ := by congr 1; ring
  have hright : rowCap t ^ 4 * power t kappa ^ 4 =
      power t (4 * (1 + delta) + 4 * kappa) := by
    change (t ^ (1 + delta)) ^ 4 * (t ^ kappa) ^ 4 =
      t ^ (4 * (1 + delta) + 4 * kappa)
    rw [← Real.rpow_mul_natCast ht.le (1 + delta) 4,
      ← Real.rpow_mul_natCast ht.le kappa 4, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hleft, hright]
  exact Real.rpow_le_rpow_of_exponent_ge ht ht1
    (by norm_num [AndersonAC.S45.beta, delta, kappa])

theorem fourth_restored_linear_mean_bound {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t C A M : ℝ) (μ : P → ℂ) (i : P)
    (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 < C) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hsym : s.g.IsSymm) (hward : s.ward t) (hp : ∀ j, 1 / C ≤ s.p j)
    (hrow : ∀ r, (∑ j, s.F t r j) ≤ A)
    (hfourth : (∑ j, ‖s.h t i j‖ ^ 4) ≤ rowCap t)
    (hμ : ∀ x, ‖μ x‖ ≤ M * Real.sqrt t * power t AndersonAC.S45.beta) :
    (∑ j, ‖s.h t i j‖ ^ 3 *
      ‖∑ x, μ x * s.h t i x * s.h t x j‖) ≤
        (C ^ 2 * A ^ 3 * M ^ 4 + 1) * rowCap t * power t kappa := by
  classical
  let B := fun j => ∑ x, μ x * s.h t i x * s.h t x j
  let m := M * Real.sqrt t * power t AndersonAC.S45.beta
  have hm : 0 ≤ m := by dsimp [m, power]; positivity
  obtain ⟨hmax, hl2⟩ := mean_contraction_row_bounds s t μ i A m hsym hA hm hrow hμ
  have hop := ward_h_operator_bound s t C ht hC hsym hward hp
  have hop2 : ‖s.h t‖ ^ 2 ≤ C ^ 2 / t := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C / Real.sqrt t)).2 hop
    simpa [div_pow, Real.sq_sqrt ht.le] using hs
  have hrowpos : 0 ≤ rowCap t := (Real.rpow_pos_of_pos ht _).le
  have hsum4 := fourth_weighted_sum_bound
    (fun j => ‖s.h t i j‖) (fun j => ‖B j‖) (rowCap t) (m * A)
    (‖s.h t‖ ^ 2 * m ^ 2 * A) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (by positivity) hrowpos (by positivity) hfourth hmax hl2
  have hcoeff : rowCap t ^ 3 * (m * A) ^ 2 * (‖s.h t‖ ^ 2 * m ^ 2 * A) ≤
      (C ^ 2 * A ^ 3 * M ^ 4) * (rowCap t ^ 3 * t * power t AndersonAC.S45.beta ^ 4) := by
    calc
      _ = ‖s.h t‖ ^ 2 * (rowCap t ^ 3 * m ^ 4 * A ^ 3) := by ring
      _ ≤ (C ^ 2 / t) * (rowCap t ^ 3 * m ^ 4 * A ^ 3) :=
        mul_le_mul_of_nonneg_right hop2 (by positivity)
      _ = _ := by
        dsimp [m]
        have hsqrt : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
        have hsqrt4 : Real.sqrt t ^ 4 = t ^ 2 := by
          calc
            _ = (Real.sqrt t ^ 2) ^ 2 := by ring
            _ = _ := by rw [hsqrt]
        simp only [mul_pow, hsqrt4]
        field_simp
        <;> ring
  let Q := C ^ 2 * A ^ 3 * M ^ 4
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hD : Q ≤ (Q + 1) ^ 4 := by
    nlinarith [pow_nonneg hQ 3, pow_nonneg hQ 4]
  have hbound4 : (∑ j, ‖s.h t i j‖ ^ 3 * ‖B j‖) ^ 4 ≤
      ((Q + 1) * rowCap t * power t kappa) ^ 4 := by
    calc
      _ ≤ Q * (rowCap t ^ 3 * t * power t AndersonAC.S45.beta ^ 4) := hsum4.trans hcoeff
      _ ≤ Q * (rowCap t ^ 4 * power t kappa ^ 4) :=
        mul_le_mul_of_nonneg_left (fourth_mean_power_budget ht ht1) hQ
      _ ≤ (Q + 1) ^ 4 * (rowCap t ^ 4 * power t kappa ^ 4) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
      _ = _ := by ring
  have htarget : 0 ≤ (Q + 1) * rowCap t * power t kappa := by
    exact mul_nonneg (mul_nonneg (by positivity) hrowpos) (Real.rpow_pos_of_pos ht _).le
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun j _ => by positivity)
    htarget (by decide : (4 : ℕ) ≠ 0)).1 hbound4

def fourthCoeff {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (cols : Finset P) (i x : P) : ℂ :=
  if i = x then 0 else ∑ j ∈ cols.erase x,
    ((‖s.h t i j‖ ^ 2 : ℝ) : ℂ) * star (s.h t i j) * s.h t i x * s.h t x j

theorem fourth_increment_remainder_bound' (a b : ℂ) :
    |‖a - b‖ ^ 4 - ‖a‖ ^ 4 +
      4 * (((‖a‖ ^ 2 : ℝ) : ℂ) * star a * b).re| ≤
        8 * ‖a‖ ^ 2 * ‖b‖ ^ 2 + 3 * ‖b‖ ^ 4 := by
  have heq : (((‖a‖ ^ 2 : ℝ) : ℂ) * star a * b).re =
      ‖a‖ ^ 2 * (a * star b).re := by
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, RCLike.star_def, Complex.conj_re, Complex.conj_im]
    ring
  rw [heq]
  simpa only [mul_assoc] using fourth_increment_remainder_bound a b

theorem fourthProxy_remainder_bound {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (cols : Finset P) (i x : P) (ξ G H : ℝ)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hγ : ‖gamma t s x ξ‖ ≤ G)
    (hrow : (∑ j, s.F t x j ^ 2) ≤ H) :
    |fourthProxy t s cols i x ξ + 4 * (gamma t s x ξ * fourthCoeff t s cols i x).re| ≤
      8 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
        3 * G ^ 4 * s.F t i x ^ 2 * H := by
  classical
  have hF : ∀ a b, 0 ≤ s.F t a b := fun a b => sq_nonneg _
  by_cases hix : i = x
  · simp only [fourthProxy, fourthCoeff, if_pos hix, mul_zero, Complex.zero_re, add_zero, abs_zero]
    have hf := hF i x
    have hc : 0 ≤ ∑ j, s.F t i j * s.F t x j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hF i j) (hF x j)
    positivity
  · have heq : fourthProxy t s cols i x ξ +
        4 * (gamma t s x ξ * fourthCoeff t s cols i x).re =
        ∑ j ∈ cols.erase x, (‖s.h t i j - gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 4 -
          ‖s.h t i j‖ ^ 4 + 4 *
          (((‖s.h t i j‖ ^ 2 : ℝ) : ℂ) * star (s.h t i j) *
            (gamma t s x ξ * s.h t i x * s.h t x j)).re) := by
      simp only [fourthProxy, fourthCoeff, if_neg hix, Finset.mul_sum,
        Complex.re_sum, Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      congr 2
      ring
    rw [heq]
    calc
      _ ≤ ∑ j ∈ cols.erase x,
          |‖s.h t i j - gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 4 -
            ‖s.h t i j‖ ^ 4 + 4 *
            (((‖s.h t i j‖ ^ 2 : ℝ) : ℂ) * star (s.h t i j) *
              (gamma t s x ξ * s.h t i x * s.h t x j)).re| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ cols.erase x,
          (8 * G ^ 2 * s.F t i x * (s.F t i j * s.F t x j) +
            3 * G ^ 4 * s.F t i x ^ 2 * s.F t x j ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        have hb : ‖gamma t s x ξ * s.h t i x * s.h t x j‖ ≤
            G * ‖s.h t i x‖ * ‖s.h t x j‖ := by
          simp only [norm_mul]
          gcongr
        calc
          _ ≤ 8 * ‖s.h t i j‖ ^ 2 * ‖gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 2 +
              3 * ‖gamma t s x ξ * s.h t i x * s.h t x j‖ ^ 4 :=
            fourth_increment_remainder_bound' _ _
          _ ≤ 8 * ‖s.h t i j‖ ^ 2 * (G * ‖s.h t i x‖ * ‖s.h t x j‖) ^ 2 +
              3 * (G * ‖s.h t i x‖ * ‖s.h t x j‖) ^ 4 := by gcongr
          _ = _ := by dsimp [AndersonAC.S45.State.F, entryAbsSquare]; ring
      _ ≤ ∑ j,
          (8 * G ^ 2 * s.F t i x * (s.F t i j * s.F t x j) +
            3 * G ^ 4 * s.F t i x ^ 2 * s.F t x j ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro j _ _
        have := hF i x
        have := hF i j
        have := hF x j
        positivity
      _ = 8 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
          3 * G ^ 4 * s.F t i x ^ 2 * (∑ j, s.F t x j ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by gcongr

theorem fourthCoeff_restore {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (cols : Finset P) (i x : P) (hix : i ≠ x) :
    fourthCoeff t s cols i x =
      (∑ j ∈ cols, ((‖s.h t i j‖ ^ 2 : ℝ) : ℂ) * star (s.h t i j) *
        s.h t i x * s.h t x j) -
      (if x ∈ cols then ((s.F t i x ^ 2 : ℝ) : ℂ) * s.h t x x else 0) := by
  classical
  unfold fourthCoeff
  rw [if_neg hix]
  have hx : ((‖s.h t i x‖ ^ 2 : ℝ) : ℂ) * star (s.h t i x) * s.h t i x * s.h t x x =
      ((s.F t i x ^ 2 : ℝ) : ℂ) * s.h t x x := by
    have hs : star (s.h t i x) * s.h t i x = ((‖s.h t i x‖ ^ 2 : ℝ) : ℂ) := by
      simpa [Complex.normSq_eq_norm_sq] using Complex.conj_mul' (s.h t i x)
    change _ = (((‖s.h t i x‖ ^ 2) ^ 2 : ℝ) : ℂ) * s.h t x x
    rw [mul_assoc ((‖s.h t i x‖ ^ 2 : ℝ) : ℂ), hs]
    push_cast
    ring
  by_cases hxcols : x ∈ cols
  · rw [if_pos hxcols, ← hx]
    exact Finset.sum_erase_eq_sub hxcols
  · simp [Finset.erase_eq_of_notMem hxcols, hxcols]

theorem fourthCoeff_sum_bound {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (cols : Finset P) (i : P) (μ : P → ℂ)
    (m d H : ℝ) (hm : 0 ≤ m) (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hμ : ∀ x, ‖μ x‖ ≤ m) (hzero : μ i = 0)
    (hdiag : ∀ x, ‖s.h t x x‖ ≤ d)
    (hrow : (∑ x, ‖s.h t i x‖ ^ 4) ≤ H) :
    ‖∑ x, μ x * fourthCoeff t s cols i x‖ ≤
      (∑ j, ‖s.h t i j‖ ^ 3 * ‖∑ x, μ x * s.h t i x * s.h t x j‖) + m * d * H := by
  classical
  let c := fun j => ((‖s.h t i j‖ ^ 2 : ℝ) : ℂ) * star (s.h t i j)
  let e := fun x => if x ∈ cols then ((s.F t i x ^ 2 : ℝ) : ℂ) * s.h t x x else 0
  have hrestore : ∀ x, μ x * fourthCoeff t s cols i x =
      μ x * (∑ j ∈ cols, c j * s.h t i x * s.h t x j) - μ x * e x := by
    intro x
    by_cases hix : i = x
    · subst x
      simp [hzero]
    · rw [fourthCoeff_restore t s cols i x hix]
      dsimp [c, e]
      ring
  have hswap : (∑ x, μ x * ∑ j ∈ cols, c j * s.h t i x * s.h t x j) =
      ∑ j ∈ cols, c j * ∑ x, μ x * s.h t i x * s.h t x j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have herr : ‖∑ x, μ x * e x‖ ≤ m * d * H := by
    calc
      _ ≤ ∑ x, ‖μ x * e x‖ := norm_sum_le _ _
      _ ≤ ∑ x, m * d * ‖s.h t i x‖ ^ 4 := by
        apply Finset.sum_le_sum
        intro x _
        dsimp [e]
        split_ifs with hx
        · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg (s.F t i x))]
          change ‖μ x‖ * ((‖s.h t i x‖ ^ 2) ^ 2 * ‖s.h t x x‖) ≤ _
          calc
            _ ≤ m * ((‖s.h t i x‖ ^ 2) ^ 2 * d) := by gcongr; exact hμ x; exact hdiag x
            _ = _ := by ring
        · simp only [mul_zero, norm_zero]
          positivity
      _ = m * d * ∑ x, ‖s.h t i x‖ ^ 4 := by rw [Finset.mul_sum]
      _ ≤ m * d * H := mul_le_mul_of_nonneg_left hrow (by positivity)
  calc
    _ = ‖(∑ j ∈ cols, c j * ∑ x, μ x * s.h t i x * s.h t x j) -
        ∑ x, μ x * e x‖ := by simp only [hrestore, Finset.sum_sub_distrib, hswap]
    _ ≤ ‖∑ j ∈ cols, c j * ∑ x, μ x * s.h t i x * s.h t x j‖ +
        ‖∑ x, μ x * e x‖ := norm_sub_le _ _
    _ ≤ (∑ j ∈ cols, ‖c j * ∑ x, μ x * s.h t i x * s.h t x j‖) + m * d * H :=
      add_le_add (norm_sum_le _ _) herr
    _ = (∑ j ∈ cols, ‖s.h t i j‖ ^ 3 *
        ‖∑ x, μ x * s.h t i x * s.h t x j‖) + m * d * H := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp [c, norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ cols)
        (fun j _ _ => by positivity)

theorem fourthProxy_integral_remainder_bound {P Ω : Type*}
    [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (cols : Finset P) (i x : P) (ξ : Ω → ℝ) (G H : ℝ)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hξ : Measurable ξ)
    (hγ : ∀ᵐ ω ∂μ, ‖gamma t s x (ξ ω)‖ ≤ G)
    (hrow : (∑ j, s.F t x j ^ 2) ≤ H) :
    |(∫ ω, fourthProxy t s cols i x (ξ ω) ∂μ) +
      4 * ((∫ ω, gamma t s x (ξ ω) ∂μ) * fourthCoeff t s cols i x).re| ≤
        8 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
          3 * G ^ 4 * s.F t i x ^ 2 * H := by
  classical
  let γ := fun ω => gamma t s x (ξ ω)
  let Q := fun ω => fourthProxy t s cols i x (ξ ω)
  let L := fun ω => 4 * (γ ω * fourthCoeff t s cols i x).re
  let R := fun ω => Q ω + L ω
  let K := 8 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
    3 * G ^ 4 * s.F t i x ^ 2 * H
  have hγm : Measurable γ := by dsimp [γ, gamma]; fun_prop
  have hγI : Integrable γ μ := Integrable.of_bound hγm.aestronglyMeasurable G hγ
  have hLm : Measurable L := by dsimp [L]; fun_prop
  have hLI : Integrable L μ := ((hγI.mul_const _).re).const_mul _
  have hQm : Measurable Q := by
    dsimp [Q, fourthProxy]
    change Measurable (fun ω => if i = x then 0 else
      ∑ j ∈ cols.erase x, (‖s.h t i j - γ ω * s.h t i x * s.h t x j‖ ^ 4 - ‖s.h t i j‖ ^ 4))
    split_ifs
    · fun_prop
    · fun_prop
  have hb : ∀ᵐ ω ∂μ, ‖R ω‖ ≤ K := by
    filter_upwards [hγ] with ω hω
    simpa only [Real.norm_eq_abs] using
      fourthProxy_remainder_bound t s cols i x (ξ ω) G H hG hH hω hrow
  have hRm : Measurable R := hQm.add hLm
  have hRI : Integrable R μ := Integrable.of_bound hRm.aestronglyMeasurable K hb
  have hQI : Integrable Q μ := by
    have heq : Q = fun ω => R ω - L ω := by funext ω; dsimp [R]; ring
    rw [heq]
    exact hRI.sub hLI
  have hK : 0 ≤ K := by
    have hf : 0 ≤ s.F t i x := sq_nonneg _
    have hc : 0 ≤ ∑ j, s.F t i j * s.F t x j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    dsimp [K]
    positivity
  have hbound := ae_bound_integral_norm μ R K hRI hK hb
  have hLint : (∫ ω, L ω ∂μ) = 4 * ((∫ ω, γ ω ∂μ) * fourthCoeff t s cols i x).re := by
    dsimp [L]
    have hre := integral_re (𝕜 := ℂ) (hγI.mul_const (fourthCoeff t s cols i x))
    change (∫ ω, (γ ω * fourthCoeff t s cols i x).re ∂μ) =
      (∫ ω, γ ω * fourthCoeff t s cols i x ∂μ).re at hre
    rw [integral_const_mul, hre, integral_mul_const]
  simpa only [R, integral_add hQI hLI, hLint, Real.norm_eq_abs] using hbound

theorem fourthProxy_mean_matrix_bound {P Ω : Type*}
    [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (cols S : Finset P) (i : P) (ξ : P → Ω → ℝ) (G H : ℝ)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hsym : s.g.IsSymm)
    (hξ : ∀ x ∈ S, Measurable (ξ x))
    (hγ : ∀ x ∈ S, ∀ᵐ ω ∂μ, ‖gamma t s x (ξ x ω)‖ ≤ G)
    (hrow : ∀ x, (∑ j, s.F t x j ^ 2) ≤ H) :
    |∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) ∂μ| ≤
      4 * ‖∑ x ∈ S, (∫ ω, gamma t s x (ξ x ω) ∂μ) * fourthCoeff t s cols i x‖ +
        8 * G ^ 2 * (s.F t ^ 3) i i + 3 * G ^ 4 * H ^ 2 := by
  classical
  let a := fun x => ∫ ω, fourthProxy t s cols i x (ξ x ω) ∂μ
  let b := fun x => (∫ ω, gamma t s x (ξ x ω) ∂μ) * fourthCoeff t s cols i x
  let E := fun x => 8 * G ^ 2 * s.F t i x * (∑ j, s.F t i j * s.F t x j) +
    3 * G ^ 4 * s.F t i x ^ 2 * H
  have hF : ∀ a b, 0 ≤ s.F t a b := fun _ _ => sq_nonneg _
  have hFs : (s.F t).IsSymm := by
    apply Matrix.IsSymm.ext
    intro x y
    simp [AndersonAC.S45.State.F, entryAbsSquare, AndersonAC.S45.State.h, hsym.apply y x]
  have hE : ∀ x, 0 ≤ E x := by
    intro x
    have hf := hF i x
    have hc := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => mul_nonneg (hF i j) (hF x j))
    dsimp [E]
    positivity
  have herr : |∑ x ∈ S, (a x + 4 * (b x).re)| ≤
      8 * G ^ 2 * (s.F t ^ 3) i i + 3 * G ^ 4 * H ^ 2 := by
    calc
      _ ≤ ∑ x ∈ S, |a x + 4 * (b x).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ S, E x := by
        apply Finset.sum_le_sum
        intro x hx
        exact fourthProxy_integral_remainder_bound μ t s cols i x (ξ x) G H
          hG hH (hξ x hx) (hγ x hx) (hrow x)
      _ ≤ ∑ x, E x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => hE x)
      _ = 8 * G ^ 2 * (s.F t ^ 3) i i + 3 * G ^ 4 * H * (∑ x, s.F t i x ^ 2) := by
        dsimp [E]
        simp only [Finset.sum_add_distrib]
        rw [← row_correlation_eq_cube (s.F t) hFs i]
        congr 1
        · simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
        · simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
      _ ≤ _ := by
        apply add_le_add le_rfl
        calc
          _ ≤ 3 * G ^ 4 * H * H := mul_le_mul_of_nonneg_left (hrow i) (by positivity)
          _ = _ := by ring
  have hsum : (∑ x ∈ S, (a x + 4 * (b x).re)) =
      (∑ x ∈ S, a x) + 4 * (∑ x ∈ S, b x).re := by
    simp only [Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  rw [hsum] at herr
  have hreal : |(∑ x ∈ S, b x).re| ≤ ‖∑ x ∈ S, b x‖ := Complex.abs_re_le_norm _
  have htriangle := abs_sub ( (∑ x ∈ S, a x) + 4 * (∑ x ∈ S, b x).re)
    (4 * (∑ x ∈ S, b x).re)
  rw [add_sub_cancel_right, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at htriangle
  linarith

theorem fourth_bounds_mean : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S cols : Finset P) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    (∀ i, |∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) ∂μ| ≤
      C' * power t kappa * rowCap t) := by
  intro C hC
  have hAnalytic : analyticPrestateHypothesis := analytic_prestate_proof
  obtain ⟨A, hA, tA, htA, hFacts⟩ := analyticPrestate_any C hC
  obtain ⟨G, hG, tG, htG, hGamma⟩ := gamma_norm_bound_any_of_analyticPrestate hAnalytic C hC
  obtain ⟨M, hM, tM, htM, hMean⟩ := gamma_mean_bound_any_of_analyticPrestate hAnalytic C hC
  let L := C ^ 2 * A ^ 3 * M ^ 4 + 1
  let D := 4 * (L + M * A) + 8 * G ^ 2 * A + 3 * G ^ 4
  refine ⟨D, by dsimp [D, L]; positivity, min tA (min tG tM),
    lt_min htA (lt_min htG htM), ?_⟩
  intro P Ω instFP instDP instMO μ instProb t s Λplus Wstar S cols ξ htt hs hLaw i
  classical
  have httA : t < tA := lt_of_lt_of_le htt (min_le_left _ _)
  have httG : t < tG := lt_of_lt_of_le htt
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have httM : t < tM := lt_of_lt_of_le htt
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht := hs.scale.1
  have ht1 := hs.scale.2.le
  have hH : 0 ≤ rowCap t := (Real.rpow_pos_of_pos ht _).le
  have hk : 0 ≤ power t kappa := (Real.rpow_pos_of_pos ht _).le
  have hβ : 0 ≤ power t AndersonAC.S45.beta := (Real.rpow_pos_of_pos ht _).le
  have hβ1 : power t AndersonAC.S45.beta ≤ 1 :=
    Real.rpow_le_one ht.le ht1 (by norm_num [AndersonAC.S45.beta, delta])
  have htpk : t ≤ power t kappa := by
    change t ≤ t ^ kappa
    calc
      t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
      _ ≤ t ^ kappa := Real.rpow_le_rpow_of_exponent_ge ht ht1
        (by norm_num [kappa, delta])
  have hHpk : rowCap t ≤ power t kappa :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num [kappa, delta])
  have hf := hFacts P t s Λplus Wstar httA hs
  have hrow : ∀ x, (∑ j, ‖s.h t x j‖ ^ 4) ≤ rowCap t := by
    intro x
    simpa [AndersonAC.S45.State.fourthRow] using hs.row_cap x
  have hrowsq : ∀ x, (∑ j, s.F t x j ^ 2) ≤ rowCap t := by
    intro x
    simpa only [AndersonAC.S45.State.F, entryAbsSquare, ← pow_mul] using hrow x
  let ν : P → ℂ := fun x => if x ∈ S then
    if i = x then 0 else ∫ ω, gamma t s x (ξ x ω) ∂μ else 0
  have hm : 0 ≤ M * Real.sqrt t * power t AndersonAC.S45.beta := by positivity
  have hν : ∀ x, ‖ν x‖ ≤ M * Real.sqrt t * power t AndersonAC.S45.beta := by
    intro x
    dsimp [ν]
    split_ifs with hx hix
    · simpa only [norm_zero] using hm
    · exact hMean P Ω μ t s Λplus Wstar x (ξ x) httM hs (hLaw x hx)
    · simpa only [norm_zero] using hm
  have hνzero : ν i = 0 := by simp [ν]
  have hνsum : (∑ x, ν x * fourthCoeff t s cols i x) =
      ∑ x ∈ S, (∫ ω, gamma t s x (ξ x ω) ∂μ) * fourthCoeff t s cols i x := by
    simp only [ν, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hix : i = x
    · simp [hix, fourthCoeff]
    · simp [hix]
  have hrest := fourth_restored_linear_mean_bound s t C A M ν i ht ht1
    (lt_of_lt_of_le zero_lt_one hC) hA.le hM.le hs.symmetric hs.ward
    (fun x => (hs.broad x).2.1) (fun x => (hf.1 x).2.2.1) (hrow i) hν
  have hcoeff := fourthCoeff_sum_bound t s cols i ν
    (M * Real.sqrt t * power t AndersonAC.S45.beta) (A * Real.sqrt t) (rowCap t)
    hm (by positivity) hH hν hνzero (fun x => (hf.1 x).2.2.2) (hrow i)
  rw [hνsum] at hcoeff
  have herr : (M * Real.sqrt t * power t AndersonAC.S45.beta) *
      (A * Real.sqrt t) * rowCap t ≤ M * A * (rowCap t * power t kappa) := by
    calc
      _ = M * A * rowCap t * (t * power t AndersonAC.S45.beta) := by
        calc
          _ = M * A * rowCap t * power t AndersonAC.S45.beta * (Real.sqrt t) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt ht.le]; ring
      _ ≤ M * A * rowCap t * power t kappa := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_left hβ1 ht.le).trans (by simpa using htpk)
      _ = _ := by ring
  have hcoeffBound : ‖∑ x ∈ S, (∫ ω, gamma t s x (ξ x ω) ∂μ) * fourthCoeff t s cols i x‖ ≤
      (L + M * A) * (rowCap t * power t kappa) := by
    calc
      _ ≤ (∑ j, ‖s.h t i j‖ ^ 3 * ‖∑ x, ν x * s.h t i x * s.h t x j‖) +
          (M * Real.sqrt t * power t AndersonAC.S45.beta) * (A * Real.sqrt t) * rowCap t := hcoeff
      _ ≤ L * rowCap t * power t kappa + M * A * (rowCap t * power t kappa) :=
        add_le_add hrest herr
      _ = _ := by ring
  have hgammaAE : ∀ x ∈ S, ∀ᵐ ω ∂μ, ‖gamma t s x (ξ x ω)‖ ≤ G := by
    intro x hx
    filter_upwards [(hLaw x hx).bounded] with ω hω
    exact hGamma P t s Λplus Wstar x (ξ x ω) httG hs hω
  have hmatrix := fourthProxy_mean_matrix_bound μ t s cols S i ξ G (rowCap t)
    hG.le hH hs.symmetric (fun x hx => (hLaw x hx).measurable) hgammaAE hrowsq
  have hcube := hf.2.2 i
  have hHsq : rowCap t ^ 2 ≤ rowCap t * power t kappa := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hHpk hH
  calc
    _ ≤ 4 * ‖∑ x ∈ S, (∫ ω, gamma t s x (ξ x ω) ∂μ) * fourthCoeff t s cols i x‖ +
        8 * G ^ 2 * (s.F t ^ 3) i i + 3 * G ^ 4 * rowCap t ^ 2 := hmatrix
    _ ≤ 4 * ((L + M * A) * (rowCap t * power t kappa)) +
        8 * G ^ 2 * (A * power t kappa * rowCap t) +
        3 * G ^ 4 * (rowCap t * power t kappa) := by gcongr
    _ = D * power t kappa * rowCap t := by dsimp [D]; ring

theorem fourth_bounds_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S cols : Finset P) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    (∀ i, |∑ x ∈ S, ∫ ω, fourthProxy t s cols i x (ξ x ω) ∂μ| ≤
      C' * power t kappa * rowCap t) ∧
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ i,
      (∑ x ∈ S, |fourthProxy t s cols i x (z x)| ^ 2) ≤
        C' * power t kappa * rowCap t ^ 2) := by
  intro C hC
  obtain ⟨M, hM, tM, htM, hmean⟩ := fourth_bounds_mean C hC
  obtain ⟨G, hG, tG, htG, hstack⟩ :=
    fourth_bounds_square_stack_of_analyticPrestate analytic_prestate_proof C hC
  refine ⟨max M G, lt_of_lt_of_le hM (le_max_left _ _), min tM tG,
    lt_min htM htG, ?_⟩
  intro P Ω instFP instDP instMO μ instProb t s Λplus Wstar S cols ξ htt hs hLaw
  have hpk : 0 ≤ power t kappa := (Real.rpow_pos_of_pos hs.scale.1 _).le
  have hH : 0 ≤ rowCap t := (Real.rpow_pos_of_pos hs.scale.1 _).le
  constructor
  · intro i
    exact (hmean P Ω μ t s Λplus Wstar S cols ξ
      (lt_of_lt_of_le htt (min_le_left _ _)) hs hLaw i).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left M G) hpk) hH)
  · intro z hz i
    exact (hstack P Ω μ t s Λplus Wstar S cols ξ
      (lt_of_lt_of_le htt (min_le_right _ _)) hs hLaw z hz i).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right M G) hpk) (sq_nonneg _))

def Jmodel {P : Type*} [DecidableEq P] (h : CMat P) (x : P) (a b : ℂ) : CMat P :=
  fun i j => if i = x ∨ j = x then 0 else
    a * h i x * h i j * h x j + b * h i x ^ 2 * h x j ^ 2

theorem Jinc_eq_model {P : Type*} [Fintype P] [DecidableEq P]
    (t : ℝ) (s : State P) (x : P) (ξ : ℝ) :
    Jinc t s x ξ = Jmodel (s.h t) x (-2 * gamma t s x ξ)
      (gamma t s x ξ ^ 2 - (1 - s.K t x x)⁻¹) := by
  ext i j
  by_cases hi : i = x <;> by_cases hj : j = x
  · simp [Jinc, Jmodel, pad, survivors, hi]
  · simp [Jinc, Jmodel, pad, survivors, hi]
  · simp [Jinc, Jmodel, pad, survivors, hj]
  · simp [Jinc, Jmodel, pad, survivors, hi, hj, AndersonAC.S45.State.K,
      AndersonAC.S45.entrywiseSquare, AndersonAC.Blueprint.entrywiseSquare]

theorem Jmodel_decompose {P : Type*} [DecidableEq P]
    (h : CMat P) (x : P) (a b : ℂ) :
    Jmodel h x a b = a • Jmodel h x 1 0 + b • Jmodel h x 0 1 := by
  ext i j
  simp only [Jmodel, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem Jmodel_apply_symm {P : Type*} [DecidableEq P]
    (h : CMat P) (x : P) (a b : ℂ) (hh : ∀ i j, h j i = h i j) (i j : P) :
    (Jmodel h x a b) j i = (Jmodel h x a b) i j := by
  dsimp only [Jmodel]
  by_cases hi : i = x <;> by_cases hj : j = x
  · simp [hi, hj]
  · simp [hi, hj]
  · simp [hi, hj]
  · simp only [hi, hj, or_false, false_or, if_false]
    rw [hh j i, hh j x, hh x i]
    ring

theorem Jmodel_symm {P : Type*} [DecidableEq P]
    (h : CMat P) (x : P) (a b : ℂ) (hh : h.IsSymm) :
    (Jmodel h x a b).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact Jmodel_apply_symm h x a b (fun p q => hh.apply p q) i j

theorem complex_norm_add_sq_le (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have ht := (sq_le_sq₀ (norm_nonneg (a + b)) (by positivity : 0 ≤ ‖a‖ + ‖b‖)).2
    (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem complex_norm_sub_sq_le (a b : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  simpa only [sub_eq_add_neg, norm_neg] using complex_norm_add_sq_le a (-b)

theorem matrix_norm_le_of_l2sq_bound {P : Type*} [Fintype P] [DecidableEq P]
    (A : CMat P) (R : ℝ) (hR : 0 ≤ R)
    (hvec : ∀ u, l2sq (A *ᵥ u) ≤ R ^ 2 * l2sq u) : ‖A‖ ≤ R := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro u
  rw [← WithLp.toLp_ofLp (p := 2) u, Matrix.toEuclideanCLM_toLp]
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  calc
    _ ≤ Real.sqrt (R ^ 2 * l2sq (WithLp.ofLp u)) := Real.sqrt_le_sqrt (hvec _)
    _ = R * Real.sqrt (l2sq (WithLp.ofLp u)) := by
      rw [Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR]

theorem matrix_symmetric_row_bound {P : Type*} [Fintype P] [DecidableEq P]
    (A : CMat P) (R : ℝ) (hR : 0 ≤ R)
    (hsym : ∀ i j, ‖A i j‖ = ‖A j i‖) (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ R) :
    ‖A‖ ≤ R := by
  apply matrix_norm_le_of_l2sq_bound A R hR
  intro u
  have hcell : ∀ i, ‖(A *ᵥ u) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖u j‖ ^ 2 := by
    intro i
    have htri : ‖(A *ᵥ u) i‖ ≤ ∑ j, ‖A i j‖ * ‖u j‖ := by
      simpa only [Matrix.mulVec, dotProduct, norm_mul] using
        norm_sum_le Finset.univ (fun j => A i j * u j)
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun j => ‖A i j‖ * ‖u j‖) (f := fun j => ‖A i j‖)
      (g := fun j => ‖A i j‖ * ‖u j‖ ^ 2)
      (fun j _ => norm_nonneg _) (fun j _ => by positivity)
      (fun j _ => by nlinarith)
    calc
      _ ≤ (∑ j, ‖A i j‖ * ‖u j‖) ^ 2 := by gcongr
      _ ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖u j‖ ^ 2 := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (Finset.sum_nonneg fun j _ => by positivity)
  calc
    _ ≤ ∑ i, R * ∑ j, ‖A i j‖ * ‖u j‖ ^ 2 := Finset.sum_le_sum fun i _ => hcell i
    _ = R * ∑ j, ‖u j‖ ^ 2 * ∑ i, ‖A j i‖ := by
      rw [← Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hsym i j]
      ring
    _ ≤ R * ∑ j, ‖u j‖ ^ 2 * R := by
      apply mul_le_mul_of_nonneg_left _ hR
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hrow j) (sq_nonneg _)
    _ = R ^ 2 * l2sq u := by simp [l2sq, Finset.mul_sum]; ring

/-- The scaled Green matrix is symmetric when the unscaled one is. -/
theorem State_h_symm {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (hsym : s.g.IsSymm) (p q : P) :
    s.h t q p = s.h t p q := by
  have hgpq : s.g q p = s.g p q := hsym.apply p q
  simp only [State.h, Matrix.smul_apply, smul_eq_mul, hgpq]

/-- The entrywise square is symmetric under the same hypothesis. -/
theorem State_K_symm {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (hsym : s.g.IsSymm) (p q : P) :
    s.K t q p = s.K t p q := by
  simp only [State.K, AndersonAC.S45.entrywiseSquare,
    AndersonAC.Blueprint.entrywiseSquare]
  rw [State_h_symm s t hsym p q]

/-- Norms of the entrywise square are the `F` weights. -/
theorem State_K_norm {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (i j : P) : ‖s.K t i j‖ = s.F t i j := by
  simp only [State.K, AndersonAC.S45.entrywiseSquare,
    AndersonAC.Blueprint.entrywiseSquare, State.F, entryAbsSquare, norm_pow]

/-- Row sums of the restored linear mean matrix, via the contraction bounds. -/
theorem Jlin_restored_rowsum {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (μ : P → ℂ) (S : Finset P) (m A : ℝ)
    (hsym : s.g.IsSymm) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hrow : ∀ r, (∑ j, s.F t r j) ≤ A)
    (hμ : ∀ x ∈ S, ‖μ x‖ ≤ m) (i : P) :
    (∑ j, ‖∑ x ∈ S, μ x * s.h t i x * s.h t i j * s.h t x j‖) ≤
      A * m * ‖s.h t‖ := by
  classical
  let μ' : P → ℂ := fun x => if x ∈ S then μ x else 0
  have hμ' : ∀ x, ‖μ' x‖ ≤ m := by
    intro x
    dsimp only [μ']
    split_ifs with hx
    · exact hμ x hx
    · simpa only [norm_zero] using hm
  obtain ⟨hmax, hl2⟩ :=
    mean_contraction_row_bounds s t μ' i A m hsym hA hm hrow hμ'
  have hsplit : ∀ j, (∑ x, μ' x * s.h t i x * s.h t x j)
      = ∑ x ∈ S, μ x * s.h t i x * s.h t x j := by
    intro j
    simp only [μ', ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  have heq : ∀ j, (∑ x ∈ S, μ x * s.h t i x * s.h t i j * s.h t x j)
      = s.h t i j * (∑ x, μ' x * s.h t i x * s.h t x j) := by
    intro j
    rw [hsplit j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hl2nn : 0 ≤ l2sq (fun j => ∑ x, μ' x * s.h t i x * s.h t x j) := by
    unfold l2sq
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcs : (∑ j, ‖s.h t i j‖ * ‖∑ x, μ' x * s.h t i x * s.h t x j‖) ^ 2 ≤
      (A * m * ‖s.h t‖) ^ 2 := by
    calc
      _ ≤ (∑ j, ‖s.h t i j‖ ^ 2) *
          (∑ j, ‖∑ x, μ' x * s.h t i x * s.h t x j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, s.F t i j) *
          l2sq (fun j => ∑ x, μ' x * s.h t i x * s.h t x j) := by
        simp only [l2sq, State.F, entryAbsSquare]
      _ ≤ A * (‖s.h t‖ ^ 2 * m ^ 2 * A) :=
        mul_le_mul (hrow i) hl2 hl2nn hA
      _ = (A * m * ‖s.h t‖) ^ 2 := by ring
  have hsum : (∑ j, ‖∑ x ∈ S, μ x * s.h t i x * s.h t i j * s.h t x j‖)
      = ∑ j, ‖s.h t i j‖ * ‖∑ x, μ' x * s.h t i x * s.h t x j‖ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [heq j, norm_mul]
  rw [hsum]
  exact (sq_le_sq₀ (Finset.sum_nonneg fun j _ => by positivity)
    (mul_nonneg (mul_nonneg hA hm) (norm_nonneg _))).1 hcs

/-- Restored linear mean matrix (pivot zeroing removed). -/
def JlinRestored {P : Type*} [Fintype P] [DecidableEq P]
    (h : CMat P) (μ : P → ℂ) (S : Finset P) : CMat P :=
  fun i j => ∑ x ∈ S, μ x * h i x * h i j * h x j

/-- Pivot-restoration correction for the linear mean. -/
def JlinCorrection {P : Type*} [Fintype P] [DecidableEq P]
    (h : CMat P) (μ : P → ℂ) : CMat P :=
  fun i j => μ i * h i i * h i j ^ 2 +
    (if j = i then 0 else μ j * h i j ^ 2 * h j j)

/-- Restored quadratic mean matrix. -/
def JquadRestored {P : Type*} [Fintype P] [DecidableEq P]
    (K : CMat P) (c : P → ℂ) (S : Finset P) : CMat P :=
  fun i j => ∑ x ∈ S, c x * K i x * K x j

/-- Pivot-restoration correction for the quadratic mean. -/
def JquadCorrection {P : Type*} [Fintype P] [DecidableEq P]
    (K : CMat P) (c : P → ℂ) : CMat P :=
  fun i j => c i * K i i * K i j +
    (if j = i then 0 else c j * K i j * K j j)

/-- Nonnegativity of the `F` weights. -/
theorem State_F_nonneg {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (a b : P) : 0 ≤ s.F t a b := by
  simp only [State.F, entryAbsSquare]
  positivity

/-- Operator norm of the restored linear mean matrix. -/
theorem Jlin_restored_norm {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (μ : P → ℂ) (S : Finset P) (m A : ℝ)
    (hsym : s.g.IsSymm) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hrow : ∀ r, (∑ j, s.F t r j) ≤ A)
    (hμ : ∀ x ∈ S, ‖μ x‖ ≤ m) :
    ‖JlinRestored (s.h t) μ S‖ ≤ A * m * ‖s.h t‖ := by
  apply matrix_symmetric_row_bound _ _
    (mul_nonneg (mul_nonneg hA hm) (norm_nonneg _))
  · intro i j
    simp only [JlinRestored]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    simp only [State_h_symm s t hsym x j, State_h_symm s t hsym i j,
      State_h_symm s t hsym i x]
    ring
  · intro i
    simp only [JlinRestored]
    exact Jlin_restored_rowsum s t μ S m A hsym hm hA hrow hμ i

/-- Operator norm of the pivot-restoration correction for the linear mean. -/
theorem Jlin_correction_norm {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (μ : P → ℂ) (m d A : ℝ)
    (hsym : s.g.IsSymm) (hm : 0 ≤ m) (hd : 0 ≤ d) (hA : 0 ≤ A)
    (hrow : ∀ r, (∑ j, s.F t r j) ≤ A)
    (hdiag : ∀ x, ‖s.h t x x‖ ≤ d)
    (hμ : ∀ x, ‖μ x‖ ≤ m) :
    ‖JlinCorrection (s.h t) μ‖ ≤ 2 * m * d * A := by
  classical
  have hhsym : ∀ p q, s.h t q p = s.h t p q :=
    fun p q => State_h_symm s t hsym p q
  apply matrix_symmetric_row_bound _ _ (by positivity)
  · intro i j
    simp only [JlinCorrection]
    congr 1
    by_cases hij : j = i
    · subst hij
      simp
    · have hji : ¬ i = j := fun h => hij h.symm
      simp only [if_neg hij, if_neg hji]
      have hsq : s.h t j i ^ 2 = s.h t i j ^ 2 := by rw [hhsym i j]
      simp only [hsq]
      ring
  · intro i
    simp only [JlinCorrection]
    have hfirst : ∀ j, ‖μ i * s.h t i i * s.h t i j ^ 2‖ =
        ‖μ i‖ * ‖s.h t i i‖ * s.F t i j := by
      intro j
      rw [norm_mul, norm_mul, norm_pow, State.F, entryAbsSquare]
    have hsecond : ∀ j, ‖(if j = i then (0 : ℂ)
        else μ j * s.h t i j ^ 2 * s.h t j j)‖ ≤
        ‖μ j‖ * ‖s.h t j j‖ * s.F t i j := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp only [ite_true, norm_zero]
        exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (State_F_nonneg s t _ _)
      · simp only [if_neg hji]
        calc ‖μ j * s.h t i j ^ 2 * s.h t j j‖
            = ‖μ j‖ * ‖s.h t j j‖ * s.F t i j := by
              rw [norm_mul, norm_mul, norm_pow, State.F, entryAbsSquare]
              ring
          _ ≤ _ := le_rfl
    calc
      _ ≤ ∑ j, (‖μ i‖ * ‖s.h t i i‖ * s.F t i j +
          (‖μ j‖ * ‖s.h t j j‖ * s.F t i j)) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ ‖μ i * s.h t i i * s.h t i j ^ 2‖ +
              ‖(if j = i then (0 : ℂ) else μ j * s.h t i j ^ 2 * s.h t j j)‖ :=
            norm_add_le _ _
          _ ≤ _ := add_le_add (le_of_eq (hfirst j)) (hsecond j)
      _ = (∑ j, ‖μ i‖ * ‖s.h t i i‖ * s.F t i j) +
          ∑ j, ‖μ j‖ * ‖s.h t j j‖ * s.F t i j := by
        rw [Finset.sum_add_distrib]
      _ ≤ m * d * A + m * d * A := by
        apply add_le_add _ _
        · calc
            _ = ‖μ i‖ * ‖s.h t i i‖ * ∑ j, s.F t i j := by
              rw [Finset.mul_sum]
            _ ≤ m * d * A :=
              mul_le_mul (mul_le_mul (hμ i) (hdiag i) (norm_nonneg _) hm)
                (hrow i) (Finset.sum_nonneg fun j _ => State_F_nonneg s t _ _)
                (mul_nonneg hm hd)
        · calc
            _ ≤ ∑ j, m * d * s.F t i j := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul (mul_le_mul (hμ j) (hdiag j) (norm_nonneg _) hm)
                le_rfl (State_F_nonneg s t _ _) (mul_nonneg hm hd)
            _ = m * d * ∑ j, s.F t i j := by rw [Finset.mul_sum]
            _ ≤ m * d * A :=
              mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg hm hd)
      _ = 2 * m * d * A := by ring

/-- Operator norm of the restored quadratic mean matrix. -/
theorem Jquad_restored_norm {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (c : P → ℂ) (S : Finset P) (q A : ℝ)
    (hsym : s.g.IsSymm) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hrow : ∀ r, (∑ j, s.F t r j) ≤ A)
    (hc : ∀ x ∈ S, ‖c x‖ ≤ q) :
    ‖JquadRestored (s.K t) c S‖ ≤ q * A ^ 2 := by
  classical
  have hK : ∀ p q, s.K t q p = s.K t p q :=
    fun p q => State_K_symm s t hsym p q
  have hKn : ∀ a b, ‖s.K t a b‖ = s.F t a b :=
    fun a b => State_K_norm s t a b
  apply matrix_symmetric_row_bound _ _ (mul_nonneg hq (sq_nonneg A))
  · intro i j
    simp only [JquadRestored]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    simp only [hK x j, hK i j, hK i x]
    ring
  · intro i
    simp only [JquadRestored]
    calc
      _ ≤ ∑ x ∈ S, ‖c x‖ * s.F t i x * A := by
        calc
          _ ≤ ∑ j, ∑ x ∈ S, ‖c x‖ * ‖s.K t i x‖ * ‖s.K t x j‖ := by
            apply Finset.sum_le_sum
            intro j _
            calc
              _ ≤ ∑ x ∈ S, ‖c x * s.K t i x * s.K t x j‖ :=
                norm_sum_le _ _
              _ = _ := by
                apply Finset.sum_congr rfl
                intro x _
                simp only [norm_mul]
          _ = ∑ x ∈ S, ∑ j, ‖c x‖ * ‖s.K t i x‖ * ‖s.K t x j‖ := by
            rw [Finset.sum_comm]
          _ ≤ ∑ x ∈ S, ‖c x‖ * s.F t i x * A := by
            apply Finset.sum_le_sum
            intro x _
            calc
              _ = ‖c x‖ * ‖s.K t i x‖ * ∑ j, ‖s.K t x j‖ := by
                rw [Finset.mul_sum]
              _ = ‖c x‖ * s.F t i x * ∑ j, s.F t x j := by
                simp only [hKn]
              _ ≤ ‖c x‖ * s.F t i x * A :=
                mul_le_mul_of_nonneg_left (hrow x)
                  (mul_nonneg (norm_nonneg _) (sq_nonneg _))
      _ ≤ ∑ x ∈ S, q * s.F t i x * A := by
        apply Finset.sum_le_sum
        intro x hx
        have h1 : ‖c x‖ * s.F t i x ≤ q * s.F t i x :=
          mul_le_mul_of_nonneg_right (hc x hx) (State_F_nonneg s t _ _)
        exact mul_le_mul_of_nonneg_right h1 hA
      _ = q * A * ∑ x ∈ S, s.F t i x := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ q * A * A := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hq hA)
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun x _ _ => sq_nonneg _)).trans (hrow i)
      _ = q * A ^ 2 := by ring

/-- Operator norm of the pivot-restoration correction for the quadratic mean. -/
theorem Jquad_correction_norm {P : Type*} [Fintype P] [DecidableEq P]
    (s : State P) (t : ℝ) (c : P → ℂ) (q e A : ℝ)
    (hsym : s.g.IsSymm) (hq : 0 ≤ q) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hrow : ∀ r, (∑ j, s.F t r j) ≤ A)
    (hKdiag : ∀ x, ‖s.K t x x‖ ≤ e)
    (hc : ∀ x, ‖c x‖ ≤ q) :
    ‖JquadCorrection (s.K t) c‖ ≤
      2 * q * e * A := by
  classical
  have hK : ∀ p q, s.K t q p = s.K t p q :=
    fun p q => State_K_symm s t hsym p q
  have hKn : ∀ a b, ‖s.K t a b‖ = s.F t a b :=
    fun a b => State_K_norm s t a b
  apply matrix_symmetric_row_bound _ _ (by positivity)
  · intro i j
    simp only [JquadCorrection]
    congr 1
    by_cases hij : j = i
    · subst hij
      simp
    · have hji : ¬ i = j := fun h => hij h.symm
      simp only [if_neg hij, if_neg hji]
      have hsq : s.K t j i = s.K t i j := hK i j
      simp only [hsq]
      ring
  · intro i
    simp only [JquadCorrection]
    have hfirst : ∀ j, ‖c i * s.K t i i * s.K t i j‖ =
        ‖c i‖ * ‖s.K t i i‖ * s.F t i j := by
      intro j
      simp only [norm_mul, hKn]
    have hsecond : ∀ j, ‖(if j = i then (0 : ℂ)
        else c j * s.K t i j * s.K t j j)‖ ≤
        ‖c j‖ * ‖s.K t j j‖ * s.F t i j := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp only [ite_true, norm_zero]
        exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (State_F_nonneg s t _ _)
      · simp only [if_neg hji]
        calc ‖c j * s.K t i j * s.K t j j‖
            = ‖c j‖ * ‖s.K t j j‖ * s.F t i j := by
              simp only [norm_mul, hKn]
              ring
          _ ≤ _ := le_rfl
    calc
      _ ≤ ∑ j, (‖c i‖ * ‖s.K t i i‖ * s.F t i j +
          (‖c j‖ * ‖s.K t j j‖ * s.F t i j)) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ ‖c i * s.K t i i * s.K t i j‖ +
              ‖(if j = i then (0 : ℂ) else c j * s.K t i j * s.K t j j)‖ :=
            norm_add_le _ _
          _ ≤ _ := add_le_add (le_of_eq (hfirst j)) (hsecond j)
      _ = (∑ j, ‖c i‖ * ‖s.K t i i‖ * s.F t i j) +
          ∑ j, ‖c j‖ * ‖s.K t j j‖ * s.F t i j := by
        rw [Finset.sum_add_distrib]
      _ ≤ q * e * A + q * e * A := by
        apply add_le_add _ _
        · calc
            _ = ‖c i‖ * ‖s.K t i i‖ * ∑ j, s.F t i j := by
              rw [Finset.mul_sum]
            _ ≤ q * e * A :=
              mul_le_mul (mul_le_mul (hc i) (hKdiag i) (norm_nonneg _) hq)
                (hrow i) (Finset.sum_nonneg fun j _ => State_F_nonneg s t _ _)
                (mul_nonneg hq he)
        · calc
            _ ≤ ∑ j, q * e * s.F t i j := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul (mul_le_mul (hc j) (hKdiag j) (norm_nonneg _) hq)
                le_rfl (State_F_nonneg s t _ _) (mul_nonneg hq he)
            _ = q * e * ∑ j, s.F t i j := by rw [Finset.mul_sum]
            _ ≤ q * e * A :=
              mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg hq he)
      _ = 2 * q * e * A := by ring

/-- Padded pivot sums equal restored sums minus the pivot correction.
The zero-extension hypothesis makes the correction exact on every entry. -/
theorem padded_eq_restored_sub_correction {P : Type*} [Fintype P] [DecidableEq P]
    (f : P → ℂ) (S : Finset P) (d1 d2 : ℂ) (i j : P)
    (hdi : d1 = f i) (hdj : d2 = f j)
    (hμ0 : ∀ x ∉ S, f x = 0) :
    (∑ x ∈ S, (if i = x ∨ j = x then (0 : ℂ) else f x))
    = (∑ x ∈ S, f x) - (d1 + (if j = i then 0 else d2)) := by
  classical
  have hD : d1 + (if j = i then 0 else d2)
      = ∑ x ∈ S, (if i = x ∨ j = x then f x else 0) := by
    by_cases hij : j = i
    · simp only [hij]
      simp only [eq_self_iff_true, ite_true, add_zero, or_self]
      rw [hdi, Finset.sum_ite_eq]
      by_cases hiS : i ∈ S
      · rw [if_pos hiS]
      · rw [if_neg hiS]
        exact hμ0 i hiS
    · have hji : ¬ i = j := fun h => hij h.symm
      rw [if_neg hij, hdi, hdj]
      have hsplit : (∑ x ∈ S, (if i = x ∨ j = x then f x else 0))
          = (∑ x ∈ S, (if x = i then f x else 0))
          + ∑ x ∈ S, (if x = j then f x else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx1 : x = i <;> by_cases hx2 : x = j
        · exact absurd (hx2.symm.trans hx1) hij
        · have cL : i = x ∨ j = x := Or.inl hx1.symm
          rw [if_pos cL, if_pos hx1, if_neg hx2, add_zero]
        · have cL : i = x ∨ j = x := Or.inr hx2.symm
          rw [if_pos cL, if_neg hx1, if_pos hx2, zero_add]
        · have cL : ¬ (i = x ∨ j = x) :=
            fun h => h.elim (fun h1 => hx1 h1.symm) (fun h2 => hx2 h2.symm)
          rw [if_neg cL, if_neg hx1, if_neg hx2, add_zero]
      rw [hsplit]
      have e1 : (∑ x ∈ S, (if x = i then f x else 0)) = f i := by
        rw [Finset.sum_ite_eq']
        by_cases hiS : i ∈ S
        · rw [if_pos hiS]
        · rw [if_neg hiS]
          exact (hμ0 i hiS).symm
      have e2 : (∑ x ∈ S, (if x = j then f x else 0)) = f j := by
        rw [Finset.sum_ite_eq']
        by_cases hjS : j ∈ S
        · rw [if_pos hjS]
        · rw [if_neg hjS]
          exact (hμ0 j hjS).symm
      rw [e1, e2]
  have hmain : (∑ x ∈ S, (if i = x ∨ j = x then (0 : ℂ) else f x))
      + (∑ x ∈ S, (if i = x ∨ j = x then f x else 0)) = ∑ x ∈ S, f x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hC : i = x ∨ j = x <;> simp [hC]
  linear_combination hmain + hD

/-- The mean increment splits into scalar integrals against fixed matrices. -/
theorem Jint_eq {P Ω : Type*} [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P) (x : P)
    (ξ : Ω → ℝ)
    (hγ : Integrable (fun ω => gamma t s x (ξ ω)) μ)
    (hγ2 : Integrable (fun ω => gamma t s x (ξ ω) ^ 2) μ) :
    (∫ ω, Jinc t s x (ξ ω) ∂μ)
    = (∫ ω, (-2 * gamma t s x (ξ ω)) ∂μ) • Jmodel (s.h t) x 1 0
    + (∫ ω, (gamma t s x (ξ ω) ^ 2 - (1 - s.K t x x)⁻¹) ∂μ) •
      Jmodel (s.h t) x 0 1 := by
  have hpoint : ∀ ω, Jinc t s x (ξ ω)
      = ((-2 * gamma t s x (ξ ω)) • Jmodel (s.h t) x 1 0
      + (gamma t s x (ξ ω) ^ 2 - (1 - s.K t x x)⁻¹) •
        Jmodel (s.h t) x 0 1) := by
    intro ω
    rw [Jinc_eq_model]
    exact Jmodel_decompose _ _ _ _
  have h1f : Integrable
      (fun ω => (-2 * gamma t s x (ξ ω)) • Jmodel (s.h t) x 1 0) μ :=
    (hγ.const_mul (-2)).smul_const _
  have h2f : Integrable (fun ω => (gamma t s x (ξ ω) ^ 2 - (1 - s.K t x x)⁻¹) •
      Jmodel (s.h t) x 0 1) μ :=
    (hγ2.sub (integrable_const _)).smul_const _
  have hcongr : (∫ ω, Jinc t s x (ξ ω) ∂μ)
      = ∫ ω, (((-2 * gamma t s x (ξ ω)) • Jmodel (s.h t) x 1 0)
        + ((gamma t s x (ξ ω) ^ 2 - (1 - s.K t x x)⁻¹) •
          Jmodel (s.h t) x 0 1)) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [hcongr, MeasureTheory.integral_add h1f h2f,
    integral_smul_const, integral_smul_const]

/-- Zero-extended linear mean coefficients for the J estimate. -/
def JmeanLin {P Ω : Type*} [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) (t : ℝ) (s : State P) (S : Finset P)
    (ξ : P → Ω → ℝ) : P → ℂ :=
  fun x => if x ∈ S then (∫ ω, (-2 * gamma t s x (ξ x ω)) ∂μ) else 0

theorem JmeanLin_mem {P Ω : Type*} [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) (t : ℝ) (s : State P) (S : Finset P) (ξ : P → Ω → ℝ)
    (x : P) (hx : x ∈ S) :
    JmeanLin μ t s S ξ x = ∫ ω, (-2 * gamma t s x (ξ x ω)) ∂μ := by
  simp [JmeanLin, hx]

theorem JmeanLin_notMem {P Ω : Type*} [Fintype P] [DecidableEq P]
    [MeasurableSpace Ω] (μ : Measure Ω) (t : ℝ) (s : State P) (S : Finset P)
    (ξ : P → Ω → ℝ) (x : P) (hx : x ∉ S) : JmeanLin μ t s S ξ x = 0 := by
  simp [JmeanLin, hx]

/-- Zero-extended quadratic mean coefficients for the J estimate. -/
def JmeanQuad {P Ω : Type*} [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) (t : ℝ) (s : State P) (S : Finset P)
    (ξ : P → Ω → ℝ) : P → ℂ :=
  fun x => if x ∈ S then
    ((∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹) else 0

theorem JmeanQuad_mem {P Ω : Type*} [Fintype P] [DecidableEq P]
    [MeasurableSpace Ω] (μ : Measure Ω) (t : ℝ) (s : State P) (S : Finset P)
    (ξ : P → Ω → ℝ) (x : P) (hx : x ∈ S) :
    JmeanQuad μ t s S ξ x =
      ((∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹) := by
  simp [JmeanQuad, hx]

theorem JmeanQuad_notMem {P Ω : Type*} [Fintype P] [DecidableEq P]
    [MeasurableSpace Ω] (μ : Measure Ω) (t : ℝ) (s : State P) (S : Finset P)
    (ξ : P → Ω → ℝ) (x : P) (hx : x ∉ S) : JmeanQuad μ t s S ξ x = 0 := by
  simp [JmeanQuad, hx]

/-- Signed mean estimate for the J increment (paper Lemma 4.4, mean half). -/
theorem J_bounds_mean : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S : Finset P) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    ‖∑ x ∈ S, ∫ ω, Jinc t s x (ξ x ω) ∂μ‖ ≤ C' * AndersonAC.S45.power t AndersonAC.S45.beta := by
  intro C hC
  have hAnalytic : analyticPrestateHypothesis := analytic_prestate_proof
  obtain ⟨A, hApos, tA, htA, hFacts⟩ := analyticPrestate_any C hC
  obtain ⟨M, hMpos, tM, htM, hMean⟩ :=
    gamma_mean_bound_any_of_analyticPrestate hAnalytic C hC
  have hC1 : 1 ≤ 2 * C + A := by linarith
  obtain ⟨G₂, hG₂pos, tG, htG, hGamma⟩ := gamma_moments_proof (2 * C + A) hC1
  refine ⟨2 * A * C * M + 4 * M * A ^ 2 + (G₂ + 2 * A ^ 2) * A ^ 2
    + 2 * (G₂ + 2 * A ^ 2) * A ^ 3, by positivity,
    min tA (min tM (min tG (min 1 (1 / (2 * (A ^ 2 + 1)))))),
    lt_min htA (lt_min htM (lt_min htG (lt_min one_pos (by positivity)))), ?_⟩
  intro P Ω instFP instDP instMO μ instProb t s Λplus Wstar S ξ htt hs hLaw
  classical
  have httA : t < tA := lt_of_lt_of_le htt (min_le_left _ _)
  have httM : t < tM :=
    lt_of_lt_of_le htt (le_trans (min_le_right _ _) (min_le_left _ _))
  have httG : t < tG :=
    lt_of_lt_of_le htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have htt1 : t < 1 :=
    lt_of_lt_of_le htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have httK : t < 1 / (2 * (A ^ 2 + 1)) :=
    lt_of_lt_of_le htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  have ht : 0 < t := hs.scale.1
  have ht1 : t ≤ 1 := htt1.le
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrt_nn : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have hf := hFacts P t s Λplus Wstar httA hs
  have hrow : ∀ r, (∑ j, s.F t r j) ≤ A := fun r => (hf.1 r).2.2.1
  have hdiag : ∀ x, ‖s.h t x x‖ ≤ A * Real.sqrt t := fun x => (hf.1 x).2.2.2
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hop : ‖s.h t‖ ≤ C / Real.sqrt t :=
    ward_h_operator_bound s t C ht hCpos hs.symmetric hs.ward
      (fun i => (hs.broad i).2.1)
  have hβnn : 0 ≤ AndersonAC.S45.beta := by norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta]
  have hβ12 : AndersonAC.S45.beta ≤ 1 / 2 := by norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta]
  have hβ1 : AndersonAC.S45.beta ≤ 1 := by norm_num [AndersonAC.S45.beta, AndersonAC.S45.delta]
  have hpow1 : AndersonAC.S45.power t AndersonAC.S45.beta ≤ 1 := Real.rpow_le_one ht.le ht1 hβnn
  have hpow_nn : 0 ≤ AndersonAC.S45.power t AndersonAC.S45.beta := (Real.rpow_pos_of_pos ht _).le
  have hsqrt_beta : Real.sqrt t ≤ AndersonAC.S45.power t AndersonAC.S45.beta := by
    dsimp [AndersonAC.S45.power]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 hβ12
  have ht_beta : t ≤ AndersonAC.S45.power t AndersonAC.S45.beta := by
    calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
      _ ≤ t ^ AndersonAC.S45.beta := Real.rpow_le_rpow_of_exponent_ge ht ht1 hβ1
  have ht_sqrt : t ≤ Real.sqrt t := by
    have h1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
    calc t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
      _ = Real.sqrt t * Real.sqrt t := by ring
      _ ≤ Real.sqrt t * 1 := mul_le_mul_of_nonneg_left h1 hsqrt_nn
      _ = Real.sqrt t := mul_one _
  have htsqrt_beta : t * Real.sqrt t ≤ AndersonAC.S45.power t AndersonAC.S45.beta := by
    calc t * Real.sqrt t ≤ 1 * Real.sqrt t :=
          mul_le_mul_of_nonneg_right ht1 hsqrt_nn
      _ = Real.sqrt t := one_mul _
      _ ≤ AndersonAC.S45.power t AndersonAC.S45.beta := hsqrt_beta
  have hKxx : ∀ x, ‖s.K t x x‖ ≤ A ^ 2 * t := by
    intro x
    calc ‖s.K t x x‖ = ‖s.h t x x‖ ^ 2 := by
            rw [State_K_norm]; simp [State.F, entryAbsSquare]
      _ ≤ (A * Real.sqrt t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdiag x) 2
      _ = A ^ 2 * t := by rw [mul_pow, Real.sq_sqrt ht.le]
  have hden : 0 < 2 * (A ^ 2 + 1) := by positivity
  have hKsmall : ∀ x, ‖s.K t x x‖ ≤ 1 / 2 := by
    intro x
    have h2 : A ^ 2 * t ≤ A ^ 2 * (1 / (2 * (A ^ 2 + 1))) :=
      mul_le_mul_of_nonneg_left httK.le (sq_nonneg A)
    have h3 : A ^ 2 * (1 / (2 * (A ^ 2 + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hden]
      nlinarith [sq_nonneg A]
    linarith [hKxx x]
  have hC1state : ∀ x, ‖s.g x x‖ + ‖s.r x‖ ≤ 2 * C + A := by
    intro x
    have hraw : ‖s.rawLag x‖ ≤ A * AndersonAC.S45.power t AndersonAC.S45.beta := (hf.1 x).1
    have hr : ‖s.r x‖ ≤ C := (hs.broad x).1
    have hg : ‖s.g x x‖ ≤ C + A := by
      have hAterm := mul_le_mul_of_nonneg_left hpow1 hApos.le
      calc ‖s.g x x‖ = ‖s.r x + s.rawLag x‖ := by
            congr 1
            simp [State.rawLag]
        _ ≤ ‖s.r x‖ + ‖s.rawLag x‖ := norm_add_le _ _
        _ ≤ C + A * AndersonAC.S45.power t AndersonAC.S45.beta := add_le_add hr hraw
        _ ≤ C + A := by linarith
    linarith
  have hLaw1 : ∀ x ∈ S, MomentLaw μ t (2 * C + A) (ξ x) := by
    intro x hx
    have hL := hLaw x hx
    have hCle : C ≤ 2 * C + A := by linarith [hCpos, hApos]
    have hbdd : ∀ᵐ ω ∂μ, |ξ x ω| ≤ (2 * C + A) * Real.sqrt t :=
      hL.bounded.mono fun ω hω =>
        hω.trans (mul_le_mul_of_nonneg_right hCle (Real.sqrt_nonneg t))
    exact ⟨hL.measurable, hL.mean, hL.variance, hbdd⟩
  have hγm : ∀ x ∈ S, Measurable (fun ω => gamma t s x (ξ x ω)) := by
    intro x hx
    have hmξ := (hLaw x hx).measurable
    dsimp [gamma]
    fun_prop
  have hae : ∀ x ∈ S, ∀ᵐ ω ∂μ, ‖gamma t s x (ξ x ω)‖ ≤ G₂ := by
    intro x hx
    have hGx := hGamma P Ω μ t s x (ξ x) ht httG (hC1state x) (hLaw1 x hx)
    exact hGx.1.mono fun ω h => h.1
  have hγI : ∀ x ∈ S, Integrable (fun ω => gamma t s x (ξ x ω)) μ := by
    intro x hx
    exact Integrable.of_bound (hγm x hx).aestronglyMeasurable G₂ (hae x hx)
  have hγ2m : ∀ x ∈ S, Measurable (fun ω => gamma t s x (ξ x ω) ^ 2) := by
    intro x hx
    have hm := hγm x hx
    fun_prop
  have hae2 : ∀ x ∈ S, ∀ᵐ ω ∂μ, ‖gamma t s x (ξ x ω) ^ 2‖ ≤ G₂ ^ 2 := by
    intro x hx
    filter_upwards [hae x hx] with ω hω
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hγ2I : ∀ x ∈ S, Integrable (fun ω => gamma t s x (ξ x ω) ^ 2) μ := by
    intro x hx
    exact Integrable.of_bound (hγ2m x hx).aestronglyMeasurable (G₂ ^ 2)
      (hae2 x hx)
  have hMx : ∀ x ∈ S,
      ‖(∫ ω, gamma t s x (ξ x ω) ∂μ)‖ ≤ M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by
    intro x hx
    exact hMean P Ω μ t s Λplus Wstar x (ξ x) httM hs (hLaw x hx)
  have hSx : ∀ x ∈ S,
      ‖(∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - 1‖ ≤ G₂ * Real.sqrt t := by
    intro x hx
    exact (hGamma P Ω μ t s x (ξ x) ht httG (hC1state x) (hLaw1 x hx)).2.2.1
  have hn2 : ‖(-2 : ℂ)‖ = 2 := by
    simp only [show (-2 : ℂ) = -(2 : ℂ) by ring, norm_neg, RCLike.norm_ofNat]
  have hμ'b : ∀ x, ‖JmeanLin μ t s S ξ x‖ ≤ 2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by
    intro x
    by_cases hx : x ∈ S
    · rw [JmeanLin_mem μ t s S ξ x hx, MeasureTheory.integral_const_mul,
        norm_mul, hn2]
      calc 2 * ‖(∫ ω, gamma t s x (ξ x ω) ∂μ)‖
          ≤ 2 * (M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) :=
            mul_le_mul_of_nonneg_left (hMx x hx) (by norm_num)
        _ = 2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta := by ring
    · rw [JmeanLin_notMem μ t s S ξ x hx]
      simp only [norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMpos.le)
        hsqrt_nn) hpow_nn
  have ha_quad : ∀ x, ‖(1 : ℂ) - (1 - s.K t x x)⁻¹‖ ≤ 2 * A ^ 2 * t := by
    intro x
    have hKne : (1 : ℂ) - s.K t x x ≠ 0 := by
      intro hcon
      have heq : s.K t x x = 1 := by
        have h := eq_of_sub_eq_zero hcon
        simpa using h.symm
      have h1 : ‖s.K t x x‖ = 1 := by rw [heq, norm_one]
      linarith [hKsmall x]
    have h1 : (1 : ℂ) = ((1 : ℂ) - s.K t x x) * ((1 : ℂ) - s.K t x x)⁻¹ :=
      (mul_inv_cancel₀ hKne).symm
    have heq : (1 : ℂ) - ((1 : ℂ) - s.K t x x)⁻¹
        = -((s.K t x x) * ((1 : ℂ) - s.K t x x)⁻¹) := by
      calc (1 : ℂ) - ((1 : ℂ) - s.K t x x)⁻¹
          = ((1 : ℂ) - s.K t x x) * ((1 : ℂ) - s.K t x x)⁻¹
            - ((1 : ℂ) - s.K t x x)⁻¹ := by rw [← h1]
        _ = _ := by ring
    have hden : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - s.K t x x‖ := by
      have htri : ‖(1 : ℂ)‖
          ≤ ‖(1 : ℂ) - s.K t x x‖ + ‖s.K t x x‖ := by
        calc ‖(1 : ℂ)‖ = ‖((1 : ℂ) - s.K t x x) + s.K t x x‖ := by
                congr 1
                abel
          _ ≤ _ := norm_add_le _ _
      simp only [norm_one] at htri
      linarith [hKsmall x]
    rw [heq, norm_neg, norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)]
    calc ‖s.K t x x‖ ≤ A ^ 2 * t := hKxx x
      _ = (2 * A ^ 2 * t) * (1 / 2) := by ring
      _ ≤ (2 * A ^ 2 * t) * ‖(1 : ℂ) - s.K t x x‖ :=
        mul_le_mul_of_nonneg_left hden
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A)) ht.le)
  have hccb : ∀ x, ‖JmeanQuad μ t s S ξ x‖ ≤ (G₂ + 2 * A ^ 2) * Real.sqrt t := by
    intro x
    by_cases hx : x ∈ S
    · rw [JmeanQuad_mem μ t s S ξ x hx]
      have h1 := hSx x hx
      have h2 := ha_quad x
      have htt2 : 2 * A ^ 2 * t ≤ 2 * A ^ 2 * Real.sqrt t :=
        mul_le_mul_of_nonneg_left ht_sqrt
          (mul_nonneg (by norm_num) (sq_nonneg A))
      calc ‖(∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹‖
          = ‖((∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - 1)
            + (1 - (1 - s.K t x x)⁻¹)‖ := by
              congr 1
              abel
        _ ≤ ‖(∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - 1‖
            + ‖(1 : ℂ) - (1 - s.K t x x)⁻¹‖ := norm_add_le _ _
        _ ≤ G₂ * Real.sqrt t + 2 * A ^ 2 * Real.sqrt t :=
          add_le_add h1 (h2.trans htt2)
        _ = (G₂ + 2 * A ^ 2) * Real.sqrt t := by ring
    · rw [JmeanQuad_notMem μ t s S ξ x hx]
      simp only [norm_zero]
      exact mul_nonneg (add_nonneg hG₂pos.le
        (mul_nonneg (by norm_num) (sq_nonneg A))) hsqrt_nn
  -- matrix identity
  have hMat : (∑ x ∈ S, ∫ ω, Jinc t s x (ξ x ω) ∂μ)
      = (JlinRestored (s.h t) (JmeanLin μ t s S ξ) S
        - JlinCorrection (s.h t) (JmeanLin μ t s S ξ))
      + (JquadRestored (s.K t) (JmeanQuad μ t s S ξ) S
        - JquadCorrection (s.K t) (JmeanQuad μ t s S ξ)) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.sub_apply]
    have hper : ∀ x ∈ S, ((∫ ω, Jinc t s x (ξ x ω) ∂μ) i j)
        = (JmeanLin μ t s S ξ x)
          * (if i = x ∨ j = x then (0 : ℂ)
            else s.h t i x * s.h t i j * s.h t x j)
        + (JmeanQuad μ t s S ξ x)
          * (if i = x ∨ j = x then (0 : ℂ) else s.K t i x * s.K t x j) := by
      intro x hx
      have hJ := Jint_eq μ t s x (ξ x) (hγI x hx) (hγ2I x hx)
      have hA : Jmodel (s.h t) x 1 0 i j
          = (if i = x ∨ j = x then (0 : ℂ)
            else s.h t i x * s.h t i j * s.h t x j) := by
        by_cases hcond : i = x ∨ j = x
        · simp [Jmodel, hcond]
        · simp [Jmodel, hcond]
      have hB : Jmodel (s.h t) x 0 1 i j
          = (if i = x ∨ j = x then (0 : ℂ) else s.K t i x * s.K t x j) := by
        by_cases hcond : i = x ∨ j = x
        · simp [Jmodel, hcond]
        · simp [Jmodel, hcond, State.K, AndersonAC.S45.entrywiseSquare,
            AndersonAC.Blueprint.entrywiseSquare]
      have hsub : (∫ ω, (gamma t s x (ξ x ω) ^ 2 - (1 - s.K t x x)⁻¹) ∂μ)
          = (∫ ω, gamma t s x (ξ x ω) ^ 2 ∂μ) - (1 - s.K t x x)⁻¹ := by
        have h := MeasureTheory.integral_sub (hγ2I x hx)
          (integrable_const ((1 - s.K t x x)⁻¹ : ℂ))
        simpa using h
      rw [hJ]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hA, hB,
        hsub, JmeanLin_mem μ t s S ξ x hx, JmeanQuad_mem μ t s S ξ x hx]
    have hμ0lin : ∀ x ∉ S, (JmeanLin μ t s S ξ x) * s.h t i x * s.h t i j
        * s.h t x j = 0 := by
      intro x hx
      simp [JmeanLin_notMem μ t s S ξ x hx]
    have hμ0quad : ∀ x ∉ S, (JmeanQuad μ t s S ξ x) * s.K t i x * s.K t x j
        = 0 := by
      intro x hx
      simp [JmeanQuad_notMem μ t s S ξ x hx]
    have plin_entry : (∑ x ∈ S, (if i = x ∨ j = x then (0 : ℂ)
          else (JmeanLin μ t s S ξ x) * s.h t i x * s.h t i j * s.h t x j))
        = (∑ x ∈ S, (JmeanLin μ t s S ξ x) * s.h t i x * s.h t i j * s.h t x j)
        - ((JmeanLin μ t s S ξ i) * s.h t i i * s.h t i j ^ 2
          + (if j = i then 0 else (JmeanLin μ t s S ξ j) * s.h t i j ^ 2
            * s.h t j j)) :=
      padded_eq_restored_sub_correction _ _ _ _ _ _ (by ring) (by ring) hμ0lin
    have pquad_entry : (∑ x ∈ S, (if i = x ∨ j = x then (0 : ℂ)
          else (JmeanQuad μ t s S ξ x) * s.K t i x * s.K t x j))
        = (∑ x ∈ S, (JmeanQuad μ t s S ξ x) * s.K t i x * s.K t x j)
        - ((JmeanQuad μ t s S ξ i) * s.K t i i * s.K t i j
          + (if j = i then 0 else (JmeanQuad μ t s S ξ j) * s.K t i j
            * s.K t j j)) :=
      padded_eq_restored_sub_correction _ _ _ _ _ _ (by ring) (by ring) hμ0quad
    calc (∑ x ∈ S, ((∫ ω, Jinc t s x (ξ x ω) ∂μ) i j))
        = ∑ x ∈ S, ((JmeanLin μ t s S ξ x)
            * (if i = x ∨ j = x then (0 : ℂ)
              else s.h t i x * s.h t i j * s.h t x j)
          + (JmeanQuad μ t s S ξ x)
            * (if i = x ∨ j = x then (0 : ℂ) else s.K t i x * s.K t x j)) :=
          Finset.sum_congr rfl hper
      _ = (∑ x ∈ S, (if i = x ∨ j = x then (0 : ℂ)
            else (JmeanLin μ t s S ξ x) * s.h t i x * s.h t i j * s.h t x j))
        + (∑ x ∈ S, (if i = x ∨ j = x then (0 : ℂ)
            else (JmeanQuad μ t s S ξ x) * s.K t i x * s.K t x j)) := by
          simp only [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          by_cases hcond : i = x ∨ j = x
          · simp [hcond]
          · simp only [if_neg hcond]
            ring
      _ = ((∑ x ∈ S, (JmeanLin μ t s S ξ x) * s.h t i x * s.h t i j * s.h t x j)
          - ((JmeanLin μ t s S ξ i) * s.h t i i * s.h t i j ^ 2
            + (if j = i then 0 else (JmeanLin μ t s S ξ j) * s.h t i j ^ 2
              * s.h t j j)))
        + ((∑ x ∈ S, (JmeanQuad μ t s S ξ x) * s.K t i x * s.K t x j)
          - ((JmeanQuad μ t s S ξ i) * s.K t i i * s.K t i j
            + (if j = i then 0 else (JmeanQuad μ t s S ξ j) * s.K t i j
              * s.K t j j))) := by
          rw [plin_entry, pquad_entry]
      _ = _ := by
          simp only [JlinRestored, JlinCorrection, JquadRestored,
            JquadCorrection, Matrix.sub_apply]
  -- norm bounds on the four pieces
  have hm_nn : 0 ≤ 2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMpos.le)
      hsqrt_nn) hpow_nn
  have hq_nn : 0 ≤ (G₂ + 2 * A ^ 2) * Real.sqrt t :=
    mul_nonneg (add_nonneg hG₂pos.le
      (mul_nonneg (by norm_num) (sq_nonneg A))) hsqrt_nn
  have hd_nn : 0 ≤ A * Real.sqrt t := mul_nonneg hApos.le hsqrt_nn
  have he_nn : 0 ≤ A ^ 2 * t := mul_nonneg (sq_nonneg A) ht.le
  have hRlin : ‖JlinRestored (s.h t) (JmeanLin μ t s S ξ) S‖
      ≤ A * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * ‖s.h t‖ :=
    Jlin_restored_norm s t _ S _ A hs.symmetric hm_nn hApos.le hrow
      (fun x hx => hμ'b x)
  have hDlin : ‖JlinCorrection (s.h t) (JmeanLin μ t s S ξ)‖
      ≤ 2 * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * (A * Real.sqrt t) * A :=
    Jlin_correction_norm s t _ _ _ _ hs.symmetric hm_nn hd_nn hApos.le hrow
      hdiag hμ'b
  have hRquad : ‖JquadRestored (s.K t) (JmeanQuad μ t s S ξ) S‖
      ≤ ((G₂ + 2 * A ^ 2) * Real.sqrt t) * A ^ 2 :=
    Jquad_restored_norm s t _ S _ A hs.symmetric hq_nn hApos.le hrow
      (fun x hx => hccb x)
  have hDquad : ‖JquadCorrection (s.K t) (JmeanQuad μ t s S ξ)‖
      ≤ 2 * ((G₂ + 2 * A ^ 2) * Real.sqrt t) * (A ^ 2 * t) * A :=
    Jquad_correction_norm s t _ _ _ _ hs.symmetric hq_nn he_nn hApos.le hrow
      hKxx hccb
  have eRlin : A * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * (C / Real.sqrt t)
      = (2 * A * C * M) * AndersonAC.S45.power t AndersonAC.S45.beta := by
    field_simp
  have eDlin : 2 * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * (A * Real.sqrt t) * A
      ≤ (4 * M * A ^ 2) * AndersonAC.S45.power t AndersonAC.S45.beta := by
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have heq : 2 * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * (A * Real.sqrt t) * A
        = (4 * M * A ^ 2) * (AndersonAC.S45.power t AndersonAC.S45.beta * t) := by
      calc 2 * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * (A * Real.sqrt t) * A
          = (4 * M * A ^ 2 * AndersonAC.S45.power t AndersonAC.S45.beta) * (Real.sqrt t * Real.sqrt t) := by
            ring
        _ = (4 * M * A ^ 2) * (AndersonAC.S45.power t AndersonAC.S45.beta * t) := by rw [hsq]; ring
    have httβ : AndersonAC.S45.power t AndersonAC.S45.beta * t ≤ AndersonAC.S45.power t AndersonAC.S45.beta :=
      calc AndersonAC.S45.power t AndersonAC.S45.beta * t ≤ AndersonAC.S45.power t AndersonAC.S45.beta * 1 :=
            mul_le_mul_of_nonneg_left ht1 hpow_nn
        _ = AndersonAC.S45.power t AndersonAC.S45.beta := mul_one _
    calc 2 * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * (A * Real.sqrt t) * A
        = (4 * M * A ^ 2) * (AndersonAC.S45.power t AndersonAC.S45.beta * t) := heq
      _ ≤ (4 * M * A ^ 2) * AndersonAC.S45.power t AndersonAC.S45.beta :=
        mul_le_mul_of_nonneg_left httβ
          (mul_nonneg (mul_nonneg (by norm_num) hMpos.le) (sq_nonneg A))
  have eRquad : ((G₂ + 2 * A ^ 2) * Real.sqrt t) * A ^ 2
      ≤ ((G₂ + 2 * A ^ 2) * A ^ 2) * AndersonAC.S45.power t AndersonAC.S45.beta := by
    calc ((G₂ + 2 * A ^ 2) * Real.sqrt t) * A ^ 2
        = ((G₂ + 2 * A ^ 2) * A ^ 2) * Real.sqrt t := by ring
      _ ≤ ((G₂ + 2 * A ^ 2) * A ^ 2) * AndersonAC.S45.power t AndersonAC.S45.beta :=
        mul_le_mul_of_nonneg_left hsqrt_beta
          (mul_nonneg (add_nonneg hG₂pos.le
            (mul_nonneg (by norm_num) (sq_nonneg A))) (sq_nonneg A))
  have eDquad : 2 * ((G₂ + 2 * A ^ 2) * Real.sqrt t) * (A ^ 2 * t) * A
      ≤ (2 * (G₂ + 2 * A ^ 2) * A ^ 3) * AndersonAC.S45.power t AndersonAC.S45.beta := by
    have heq : 2 * ((G₂ + 2 * A ^ 2) * Real.sqrt t) * (A ^ 2 * t) * A
        = (2 * (G₂ + 2 * A ^ 2) * A ^ 3) * (Real.sqrt t * t) := by ring
    have httβ : Real.sqrt t * t ≤ AndersonAC.S45.power t AndersonAC.S45.beta := by
      calc Real.sqrt t * t = t * Real.sqrt t := mul_comm _ _
        _ ≤ AndersonAC.S45.power t AndersonAC.S45.beta := htsqrt_beta
    calc 2 * ((G₂ + 2 * A ^ 2) * Real.sqrt t) * (A ^ 2 * t) * A
        = (2 * (G₂ + 2 * A ^ 2) * A ^ 3) * (Real.sqrt t * t) := heq
      _ ≤ (2 * (G₂ + 2 * A ^ 2) * A ^ 3) * AndersonAC.S45.power t AndersonAC.S45.beta :=
        mul_le_mul_of_nonneg_left httβ
          (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hG₂pos.le
            (mul_nonneg (by norm_num) (sq_nonneg A)))) (pow_nonneg hApos.le 3))
  have hRlin' : ‖JlinRestored (s.h t) (JmeanLin μ t s S ξ) S‖
      ≤ (2 * A * C * M) * AndersonAC.S45.power t AndersonAC.S45.beta :=
    calc ‖JlinRestored (s.h t) (JmeanLin μ t s S ξ) S‖
        ≤ A * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * ‖s.h t‖ := hRlin
      _ ≤ A * (2 * M * Real.sqrt t * AndersonAC.S45.power t AndersonAC.S45.beta) * (C / Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hop (mul_nonneg hApos.le hm_nn)
      _ = (2 * A * C * M) * AndersonAC.S45.power t AndersonAC.S45.beta := eRlin
  have hDlin' : ‖JlinCorrection (s.h t) (JmeanLin μ t s S ξ)‖
      ≤ (4 * M * A ^ 2) * AndersonAC.S45.power t AndersonAC.S45.beta := hDlin.trans eDlin
  have hRquad' : ‖JquadRestored (s.K t) (JmeanQuad μ t s S ξ) S‖
      ≤ ((G₂ + 2 * A ^ 2) * A ^ 2) * AndersonAC.S45.power t AndersonAC.S45.beta := hRquad.trans eRquad
  have hDquad' : ‖JquadCorrection (s.K t) (JmeanQuad μ t s S ξ)‖
      ≤ (2 * (G₂ + 2 * A ^ 2) * A ^ 3) * AndersonAC.S45.power t AndersonAC.S45.beta := hDquad.trans eDquad
  calc ‖∑ x ∈ S, ∫ ω, Jinc t s x (ξ x ω) ∂μ‖
      = ‖(JlinRestored (s.h t) (JmeanLin μ t s S ξ) S
        - JlinCorrection (s.h t) (JmeanLin μ t s S ξ))
      + (JquadRestored (s.K t) (JmeanQuad μ t s S ξ) S
        - JquadCorrection (s.K t) (JmeanQuad μ t s S ξ))‖ := by rw [hMat]
    _ ≤ (‖JlinRestored (s.h t) (JmeanLin μ t s S ξ) S‖
        + ‖JlinCorrection (s.h t) (JmeanLin μ t s S ξ)‖)
      + (‖JquadRestored (s.K t) (JmeanQuad μ t s S ξ) S‖
        + ‖JquadCorrection (s.K t) (JmeanQuad μ t s S ξ)‖) := by
        calc _ ≤ ‖JlinRestored (s.h t) (JmeanLin μ t s S ξ) S
            - JlinCorrection (s.h t) (JmeanLin μ t s S ξ)‖
            + ‖JquadRestored (s.K t) (JmeanQuad μ t s S ξ) S
            - JquadCorrection (s.K t) (JmeanQuad μ t s S ξ)‖ :=
              norm_add_le _ _
          _ ≤ _ := add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ ≤ ((2 * A * C * M) * AndersonAC.S45.power t AndersonAC.S45.beta + (4 * M * A ^ 2) * AndersonAC.S45.power t AndersonAC.S45.beta)
      + (((G₂ + 2 * A ^ 2) * A ^ 2) * AndersonAC.S45.power t AndersonAC.S45.beta
        + (2 * (G₂ + 2 * A ^ 2) * A ^ 3) * AndersonAC.S45.power t AndersonAC.S45.beta) :=
        add_le_add (add_le_add hRlin' hDlin') (add_le_add hRquad' hDquad')
    _ = (2 * A * C * M + 4 * M * A ^ 2 + (G₂ + 2 * A ^ 2) * A ^ 2
        + 2 * (G₂ + 2 * A ^ 2) * A ^ 3) * AndersonAC.S45.power t AndersonAC.S45.beta := by ring

/-- Linear cell contraction through the restored row (stack half). -/
theorem Jlin_cell_bound {P : Type*} [Fintype P] [DecidableEq P]
    (h : CMat P) (x i : P) (a : ℂ) (u : P → ℂ) (G d : ℝ)
    (hG : 0 ≤ G) (ha : ‖a‖ ≤ G)
    (hxx : ‖h x x‖ ≤ d)
    (hi : i ≠ x) :
    ‖((Jmodel h x a 0) *ᵥ u) i‖ ^ 2
    ≤ 2 * G ^ 2 * (‖h i x‖ ^ 2 * ‖(h *ᵥ fun j => h i j * u j) x‖ ^ 2)
    + 2 * G ^ 2 * d ^ 2 * ((‖h i x‖ ^ 2) ^ 2 * ‖u x‖ ^ 2) := by
  classical
  have hi' : ¬ i = x := hi
  have hfactor : ((Jmodel h x a 0) *ᵥ u) i
      = a * h i x * ∑ j ∈ Finset.univ.erase x, h x j * (h i j * u j) := by
    have hmulvec : ((Jmodel h x a 0) *ᵥ u) i
        = ∑ j, Jmodel h x a 0 i j * u j := rfl
    have hzero : ∀ j ∈ (Finset.univ : Finset P), j ∉ Finset.univ.erase x →
        Jmodel h x a 0 i j * u j = 0 := by
      intro j _ hj
      have hjx : j = x := by
        by_contra hne
        exact hj (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩)
      simp [Jmodel, hjx, hi']
    have hsub := Finset.sum_subset (Finset.erase_subset x Finset.univ)
      (fun j _ hj => hzero j (Finset.mem_univ j) hj)
    rw [hmulvec, ← hsub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjx : j ≠ x := Finset.ne_of_mem_erase hj
    have hjx' : ¬ j = x := hjx
    simp only [Jmodel, hi', hjx', or_false, false_or, if_false]
    ring
  have herase := Finset.add_sum_erase (Finset.univ : Finset P)
    (fun j => h x j * (h i j * u j)) (Finset.mem_univ x)
  have herase' : h x x * (h i x * u x)
      + ∑ j ∈ Finset.univ.erase x, h x j * (h i j * u j)
      = ∑ j, h x j * (h i j * u j) := herase
  have hW : (h *ᵥ (fun j => h i j * u j)) x
      = ∑ j, h x j * (h i j * u j) := rfl
  have eT : (∑ j ∈ Finset.univ.erase x, h x j * (h i j * u j))
      = (h *ᵥ (fun j => h i j * u j)) x
        + (-(h x x * (h i x * u x))) := by
    linear_combination herase' - hW
  have ha2 : ‖a‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have herr : ‖-(h x x * (h i x * u x))‖ ^ 2
      ≤ d ^ 2 * (‖h i x‖ ^ 2 * ‖u x‖ ^ 2) := by
    have e1 : ‖-(h x x * (h i x * u x))‖
        = ‖h x x‖ * (‖h i x‖ * ‖u x‖) := by
      rw [norm_neg, norm_mul, norm_mul]
    have hbase : ‖h x x‖ * (‖h i x‖ * ‖u x‖)
        ≤ d * (‖h i x‖ * ‖u x‖) :=
      mul_le_mul_of_nonneg_right hxx
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hpow : (‖h x x‖ * (‖h i x‖ * ‖u x‖)) ^ 2
        ≤ (d * (‖h i x‖ * ‖u x‖)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbase 2
    calc ‖-(h x x * (h i x * u x))‖ ^ 2 = (‖h x x‖ * (‖h i x‖ * ‖u x‖)) ^ 2 :=
          by rw [e1]
      _ ≤ (d * (‖h i x‖ * ‖u x‖)) ^ 2 := hpow
      _ = d ^ 2 * (‖h i x‖ ^ 2 * ‖u x‖ ^ 2) := by ring
  have hWnorm : ‖(h *ᵥ (fun j => h i j * u j)) x
      + (-(h x x * (h i x * u x)))‖ ^ 2
      ≤ 2 * ‖(h *ᵥ (fun j => h i j * u j)) x‖ ^ 2
      + 2 * (d ^ 2 * (‖h i x‖ ^ 2 * ‖u x‖ ^ 2)) := by
    calc ‖(h *ᵥ (fun j => h i j * u j)) x + (-(h x x * (h i x * u x)))‖ ^ 2
        ≤ 2 * ‖(h *ᵥ (fun j => h i j * u j)) x‖ ^ 2
          + 2 * ‖-(h x x * (h i x * u x))‖ ^ 2 :=
            complex_norm_add_sq_le _ _
      _ ≤ 2 * ‖(h *ᵥ (fun j => h i j * u j)) x‖ ^ 2
          + 2 * (d ^ 2 * (‖h i x‖ ^ 2 * ‖u x‖ ^ 2)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left herr (by norm_num))
  have enorm : ‖a * h i x
      * (∑ j ∈ Finset.univ.erase x, h x j * (h i j * u j))‖ ^ 2
      = ‖a‖ ^ 2 * ‖h i x‖ ^ 2
        * ‖∑ j ∈ Finset.univ.erase x, h x j * (h i j * u j)‖ ^ 2 := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow]
  rw [hfactor, enorm, eT]
  calc ‖a‖ ^ 2 * ‖h i x‖ ^ 2
        * ‖(h *ᵥ (fun j => h i j * u j)) x + (-(h x x * (h i x * u x)))‖ ^ 2
      ≤ (G ^ 2 * ‖h i x‖ ^ 2)
        * (2 * ‖(h *ᵥ (fun j => h i j * u j)) x‖ ^ 2
          + 2 * (d ^ 2 * (‖h i x‖ ^ 2 * ‖u x‖ ^ 2))) :=
        mul_le_mul (mul_le_mul ha2 le_rfl (sq_nonneg _) (pow_nonneg hG 2))
          hWnorm (sq_nonneg _) (mul_nonneg (pow_nonneg hG 2) (sq_nonneg _))
    _ = 2 * G ^ 2 * (‖h i x‖ ^ 2 * ‖(h *ᵥ fun j => h i j * u j) x‖ ^ 2)
        + 2 * G ^ 2 * d ^ 2 * ((‖h i x‖ ^ 2) ^ 2 * ‖u x‖ ^ 2) := by ring

/-- Quadratic cell contraction through the restored row (stack half). -/
theorem Jquad_cell_bound {P : Type*} [Fintype P] [DecidableEq P]
    (h K : CMat P) (x i : P) (b : ℂ) (u : P → ℂ) (Q e : ℝ)
    (hQ : 0 ≤ Q) (hb : ‖b‖ ≤ Q)
    (hK : ∀ p q, K p q = h p q ^ 2)
    (hKxx : ‖K x x‖ ≤ e)
    (hi : i ≠ x) :
    ‖((Jmodel h x 0 b) *ᵥ u) i‖ ^ 2
    ≤ 2 * Q ^ 2 * (‖K i x‖ ^ 2 * ‖(K *ᵥ u) x‖ ^ 2)
    + 2 * Q ^ 2 * e ^ 2 * (‖K i x‖ ^ 2 * ‖u x‖ ^ 2) := by
  classical
  have hi' : ¬ i = x := hi
  have hfactor : ((Jmodel h x 0 b) *ᵥ u) i
      = b * K i x * ∑ j ∈ Finset.univ.erase x, K x j * u j := by
    have hmulvec : ((Jmodel h x 0 b) *ᵥ u) i
        = ∑ j, Jmodel h x 0 b i j * u j := rfl
    have hzero : ∀ j ∈ (Finset.univ : Finset P), j ∉ Finset.univ.erase x →
        Jmodel h x 0 b i j * u j = 0 := by
      intro j _ hj
      have hjx : j = x := by
        by_contra hne
        exact hj (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩)
      simp [Jmodel, hjx, hi']
    have hsub := Finset.sum_subset (Finset.erase_subset x Finset.univ)
      (fun j _ hj => hzero j (Finset.mem_univ j) hj)
    rw [hmulvec, ← hsub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjx : j ≠ x := Finset.ne_of_mem_erase hj
    have hjx' : ¬ j = x := hjx
    simp only [Jmodel, hi', hjx', or_false, false_or, if_false]
    rw [hK i x, hK x j]
    ring
  have herase := Finset.add_sum_erase (Finset.univ : Finset P)
    (fun j => K x j * u j) (Finset.mem_univ x)
  have herase' : K x x * u x
      + ∑ j ∈ Finset.univ.erase x, K x j * u j
      = ∑ j, K x j * u j := herase
  have hW : (K *ᵥ u) x = ∑ j, K x j * u j := rfl
  have eT : (∑ j ∈ Finset.univ.erase x, K x j * u j)
      = (K *ᵥ u) x + (-(K x x * u x)) := by
    linear_combination herase' - hW
  have hb2 : ‖b‖ ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have herr : ‖-(K x x * u x)‖ ^ 2 ≤ e ^ 2 * ‖u x‖ ^ 2 := by
    have e1 : ‖-(K x x * u x)‖ = ‖K x x‖ * ‖u x‖ := by
      rw [norm_neg, norm_mul]
    have hbase : ‖K x x‖ * ‖u x‖ ≤ e * ‖u x‖ :=
      mul_le_mul_of_nonneg_right hKxx (norm_nonneg _)
    have hpow : (‖K x x‖ * ‖u x‖) ^ 2 ≤ (e * ‖u x‖) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbase 2
    calc ‖-(K x x * u x)‖ ^ 2 = (‖K x x‖ * ‖u x‖) ^ 2 := by rw [e1]
      _ ≤ (e * ‖u x‖) ^ 2 := hpow
      _ = e ^ 2 * ‖u x‖ ^ 2 := by ring
  have hWnorm : ‖(K *ᵥ u) x + (-(K x x * u x))‖ ^ 2
      ≤ 2 * ‖(K *ᵥ u) x‖ ^ 2 + 2 * (e ^ 2 * ‖u x‖ ^ 2) := by
    calc ‖(K *ᵥ u) x + (-(K x x * u x))‖ ^ 2
        ≤ 2 * ‖(K *ᵥ u) x‖ ^ 2 + 2 * ‖-(K x x * u x)‖ ^ 2 :=
            complex_norm_add_sq_le _ _
      _ ≤ 2 * ‖(K *ᵥ u) x‖ ^ 2 + 2 * (e ^ 2 * ‖u x‖ ^ 2) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left herr (by norm_num))
  have enorm : ‖b * K i x
      * (∑ j ∈ Finset.univ.erase x, K x j * u j)‖ ^ 2
      = ‖b‖ ^ 2 * ‖K i x‖ ^ 2
        * ‖∑ j ∈ Finset.univ.erase x, K x j * u j‖ ^ 2 := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow]
  rw [hfactor, enorm, eT]
  calc ‖b‖ ^ 2 * ‖K i x‖ ^ 2
        * ‖(K *ᵥ u) x + (-(K x x * u x))‖ ^ 2
      ≤ (Q ^ 2 * ‖K i x‖ ^ 2)
        * (2 * ‖(K *ᵥ u) x‖ ^ 2 + 2 * (e ^ 2 * ‖u x‖ ^ 2)) :=
        mul_le_mul (mul_le_mul hb2 le_rfl (sq_nonneg _) (pow_nonneg hQ 2))
          hWnorm (sq_nonneg _) (mul_nonneg (pow_nonneg hQ 2) (sq_nonneg _))
    _ = 2 * Q ^ 2 * (‖K i x‖ ^ 2 * ‖(K *ᵥ u) x‖ ^ 2)
        + 2 * Q ^ 2 * e ^ 2 * (‖K i x‖ ^ 2 * ‖u x‖ ^ 2) := by ring

/-- `l2sq` is nonnegative. -/
theorem l2sq_nonneg {P 𝕜 : Type*} [Fintype P] [RCLike 𝕜] (f : P → 𝕜) :
    0 ≤ l2sq f := by
  unfold l2sq
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Triangle-splitting for `l2sq` over `ℂ`. -/
theorem l2sq_add_le {P : Type*} [Fintype P] (f g : P → ℂ) :
    l2sq (f + g) ≤ 2 * l2sq f + 2 * l2sq g := by
  simp only [l2sq, Pi.add_apply]
  calc ∑ i, ‖f i + g i‖ ^ 2
      ≤ ∑ i, (2 * ‖f i‖ ^ 2 + 2 * ‖g i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => complex_norm_add_sq_le _ _
    _ = 2 * (∑ i, ‖f i‖ ^ 2) + 2 * (∑ i, ‖g i‖ ^ 2) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- The padded increment vanishes at its pivot row. -/
theorem Jmodel_pivot_zero {P : Type*} [Fintype P] [DecidableEq P]
    (h : CMat P) (x : P) (a b : ℂ) (u : P → ℂ) :
    ((Jmodel h x a b) *ᵥ u) x = 0 := by
  show (∑ j, Jmodel h x a b x j * u j) = 0
  apply Finset.sum_eq_zero
  intro j _
  simp [Jmodel]

/-- The model splits into linear and quadratic parts. -/
theorem Jmodel_split {P : Type*} [DecidableEq P]
    (h : CMat P) (x : P) (a b : ℂ) :
    Jmodel h x a b = Jmodel h x a 0 + Jmodel h x 0 b := by
  rw [Jmodel_decompose h x a b, Jmodel_decompose h x a 0,
    Jmodel_decompose h x 0 b]
  simp

/-- Reshuffling of double sums with constant factors (opaque summands). -/
theorem sum_reshuffle4 {P Q : Type*} (S : Finset P) (T : Finset Q)
    (a b c d : P → Q → ℝ) :
    (∑ x ∈ S, (2 * (∑ i ∈ T, (a x i + b x i))
      + 2 * (∑ i ∈ T, (c x i + d x i))))
    = ((2 * (∑ x ∈ S, ∑ i ∈ T, a x i) + 2 * (∑ x ∈ S, ∑ i ∈ T, b x i))
      + (2 * (∑ x ∈ S, ∑ i ∈ T, c x i) + 2 * (∑ x ∈ S, ∑ i ∈ T, d x i))) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]

/-- Single (non-adjoint) square stack for the J increment. -/
theorem J_stack_one : ∀ (C : ℝ), 1 ≤ C → ∃ C₁ > 0, ∃ t0 > 0,
    ∀ (P : Type) [Fintype P] [DecidableEq P] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S : Finset P) (z : P → ℝ) (u : P → ℂ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) →
    (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u))
      ≤ C₁ * power t (AndersonAC.S45.delta / 2) * l2sq u := by
  intro C hC
  have hAnalytic : analyticPrestateHypothesis := analytic_prestate_proof
  obtain ⟨A, hApos, tA, htA, hFacts⟩ := analyticPrestate_any C hC
  obtain ⟨G, hGpos, tG, htG, hGamma⟩ :=
    gamma_norm_bound_any_of_analyticPrestate hAnalytic C hC
  refine ⟨32 * G ^ 2 * A ^ 2 + 4 * (G ^ 2 + 2) ^ 2 * A ^ 2
    + 4 * (G ^ 2 + 2) ^ 2 * A ^ 4, by positivity,
    min tA (min tG (min 1 (1 / (2 * (A ^ 2 + 1))))),
    lt_min htA (lt_min htG (lt_min one_pos (by positivity))), ?_⟩
  intro P instFP instDP t s Λplus Wstar S z u htt hs hz
  classical
  have httA : t < tA := lt_of_lt_of_le htt (min_le_left _ _)
  have httG : t < tG :=
    lt_of_lt_of_le htt (le_trans (min_le_right _ _) (min_le_left _ _))
  have htt1 : t < 1 :=
    lt_of_lt_of_le htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have httK : t < 1 / (2 * (A ^ 2 + 1)) :=
    lt_of_lt_of_le htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_right _ _)))
  have ht : 0 < t := hs.scale.1
  have ht1 : t ≤ 1 := htt1.le
  have hsqrt_nn : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hf := hFacts P t s Λplus Wstar httA hs
  have hrow : ∀ r, (∑ j, s.F t r j) ≤ A := fun r => (hf.1 r).2.2.1
  have hdiag : ∀ x, ‖s.h t x x‖ ≤ A * Real.sqrt t := fun x => (hf.1 x).2.2.2
  have hT : ∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2
      ≤ A * power t (AndersonAC.S45.delta / 2) := hf.2.1
  have hF2 : ∀ a b, ‖s.h t a b‖ ^ 2 = s.F t a b := by
    intro a b
    simp only [State.F, entryAbsSquare]
  have hFsymm : ∀ a b, s.F t a b = s.F t b a := by
    intro a b
    simp only [State.F, entryAbsSquare]
    rw [State_h_symm s t hs.symmetric a b]
  have hrow2 : ∀ r, (∑ j, ‖s.h t r j‖ ^ 2) ≤ A := by
    intro r
    calc ∑ j, ‖s.h t r j‖ ^ 2 = ∑ j, s.F t r j :=
          Finset.sum_congr rfl fun j _ => hF2 r j
      _ ≤ A := hrow r
  have hF4col : ∀ x, (∑ i, s.F t i x ^ 2) ≤ rowCap t := by
    intro x
    calc ∑ i, s.F t i x ^ 2 = ∑ i, ‖s.h t i x‖ ^ 4 := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [← hF2 i x]
            ring
      _ = ∑ i, ‖s.h t x i‖ ^ 4 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← State_h_symm s t hs.symmetric i x]
      _ ≤ rowCap t := by
            simpa [State.fourthRow] using hs.row_cap x
  have hopK : ‖s.K t‖ ≤ A := by
    apply matrix_symmetric_row_bound _ _ hApos.le
    · intro i j
      simp only [State_K_norm]
      simp only [State.F, entryAbsSquare]
      rw [State_h_symm s t hs.symmetric i j]
    · intro i
      calc ∑ j, ‖s.K t i j‖ = ∑ j, s.F t i j :=
            Finset.sum_congr rfl fun j _ => State_K_norm s t i j
        _ ≤ A := hrow i
  have hKxx : ∀ x, ‖s.K t x x‖ ≤ A ^ 2 * t := by
    intro x
    calc ‖s.K t x x‖ = ‖s.h t x x‖ ^ 2 := by
            rw [State_K_norm]; simp [State.F, entryAbsSquare]
      _ ≤ (A * Real.sqrt t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdiag x) 2
      _ = A ^ 2 * t := by rw [mul_pow, Real.sq_sqrt ht.le]
  have hden : 0 < 2 * (A ^ 2 + 1) := by positivity
  have hKsmall : ∀ x, ‖s.K t x x‖ ≤ 1 / 2 := by
    intro x
    have h2 : A ^ 2 * t ≤ A ^ 2 * (1 / (2 * (A ^ 2 + 1))) :=
      mul_le_mul_of_nonneg_left httK.le (sq_nonneg A)
    have h3 : A ^ 2 * (1 / (2 * (A ^ 2 + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hden]
      nlinarith [sq_nonneg A]
    linarith [hKxx x]
  have hKne : ∀ x, (1 : ℂ) - s.K t x x ≠ 0 := by
    intro x hcon
    have heq : s.K t x x = 1 := by
      have h := eq_of_sub_eq_zero hcon
      simpa using h.symm
    have h1 : ‖s.K t x x‖ = 1 := by rw [heq, norm_one]
    linarith [hKsmall x]
  have hKinv : ∀ x, ‖((1 - s.K t x x)⁻¹ : ℂ)‖ ≤ 2 := by
    intro x
    have hdenx : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - s.K t x x‖ := by
      have htri : ‖(1 : ℂ)‖
          ≤ ‖(1 : ℂ) - s.K t x x‖ + ‖s.K t x x‖ := by
        calc ‖(1 : ℂ)‖ = ‖((1 : ℂ) - s.K t x x) + s.K t x x‖ := by
                congr 1
                abel
          _ ≤ _ := norm_add_le _ _
      simp only [norm_one] at htri
      linarith [hKsmall x]
    have hpos1 : 0 < ‖(1 : ℂ) - s.K t x x‖ :=
      lt_of_lt_of_le (by norm_num) hdenx
    calc ‖((1 - s.K t x x)⁻¹ : ℂ)‖ = (‖(1 : ℂ) - s.K t x x‖)⁻¹ := norm_inv _
      _ = 1 / ‖(1 : ℂ) - s.K t x x‖ := (one_div _).symm
      _ ≤ 2 := by
        rw [div_le_iff₀ hpos1]
        linarith [hdenx]
  have hKinv : ∀ x, ‖((1 - s.K t x x)⁻¹ : ℂ)‖ ≤ 2 := by
    intro x
    have hdenx : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - s.K t x x‖ := by
      have htri : ‖(1 : ℂ)‖
          ≤ ‖(1 : ℂ) - s.K t x x‖ + ‖s.K t x x‖ := by
        calc ‖(1 : ℂ)‖ = ‖((1 : ℂ) - s.K t x x) + s.K t x x‖ := by
                congr 1
                abel
          _ ≤ _ := norm_add_le _ _
      simp only [norm_one] at htri
      linarith [hKsmall x]
    have hpos1 : 0 < ‖(1 : ℂ) - s.K t x x‖ :=
      lt_of_lt_of_le (by norm_num) hdenx
    calc ‖((1 - s.K t x x)⁻¹ : ℂ)‖ = (‖(1 : ℂ) - s.K t x x‖)⁻¹ := norm_inv _
      _ = 1 / ‖(1 : ℂ) - s.K t x x‖ := (one_div _).symm
      _ ≤ 2 := by
        rw [div_le_iff₀ hpos1]
        linarith [hdenx]
  have hGbound : ∀ x ∈ S, ‖gamma t s x (z x)‖ ≤ G := by
    intro x hx
    exact hGamma P t s Λplus Wstar x (z x) httG hs (hz x hx)
  have hcol : ∀ j, (∑ i, s.F t i j) ≤ A := by
    intro j
    calc ∑ i, s.F t i j = ∑ i, s.F t j i :=
          Finset.sum_congr rfl fun i _ => hFsymm i j
      _ ≤ A := hrow j
  have hpow_nn' : 0 ≤ power t (AndersonAC.S45.delta / 2) :=
    (Real.rpow_pos_of_pos ht _).le
  have hpow_le1 : power t (1 + AndersonAC.S45.delta)
      ≤ power t (AndersonAC.S45.delta / 2) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1
      (by norm_num [AndersonAC.S45.delta])
  have hpow_le2 : power t (2 + AndersonAC.S45.delta)
      ≤ power t (AndersonAC.S45.delta / 2) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1
      (by norm_num [AndersonAC.S45.delta])
  have hpow_le3 : power t (3 + AndersonAC.S45.delta)
      ≤ power t (AndersonAC.S45.delta / 2) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1
      (by norm_num [AndersonAC.S45.delta])
  have hrc : rowCap t = power t (1 + AndersonAC.S45.delta) := rfl
  -- per-pivot coefficient bounds
  have ha_bound : ∀ x ∈ S, ‖(-2 * gamma t s x (z x) : ℂ)‖ ≤ 2 * G := by
    intro x hx
    have hγ := hGbound x hx
    have hn2 : ‖(-2 : ℂ)‖ = 2 := by
      simp only [show (-2 : ℂ) = -(2 : ℂ) by ring, norm_neg, RCLike.norm_ofNat]
    calc ‖(-2 * gamma t s x (z x) : ℂ)‖
        = ‖(-2 : ℂ)‖ * ‖gamma t s x (z x)‖ := norm_mul _ _
      _ = 2 * ‖gamma t s x (z x)‖ := by rw [hn2]
      _ ≤ 2 * G := mul_le_mul_of_nonneg_left hγ (by norm_num)
  have hb_bound : ∀ x ∈ S,
      ‖(gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹ : ℂ)‖ ≤ G ^ 2 + 2 := by
    intro x hx
    have hγ := hGbound x hx
    have h1 : ‖gamma t s x (z x) ^ 2‖ ≤ G ^ 2 :=
      calc ‖gamma t s x (z x) ^ 2‖ = ‖gamma t s x (z x)‖ ^ 2 := norm_pow _ _
        _ ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hγ 2
    calc ‖gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹‖
        ≤ ‖gamma t s x (z x) ^ 2‖ + ‖((1 - s.K t x x)⁻¹ : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ G ^ 2 + 2 := add_le_add h1 (hKinv x)
  have hKeq : ∀ p q, s.K t p q = s.h t p q ^ 2 := fun p q => rfl
  -- row operator bound applied to each output row
  have hdouble : (∑ i, ∑ j, s.F t i j * ‖u j‖ ^ 2) ≤ A * l2sq u := by
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, s.F t i j * ‖u j‖ ^ 2
        = ∑ j, (∑ i, s.F t i j) * ‖u j‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
      _ ≤ ∑ j, A * ‖u j‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
      _ = A * l2sq u := by
          simp only [l2sq, ← Finset.mul_sum]
  -- row sum with the analytic operator bound, in sum form
  have hWopS : ∀ i, (∑ x ∈ S, ‖s.h t i x‖ ^ 2
      * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2)
      ≤ (A * power t (AndersonAC.S45.delta / 2))
        * (∑ j, s.F t i j * ‖u j‖ ^ 2) := by
    intro i
    have hMW : ((diagonal (s.h t i) * s.h t)
        *ᵥ (fun j => s.h t i j * u j))
        = fun x => s.h t i x * ((s.h t *ᵥ (fun j => s.h t i j * u j)) x) := by
      rw [← Matrix.mulVec_mulVec]
      funext x
      exact Matrix.mulVec_diagonal _ _ _
    have hvF : l2sq (fun j => s.h t i j * u j)
        = ∑ j, s.F t i j * ‖u j‖ ^ 2 := by
      simp only [l2sq, norm_mul, mul_pow, hF2]
    have hinner : l2sq (fun x => s.h t i x
        * ((s.h t *ᵥ (fun j => s.h t i j * u j)) x))
        = ∑ x, ‖s.h t i x‖ ^ 2
          * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2 := by
      simp only [l2sq, norm_mul, mul_pow]
    calc ∑ x ∈ S, ‖s.h t i x‖ ^ 2
          * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2
        ≤ l2sq (fun x => s.h t i x
          * ((s.h t *ᵥ (fun j => s.h t i j * u j)) x)) := by
          rw [hinner]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun x _ _ => by positivity)
      _ = l2sq (((diagonal (s.h t i) * s.h t))
          *ᵥ (fun j => s.h t i j * u j)) := by rw [hMW]
      _ ≤ ‖diagonal (s.h t i) * s.h t‖ ^ 2
          * l2sq (fun j => s.h t i j * u j) :=
          l2sq_mulVec_le_opNorm_sq _ _
      _ ≤ (A * power t (AndersonAC.S45.delta / 2))
          * (∑ j, s.F t i j * ‖u j‖ ^ 2) := by
        rw [hvF]
        exact mul_le_mul (hT i) le_rfl
          (Finset.sum_nonneg fun j _ =>
            mul_nonneg (State_F_nonneg s t _ _) (sq_nonneg _))
          (mul_nonneg hApos.le hpow_nn')
  -- the four double sums
  have hS1 : 2 * (∑ x ∈ S, ∑ i, 2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
      * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2))
      ≤ (16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2) * l2sq u := by
    rw [Finset.sum_comm]
    have hrow1 : ∀ i, (∑ x ∈ S, 2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
        * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2))
        ≤ (2 * (2 * G) ^ 2)
          * ((A * power t (AndersonAC.S45.delta / 2))
            * (∑ j, s.F t i j * ‖u j‖ ^ 2)) := by
      intro i
      calc ∑ x ∈ S, 2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
            * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2)
          = 2 * (2 * G) ^ 2 * ∑ x ∈ S, (‖s.h t i x‖ ^ 2
            * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2) := by
            rw [Finset.mul_sum]
        _ ≤ 2 * (2 * G) ^ 2 * ((A * power t (AndersonAC.S45.delta / 2))
            * (∑ j, s.F t i j * ‖u j‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (hWopS i) (by positivity)
    calc 2 * (∑ i, ∑ x ∈ S, 2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
          * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2))
        ≤ 2 * (∑ i, (2 * (2 * G) ^ 2)
          * ((A * power t (AndersonAC.S45.delta / 2))
            * (∑ j, s.F t i j * ‖u j‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i _ => hrow1 i) (by norm_num)
      _ = 2 * ((2 * (2 * G) ^ 2) * ((A * power t (AndersonAC.S45.delta / 2))
          * (∑ i, ∑ j, s.F t i j * ‖u j‖ ^ 2))) := by
          simp only [← Finset.mul_sum]
      _ ≤ 2 * ((2 * (2 * G) ^ 2) * ((A * power t (AndersonAC.S45.delta / 2))
          * (A * l2sq u))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hdouble (by positivity))
              (by positivity)) (by norm_num)
      _ = (16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2) * l2sq u := by
          ring
  -- per-pivot l2sq bound
  have hper : ∀ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u)
      ≤ 2 * (∑ i, (2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
          * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2)
        + 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
          * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2)))
      + 2 * (∑ i, (2 * (G ^ 2 + 2) ^ 2 * ((‖s.K t i x‖ ^ 2)
          * ‖(s.K t *ᵥ u) x‖ ^ 2)
        + 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
          * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2))) := by
    intro x hx
    have hsplitM : Jinc t s x (z x)
        = Jmodel (s.h t) x (-2 * gamma t s x (z x)) 0
        + Jmodel (s.h t) x 0
          (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹) := by
      rw [Jinc_eq_model]
      exact Jmodel_split _ _ _ _
    have hsplitV : (Jinc t s x (z x) *ᵥ u)
        = ((Jmodel (s.h t) x (-2 * gamma t s x (z x)) 0) *ᵥ u)
        + ((Jmodel (s.h t) x 0
          (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹)) *ᵥ u) := by
      rw [hsplitM, Matrix.add_mulVec]
    have hL : l2sq ((Jmodel (s.h t) x (-2 * gamma t s x (z x)) 0) *ᵥ u)
        ≤ ∑ i, (2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
          * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2)
        + 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
          * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2)) := by
      have hx0 := Jmodel_pivot_zero (s.h t) x (-2 * gamma t s x (z x)) 0 u
      have hsum : l2sq ((Jmodel (s.h t) x (-2 * gamma t s x (z x)) 0) *ᵥ u)
          = ∑ i ∈ Finset.univ.erase x,
            ‖((Jmodel (s.h t) x (-2 * gamma t s x (z x)) 0) *ᵥ u) i‖ ^ 2 := by
        simp only [l2sq]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hx0]
        simp
      rw [hsum]
      calc ∑ i ∈ Finset.univ.erase x,
            ‖((Jmodel (s.h t) x (-2 * gamma t s x (z x)) 0) *ᵥ u) i‖ ^ 2
          ≤ ∑ i ∈ Finset.univ.erase x, (2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
            * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2)
          + 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
            * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact Jlin_cell_bound (s.h t) x i (-2 * gamma t s x (z x)) u
              (2 * G) (A * Real.sqrt t) (by positivity) (ha_bound x hx)
              (hdiag x) (Finset.ne_of_mem_erase hi)
        _ ≤ ∑ i, (2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
            * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2)
          + 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
            * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.erase_subset x Finset.univ) (fun i _ _ => by positivity)
    have hQ : l2sq ((Jmodel (s.h t) x 0
        (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹)) *ᵥ u)
        ≤ ∑ i, (2 * (G ^ 2 + 2) ^ 2 * ((‖s.K t i x‖ ^ 2)
          * ‖(s.K t *ᵥ u) x‖ ^ 2)
        + 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
          * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2)) := by
      have hx0 := Jmodel_pivot_zero (s.h t) x 0
        (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹) u
      have hsum : l2sq ((Jmodel (s.h t) x 0
          (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹)) *ᵥ u)
          = ∑ i ∈ Finset.univ.erase x,
            ‖((Jmodel (s.h t) x 0
              (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹)) *ᵥ u) i‖ ^ 2 := by
        simp only [l2sq]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hx0]
        simp
      rw [hsum]
      calc ∑ i ∈ Finset.univ.erase x,
            ‖((Jmodel (s.h t) x 0
              (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹)) *ᵥ u) i‖ ^ 2
          ≤ ∑ i ∈ Finset.univ.erase x, (2 * (G ^ 2 + 2) ^ 2
            * ((‖s.K t i x‖ ^ 2) * ‖(s.K t *ᵥ u) x‖ ^ 2)
          + 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
            * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact Jquad_cell_bound (s.h t) (s.K t) x i
              (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹) u
              (G ^ 2 + 2) (A ^ 2 * t) (by positivity) (hb_bound x hx)
              hKeq (hKxx x) (Finset.ne_of_mem_erase hi)
        _ ≤ ∑ i, (2 * (G ^ 2 + 2) ^ 2 * ((‖s.K t i x‖ ^ 2)
            * ‖(s.K t *ᵥ u) x‖ ^ 2)
          + 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
            * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.erase_subset x Finset.univ) (fun i _ _ => by positivity)
    calc l2sq (Jinc t s x (z x) *ᵥ u)
        ≤ 2 * l2sq ((Jmodel (s.h t) x (-2 * gamma t s x (z x)) 0) *ᵥ u)
        + 2 * l2sq ((Jmodel (s.h t) x 0
          (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹)) *ᵥ u) := by
          rw [hsplitV]
          exact l2sq_add_le _ _
      _ ≤ 2 * (∑ i, (2 * (2 * G) ^ 2 * (‖s.h t i x‖ ^ 2
          * ‖(s.h t *ᵥ fun j => s.h t i j * u j) x‖ ^ 2)
        + 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
          * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2)))
      + 2 * (∑ i, (2 * (G ^ 2 + 2) ^ 2 * ((‖s.K t i x‖ ^ 2)
          * ‖(s.K t *ᵥ u) x‖ ^ 2)
        + 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
          * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2))) :=
          add_le_add (mul_le_mul_of_nonneg_left hL (by norm_num))
            (mul_le_mul_of_nonneg_left hQ (by norm_num))
  have hN2F : ∀ x, (∑ i, ((‖s.h t i x‖ ^ 2) ^ 2)) = ∑ i, s.F t i x ^ 2 :=
    fun x => Finset.sum_congr rfl fun i _ => by rw [hF2 i x]
  have hK2F : ∀ x, (∑ i, ‖s.K t i x‖ ^ 2) = ∑ i, s.F t i x ^ 2 :=
    fun x => Finset.sum_congr rfl fun i _ => by rw [State_K_norm]
  have hS2 : 2 * (∑ x ∈ S, ∑ i, 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
      * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2))
      ≤ (16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2) * l2sq u := by
    have hinner2 : ∀ x ∈ S, (∑ i, 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
        * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2))
        ≤ (2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2)
          * ((∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2) := by
      intro x hx
      apply le_of_eq
      calc ∑ i, 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
            * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2)
          = 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
            * ((∑ i, ((‖s.h t i x‖ ^ 2) ^ 2)) * ‖u x‖ ^ 2) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
        _ = 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
            * ((∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2) := by rw [hN2F x]
    have hdH : (A * Real.sqrt t) ^ 2 * rowCap t
        ≤ A ^ 2 * power t (AndersonAC.S45.delta / 2) := by
      have e1 : (A * Real.sqrt t) ^ 2 * rowCap t
          = A ^ 2 * power t (2 + AndersonAC.S45.delta) := by
        have hsq : (A * Real.sqrt t) ^ 2 = A ^ 2 * t := by
          rw [mul_pow, Real.sq_sqrt ht.le]
        rw [hsq, hrc]
        dsimp [power]
        calc A ^ 2 * t * t ^ (1 + AndersonAC.S45.delta)
            = A ^ 2 * (t ^ (1 : ℝ) * t ^ (1 + AndersonAC.S45.delta)) := by
              rw [Real.rpow_one]; ring
          _ = A ^ 2 * t ^ ((1 : ℝ) + (1 + AndersonAC.S45.delta)) := by
              rw [← Real.rpow_add ht]
          _ = A ^ 2 * t ^ (2 + AndersonAC.S45.delta) := by
              have hexp : (1 : ℝ) + (1 + AndersonAC.S45.delta)
                = 2 + AndersonAC.S45.delta := by ring
              rw [hexp]
      calc (A * Real.sqrt t) ^ 2 * rowCap t
          = A ^ 2 * power t (2 + AndersonAC.S45.delta) := e1
        _ ≤ A ^ 2 * power t (AndersonAC.S45.delta / 2) :=
          mul_le_mul_of_nonneg_left hpow_le2 (sq_nonneg A)
    calc 2 * (∑ x ∈ S, ∑ i, 2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2
          * (((‖s.h t i x‖ ^ 2) ^ 2) * ‖u x‖ ^ 2))
        ≤ 2 * (∑ x ∈ S, (2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2)
          * ((∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun x hx => hinner2 x hx) (by norm_num)
      _ = 2 * ((2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2)
          * (∑ x ∈ S, ((∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2))) := by
          simp only [← Finset.mul_sum]
      _ ≤ 2 * ((2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2)
          * (rowCap t * l2sq u)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ x ∈ S, (∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2
              ≤ ∑ x ∈ S, rowCap t * ‖u x‖ ^ 2 :=
                Finset.sum_le_sum fun x hx =>
                  mul_le_mul_of_nonneg_right (hF4col x) (sq_nonneg _)
            _ = rowCap t * ∑ x ∈ S, ‖u x‖ ^ 2 := by
                simp only [← Finset.mul_sum]
            _ ≤ rowCap t * l2sq u := by
              have heq : l2sq u = ∑ x, ‖u x‖ ^ 2 := rfl
              rw [heq]
              exact mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
                  (fun x _ _ => sq_nonneg _))
                (Real.rpow_pos_of_pos ht _).le
      _ ≤ (16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2) * l2sq u := by
          have e2 : 2 * (2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2) * rowCap t
              = (16 * G ^ 2) * ((A * Real.sqrt t) ^ 2 * rowCap t) := by ring
          calc 2 * ((2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2)
              * (rowCap t * l2sq u))
              = (2 * (2 * (2 * G) ^ 2 * (A * Real.sqrt t) ^ 2) * rowCap t)
                * l2sq u := by ring
            _ = ((16 * G ^ 2) * ((A * Real.sqrt t) ^ 2 * rowCap t)) * l2sq u := by
                rw [e2]
            _ ≤ ((16 * G ^ 2) * (A ^ 2 * power t (AndersonAC.S45.delta / 2)))
                * l2sq u :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hdH (by positivity))
                  (l2sq_nonneg u)
            _ = (16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2)
                * l2sq u := by ring
  have hS3 : 2 * (∑ x ∈ S, ∑ i, 2 * (G ^ 2 + 2) ^ 2 * ((‖s.K t i x‖ ^ 2)
      * ‖(s.K t *ᵥ u) x‖ ^ 2))
      ≤ (4 * (G ^ 2 + 2) ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2)
        * l2sq u := by
    have hinner3 : ∀ x ∈ S, (∑ i, 2 * (G ^ 2 + 2) ^ 2 * ((‖s.K t i x‖ ^ 2)
        * ‖(s.K t *ᵥ u) x‖ ^ 2))
        ≤ (2 * (G ^ 2 + 2) ^ 2)
          * ((∑ i, s.F t i x ^ 2) * ‖(s.K t *ᵥ u) x‖ ^ 2) := by
      intro x hx
      apply le_of_eq
      calc ∑ i, 2 * (G ^ 2 + 2) ^ 2 * ((‖s.K t i x‖ ^ 2)
            * ‖(s.K t *ᵥ u) x‖ ^ 2)
          = 2 * (G ^ 2 + 2) ^ 2 * ((∑ i, ‖s.K t i x‖ ^ 2)
            * ‖(s.K t *ᵥ u) x‖ ^ 2) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
        _ = 2 * (G ^ 2 + 2) ^ 2 * ((∑ i, s.F t i x ^ 2)
            * ‖(s.K t *ᵥ u) x‖ ^ 2) := by rw [hK2F x]
    have hKu : l2sq (s.K t *ᵥ u) ≤ A ^ 2 * l2sq u := by
      calc l2sq (s.K t *ᵥ u) ≤ ‖s.K t‖ ^ 2 * l2sq u :=
            l2sq_mulVec_le_opNorm_sq _ _
        _ ≤ A ^ 2 * l2sq u :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hopK 2) (l2sq_nonneg u)
    calc 2 * (∑ x ∈ S, ∑ i, 2 * (G ^ 2 + 2) ^ 2 * ((‖s.K t i x‖ ^ 2)
          * ‖(s.K t *ᵥ u) x‖ ^ 2))
        ≤ 2 * (∑ x ∈ S, (2 * (G ^ 2 + 2) ^ 2)
          * ((∑ i, s.F t i x ^ 2) * ‖(s.K t *ᵥ u) x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun x hx => hinner3 x hx) (by norm_num)
      _ = 2 * ((2 * (G ^ 2 + 2) ^ 2)
          * (∑ x ∈ S, ((∑ i, s.F t i x ^ 2) * ‖(s.K t *ᵥ u) x‖ ^ 2))) := by
          simp only [← Finset.mul_sum]
      _ ≤ 2 * ((2 * (G ^ 2 + 2) ^ 2) * (rowCap t * l2sq (s.K t *ᵥ u))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ x ∈ S, (∑ i, s.F t i x ^ 2) * ‖(s.K t *ᵥ u) x‖ ^ 2
              ≤ ∑ x ∈ S, rowCap t * ‖(s.K t *ᵥ u) x‖ ^ 2 :=
                Finset.sum_le_sum fun x hx =>
                  mul_le_mul_of_nonneg_right (hF4col x) (sq_nonneg _)
            _ = rowCap t * ∑ x ∈ S, ‖(s.K t *ᵥ u) x‖ ^ 2 := by
                simp only [← Finset.mul_sum]
            _ ≤ rowCap t * l2sq (s.K t *ᵥ u) := by
              have heq : l2sq (s.K t *ᵥ u) = ∑ x, ‖(s.K t *ᵥ u) x‖ ^ 2 := rfl
              rw [heq]
              exact mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
                  (fun x _ _ => sq_nonneg _))
                (Real.rpow_pos_of_pos ht _).le
      _ ≤ 2 * ((2 * (G ^ 2 + 2) ^ 2) * (rowCap t * (A ^ 2 * l2sq u))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hKu
            (Real.rpow_pos_of_pos ht _).le
      _ ≤ (4 * (G ^ 2 + 2) ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2)
          * l2sq u := by
          have hHle : rowCap t ≤ power t (AndersonAC.S45.delta / 2) := by
            rw [hrc]; exact hpow_le1
          calc 2 * ((2 * (G ^ 2 + 2) ^ 2) * (rowCap t * (A ^ 2 * l2sq u)))
              = (4 * (G ^ 2 + 2) ^ 2 * A ^ 2) * (rowCap t * l2sq u) := by ring
            _ ≤ (4 * (G ^ 2 + 2) ^ 2 * A ^ 2)
                * (power t (AndersonAC.S45.delta / 2) * l2sq u) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hHle (l2sq_nonneg u)) (by positivity)
            _ = (4 * (G ^ 2 + 2) ^ 2 * A ^ 2)
                * power t (AndersonAC.S45.delta / 2) * l2sq u := by ring
  have hHnn : 0 ≤ rowCap t := (Real.rpow_pos_of_pos ht _).le
  have heH : (A ^ 2 * t) ^ 2 * rowCap t
      ≤ A ^ 4 * power t (AndersonAC.S45.delta / 2) := by
    have ht2 : t ^ 2 ≤ (1 : ℝ) := by
      calc t ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ ht.le ht1 2
        _ = 1 := one_pow 2
    calc (A ^ 2 * t) ^ 2 * rowCap t = (A ^ 4 * t ^ 2) * rowCap t := by ring
      _ ≤ (A ^ 4 * 1) * rowCap t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht2 (pow_nonneg hApos.le 4)) hHnn
      _ = A ^ 4 * rowCap t := by ring
      _ ≤ A ^ 4 * power t (AndersonAC.S45.delta / 2) := by
        rw [hrc]
        exact mul_le_mul_of_nonneg_left hpow_le1 (pow_nonneg hApos.le 4)
  have hS4 : 2 * (∑ x ∈ S, ∑ i, 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
      * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2))
      ≤ (4 * (G ^ 2 + 2) ^ 2 * A ^ 4) * power t (AndersonAC.S45.delta / 2)
        * l2sq u := by
    have hinner4 : ∀ x ∈ S, (∑ i, 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
        * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2))
        ≤ (2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2)
          * ((∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2) := by
      intro x hx
      apply le_of_eq
      calc ∑ i, 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
            * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2)
          = 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
            * ((∑ i, ‖s.K t i x‖ ^ 2) * ‖u x‖ ^ 2) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
        _ = 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
            * ((∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2) := by rw [hK2F x]
    calc 2 * (∑ x ∈ S, ∑ i, 2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2
          * (((‖s.K t i x‖ ^ 2)) * ‖u x‖ ^ 2))
        ≤ 2 * (∑ x ∈ S, (2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2)
          * ((∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun x hx => hinner4 x hx) (by norm_num)
      _ = 2 * ((2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2)
          * (∑ x ∈ S, ((∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2))) := by
          simp only [← Finset.mul_sum]
      _ ≤ 2 * ((2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2)
          * (rowCap t * l2sq u)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ x ∈ S, (∑ i, s.F t i x ^ 2) * ‖u x‖ ^ 2
              ≤ ∑ x ∈ S, rowCap t * ‖u x‖ ^ 2 :=
                Finset.sum_le_sum fun x hx =>
                  mul_le_mul_of_nonneg_right (hF4col x) (sq_nonneg _)
            _ = rowCap t * ∑ x ∈ S, ‖u x‖ ^ 2 := by
                simp only [← Finset.mul_sum]
            _ ≤ rowCap t * l2sq u := by
              have heq : l2sq u = ∑ x, ‖u x‖ ^ 2 := rfl
              rw [heq]
              exact mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
                  (fun x _ _ => sq_nonneg _)) hHnn
      _ ≤ (4 * (G ^ 2 + 2) ^ 2 * A ^ 4) * power t (AndersonAC.S45.delta / 2)
          * l2sq u := by
          calc 2 * ((2 * (G ^ 2 + 2) ^ 2 * (A ^ 2 * t) ^ 2)
              * (rowCap t * l2sq u))
              = (4 * (G ^ 2 + 2) ^ 2 * ((A ^ 2 * t) ^ 2 * rowCap t))
                * l2sq u := by ring
            _ ≤ (4 * (G ^ 2 + 2) ^ 2 * (A ^ 4 * power t (AndersonAC.S45.delta / 2)))
                * l2sq u :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left heH (by positivity)) (l2sq_nonneg u)
            _ = (4 * (G ^ 2 + 2) ^ 2 * A ^ 4)
                * power t (AndersonAC.S45.delta / 2) * l2sq u := by ring
  -- join the four double sums
  have hsum : (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u))
      ≤ (((16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2) * l2sq u
        + (16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2) * l2sq u)
      + (((4 * (G ^ 2 + 2) ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2)
          * l2sq u)
        + (4 * (G ^ 2 + 2) ^ 2 * A ^ 4) * power t (AndersonAC.S45.delta / 2)
          * l2sq u)) := by
    calc ∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u)
        ≤ _ := Finset.sum_le_sum fun x hx => hper x hx
      _ = _ := sum_reshuffle4 _ _ _ _ _ _
      _ ≤ _ := add_le_add (add_le_add hS1 hS2) (add_le_add hS3 hS4)
  calc (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u))
      ≤ (((16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2) * l2sq u
        + (16 * G ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2) * l2sq u)
      + (((4 * (G ^ 2 + 2) ^ 2 * A ^ 2) * power t (AndersonAC.S45.delta / 2)
          * l2sq u)
        + (4 * (G ^ 2 + 2) ^ 2 * A ^ 4) * power t (AndersonAC.S45.delta / 2)
          * l2sq u)) := hsum
    _ = (32 * G ^ 2 * A ^ 2 + 4 * (G ^ 2 + 2) ^ 2 * A ^ 2
        + 4 * (G ^ 2 + 2) ^ 2 * A ^ 4) * power t (AndersonAC.S45.delta / 2)
        * l2sq u := by ring

/-- Adjoint stack transfers to the conjugate vector by complex symmetry. -/
theorem Jmodel_adjoint_l2sq {P : Type*} [Fintype P] [DecidableEq P]
    (h : CMat P) (x : P) (a b : ℂ) (u : P → ℂ)
    (hsym : ∀ i j, h j i = h i j) :
    l2sq (((Jmodel h x a b)ᴴ) *ᵥ u)
      = l2sq ((Jmodel h x a b) *ᵥ (fun j => star (u j))) := by
  classical
  have hsymM : ∀ i j, (Jmodel h x a b) j i = (Jmodel h x a b) i j :=
    fun i j => Jmodel_apply_symm h x a b hsym i j
  have hnc : ∀ z : ℂ, ‖star z‖ = ‖z‖ := fun z => by simp
  have e : ∀ i, (((Jmodel h x a b)ᴴ) *ᵥ u) i
      = star (((Jmodel h x a b) *ᵥ (fun j => star (u j))) i) := by
    intro i
    show (∑ j, ((Jmodel h x a b)ᴴ) i j * u j)
      = star (∑ j, (Jmodel h x a b) i j * star (u j))
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.conjTranspose_apply, hsymM i j, star_mul, star_star,
      mul_comm]
  simp only [l2sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [e i, hnc]

/-- Full Lemma 4.4: mean plus both square stacks. -/
theorem J_bounds_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (n Ω : Type) [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State n)
    (Λplus Wstar : Form n) (S : Finset n) (ξ : n → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    ‖∑ x ∈ S, ∫ ω, Jinc t s x (ξ x ω) ∂μ‖
      ≤ C' * AndersonAC.S45.power t AndersonAC.S45.beta ∧
    (∀ z : n → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ u : n → ℂ,
      (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u)) +
      (∑ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u)) ≤
        C' * AndersonAC.S45.power t (AndersonAC.S45.delta / 2) * l2sq u) := by
  intro C hC
  obtain ⟨M1, hM1pos, tM, htM, hmean⟩ := J_bounds_mean C hC
  obtain ⟨C1, hC1pos, tS, htS, hstack⟩ := J_stack_one C hC
  have hmaxpos : 0 < max M1 C1 := lt_of_lt_of_le hM1pos (le_max_left _ _)
  refine ⟨2 * max M1 C1, mul_pos (by norm_num) hmaxpos,
    min tM tS, lt_min htM htS, ?_⟩
  intro n Ω instF instD instM μ instP t s Λplus Wstar S ξ htt hs hLaw
  classical
  have httM : t < tM := lt_of_lt_of_le htt (min_le_left _ _)
  have httS : t < tS := lt_of_lt_of_le htt (min_le_right _ _)
  have hpowB : 0 ≤ AndersonAC.S45.power t AndersonAC.S45.beta :=
    (Real.rpow_pos_of_pos hs.scale.1 _).le
  have hpowD : 0 ≤ AndersonAC.S45.power t (AndersonAC.S45.delta / 2) :=
    (Real.rpow_pos_of_pos hs.scale.1 _).le
  have hM1le : M1 ≤ 2 * max M1 C1 := by
    have h1 : M1 ≤ max M1 C1 := le_max_left _ _
    have h2 : 0 ≤ max M1 C1 := le_trans hM1pos.le h1
    linarith
  have hC1le : C1 + C1 ≤ 2 * max M1 C1 := by
    have h1 : C1 ≤ max M1 C1 := le_max_right _ _
    linarith
  constructor
  · calc ‖∑ x ∈ S, ∫ ω, Jinc t s x (ξ x ω) ∂μ‖
        ≤ M1 * AndersonAC.S45.power t AndersonAC.S45.beta :=
          hmean n Ω μ t s Λplus Wstar S ξ httM hs hLaw
      _ ≤ (2 * max M1 C1) * AndersonAC.S45.power t AndersonAC.S45.beta :=
          mul_le_mul_of_nonneg_right hM1le hpowB
  · intro z hz u
    have h1 : (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u))
        ≤ C1 * AndersonAC.S45.power t (AndersonAC.S45.delta / 2) * l2sq u :=
      hstack n t s Λplus Wstar S z u httS hs hz
    have hsymh : ∀ i j, s.h t j i = s.h t i j :=
      fun i j => State_h_symm s t hs.symmetric i j
    have hadj : ∀ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u)
        = l2sq (Jinc t s x (z x) *ᵥ (fun j => star (u j))) := by
      intro x hx
      have hJ : Jinc t s x (z x)
          = Jmodel (s.h t) x (-2 * gamma t s x (z x))
            (gamma t s x (z x) ^ 2 - (1 - s.K t x x)⁻¹) :=
        Jinc_eq_model t s x (z x)
      rw [hJ]
      exact Jmodel_adjoint_l2sq (s.h t) x _ _ _ hsymh
    have h2 : (∑ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u))
        ≤ C1 * AndersonAC.S45.power t (AndersonAC.S45.delta / 2) * l2sq u := by
      have hconj : l2sq (fun j => star (u j)) = l2sq u := by
        simp only [l2sq]
        apply Finset.sum_congr rfl
        intro j _
        have hnc : ‖star (u j)‖ = ‖u j‖ := by simp
        rw [hnc]
      calc ∑ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u)
          = ∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ (fun j => star (u j))) :=
            Finset.sum_congr rfl fun x hx => hadj x hx
        _ ≤ C1 * AndersonAC.S45.power t (AndersonAC.S45.delta / 2)
            * l2sq (fun j => star (u j)) :=
            hstack n t s Λplus Wstar S z (fun j => star (u j)) httS hs hz
        _ = C1 * AndersonAC.S45.power t (AndersonAC.S45.delta / 2) * l2sq u := by
            rw [hconj]
    calc (∑ x ∈ S, l2sq (Jinc t s x (z x) *ᵥ u)) +
        (∑ x ∈ S, l2sq ((Jinc t s x (z x))ᴴ *ᵥ u))
        ≤ C1 * AndersonAC.S45.power t (AndersonAC.S45.delta / 2) * l2sq u
        + C1 * AndersonAC.S45.power t (AndersonAC.S45.delta / 2) * l2sq u :=
          add_le_add h1 h2
      _ = (C1 + C1) * AndersonAC.S45.power t (AndersonAC.S45.delta / 2)
          * l2sq u := by ring
      _ ≤ (2 * max M1 C1) * AndersonAC.S45.power t (AndersonAC.S45.delta / 2)
          * l2sq u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC1le hpowD) (l2sq_nonneg u)

end AndersonAC.AgentS45
