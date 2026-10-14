import AndersonAC.AgentS78.Construction.ResetRowShell
import AndersonAC.AgentS78.Construction.StagePhaseRowInput
import AndersonAC.AgentS78.SweepJoin
import AndersonAC.AgentS78.ResetJoin
import AndersonAC.S45.LocalityProof

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

/-- The induced sup norm of a finite matrix is bounded by its maximum absolute row sum. -/
theorem rowNorm_mulVec_bound {n : ℕ} (A : AndersonAC.S45.CMat (Fin n))
    (v : Fin n → ℂ) :
    ‖A.mulVec v‖ ≤ AndersonAC.S45.rowNorm A * ‖v‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro i
  have hrow : AndersonAC.S45.l1 (A i) ≤ AndersonAC.S45.rowNorm A := by
    have h := norm_le_pi_norm (fun j => AndersonAC.S45.l1 (A j)) i
    have hnonneg : 0 ≤ AndersonAC.S45.l1 (A i) := by
      unfold AndersonAC.S45.l1
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at h
    simpa [AndersonAC.S45.rowNorm] using h
  calc
    ‖(A.mulVec v) i‖ = ‖∑ j, A i j * v j‖ := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
    _ = ∑ j, ‖A i j‖ * ‖v j‖ := by simp
    _ ≤ ∑ j, ‖A i j‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = AndersonAC.S45.l1 (A i) * ‖v‖ := by
      rw [← Finset.sum_mul]
      rfl
    _ ≤ AndersonAC.S45.rowNorm A * ‖v‖ :=
      mul_le_mul_of_nonneg_right hrow (norm_nonneg _)

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- The committed endpoint satisfies the inverse-row bound required by the reset. -/
theorem resetRow_proof (d : ℕ) (hd : 3 ≤ d) : ResetRowStatement d := by
  intro CA cA PA hCA hcA hPA
  obtain ⟨Csh, hCsh1, hShellAll⟩ := physicalShellBounds d
  let C : ℝ := max (max CA (4 / cA)) (max 4 Csh)
  have hCCA : CA ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hC4div : 4 / cA ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hC4 : 4 ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCsh : Csh ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hC1 : 1 ≤ C := le_trans (by norm_num) hC4
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC1
  have hCprod : 4 ≤ C * cA := by
    have h := (div_le_iff₀ hcA).mp hC4div
    nlinarith [h]
  have hRecip : 1 / C ≤ cA := by
    rw [div_le_iff₀ hCpos]
    nlinarith [hCprod]
  let β : ℝ := 0.36 * AndersonAC.S78.delta
  have hβ : 0 < β := by
    dsimp [β, AndersonAC.S78.delta]
    norm_num
  obtain ⟨Cout, hCout, cdec, hcdec, tInv, htInv, hinverse⟩ :=
    AndersonAC.AgentS45.inverse_row_proof d C (1 / 2 : ℝ) β
      hC1 (by norm_num) (by norm_num) hβ
  let t₀ : ℝ := min tInv (Real.exp (-1))
  have ht₀ : 0 < t₀ := by
    dsimp [t₀]
    exact lt_min htInv (Real.exp_pos _)
  refine ⟨2 * Cout, t₀, ht₀, ?_⟩
  intro m k t b r I hIC hIc hIP ht hKn hlag
  have htpos : 0 < t := I.positive.1
  have ht1 : t ≤ 1 := I.positive.2.1
  have htInv' : t < tInv := ht.trans_le (min_le_left _ _)
  have htExp : t < Real.exp (-1) := ht.trans_le (min_le_right _ _)
  have hexp1 : Real.exp 1 * t ≤ 1 := by
    calc
      Real.exp 1 * t ≤ Real.exp 1 * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left htExp.le (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have hlogArg : Real.exp 1 ≤ 1 / t := (le_div_iff₀ htpos).2 (by
    simpa [mul_comm] using hexp1)
  have hlog : 1 ≤ Real.log (1 / t) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log (1 / t) := Real.log_le_log (Real.exp_pos _) hlogArg
  have hlogF : AndersonAC.S45.logFactor t ≤ 2 * Real.log (1 / t) := by
    rw [AndersonAC.S45.logFactor]
    linarith
  have hlogF_nonneg : 0 ≤ AndersonAC.S45.logFactor t := by
    rw [AndersonAC.S45.logFactor]
    linarith
  let ep : Endpoint (Torus d m) := I.state (Fin.last k)
  let A : Finset (Torus d m) := ep.active
  let n : ℕ := Fintype.card A
  let e : Fin n ≃ A := (Fintype.equivFin A).symm
  let s : AndersonAC.S45.State (Fin n) := toS45 ep r e
  let dist : Fin n → Fin n → ℝ := fun i j =>
    physicalDistance d m (e i).val (e j).val
  have hShell0 := hShellAll A e
  have hShell : AndersonAC.S45.ShellBounds d C dist := by
    exact shellBounds_mono_fin hCsh hShell0
  have hD : IsDampedEndpoint ep r t := I.physical (Fin.last k)
  have hzero : ∀ i j, i ∉ ep.active ∨ j ∉ ep.active → ep.g i j = 0 := hD.2.1
  obtain ⟨hsym, hward⟩ := ward_of_damped ep r t htpos.le hD e
  have hK : ‖s.K t‖ ≤ 1 / 2 := by
    change ‖(toS45 ep r e).K t‖ ≤ 1 / 2
    rw [← Kn_eq_S45 ep r t hzero e]
    exact hKn
  have hPbounds : ∀ i, 1 / C ≤ s.p i ∧ s.p i ≤ C := by
    intro i
    have hi := I.damping (e i).val
    rw [hIC, hIc] at hi
    change 1 / C ≤ (r (e i).val).im ∧ (r (e i).val).im ≤ C
    exact ⟨hRecip.trans hi.1, hi.2.1.trans hCCA⟩
  have hFp : s.F t *ᵥ s.p = s.q := by
    ext i
    change (∑ j, s.F t i j * s.p j) = s.q i
    rw [S45_ward_row s t hward i]
    apply Finset.sum_congr rfl
    intro j hj
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare]
    ring
  have hlagG : ∀ i, ‖s.g i i - s.r i‖ ≤ t ^ β := by
    intro i
    have hi := hlag (e i).val (e i).property
    simpa [s, toS45, β] using hi
  have hqp : ∀ i, |s.q i - s.p i| ≤ C * AndersonAC.S45.power t β := by
    intro i
    have hEq : s.q i - s.p i = (s.g i i - s.r i).im := by
      simp [s, toS45, AndersonAC.S45.State.q, AndersonAC.S45.State.p, Complex.sub_im]
    calc
      |s.q i - s.p i| = |(s.g i i - s.r i).im| := by rw [hEq]
      _ ≤ ‖s.g i i - s.r i‖ := Complex.abs_im_le_norm _
      _ ≤ t ^ β := hlagG i
      _ = 1 * AndersonAC.S45.power t β := by simp [AndersonAC.S45.power]
      _ ≤ C * AndersonAC.S45.power t β :=
        mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg htpos.le _)
  have hEntry : ∀ i j, ‖s.h t i j‖ ≤ C / Real.sqrt t := by
    intro i j
    have hdec := I.resolventDecay (Fin.last k) (e i).val (e j).val
    rw [hIC, hIc] at hdec
    have heq : s.h t i j = normalizedInverse ep t (e i).val (e j).val := by
      rfl
    have hdec' : ‖s.h t i j‖ ≤ CA / Real.sqrt t *
        Real.exp (-cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0) := by
      rw [heq]
      simpa [dist] using hdec
    have hmax : 0 ≤ max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0 := le_max_right _ _
    have hprod : 0 ≤ cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0 :=
      mul_nonneg (mul_nonneg hcA.le htpos.le) hmax
    have hexp : Real.exp (-cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0) ≤ 1 := by
      calc
        Real.exp (-cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by nlinarith [hprod])
        _ = 1 := Real.exp_zero
    have hcoef_nonneg : 0 ≤ CA / Real.sqrt t :=
      div_nonneg (by linarith) (Real.sqrt_nonneg _)
    calc
      ‖s.h t i j‖ ≤ CA / Real.sqrt t *
          Real.exp (-cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0) := hdec'
      _ ≤ CA / Real.sqrt t := by
        calc
          CA / Real.sqrt t * Real.exp (-cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0)
              ≤ CA / Real.sqrt t * 1 := mul_le_mul_of_nonneg_left hexp hcoef_nonneg
          _ = CA / Real.sqrt t := by ring
      _ ≤ C / Real.sqrt t := div_le_div_of_nonneg_right hCCA (Real.sqrt_nonneg _)
  have hdecay : ∀ i j, C * AndersonAC.S45.power t (-2) < dist i j →
      ‖s.h t i j‖ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C) := by
    intro i j hfar
    have hthreshold : C * AndersonAC.S45.power t (-2) < dist i j := hfar
    have hdist0 : 0 ≤ dist i j := hShell.nonneg i j
    have hpow : t ^ (-1.03 : ℝ) ≤ t ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge htpos ht1 (by norm_num)
    have hdiv : t ^ (-2 : ℝ) < dist i j / C := by
      rw [lt_div_iff₀ hCpos]
      simpa [AndersonAC.S45.power, mul_comm] using hthreshold
    have hdiv4 : dist i j / C ≤ dist i j / 4 :=
      div_le_div_of_nonneg_left hdist0 (by norm_num) hC4
    have hthresholdSmall : t ^ (-1.03 : ℝ) < dist i j / 4 :=
      lt_of_le_of_lt hpow (lt_of_lt_of_le hdiv hdiv4)
    have harg : dist i j / 4 ≤ max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0 := by
      exact le_trans (by linarith) (le_max_left _ _)
    have hcoeff : 1 / C ≤ cA / 4 := by
      rw [div_le_div_iff₀ hCpos (by norm_num)]
      nlinarith [hCprod]
    have htd : 0 ≤ t * dist i j := mul_nonneg htpos.le hdist0
    have hscale : t * dist i j / C ≤
        cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0 := by
      calc
        t * dist i j / C = (1 / C) * (t * dist i j) := by ring
        _ ≤ (cA / 4) * (t * dist i j) := mul_le_mul_of_nonneg_right hcoeff htd
        _ = cA * t * (dist i j / 4) := by ring
        _ ≤ cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0 :=
          mul_le_mul_of_nonneg_left harg (mul_nonneg hcA.le htpos.le)
    have hargExp : -cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0 ≤
        -t * dist i j / C := by
      calc
        -cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0 =
            -(cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0) := by ring
        _ ≤ -(t * dist i j / C) := neg_le_neg hscale
        _ = -t * dist i j / C := by ring
    have hexp := Real.exp_le_exp.mpr hargExp
    have hdec := I.resolventDecay (Fin.last k) (e i).val (e j).val
    rw [hIC, hIc] at hdec
    have heq : s.h t i j = normalizedInverse ep t (e i).val (e j).val := by
      rfl
    have hdec' : ‖s.h t i j‖ ≤ CA / Real.sqrt t *
        Real.exp (-cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0) := by
      rw [heq]
      simpa [dist] using hdec
    have hcoef_nonneg : 0 ≤ CA / Real.sqrt t :=
      div_nonneg (by linarith) (Real.sqrt_nonneg _)
    calc
      ‖s.h t i j‖ ≤ CA / Real.sqrt t *
          Real.exp (-cA * t * max (dist i j / 2 - t ^ (-1.03 : ℝ)) 0) := hdec'
      _ ≤ CA / Real.sqrt t * Real.exp (-t * dist i j / C) :=
        mul_le_mul_of_nonneg_left hexp hcoef_nonneg
      _ ≤ C / Real.sqrt t * Real.exp (-t * dist i j / C) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hCCA (Real.sqrt_nonneg _)) (Real.exp_nonneg _)
  have hrow := hinverse n t s dist htpos htInv' hShell hK hsym hPbounds hFp hqp hEntry hdecay
  let M := activeBlock ep
  let rA : A → ℂ := fun a => r a.val
  let Kactive := squareKernel ((Real.sqrt t : ℂ) • resetInverse M rA t)
  let Pactive := (1 - Kactive)⁻¹
  have hG := g_eq_padM_resetInverse ep r t hD
  have hGactive : s.g = (resetInverse M rA t).submatrix e e := by
    ext i j
    have hij := congrFun (congrFun hG (e i).val) (e j).val
    rw [padM_val] at hij
    simpa [s, toS45, M, rA, activeBlock] using hij
  have hKsub : s.K t = Kactive.submatrix e e := by
    ext i j
    change ((Real.sqrt t : ℂ) * ep.g (e i).val (e j).val) ^ 2 =
      ((Real.sqrt t : ℂ) * resetInverse M rA t (e i) (e j)) ^ 2
    have hgij : ep.g (e i).val (e j).val = resetInverse M rA t (e i) (e j) := by
      have h := congrFun (congrFun hGactive i) j
      simpa [s, toS45, Matrix.submatrix_apply] using h
    rw [hgij]
  have hsub : (1 - Kactive).submatrix e e = 1 - Kactive.submatrix e e := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply]
    by_cases hij : i = j
    · subst j
      simp
    · have heq : e i ≠ e j := by
        intro h
        exact hij (e.injective h)
      simp [hij, heq]
  have hPsub : s.P t = Pactive.submatrix e e := by
    calc
      s.P t = (1 - Kactive.submatrix e e)⁻¹ := by
        simp [AndersonAC.S45.State.P, hKsub]
      _ = ((1 - Kactive).submatrix e e)⁻¹ := by rw [← hsub]
      _ = (1 - Kactive)⁻¹.submatrix e e := Matrix.inv_submatrix_equiv _ _ _
      _ = Pactive.submatrix e e := rfl
  have hlogCoef : Cout * AndersonAC.S45.logFactor t ≤
      (2 * Cout) * Real.log (1 / t) := by
    calc
      Cout * AndersonAC.S45.logFactor t ≤ Cout * (2 * Real.log (1 / t)) :=
        mul_le_mul_of_nonneg_left hlogF hCout.le
      _ = (2 * Cout) * Real.log (1 / t) := by ring
  have hactiveBound : ∀ v : A → ℂ,
      ‖Pactive.mulVec v‖ ≤ Cout * AndersonAC.S45.logFactor t * ‖v‖ := by
    intro v
    let vFin : Fin n → ℂ := fun i => v (e i)
    have hvFin : ‖vFin‖ ≤ ‖v‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
      intro i
      exact norm_le_pi_norm v (e i)
    have hmul (i : Fin n) : (Pactive.mulVec v) (e i) = (s.P t).mulVec vFin i := by
      change (∑ a : A, Pactive (e i) a * v a) =
        ∑ j : Fin n, s.P t i j * vFin j
      calc
        (∑ a : A, Pactive (e i) a * v a) =
            ∑ j : Fin n, Pactive (e i) (e j) * v (e j) :=
              (Equiv.sum_comp e (fun a : A => Pactive (e i) a * v a)).symm
        _ = ∑ j : Fin n, s.P t i j * vFin j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hpij : s.P t i j = Pactive (e i) (e j) := by
            simpa [Matrix.submatrix_apply] using congrFun (congrFun hPsub i) j
          simp [vFin, hpij]
    have hfinBound : ‖(s.P t).mulVec vFin‖ ≤
        Cout * AndersonAC.S45.logFactor t * ‖v‖ := by
      calc
        ‖(s.P t).mulVec vFin‖ ≤ AndersonAC.S45.rowNorm (s.P t) * ‖vFin‖ :=
          rowNorm_mulVec_bound (s.P t) vFin
        _ ≤ (Cout * AndersonAC.S45.logFactor t) * ‖vFin‖ :=
          mul_le_mul_of_nonneg_right hrow.2.1 (norm_nonneg _)
        _ ≤ Cout * AndersonAC.S45.logFactor t * ‖v‖ :=
          mul_le_mul_of_nonneg_left hvFin (mul_nonneg hCout.le hlogF_nonneg)
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_nonneg hCout.le hlogF_nonneg) (norm_nonneg v))).2
    intro a
    let i := e.symm a
    calc
      ‖(Pactive.mulVec v) a‖ = ‖(Pactive.mulVec v) (e i)‖ := by simp [i]
      _ = ‖(s.P t).mulVec vFin i‖ := by rw [hmul]
      _ ≤ ‖(s.P t).mulVec vFin‖ := norm_le_pi_norm _ _
      _ ≤ Cout * AndersonAC.S45.logFactor t * ‖v‖ := hfinBound
  have hresetRow : ResetRowBound (2 * Cout) ep r t := by
    intro v
    change ‖Pactive.mulVec v‖ ≤ (2 * Cout) * Real.log (1 / t) * ‖v‖
    calc
      ‖Pactive.mulVec v‖ ≤ Cout * AndersonAC.S45.logFactor t * ‖v‖ := hactiveBound v
      _ ≤ (2 * Cout) * Real.log (1 / t) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hlogCoef (norm_nonneg _)
  exact hresetRow

end AndersonAC.AgentS78
