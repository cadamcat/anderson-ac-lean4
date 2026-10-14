import AndersonAC.AgentS78.Construction.BoxPhases
import AndersonAC.AgentS78.Construction.SweepEndReserve
import AndersonAC.AgentS78.Construction.SweepRowTail

/-!
# The sweep end with uniform assembly constants (agent-s78box)

`sweepEndUniform_of_parts`: `SweepEndUniformStatement d` (BoxPhases.lean) from the transport
contract `SweepTransportStatement` and the terminal Combes–Thomas contract
`TerminalCTStatement` (the row tails are proved, `sweepRowTail_proof`). The proofs are those of
agent-s78send's `sweepEndResolvent_of_terminalCT` and `sweepEnd_proof` (SweepEndDecay.lean,
SweepEnd.lean) with the assembly constants chosen before the history constant `Cb`; they did
not depend on `Cb`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- `SweepEndResolventStatement` with `CA₀ cA₀ t0` chosen before `C Cb` (same proof as
`sweepEndResolvent_of_terminalCT`, agent-s78send). -/
theorem sweepEndResolventU_of_terminalCT (hCT : TerminalCTStatement d) :
  ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ →
  ∃ CA₀ > (0 : ℝ), ∃ cA₀ > (0 : ℝ), ∃ t0 > (0 : ℝ), ∀ C Cb : ℝ, 1 ≤ C → 1 ≤ Cb →
  ∀ CA ≥ CA₀, ∀ cA : ℝ, 0 < cA → cA ≤ cA₀ →
  ∀ (m n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (P : TilePlan d m) (j : ℕ) (x : RunRecord d m),
    P.n₀ = n₀ → P.u = u → u ∈ Set.Ioc (1 / 4 : ℝ) 1 → n₀ < j → j ≤ m →
    sweepScale u m j < t0 →
    StageBounds d m n₀ (j - 1) u cP CP cL CL C₀ x.endpoint x.r →
    TileSweepCore C P j n₀ u E ρ Cb Finset.univ x →
    PhysicalIdentity E (sweepEndMapTheta (sweepTheta P.u m j) x) →
    SweepFacts Cb (stageScale u (j - 1) m) (stageScale u j m) x.endpoint
      (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint x.r →
    IsDampedEndpoint (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint x.r (stageScale u j m) →
    (∀ i, rowFour (normalizedInverse (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint
      (stageScale u j m)) i ≤ 0.7 * stageScale u j m ^ (1 + delta)) →
    ∀ i i', ‖normalizedInverse (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint
        (stageScale u j m) i i'‖ ≤
      CA / Real.sqrt (stageScale u j m) * Real.exp (-cA * stageScale u j m *
        max (physicalDistance d m i i' / 2 - stageScale u j m ^ (-1.03 : ℝ)) 0) := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀
  obtain ⟨a, ha, Cc, hCc, t0, ht0, hct⟩ := hCT cP CP hcP hCP
  refine ⟨Cc, lt_of_lt_of_le one_pos hCc, a, ha, t0, ht0, fun C Cb hC hCb CA hCA cA hcA hcAa => ?_⟩
  intro m n₀ u E ρ P j x hn hu' hu hnj hjm hsmall hSB hcore hphys hsw hDs hrows
  subst hn hu'
  have hu0 : 0 < P.u := lt_trans (by norm_num) hu.1
  obtain ⟨ht, hθt, hθ1, hθ2⟩ := digitSweep_scales hu0 (by omega : 1 ≤ j) hjm
  set t := stageScale P.u (j - 1) m with ht_def
  set t' := stageScale P.u j m with ht'_def
  set θ := sweepTheta P.u m j with hθ_def
  have ht' : 0 < t' := stageScale_pos' hu j m
  have ht't : t' ≤ t := by rw [← hθt]; nlinarith
  have hsmall' : t' < t0 := by
    have : t < t0 := by have h := hsmall; rwa [sweepScale_digit hjm] at h
    linarith
  set sw := (sweepEndMapTheta θ x).endpoint with hsw_def
  have hact : sw.active = x.endpoint.active := hsw.active
  unfold StageBounds at hSB
  dsimp only at hSB
  obtain ⟨hdiag, -, -, -, -, hmet, -⟩ := hSB
  -- the damped identity in the form `M_A + diag(D − iτ)`
  have hBG : (sw.M.submatrix (Subtype.val : sw.active → Torus d m) Subtype.val +
        Matrix.diagonal (fun i : sw.active =>
          ((-(t' * (x.r i.val).re) : ℝ) : ℂ) - Complex.I * (((t' * (x.r i.val).im) : ℝ) : ℂ))) *
      sw.g.submatrix Subtype.val Subtype.val = 1 := by
    obtain ⟨h3, -⟩ := hDs.2.2
    convert h3 using 2
    rw [sub_eq_add_neg, ← Matrix.diagonal_smul, Matrix.diagonal_neg]
    congr 2
    funext i
    apply Complex.ext <;> simp
  have hτ : ∀ i ∈ sw.active, cP * t' ≤ t' * (x.r i).im ∧ t' * (x.r i).im ≤ CP * t' := by
    intro i hi
    rw [hact] at hi
    obtain ⟨-, h1, h2, -⟩ := hdiag i hi
    constructor <;> nlinarith
  intro i i'
  by_cases hii : i ∈ sw.active ∧ i' ∈ sw.active
  · have H := hct m t' E (sweepEndMapTheta θ x) (fun i => -(t' * (x.r i).re))
      (fun i => t' * (x.r i).im) sw.g ht' hsmall' hphys hτ hBG i hii.1 i' hii.2
    -- the metric: d_T ≥ dist/2 − t_j^{-1.03}
    have hpow : t ^ (-1.03 : ℝ) ≤ t' ^ (-1.03 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ht' ht't (by norm_num)
    have hdT0 : (0 : ℝ) ≤ terminalDistance (nnGraph d m) (Finset.univ \ sw.active) i i' :=
      Nat.cast_nonneg _
    have hdT : max (physicalDistance d m i i' / 2 - t' ^ (-1.03 : ℝ)) 0 ≤
        terminalDistance (nnGraph d m) (Finset.univ \ sw.active) i i' := by
      refine max_le ?_ hdT0
      have := hmet i i'
      rw [← hact] at this
      linarith
    have hnorm : ‖normalizedInverse sw t' i i'‖ = ‖(Real.sqrt t' : ℂ) * sw.g i i'‖ := by
      simp [normalizedInverse]
    rw [hnorm]
    refine H.trans ?_
    have hsq : 0 < Real.sqrt t' := Real.sqrt_pos.mpr ht'
    have hexp : Real.exp (-a * t' * terminalDistance (nnGraph d m) (Finset.univ \ sw.active) i i') ≤
        Real.exp (-cA * t' * max (physicalDistance d m i i' / 2 - t' ^ (-1.03 : ℝ)) 0) := by
      apply Real.exp_le_exp.mpr
      have hm0 : 0 ≤ max (physicalDistance d m i i' / 2 - t' ^ (-1.03 : ℝ)) 0 := le_max_right _ _
      have h1 : cA * max (physicalDistance d m i i' / 2 - t' ^ (-1.03 : ℝ)) 0 ≤
          a * terminalDistance (nnGraph d m) (Finset.univ \ sw.active) i i' :=
        mul_le_mul hcAa hdT hm0 ha.le
      nlinarith
    have hC' : Cc / Real.sqrt t' ≤ CA / Real.sqrt t' :=
      div_le_div_of_nonneg_right hCA hsq.le
    have hCA0 : 0 ≤ CA := le_trans (le_of_lt (lt_of_lt_of_le one_pos hCc)) hCA
    exact mul_le_mul hC' hexp (Real.exp_pos _).le (div_nonneg hCA0 hsq.le)
  · have hz : sw.g i i' = 0 := hDs.2.1 i i' (by tauto)
    simp only [normalizedInverse, Matrix.smul_apply, hz, smul_zero, norm_zero]
    have : 0 < Real.sqrt t' := Real.sqrt_pos.mpr ht'
    have : 0 ≤ CA := le_trans (le_of_lt (lt_of_lt_of_le one_pos hCc)) hCA
    positivity

/-- **`SweepEndUniformStatement` from the transport and terminal Combes–Thomas contracts.** -/
theorem sweepEndUniform_of_parts (hT : SweepTransportStatement d)
    (hTail : SweepRowTailStatement d) (hCT : TerminalCTStatement d) :
    SweepEndUniformStatement d := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨Cb₀, hCb₀, CA₁, hCA₁, t1, ht1, hcore⟩ :=
    sweepEnd_core hT (sweepReserveRow_of_tails hTail) cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C hC
  obtain ⟨CA₂, hCA₂, cA₂, hcA₂, t2, ht2, hdecU⟩ :=
    sweepEndResolventU_of_terminalCT hCT cP CP cL CL C₀ hcP hCP hcL hCL hC₀
  -- the comparison constants
  set cc := min cL (3 / (8 * CP ^ 2)) / 2 with hcc
  set CC := 3 / 2 * max (C₀ + 1 / cP ^ 2) CL with hCC
  have hCPpos : 0 < CP := lt_of_lt_of_le hcP hCP
  have hcc0 : 0 < cc := by
    have : 0 < min cL (3 / (8 * CP ^ 2)) := lt_min hcL (by positivity)
    rw [hcc]; linarith
  have hCC0 : 0 < CC := by
    have : 0 < max (C₀ + 1 / cP ^ 2) CL := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    rw [hCC]; positivity
  refine ⟨max (max CA₁ CA₂) cc⁻¹, lt_of_lt_of_le hCA₁ ((le_max_left _ _).trans (le_max_left _ _)),
    min cA₂ CC⁻¹, lt_min hcA₂ (inv_pos.mpr hCC0), max Cb₀ 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), fun Cb hCb CA hCA cA hcA hcA' => ?_⟩
  have hCb1 : 1 ≤ Cb := le_trans (le_max_right _ _) hCb
  have hdec := hdecU C Cb hC hCb1
  obtain ⟨t3, ht3, hε⟩ := AgentS45.power_small (e := 0.10 * delta) (by norm_num [delta])
    (a := 1 / (2 * Cb)) (by positivity)
  refine ⟨min t1 (min t2 t3), lt_min ht1 (lt_min ht2 ht3), ?_⟩
  intro m n₀ u E ρ P j x hn hu' hu hnj hjm hsmall hSB hphys hcore'
  have hCA1 : CA₁ ≤ CA := (le_max_left _ _).trans ((le_max_left _ _).trans hCA)
  have hCA2 : CA₂ ≤ CA := (le_max_right _ _).trans ((le_max_left _ _).trans hCA)
  have hCA3 : cc⁻¹ ≤ CA := (le_max_right _ _).trans hCA
  obtain ⟨hsw, hDs, hrows, hlag⟩ := hcore Cb (le_trans (le_max_left _ _) hCb) CA hCA1
    m n₀ u E ρ P j x hn hu' hu hnj hjm
    (lt_of_lt_of_le hsmall (min_le_left _ _)) hSB hcore'
  have hdecay := hdec CA hCA2 cA hcA (hcA'.trans (min_le_left _ _)) m n₀ u E ρ P j x
    hn hu' hu hnj hjm (lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_left _ _)))
    hSB hcore' hphys hsw hDs hrows
  -- the initial comparison
  subst hn hu'
  have hu0 : 0 < P.u := lt_trans (by norm_num) hu.1
  obtain ⟨ht, hθt, hθ1, hθ2⟩ := digitSweep_scales hu0 (by omega : 1 ≤ j) hjm
  have hθeq : sweepTheta P.u m j = stageScale P.u j m / stageScale P.u (j - 1) m :=
    sweepTheta_digit hjm
  have htsmall : stageScale P.u (j - 1) m < t3 := by
    rw [← sweepScale_digit hjm]
    exact lt_of_lt_of_le hsmall ((min_le_right _ _).trans (min_le_right _ _))
  have hpow := hε _ ht htsmall
  have hpow0 : 0 ≤ stageScale P.u (j - 1) m ^ (0.10 * delta) := Real.rpow_nonneg ht.le _
  have hε' : Cb * stageScale P.u (j - 1) m ^ (0.10 * delta) ≤ 1 / 2 := by
    have h1 : Cb * S45.power (stageScale P.u (j - 1) m) (0.10 * delta) ≤ Cb * (1 / (2 * Cb)) :=
      mul_le_mul_of_nonneg_left hpow.le (by linarith)
    have h2 : Cb * (1 / (2 * Cb)) = 1 / 2 := by field_simp
    exact (h1.trans h2.le)
  have hcmp := sweep_initialComparison (by omega) hu hcP hcL hCL.le hC₀.le x.endpoint
    (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint x.r hSB hsw hDs
    (by rw [← hθeq]; exact hθ1) (by rw [← hθeq]; exact hθ2)
    (mul_nonneg (by linarith) hpow0) hε'
  have hS0 : ∀ f, 0 ≤ spatialEnergy (nnGraph d m)
      (sweepEndMapTheta (sweepTheta P.u m j) x).endpoint.active
      (stageScale P.u P.n₀ m * stageScale P.u j m) f := fun f =>
    spatialEnergy_nonneg' _ _ _ (mul_pos (stageScale_pos' hu _ m) (stageScale_pos' hu _ m)) f
  refine ⟨hsw, hDs, hdecay, fun f => ⟨?_, ?_⟩, hrows, hlag⟩
  · refine le_trans ?_ (hcmp f).1
    exact mul_le_mul_of_nonneg_right (hcA'.trans (min_le_right _ _)) (hS0 f)
  · refine (hcmp f).2.trans ?_
    exact mul_le_mul_of_nonneg_right hCA3 (hS0 f)

/-- **WP10 per-box run invariant packages, sweep end reduced to its two open contracts.** -/
theorem boxInvariantK_of_phases' (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hCT : ActiveCTStatement d) (hbridge : StartBridgeStatement)
    (hT : SweepTransportStatement d) (hTCT : TerminalCTStatement d)
    (hclr : ClearingPhasePackage d)
    (hRTV : RunTVClosureStatement d) (hAT : RunAllTerminalStatement d) :
    ∀ C : ℝ, 1 ≤ C → ∃ Cg : ℝ, 1 ≤ Cg ∧ ∃ Cr cp cg c : ℝ, 0 < cp ∧ 0 < cg ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ n₀ m : ℕ, N₀ ≤ n₀ → 4 * n₀ ≤ m → ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ → ∀ P : TilePlan d m, P.n₀ = n₀ → P.u = u →
      (∀ j, StageCoverFacts C ((4 : ℝ) ^ 6 * C) P.u P.n₀ j (P.cover j)) →
      Nonempty (BoxInvariantK d m n₀ u E Cr cp cg c Cg P) :=
  boxInvariantK_of_phases d hd e₂ he₂ hCT hbridge
    (sweepEndUniform_of_parts hT (sweepRowTail_proof d) hTCT) hclr hRTV hAT

end AndersonAC.AgentS78
