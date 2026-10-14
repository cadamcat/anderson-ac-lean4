import AndersonAC.AgentS78.Construction.SweepEnd

/-!
# The Combes–Thomas decay of the post-sweep endpoint

agent-s78send (2026-10-14). The field `resolventDecay` of `ClearPhaseData.ofSweep'` at the sweep
end reduces to one Combes–Thomas statement on the torus active block in the **terminal
distance** (`TerminalCTStatement`, 05:62–100: S45 Lemma `locality`, `AgentS45.locality_proof`,
transported to the torus, decay `exp(−a t d_T)` with `d_T` the collapsed/terminal distance of
the terminal set). It is the same transport as agent-s78start's `ActiveCTStatement`
(luna-s78actct) before its conversion to the physical distance, and it is what
`AssemblyInput.resolventDecay` needs: with the metric clause of the stage bounds,
`d_T ≥ dist/2 − t^{-1.03}`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open scoped Matrix.Norms.L2Operator

variable {d m : ℕ}

/-- **Combes–Thomas on the torus active block in the terminal distance (contract).** If the
real part of the endpoint matrix is the active Schur complement of the nearest-neighbour
`H − E + installed` (`PhysicalIdentity`), then for every real diagonal shift `D` and damping
`c₀ t ≤ τ ≤ C₀ t` the inverse `G` of `M_A + diag(D − iτ)` on the active block satisfies
`‖√t G_ik‖ ≤ C/√t · exp(−a t d_T(i,k))`, `d_T` the terminal distance of the inactive sites
(S45 `locality`, collapsed distance = terminal distance). -/
def TerminalCTStatement (d : ℕ) : Prop :=
  ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ a > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∃ t0 > (0 : ℝ),
    ∀ (m : ℕ) (t E : ℝ) (x : RunRecord d m) (D τ : Torus d m → ℝ)
    (G : Matrix (Torus d m) (Torus d m) ℂ), 0 < t → t < t0 →
    PhysicalIdentity E x →
    (∀ i ∈ x.endpoint.active, c₀ * t ≤ τ i ∧ τ i ≤ C₀ * t) →
    (x.endpoint.M.submatrix (Subtype.val : x.endpoint.active → Torus d m) Subtype.val +
        Matrix.diagonal (fun i : x.endpoint.active =>
          ((D i.val : ℝ) : ℂ) - Complex.I * ((τ i.val : ℝ) : ℂ))) *
      G.submatrix Subtype.val Subtype.val = 1 →
    ∀ i ∈ x.endpoint.active, ∀ k ∈ x.endpoint.active,
      ‖(Real.sqrt t : ℂ) * G i k‖ ≤ C / Real.sqrt t *
        Real.exp (-a * t * terminalDistance (nnGraph d m) (Finset.univ \ x.endpoint.active) i k)

/-- **`resolventDecay` of the post-sweep endpoint from the terminal Combes–Thomas bound.** -/
theorem sweepEndResolvent_of_terminalCT (hCT : TerminalCTStatement d) :
    SweepEndResolventStatement d := by
  intro cP CP cL CL C₀ hcP hCP hcL hCL hC₀ C Cb hC hCb
  obtain ⟨a, ha, Cc, hCc, t0, ht0, hct⟩ := hCT cP CP hcP hCP
  refine ⟨Cc, lt_of_lt_of_le one_pos hCc, a, ha, t0, ht0, fun CA hCA cA hcA hcAa => ?_⟩
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

/-- **The sweep end from the transport, reserve-row and terminal Combes–Thomas contracts.** -/
theorem sweepEnd_proof' (hT : SweepTransportStatement d) (hR : SweepReserveRowStatement d)
    (hCT : TerminalCTStatement d) :
    ∀ cP CP cL CL C₀ : ℝ, 0 < cP → cP ≤ CP → 0 < cL → 0 < CL → 0 < C₀ → ∀ C : ℝ, 1 ≤ C →
    ∃ Cb₀ > (0 : ℝ), ∀ Cb ≥ Cb₀, ∃ CA₀ > (0 : ℝ), ∃ cA₀ > (0 : ℝ), ∀ CA ≥ CA₀, ∀ cA : ℝ,
      0 < cA → cA ≤ cA₀ → SweepEndStatement d C Cb CA cA cP CP cL CL C₀ :=
  sweepEnd_proof hT hR (sweepEndResolvent_of_terminalCT hCT)

end AndersonAC.AgentS78
