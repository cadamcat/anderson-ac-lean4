import AndersonAC.AgentS78.Construction.StagePhaseRecOp
import AndersonAC.AgentS78.Construction.StagePhaseGood

/-!
# The clearing trial bound hypotheses from the clearing-phase invariant. On a record entering the clearing index `opIndex j 2 y` with
`ClearPhaseR … j (rank y)`, every clause of `ClearingGoodAt` holds except `separated`, which holds
for the components not yet reached by the anchor scan (in particular for the attempted component
`theCore j u y x`, the only one clearing trial bound uses, ClearingTrialProof.lean:250); and the record is in
`clearingGeo d Ctr`.
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.AgentS78Geo (ClearingTraceOf ClearingGeoAt clearingGeo)

variable {d m : ℕ}

/-- **The clearing trial bound hypotheses on a record entering a clearing index.** -/
theorem clearPhaseR_good (hd : 3 ≤ d) (CA cA PA : ℝ) (hCA : 1 ≤ CA) (hcA : 0 < cA)
    (hPA : 0 ≤ PA) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 0 < t₀ ∧
    ∀ {m : ℕ} (cP CP Ctr : ℝ) (n₀ : ℕ) (u E : ℝ) (ρ : ℂ) (C : ℝ) (j r : ℕ) (x : RunRecord d m),
      u ∈ Set.Ioc (1 / 4 : ℝ) 1 → stageScale u j m < t₀ →
      ClearPhaseR cP CP Ctr n₀ u E ρ C CA cA PA j r x → x.aborted = false →
      (∀ i ∈ x.endpoint.active, ‖x.r i‖ ≤ CP ∧ cP ≤ (x.r i).im ∧ (x.r i).im ≤ CP) ∧
      (∀ i : ActiveSite x,
        AndersonAC.S6.fourthRow (AndersonAC.S6.scaledInverse (stageScale u j m) (trialG0 x)) i ≤
          (4 / 5) * AndersonAC.S6.fourthCap (stageScale u j m)) ∧
      (∀ i ∈ x.endpoint.active, ‖x.endpoint.g i i - x.r i‖ ≤
        phaseQlag d C' (stageScale u j m) * stageScale u j m ^ AndersonAC.S6.betaW) ∧
      (∀ i ∈ x.endpoint.active, i ∉ x.pending → x.prefixLength i + n₀ = j) ∧
      (∀ B ∈ x.components, (∀ c ∈ B, r ≤ (siteRank d m c).val) → ∀ z ∈ x.pending, z ∉ B →
        ∀ y ∈ B, separationRadius j - inspectionRadius j / 2 < physicalDistance d m z y) ∧
      (∀ B ∈ x.components, ∃ a, ∀ y ∈ B,
        physicalDistance d m a y ≤ (B.card : ℝ) * separationRadius j) ∧
      x ∈ clearingGeo d Ctr n₀ u j := by
  obtain ⟨C', t₀, hC', ht₀, hA⟩ := clearPhase_goodAt_analytic hd CA cA PA hCA hcA hPA
  refine ⟨C', t₀, hC', ht₀, ?_⟩
  intro m cP CP Ctr n₀ u E ρ C j r x hu ht hx hab
  obtain ⟨D, hpos, -, -, hbroad⟩ := hx hab
  obtain ⟨-, h4, hlag⟩ := hA n₀ u E ρ C j x D hu ht
  have hDx : IsDampedEndpoint x.endpoint x.r (stageScale u j m) := by
    have := D.I.physical (Fin.last D.k)
    rw [D.last, ← D.frozen] at this
    exact this
  refine ⟨fun i _ => ⟨(hbroad i).2, (hbroad i).1,
      (Complex.im_le_norm (x.r i)).trans (hbroad i).2⟩, h4, hlag, hpos.base.coupled, hpos.sepU,
    fun B hB => ?_, ?_⟩
  · by_cases hne : B.Nonempty
    · obtain ⟨a, ha⟩ := hne
      exact ⟨a, fun y hy => hpos.base.componentDiam B hB a ha y hy⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ⟨fun _ => 0, fun y hy => by simp [hne] at hy⟩
  · obtain ⟨l, T, hTr, -, -⟩ := hpos.base.trace
    exact ⟨hDx, ⟨l, T, hTr⟩, hpos.base.componentDiam⟩

end AndersonAC.AgentS78
