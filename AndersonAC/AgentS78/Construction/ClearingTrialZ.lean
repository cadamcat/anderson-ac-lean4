import AndersonAC.AgentS78.Construction.ClearingTrialResidual

/-!
# WP10 construction, C4b: the trial contracts off a flip-invariant null set

Lead decision agent-s78con4 on agent-s78clrbound's defect (INTERFACE-ISSUES 03:54:15). The
frozen `ClearingTrialStatement` asks for a stopped trial whose residuals are the true residuals
at **every** sample. A stopped trial needs a nonzero real Schur pivot at every step
(`S6.HeatTransition`), which holds for the true residuals only almost surely
(02-state.tex:220–229: "almost surely every principal matrix of the true `H_m − E` is
invertible … We henceforth work on this event"). The consumer can build the trial with the true
residuals only off a null set `Z`. Not a paper gap.

The amended contracts below read the residual hypothesis off `Z`. `Z` is null and invariant
under the sign flips the residual law uses (`Residual.piece_inv`: the whole suffix mask
`siteMask y` and the single-digit masks `{Sum.inl (y, n)}`), so the sign-flip argument applies
off `Z`. The pivot-locality conclusion is read off `Z` as well. Otherwise the statements are
`ClearingTrialStatement` / `ClearingResidualStatement` verbatim (with the per-core separation
hypothesis of 06976a5).

Frozen by the lead (agent-s78con4). The proofs belong to the C4b re-proof lane (DISPATCH).
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)
open AndersonAC.SolS2 (signFlip)

/-- A null set of samples invariant under the whole-suffix and single-digit sign flips of
every site. -/
def FlipInvariantNull {d m : ℕ} {M : ℕ → ℕ} (Z : Set (RandomSources (Torus d m) M)) : Prop :=
  sourcesLaw (Torus d m) M Z = 0 ∧
    ∀ y : Torus d m, signFlip (Torus d m) (Residual.siteMask (Torus d m) y) ⁻¹' Z = Z ∧
      ∀ n : ℕ, signFlip (Torus d m) {Sum.inl (y, n)} ⁻¹' Z = Z

/-- **C4b off a null set (frozen amendment of `ClearingTrialStatement`).** -/
def ClearingTrialStatementZ (d : ℕ)
    (good : ∀ {m : ℕ}, ℕ → ℝ → ℝ → ℕ → Set (RunRecord d m)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n₀ m : ℕ, N ≤ n₀ → 4 * n₀ ≤ m →
    ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E : ℝ, ∀ j : ℕ, n₀ < j → clearingScheduled j m →
    ∀ (M : ℕ → ℕ) (x : RunRecord d m), x ∈ good n₀ u E j →
    ∀ B : Finset (ActiveSite x), B.Nonempty → B.map (Function.Embedding.subtype _) ∈ x.components →
      eligibleCore d B (stageScale u j m) →
      (∀ z ∈ x.pending, z ∉ B.map (Function.Embedding.subtype _) →
        ∀ y ∈ B.map (Function.Embedding.subtype _),
          separationRadius j - inspectionRadius j / 2 < physicalDistance d m z y) →
    ∀ (order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x)))
      (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M) B (stageScale u j m)
        (fun _ i => x.r i) (fun _ => trialG0 x) order)
      (Z : Set (RandomSources (Torus d m) M)), FlipInvariantNull Z →
      (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) →
      (∀ k ω, ω ∉ Z → k < q.stop ω → q.residual k ω =
        trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω (q.pivot k ω)
          (x.prefixLength (q.pivot k ω))) →
      (∀ k ω, ω ∉ Z → k < q.stop ω → (q.pivot k ω).val ∉ x.pending ∧
        ∃ y ∈ B, physicalDistance d m (q.pivot k ω).val y.val ≤ inspectionRadius j / 2) ∧
      sourcesLaw (Torus d m) M {ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail} ≤
        ENNReal.ofReal (birthBound c j)

/-- **C4b residual sub-contract off a null set (frozen amendment of
`ClearingResidualStatement`).** -/
def ClearingResidualStatementZ (d : ℕ)
    (good : ∀ {m : ℕ}, ℕ → ℝ → ℝ → ℕ → Set (RunRecord d m)) : Prop :=
  ∃ K : ℝ, ∃ N : ℕ, ∀ n₀ m : ℕ, N ≤ n₀ → 4 * n₀ ≤ m →
    ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E : ℝ, ∀ j : ℕ, n₀ < j → clearingScheduled j m →
    ∀ (M : ℕ → ℕ) (x : RunRecord d m), x ∈ good n₀ u E j →
    ∀ B : Finset (ActiveSite x), B.Nonempty → B.map (Function.Embedding.subtype _) ∈ x.components →
      eligibleCore d B (stageScale u j m) →
      (∀ z ∈ x.pending, z ∉ B.map (Function.Embedding.subtype _) →
        ∀ y ∈ B.map (Function.Embedding.subtype _),
          separationRadius j - inspectionRadius j / 2 < physicalDistance d m z y) →
    ∀ (order : ActiveSite x ≃ Fin (Fintype.card (ActiveSite x)))
      (q : AndersonAC.S6.StoppedTrial (Ω := RandomSources (Torus d m) M) B (stageScale u j m)
        (fun _ i => x.r i) (fun _ => trialG0 x) order)
      (Z : Set (RandomSources (Torus d m) M)), FlipInvariantNull Z →
      (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) →
      (∀ k ω, ω ∉ Z → k < q.stop ω → q.residual k ω =
        trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω (q.pivot k ω)
          (x.prefixLength (q.pivot k ω))) →
      TrialResidualInput (truncTrial q) (sourcesLaw (Torus d m) M) K
        (fun a b => physicalDistance d m a.val b.val) (inspectionRadius j)

end AndersonAC.AgentS78
