import AndersonAC.AgentS78.Construction.Record
import AndersonAC.AgentS78.Construction.TrueSpace
import AndersonAC.S6.Definitions

/-!
# WP10 construction, C4b: the clearing first-trial bound (frozen contract)

The clearing attempt of an eligible snapshot component `B` (07-assembly.tex:18–34) runs the
§6 stopped heat trial (06-clearing.tex:757–857) on the **active sites of the entering
record** with the frozen damping `r` and the committed inverse `g` as `g₀`, revealing at a
heat pivot `p` its whole true residual: the binary suffix, with coupling
`λ = scaleCoupling n₀ u` (the coupling of `installed`, PhysicalIdentity.lean), of the true
digits of `p` from height `prefixLength p` (02-state.tex:96–103).

`ClearingTrialStatement good` says: on entering records in `good` (deterministic trial
hypotheses, to be defined by the C4b lane and maintained by the deterministic induction),
(a) every heat pivot is a coupled active site within `inspectionRadius j / 2` of `B`
(S78.clearing_locality; so the clearing block's guard never fires and its read pattern is
the coupled active sites), and (b) the trial fails with probability at most `birthBound c j`
under `sourcesLaw` (Proposition 6.6, `S6.preparation_of_small_component`, with the query
history from `F₀ = ⊥`, since the record is fixed (amended 23:31 UTC at agent-s78clrtrial's
request: an arbitrary filtration breaks the residual martingale input); `t_j ≍ 4^{-j}`, `S78.stage_scale_comparison`).

Consumer: `BlockRun.product_bound` for the clearing slots, through the bridge
`localFirstFail (clearingBlock …) x = {q.outcome = fail}` (muse-s78clear) and
`S6.construct_stopped_trial` for the existence of `q`.
-/

open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78
open AndersonAC.S2 (RandomSources sourcesLaw)

variable {d m : ℕ}

/-- The whole true residual of site `y` from height `h`, with coupling `λ`. -/
def trueResidual {M : ℕ → ℕ} (lam : ℝ) (ω : RandomSources (Torus d m) M) (y : Torus d m)
    (h : ℕ) : ℝ :=
  AndersonAC.S2.binarySuffix lam h (trueDigits ω y)

/-- The active sites of a committed record (the index type of the §6 trial). -/
abbrev ActiveSite (x : RunRecord d m) := {i // i ∈ x.endpoint.active}

/-- The frozen initial inverse of the trial: the committed inverse on the active sites. -/
def trialG0 (x : RunRecord d m) : Matrix (ActiveSite x) (ActiveSite x) ℂ :=
  x.endpoint.g.submatrix Subtype.val Subtype.val

/-- **C4b (frozen contract).** The clearing first-trial bound and pivot locality on good
entering records. `good n₀ u E j` is the C4b lane's deterministic hypothesis set. -/
def ClearingTrialStatement (d : ℕ)
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
        (fun _ i => x.r i) (fun _ => trialG0 x) order),
      (∀ k, q.history k = AndersonAC.S6.queryHistory ⊥ q.pivot q.residual k) →
      (∀ k ω, k < q.stop ω → q.residual k ω =
        trueResidual (OAI.Anderson.scaleCoupling n₀ u) ω (q.pivot k ω)
          (x.prefixLength (q.pivot k ω))) →
      (∀ k ω, k < q.stop ω → (q.pivot k ω).val ∉ x.pending ∧
        ∃ y ∈ B, physicalDistance d m (q.pivot k ω).val y.val ≤ inspectionRadius j / 2) ∧
      sourcesLaw (Torus d m) M {ω | q.outcome ω = AndersonAC.S6.TrialOutcome.fail} ≤
        ENNReal.ofReal (birthBound c j)

end AndersonAC.AgentS78
