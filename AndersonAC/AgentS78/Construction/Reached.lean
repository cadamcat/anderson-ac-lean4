import AndersonAC.AgentS78.Construction.MarkingRule
import AndersonAC.AgentS78.Construction.FreezingProof

/-!
# WP10 construction, C4d glue: every block is reached almost surely

08-history.tex:24–31, 76–80 ("auxiliary retries terminate almost surely"; "the construction
reaches each subsequent scheduled trial after an almost surely finite number of
operations"). For the block run: if, from every good record, the probability that the
block-local run has not halted after `k` steps is at most `ε k → 0`, the event depends only
on a fresh pattern, and these patterns are unqueried when the block is entered, then the
next block is reached almost surely (`next_block_reached`). The bound is the frozen
retry estimate (e.g. `p^{⌊k/M⌋}` for a tile with retry failure probability `p < 1`).
-/

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources Query Answer sourcesLaw ObeysQueryRules)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}
  [MeasurableSpace Rec]

/-- The block-local run from `x` has not halted during its first `k+1` states. -/
def notHalted (B : Block ι Rec St) (x : Rec) (k : ℕ) : Set (RandomSources ι M) :=
  {ω | ∀ k' ≤ k, B.halted (localState M B x k' ω) = false}

/-- **The next block is reached almost surely.** -/
theorem next_block_reached (blocks : ℕ → Block ι Rec St) (rec₀ : Rec)
    (orderSet auxSet : ℕ → Set ℕ)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (hQ : ObeysQueryRules ι (runQ M blocks rec₀))
    (n : ℕ) (hstart : IsStoppingTime (retainedFiltration ι hQ) (blockStart M blocks rec₀ n))
    (hfin : ∀ᵐ ω ∂sourcesLaw ι M, blockStart M blocks rec₀ n ω ≠ ⊤)
    (hprest : Measurable[hstart.measurableSpace] (blockPrestate M blocks rec₀ n))
    (pat : ℕ → Rec → FreshPattern ι) (hpat : ∀ k, Measurable (pat k))
    (hmeasNH : ∀ k, MeasurableSet {p : Rec × RandomSources ι M | p.2 ∈ notHalted M (blocks n) p.1 k})
    (hloc : ∀ k x, DependsOnly ι (pat k x) (notHalted M (blocks n) x k))
    (hfresh : ∀ k, ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι (runQ M blocks rec₀)
      ((blockStart M blocks rec₀ n ω).untopD 0) (pat k (blockPrestate M blocks rec₀ n ω)) ω)
    (good : Set Rec) (hgood : ∀ᵐ ω ∂sourcesLaw ι M, blockPrestate M blocks rec₀ n ω ∈ good)
    (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ k, ∀ x ∈ good, sourcesLaw ι M (notHalted M (blocks n) x k) ≤ ENNReal.ofReal (ε k)) :
    ∀ᵐ ω ∂sourcesLaw ι M, blockStart M blocks rec₀ (n + 1) ω ≠ ⊤ := by
  set μ := sourcesLaw ι M
  -- the bad event is contained in every frozen not-halted event
  set E := {ω | blockStart M blocks rec₀ n ω ≠ ⊤ ∧ blockStart M blocks rec₀ (n + 1) ω = ⊤}
  have hsub : ∀ k, E ⊆ {ω | ω ∈ notHalted M (blocks n) (blockPrestate M blocks rec₀ n ω) k} := by
    intro k ω ⟨h1, h2⟩
    obtain ⟨s, x, hE⟩ := BlocksProof.entered_of_blockStart_ne_top M blocks rec₀ orderSet auxSet
      hdisj horders haux h1
    have hx : blockPrestate M blocks rec₀ n ω = x :=
      BlocksProof.blockPrestate_eq M blocks rec₀ orderSet auxSet hE
    show ω ∈ notHalted M (blocks n) (blockPrestate M blocks rec₀ n ω) k
    rw [hx]
    intro k' _
    by_contra hne
    have hh : ∃ k'', (blocks n).halted (localState M (blocks n) x k'' ω) = true :=
      ⟨k', by simpa using hne⟩
    classical
    have hfirst := Nat.find_spec hh
    have hbefore : ∀ k'' < Nat.find hh, (blocks n).halted (localState M (blocks n) x k'' ω) = false :=
      fun k'' hk'' => by simpa using Nat.find_min hh hk''
    have hE' := BlocksProof.entered_succ M blocks rec₀ orderSet auxSet hdisj horders haux hE
      (Nat.find hh) hbefore hfirst
    rw [BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet hE'] at h2
    exact WithTop.coe_ne_top h2
  -- each frozen event has probability at most ε k
  have hk : ∀ k, μ {ω | ω ∈ notHalted M (blocks n) (blockPrestate M blocks rec₀ n ω) k} ≤
      ENNReal.ofReal (ε k) := by
    intro k
    have hcond := freezing_proof ι M (runQ M blocks rec₀) hQ (blockStart M blocks rec₀ n) hstart
      hfin Rec (blockPrestate M blocks rec₀ n) hprest (pat k) (hpat k)
      (fun x => notHalted M (blocks n) x k) (hmeasNH k) (hloc k) (hfresh k) good hgood
      (ε k) (hε0 k) (hbound k)
    have hle := hstart.measurableSpace_le
    have hP : Measurable (blockPrestate M blocks rec₀ n) := hprest.mono hle le_rfl
    have hA : MeasurableSet {ω | ω ∈ notHalted M (blocks n) (blockPrestate M blocks rec₀ n ω) k} :=
      (hmeasNH k).preimage (hP.prodMk measurable_id)
    have hint : ∫ ω, ({ω | ω ∈ notHalted M (blocks n) (blockPrestate M blocks rec₀ n ω) k}.indicator
        (fun _ => (1 : ℝ))) ω ∂μ ≤ ε k := by
      rw [← integral_condExp hle]
      calc ∫ ω, (μ[({ω | ω ∈ notHalted M (blocks n) (blockPrestate M blocks rec₀ n ω) k}.indicator
            (fun _ => (1 : ℝ))) | hstart.measurableSpace]) ω ∂μ
          ≤ ∫ _ω, ε k ∂μ := integral_mono_ae integrable_condExp (integrable_const _) hcond
        _ = ε k := by simp
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one] at hint
    have hint' : (μ {ω | ω ∈ notHalted M (blocks n) (blockPrestate M blocks rec₀ n ω) k}).toReal
        ≤ ε k := by simpa [Measure.real] using hint
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hint'
  -- hence E is null
  have hE0 : μ E = 0 := by
    apply le_antisymm _ (zero_le)
    have hlim : Tendsto (fun k => ENNReal.ofReal (ε k)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact (ENNReal.continuous_ofReal.tendsto 0).comp hε
    exact ge_of_tendsto' hlim (fun k => (measure_mono (hsub k)).trans (hk k))
  have : ∀ᵐ ω ∂μ, ω ∉ E := measure_eq_zero_iff_ae_notMem.mp hE0
  filter_upwards [this, hfin] with ω h1 h2
  intro htop
  exact h1 ⟨h2, htop⟩

/-- **All blocks are reached almost surely** (`start_finite` of `BlockRun`), by induction
with `next_block_reached`. -/
theorem all_blocks_reached (blocks : ℕ → Block ι Rec St) (rec₀ : Rec)
    (orderSet auxSet : ℕ → Set ℕ)
    (hdisj : Pairwise fun n n' => Disjoint (orderSet n) (orderSet n'))
    (horders : BlocksProof.HOrders M blocks orderSet) (haux : BlocksProof.HAux M blocks auxSet)
    (hQ : ObeysQueryRules ι (runQ M blocks rec₀))
    (hstart : ∀ n, IsStoppingTime (retainedFiltration ι hQ) (blockStart M blocks rec₀ n))
    (hprest : ∀ n, Measurable[(hstart n).measurableSpace] (blockPrestate M blocks rec₀ n))
    (pat : ℕ → ℕ → Rec → FreshPattern ι) (hpat : ∀ n k, Measurable (pat n k))
    (hmeasNH : ∀ n k,
      MeasurableSet {p : Rec × RandomSources ι M | p.2 ∈ notHalted M (blocks n) p.1 k})
    (hloc : ∀ n k x, DependsOnly ι (pat n k x) (notHalted M (blocks n) x k))
    (hfresh : ∀ n k, ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι (runQ M blocks rec₀)
      ((blockStart M blocks rec₀ n ω).untopD 0) (pat n k (blockPrestate M blocks rec₀ n ω)) ω)
    (good : ℕ → Set Rec)
    (hgood : ∀ n, ∀ᵐ ω ∂sourcesLaw ι M, blockPrestate M blocks rec₀ n ω ∈ good n)
    (ε : ℕ → ℕ → ℝ) (hε0 : ∀ n k, 0 ≤ ε n k) (hε : ∀ n, Tendsto (ε n) atTop (𝓝 0))
    (hbound : ∀ n k, ∀ x ∈ good n,
      sourcesLaw ι M (notHalted M (blocks n) x k) ≤ ENNReal.ofReal (ε n k)) :
    ∀ n, ∀ᵐ ω ∂sourcesLaw ι M, blockStart M blocks rec₀ n ω ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [BlocksProof.blockStart_eq M blocks rec₀ orderSet auxSet
      (BlocksProof.entered_zero M blocks rec₀ orderSet auxSet ω)]
    exact WithTop.coe_ne_top
  | succ n ih =>
    exact next_block_reached M blocks rec₀ orderSet auxSet hdisj horders haux hQ n (hstart n) ih
      (hprest n) (pat n) (hpat n) (hmeasNH n) (hloc n) (hfresh n) (good n) (hgood n) (ε n)
      (hε0 n) (hε n) (hbound n)

end AndersonAC.AgentS78
