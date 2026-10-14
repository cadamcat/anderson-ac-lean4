import AndersonAC.AgentS78.Construction.Reached
import AndersonAC.AgentS78.Construction.Invariant
import AndersonAC.AgentS78.Construction.PathwiseInvariant

/-!
# all blocks are reached, with goodness from an invariant

`all_blocks_reached` takes the goodness of the entering records and the freshness of the
halting patterns almost surely for every block. Both are only available for reached blocks
(`blockPrestate_mem`, `fresh_of_declared_aux`). `all_blocks_reached_of_inv` runs the same
induction and derives them at block `n` from "block `n` is reached a.s." (the induction
hypothesis), with goodness from a record invariant kept by every block along its runs with the
answers of the sample (`blockPrestate_mem_pathwise`; since, at
request: an invariant closed under arbitrary answers cannot reach the sweep end).
-/

open MeasureTheory Filter Topology

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2 (RandomSources ObeysQueryRules sourcesLaw)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) {Rec St : Type}
  [MeasurableSpace Rec]

/-- **All blocks are reached a.s.**, from halting bounds on an invariant. -/
theorem all_blocks_reached_of_inv (blocks : ℕ → Block ι Rec St) (rec₀ : Rec)
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
    (hfresh : ∀ n k (ω : RandomSources ι M), blockStart M blocks rec₀ n ω ≠ ⊤ →
      UnqueriedAt ι (runQ M blocks rec₀)
        ((blockStart M blocks rec₀ n ω).untopD 0) (pat n k (blockPrestate M blocks rec₀ n ω)) ω)
    (Inv : ℕ → Set Rec) (h₀ : rec₀ ∈ Inv 0)
    (hInv : ∀ n x k (ω : RandomSources ι M), x ∈ Inv n →
      (∀ k' < k, (blocks n).halted (localState M (blocks n) x k' ω) = false) →
      (blocks n).halted (localState M (blocks n) x k ω) = true →
      (blocks n).exit (localState M (blocks n) x k ω) ∈ Inv (n + 1))
    (ε : ℕ → ℕ → ℝ) (hε0 : ∀ n k, 0 ≤ ε n k) (hε : ∀ n, Tendsto (ε n) atTop (𝓝 0))
    (hbound : ∀ n k, ∀ x ∈ Inv n,
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
    have hgood : ∀ᵐ ω ∂sourcesLaw ι M, blockPrestate M blocks rec₀ n ω ∈ Inv n := by
      filter_upwards [ih] with ω hω
      exact blockPrestate_mem_pathwise M blocks rec₀ orderSet auxSet hdisj horders haux ω Inv
        (fun n x k hx hk hh => hInv n x k ω hx hk hh)
        (fun h0 => by rw [blockPrestate_zero M blocks rec₀ ω h0]; exact h₀) n hω
    have hfr : ∀ k, ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι (runQ M blocks rec₀)
        ((blockStart M blocks rec₀ n ω).untopD 0) (pat n k (blockPrestate M blocks rec₀ n ω)) ω :=
      fun k => by
        filter_upwards [ih] with ω hω
        exact hfresh n k ω hω
    exact next_block_reached M blocks rec₀ orderSet auxSet hdisj horders haux hQ n (hstart n) ih
      (hprest n) (pat n) (hpat n) (hmeasNH n) (hloc n) hfr (Inv n) hgood (ε n)
      (hε0 n) (hε n) (hbound n)

end AndersonAC.AgentS78
