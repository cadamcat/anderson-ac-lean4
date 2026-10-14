import AndersonAC.AgentS78.Construction.TrueSpace
import AndersonAC.S2.RetainedMeasurable
import AndersonAC.S2.Freshness

/-!
# freezing a trial at a retained stopping time

Paper Lemma 2.2 (conditional freshness,
02-state.tex:170–219) used as in 08-history.tex:60–80: the trial started at slot `n`
reads only coordinates that are unqueried at its start (whole true suffixes from given
heights at finitely many sites, finitely many unused auxiliary signs, finitely many
unexposed orders). Its prestate `X` is known at the start. Then, conditionally on the
stopped retained σ-field, the failure probability is the product-law probability of the
trial with the prestate frozen.

`FreezingStatement` is false for `p < 0` (`not_freezingStatement`). The valid form
`FreezingStatementNonneg` assumes `0 ≤ p`; `freezing_proof` establishes it for
`slotRun_of_queryRun` (QueryRun.lean). The proof partitions by the countably many
values of `pattern ∘ X`, reduces
to cylinder events in the pattern's coordinates by a monotone-class argument, and apply
`S2.conditional_freshness_ae_stopped` (whose `completionWeight` is `∏ 1/(M o)!` on
unexposed orders, the uniform-order law).
-/

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S2

section Patterns
variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-- The retained filtration of an admissible query strategy, as a `Filtration`. -/
def retainedFiltration {M : ℕ → ℕ} {Q : ℕ → RandomSources ι M → Query ι}
    (hQ : ObeysQueryRules ι Q) :
    Filtration ℕ (inferInstance : MeasurableSpace (RandomSources ι M)) :=
  ⟨retained ι Q, retained_mono ι Q, retained_le ι hQ⟩

/-- Coordinates a trial may read: the true suffixes from `height i` on at `sites`,
the auxiliary signs `aux`, and the orders `orders`. -/
structure FreshPattern where
  sites : Finset ι
  height : ι → ℕ
  aux : Finset ℕ
  orders : Finset ℕ

instance : MeasurableSpace (FreshPattern ι) := ⊤

/-- The sign coordinates of a pattern. -/
def FreshPattern.signs {ι : Type} (π : FreshPattern ι) : Set (SignIndex ι) :=
  {z | ∃ i ∈ π.sites, ∃ k, π.height i ≤ k ∧ z = Sum.inl (i, k)} ∪
    {z | ∃ a ∈ π.aux, z = Sum.inr a}

/-- `A` is decided by the coordinates of the pattern only. -/
def DependsOnly {M : ℕ → ℕ} (π : FreshPattern ι) (A : Set (RandomSources ι M)) : Prop :=
  ∀ ω ω' : RandomSources ι M, (∀ z ∈ π.signs, ω.1 z = ω'.1 z) →
    (∀ o ∈ π.orders, ω.2 o = ω'.2 o) → (ω ∈ A ↔ ω' ∈ A)

/-- No coordinate of the pattern has been queried or exposed after `q` operations. -/
def UnqueriedAt {M : ℕ → ℕ} (Q : ℕ → RandomSources ι M → Query ι) (q : ℕ)
    (π : FreshPattern ι) (ω : RandomSources ι M) : Prop :=
  (∀ z ∈ π.signs, z ∉ queriedSigns ι Q q ω) ∧ ∀ o ∈ π.orders, orderCount ι Q q ω o = 0

end Patterns

/-- **trial freezing (contract).** Freezing a trial at an a.s. finite retained stopping time. -/
def FreezingStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ → ℕ) (Q : ℕ → RandomSources ι M → Query ι)
    (hQ : ObeysQueryRules ι Q) (τ : RandomSources ι M → WithTop ℕ)
    (hτ : IsStoppingTime (retainedFiltration ι hQ) τ)
    (_hfin : ∀ᵐ ω ∂sourcesLaw ι M, τ ω ≠ ⊤)
    (S : Type) [MeasurableSpace S] (X : RandomSources ι M → S)
    (_hX : Measurable[hτ.measurableSpace] X)
    (pattern : S → FreshPattern ι) (_hpat : Measurable pattern)
    (A : S → Set (RandomSources ι M))
    (_hA : MeasurableSet {p : S × RandomSources ι M | p.2 ∈ A p.1})
    (_hloc : ∀ x, DependsOnly ι (pattern x) (A x))
    (_hfresh : ∀ᵐ ω ∂sourcesLaw ι M, UnqueriedAt ι Q ((τ ω).untopD 0) (pattern (X ω)) ω)
    (good : Set S) (_hgood : ∀ᵐ ω ∂sourcesLaw ι M, X ω ∈ good)
    (p : ℝ) (_hp : ∀ x ∈ good, sourcesLaw ι M (A x) ≤ ENNReal.ofReal p),
    ∀ᵐ ω ∂sourcesLaw ι M,
      (sourcesLaw ι M)[{ω' | ω' ∈ A (X ω')}.indicator (fun _ => (1 : ℝ)) |
        hτ.measurableSpace] ω ≤ p

end AndersonAC.AgentS78
