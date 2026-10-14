import AndersonAC.S78Metric.Count

open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AndersonAC.SolS78

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {κ : Type} [Fintype κ]

/-- Separation constant. -/
def sepL (c μ R ℓ : ℝ) : ℝ := c * (R - 2 * ℓ) - μ

theorem sepL_pos {c μ R ℓ : ℝ} {M : ℕ} (hmargin : 2 * (M : ℝ) < c * (R - 2 * ℓ) - μ) :
    0 < sepL c μ R ℓ := by
  unfold sepL
  have : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
  linarith

theorem groups_disjoint {G : SimpleGraph ι} {O : κ → Finset ι}
    {c μ R ℓ : ℝ} {M : ℕ} (hc : 0 < c) (hμ : 0 ≤ μ)
    (hsep : ∀ a a', a ≠ a' → ∀ u ∈ O a, ∀ v ∈ O a', R - 2 * ℓ ≤ (G.dist u v : ℝ))
    (hmargin : 2 * (M : ℝ) < c * (R - 2 * ℓ) - μ)
    {a a' : κ} (hne : a ≠ a') : Disjoint (O a) (O a') := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  have h0 : (G.dist w w : ℝ) = 0 := by simp
  have h1 := hsep a a' hne w hw1 w hw2
  rw [h0] at h1
  have hL := sepL_pos (c := c) (μ := μ) (R := R) (ℓ := ℓ) (M := M) hmargin
  unfold sepL at hL
  have hcR : c * (R - 2 * ℓ) ≤ 0 := by
    have : R - 2 * ℓ ≤ 0 := h1
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) this
    linarith
  linarith

theorem sepL_le_dist {G : SimpleGraph ι} {O : κ → Finset ι}
    {c μ R ℓ : ℝ} (hc : 0 < c)
    (hsep : ∀ a a', a ≠ a' → ∀ u ∈ O a, ∀ v ∈ O a', R - 2 * ℓ ≤ (G.dist u v : ℝ))
    {a a' : κ} (hne : a ≠ a') {u v : ι} (hu : u ∈ O a) (hv : v ∈ O a') :
    sepL c μ R ℓ ≤ c * (G.dist u v : ℝ) - μ := by
  unfold sepL
  have h1 := hsep a a' hne u hu v hv
  have := mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
  linarith

end AndersonAC.SolS78
