import AndersonAC.S3.GridLemmas

/-!
Statements for the circulant symbol of the entrywise square
of the initial inverse, `Q(ζ) = t · gridAvg_k R(k) R(ζ-k)`, at grid frequencies.
Here `R = gridResolvent E t r`, `E + 2d ∈ [1/400, 1/100]`, `r` in the rectangle,
so the excess `β = E + 2d + t Re r ∈ [1/800, 3/200]` and `v = t Im r ∈ [t a₀, t B]`
for small `t`; the grid is fine: `L ≥ t⁻⁸`, `L` even.

* Small frequencies (`|gridAngle ζ|∞ ≤ η`): cancellation via the Feynman identity
  (`Reciprocal.lean`), with amplitudes `A_j(u) = |(1-u) + u e^{-iθ_j}| ∈ [1-θ_j²/4, 1]`
  and phases so that `(1-u) cos κ_j + u cos(κ_j - θ_j) = A_j cos(κ_j + φ_j)`; then the
  perturbed item of `BottomResolventStatement` and grid quadrature, uniformly in `u`.
* Other frequencies (`|gridAngle ζ j₀| ≥ η`): absolute product; a Lipschitz cutoff
  `ψ(κ) = clamp((0.21 - ‖κ‖∞)/0.01, 0, 1)` in both `κ` and `κ - θ`; off the cutoff one
  factor is `≤ 41` (`ℓ ≥ 4 sin²(0.1) > 3/200 + 0.024`) and the other averages to
  `gridAvg ‖R‖` by reindexing the grid; on the cutoff, quadrature then `LayerCake`
  with `JointShellK` (`ζ' = -θ`, `V = C/η`).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace AndersonAC.S3

/-- The symbol at small grid frequencies is logarithmic (cancellation). -/
def SmallSymbolStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ a₀ B : ℝ, 0 < a₀ → a₀ ≤ B →
    ∃ η C t₁ : ℝ, 0 < η ∧ 0 < C ∧ 0 < t₁ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
        ∀ E : ℝ, 1 / 400 ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 → ∀ r ∈ rectangle a₀ B,
          ∀ ζ : Torus d L, (∀ j, |gridAngle ζ j| ≤ η) →
            ‖gridAvg (fun k : Torus d L =>
                gridResolvent E t r k * gridResolvent E t r (ζ - k))‖ ≤
              C * Real.log (2 / t)

/-- The absolute product at grid frequencies bounded below is `O(log²)`. -/
def LargeSymbolStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ a₀ B : ℝ, 0 < a₀ → a₀ ≤ B → ∀ η : ℝ, 0 < η →
    ∃ C t₁ : ℝ, 0 < C ∧ 0 < t₁ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
        ∀ E : ℝ, 1 / 400 ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 → ∀ r ∈ rectangle a₀ B,
          ∀ ζ : Torus d L, (∃ j, η ≤ |gridAngle ζ j|) →
            gridAvgReal (fun k : Torus d L =>
                ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) ≤
              C * Real.log (2 / t) ^ 2

/-- Stronger form with the explicit inverse-displacement decay (paper eq.
`initial-absolute-product`): for every coordinate `j₀` with a nonzero grid angle,
the absolute product is `O(log² / |θ_{j₀}|)`. Same route as `LargeSymbolStatement`
(the joint shell gives `V = C/|θ_{j₀}|` for any such `j₀`; the cut-off part is
`O(log) ≤ O(π log / |θ_{j₀}|)`). It implies `LargeSymbolStatement` and is what
the comparators need at `|ζ| ≥ √t`. -/
def LargeSymbolDecayStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ a₀ B : ℝ, 0 < a₀ → a₀ ≤ B →
    ∃ C t₁ : ℝ, 0 < C ∧ 0 < t₁ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
        ∀ E : ℝ, 1 / 400 ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 → ∀ r ∈ rectangle a₀ B,
          ∀ (ζ : Torus d L) (j₀ : Fin d), gridAngle ζ j₀ ≠ 0 →
            gridAvgReal (fun k : Torus d L =>
                ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) ≤
              C * Real.log (2 / t) ^ 2 / |gridAngle ζ j₀|

/-- The decay form implies the fixed-`η` form. -/
theorem largeSymbol_of_decay (h : LargeSymbolDecayStatement) : LargeSymbolStatement := by
  intro d hd a₀ B ha₀ haB η hη
  obtain ⟨C, t₁, hC, ht₁, hb⟩ := h d hd a₀ B ha₀ haB
  refine ⟨C / η, t₁, by positivity, ht₁, ?_⟩
  intro t ht htt L _ hL hE hLb E hE1 hE2 r hr ζ ⟨j, hj⟩
  have hne : gridAngle ζ j ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hj; linarith
  refine (hb t ht htt L hL hE hLb E hE1 hE2 r hr ζ j hne).trans ?_
  have hpos : 0 < |gridAngle ζ j| := abs_pos.mpr hne
  rw [div_le_iff₀ hpos]
  have h0 : 0 ≤ C * Real.log (2 / t) ^ 2 := by positivity
  calc C * Real.log (2 / t) ^ 2 = C / η * Real.log (2 / t) ^ 2 * η := by field_simp
    _ ≤ C / η * Real.log (2 / t) ^ 2 * |gridAngle ζ j| :=
        mul_le_mul_of_nonneg_left hj (by positivity)

/-! ### Window-parametric forms (needed for the comparators at every `e₂`)

Same statements with the lower window edge `1/400` replaced by an arbitrary `w > 0`
(constants may depend on `w`); the proofs are the same with excess range
`[w/2, 3/200]` and `t₁ ≤ w/(2B)`. -/

def SmallSymbolWStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ w : ℝ, 0 < w → ∀ a₀ B : ℝ, 0 < a₀ → a₀ ≤ B →
    ∃ η C t₁ : ℝ, 0 < η ∧ 0 < C ∧ 0 < t₁ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
        ∀ E : ℝ, w ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 → ∀ r ∈ rectangle a₀ B,
          ∀ ζ : Torus d L, (∀ j, |gridAngle ζ j| ≤ η) →
            ‖gridAvg (fun k : Torus d L =>
                gridResolvent E t r k * gridResolvent E t r (ζ - k))‖ ≤
              C * Real.log (2 / t)

def LargeSymbolDecayWStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ w : ℝ, 0 < w → ∀ a₀ B : ℝ, 0 < a₀ → a₀ ≤ B →
    ∃ C t₁ : ℝ, 0 < C ∧ 0 < t₁ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
        ∀ E : ℝ, w ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 → ∀ r ∈ rectangle a₀ B,
          ∀ (ζ : Torus d L) (j₀ : Fin d), gridAngle ζ j₀ ≠ 0 →
            gridAvgReal (fun k : Torus d L =>
                ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) ≤
              C * Real.log (2 / t) ^ 2 / |gridAngle ζ j₀|

theorem smallSymbol_of_W (h : SmallSymbolWStatement) : SmallSymbolStatement :=
  fun d hd => h d hd (1 / 400) (by norm_num)

theorem largeSymbolDecay_of_W (h : LargeSymbolDecayWStatement) : LargeSymbolDecayStatement :=
  fun d hd => h d hd (1 / 400) (by norm_num)

def LargeSymbolWStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ w : ℝ, 0 < w → ∀ a₀ B : ℝ, 0 < a₀ → a₀ ≤ B → ∀ η : ℝ, 0 < η →
    ∃ C t₁ : ℝ, 0 < C ∧ 0 < t₁ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₁ → ∀ (L : ℕ) [NeZero L], 4 ≤ L → Even L → t⁻¹ ^ 8 ≤ (L : ℝ) →
        ∀ E : ℝ, w ≤ E + 2 * d → E + 2 * d ≤ 1 / 100 → ∀ r ∈ rectangle a₀ B,
          ∀ ζ : Torus d L, (∃ j, η ≤ |gridAngle ζ j|) →
            gridAvgReal (fun k : Torus d L =>
                ‖gridResolvent E t r k‖ * ‖gridResolvent E t r (ζ - k)‖) ≤
              C * Real.log (2 / t) ^ 2

theorem largeSymbolW_of_decayW (h : LargeSymbolDecayWStatement) : LargeSymbolWStatement := by
  intro d hd w hw a₀ B ha₀ haB η hη
  obtain ⟨C, t₁, hC, ht₁, hb⟩ := h d hd w hw a₀ B ha₀ haB
  refine ⟨C / η, t₁, by positivity, ht₁, ?_⟩
  intro t ht htt L _ hL hE hLb E hE1 hE2 r hr ζ ⟨j, hj⟩
  have hne : gridAngle ζ j ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hj; linarith
  refine (hb t ht htt L hL hE hLb E hE1 hE2 r hr ζ j hne).trans ?_
  have hpos : 0 < |gridAngle ζ j| := abs_pos.mpr hne
  rw [div_le_iff₀ hpos]
  have h0 : 0 ≤ C * Real.log (2 / t) ^ 2 := by positivity
  calc C * Real.log (2 / t) ^ 2 = C / η * Real.log (2 / t) ^ 2 * η := by field_simp
    _ ≤ C / η * Real.log (2 / t) ^ 2 * |gridAngle ζ j| :=
        mul_le_mul_of_nonneg_left hj (by positivity)

end AndersonAC.S3
