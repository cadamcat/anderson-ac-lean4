import AndersonAC.AgentS6Row.CoefficientMoments

noncomputable section

namespace AndersonAC.AgentS6Row

/-- Uniform constant after the five error terms in the row bias expansion are collected. -/
def biasConstant (c R V M K : ℝ) : ℝ := R + 4 + 36 * K + 16 * V + 8 * M + 32 * M / c + 1

lemma biasConstant_pos {c R V M K : ℝ} (hc : 0 < c) (hR : 0 ≤ R) (hV : 0 ≤ V)
    (hM : 0 ≤ M) (hK : 0 ≤ K) : 0 < biasConstant c R V M K := by
  unfold biasConstant
  positivity

lemma row_bias_arithmetic {t l c R V M K a ε v z : ℝ} (ht : 0 < t) (hl : 0 ≤ l)
    (hc : 0 < c) (hR : 0 ≤ R) (hV : 0 ≤ V) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (ha : 0 ≤ a) (hv : 0 ≤ v) (hs : Real.sqrt t ≤ 1)
    (haε : a ≤ ε) (hsε : Real.sqrt t ≤ ε)
    (hz : |z| ≤ R * (l ^ 2 * v / Real.sqrt t + l ^ 3 / t) +
      4 * l * v ^ 2 + 16 * V * l ^ 2 * ε +
      (4 * l * v ^ 2 + 32 * l ^ 2) * (K * Real.sqrt t) +
      2 * (M * Real.sqrt t * a) * (4 * l * v + 16 * l ^ 2 / (Real.sqrt t * c))) :
    |z| ≤ biasConstant c R V M K * l *
      (Real.sqrt t * a * v + v ^ 2 + l * ε + l * v / Real.sqrt t + l ^ 2 / t) := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hε : 0 ≤ ε := hs0.le.trans hsε
  let L := biasConstant c R V M K
  have hL1 : 8 * M ≤ L := by
    dsimp [L, biasConstant]
    have hh : 0 ≤ 32 * M / c := by positivity
    linarith
  have hL2 : 4 + 4 * K ≤ L := by
    dsimp [L, biasConstant]
    have hh : 0 ≤ 32 * M / c := by positivity
    linarith
  have hL3 : 16 * V + 32 * K + 32 * M / c ≤ L := by
    dsimp [L, biasConstant]
    linarith
  have hL4 : R ≤ L := by
    dsimp [L, biasConstant]
    have hh : 0 ≤ 32 * M / c := by positivity
    linarith
  have hexpand : R * (l ^ 2 * v / Real.sqrt t + l ^ 3 / t) +
      4 * l * v ^ 2 + 16 * V * l ^ 2 * ε +
      (4 * l * v ^ 2 + 32 * l ^ 2) * (K * Real.sqrt t) +
      2 * (M * Real.sqrt t * a) * (4 * l * v + 16 * l ^ 2 / (Real.sqrt t * c)) =
      8 * M * (l * Real.sqrt t * a * v) +
      4 * l * v ^ 2 + 4 * K * Real.sqrt t * (l * v ^ 2) +
      16 * V * (l ^ 2 * ε) + 32 * K * (l ^ 2 * Real.sqrt t) +
      (32 * M / c) * (l ^ 2 * a) +
      R * (l ^ 2 * v / Real.sqrt t) + R * (l ^ 3 / t) := by
    field_simp
    ring
  have hquad : 4 * K * Real.sqrt t * (l * v ^ 2) ≤ 4 * K * (l * v ^ 2) := by
    calc
      _ = (4 * K * (l * v ^ 2)) * Real.sqrt t := by ring
      _ ≤ (4 * K * (l * v ^ 2)) * 1 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have heps1 : 32 * K * (l ^ 2 * Real.sqrt t) ≤ 32 * K * (l ^ 2 * ε) := by gcongr
  have heps2 : (32 * M / c) * (l ^ 2 * a) ≤ (32 * M / c) * (l ^ 2 * ε) := by gcongr
  have h1 := mul_le_mul_of_nonneg_right hL1 (show 0 ≤ l * Real.sqrt t * a * v by positivity)
  have h2 := mul_le_mul_of_nonneg_right hL2 (show 0 ≤ l * v ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_right hL3 (show 0 ≤ l ^ 2 * ε by positivity)
  have h4 := mul_le_mul_of_nonneg_right hL4 (show 0 ≤ l ^ 2 * v / Real.sqrt t by positivity)
  have h5 := mul_le_mul_of_nonneg_right hL4 (show 0 ≤ l ^ 3 / t by positivity)
  rw [hexpand] at hz
  change |z| ≤ L * l * _
  calc
    _ ≤ 8 * M * (l * Real.sqrt t * a * v) + (4 + 4 * K) * (l * v ^ 2) +
        (16 * V + 32 * K + 32 * M / c) * (l ^ 2 * ε) +
        R * (l ^ 2 * v / Real.sqrt t) + R * (l ^ 3 / t) := by
          linarith only [hz, hquad, heps1, heps2]
    _ ≤ L * (l * Real.sqrt t * a * v) + L * (l * v ^ 2) + L * (l ^ 2 * ε) +
        L * (l ^ 2 * v / Real.sqrt t) + L * (l ^ 3 / t) := by
          linarith only [h1, h2, h3, h4, h5]
    _ = _ := by ring

end AndersonAC.AgentS6Row
