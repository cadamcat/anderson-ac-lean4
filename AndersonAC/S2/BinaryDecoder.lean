import AndersonAC.S2.BinaryLaws

/-! A measurable binary convention and its almost-sure inverse identities. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace AndersonAC.SolS2
open AndersonAC.S2

def binaryDigit (x : ℝ) : Bool := if 0 ≤ x then true else false

def binaryResidual : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => binaryResidual n x -
      1 / (2 : ℝ) ^ (n + 1) * signValue (binaryDigit (binaryResidual n x))

def binaryDecode (x : ℝ) : ℕ → Bool := fun n => binaryDigit (binaryResidual n x)

theorem binaryDigit_measurable : Measurable binaryDigit :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem binaryResidual_measurable (n : ℕ) : Measurable (binaryResidual n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
      exact ih.sub (measurable_const.mul
        ((measurable_of_finite signValue).comp (binaryDigit_measurable.comp ih)))

theorem binaryDecode_measurable : Measurable binaryDecode :=
  Measurable.of_eval fun n => binaryDigit_measurable.comp (binaryResidual_measurable n)

theorem binarySuffix_succ (c : ℝ) (n : ℕ) (a : ℕ → Bool) :
    binarySuffix c n a = c / (2 : ℝ) ^ (n + 1) * signValue (a n) +
      binarySuffix c (n + 1) a := by
  have hp : binaryPrefix c (n + 1) a = binaryPrefix c n a +
      c / (2 : ℝ) ^ (n + 1) * signValue (a n) := by
    simp only [binaryPrefix, Finset.sum_range_succ]
  have h₁ := binary_prefix_suffix c n a
  have h₂ := binary_prefix_suffix c (n + 1) a
  rw [hp] at h₂
  linarith

theorem binaryDigit_suffix (n : ℕ) (a : ℕ → Bool)
    (ha : binarySuffix 1 n a ≠ 0) : binaryDigit (binarySuffix 1 n a) = a n := by
  have hb := (abs_le.mp (binarySuffix_bound 1 (n + 1) a))
  norm_num only [abs_one] at hb
  have hs := binarySuffix_succ 1 n a
  cases hd : a n with
  | false =>
      simp only [hd, signValue, Bool.false_eq_true, ↓reduceIte, mul_neg_one] at hs
      have hneg : binarySuffix 1 n a < 0 := by
        have hle : binarySuffix 1 n a ≤ 0 := by linarith [hb.2]
        exact lt_of_le_of_ne hle ha
      simp [binaryDigit, not_le.mpr hneg]
  | true =>
      simp only [hd, signValue, ↓reduceIte, mul_one] at hs
      have hnonneg : 0 ≤ binarySuffix 1 n a := by linarith [hb.1]
      simp [binaryDigit, hnonneg]

theorem binarySuffix_ne_zero_ae (n : ℕ) :
    ∀ᵐ a ∂AuxiliaryLaw, binarySuffix 1 n a ≠ 0 := by
  have hz : uniformInterval (1 / (2 : ℝ) ^ n) {0} = 0 := by
    simp [uniformInterval]
  rw [← binary_suffix_uniform (by norm_num : (0 : ℝ) < 1) n,
    Measure.map_apply (binarySuffix_measurable 1 n) (measurableSet_singleton 0)] at hz
  change AuxiliaryLaw {a | binarySuffix 1 n a = 0} = 0 at hz
  simpa only [ae_iff, not_not] using hz

theorem binaryDecode_left_inverse_ae :
    ∀ᵐ a ∂AuxiliaryLaw, binaryDecode (binaryValue 1 a) = a := by
  have hgood : ∀ᵐ a ∂AuxiliaryLaw, ∀ n, binarySuffix 1 n a ≠ 0 :=
    ae_all_iff.mpr binarySuffix_ne_zero_ae
  filter_upwards [hgood] with a ha
  have hr : ∀ n, binaryResidual n (binaryValue 1 a) = binarySuffix 1 n a := by
    intro n
    induction n with
    | zero => simp [binaryResidual, binarySuffix, binaryValue]
    | succ n ih =>
        rw [binaryResidual, ih, binaryDigit_suffix n a (ha n)]
        have hs := binarySuffix_succ 1 n a
        linarith
  funext n
  exact (congrArg binaryDigit (hr n)).trans (binaryDigit_suffix n a (ha n))

end AndersonAC.SolS2

namespace AndersonAC.S2
open AndersonAC.SolS2

theorem binary_decoder : ∃ decode : ℝ → (ℕ → Bool), Measurable decode ∧
    (∀ᵐ a ∂AuxiliaryLaw, decode (binaryValue 1 a) = a) ∧
    (uniformInterval 1).map decode = AuxiliaryLaw ∧
    ∀ᵐ x ∂uniformInterval 1, binaryValue 1 (decode x) = x := by
  refine ⟨binaryDecode, binaryDecode_measurable, binaryDecode_left_inverse_ae, ?_, ?_⟩
  · rw [← binary_uniform (by norm_num : (0 : ℝ) < 1),
      Measure.map_map binaryDecode_measurable (binaryValue_measurable 1)]
    have hcomp : binaryDecode ∘ binaryValue 1 =ᵐ[AuxiliaryLaw] id :=
      binaryDecode_left_inverse_ae
    rw [Measure.map_congr hcomp, Measure.map_id]
  · rw [← binary_uniform (by norm_num : (0 : ℝ) < 1)]
    apply (ae_map_iff (binaryValue_measurable 1).aemeasurable
      (measurableSet_eq_fun ((binaryValue_measurable 1).comp binaryDecode_measurable)
        measurable_id)).mpr
    filter_upwards [binaryDecode_left_inverse_ae] with a ha
    exact congrArg (binaryValue 1) ha

end AndersonAC.S2
