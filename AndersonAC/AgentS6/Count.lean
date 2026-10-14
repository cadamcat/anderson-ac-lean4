import AndersonAC.AgentS6.Potential
import AndersonAC.S6.CoreHeatStatements
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Heat-limit failure mode of Proposition 6.6 (06-clearing.tex:742–747, 1112–1115):
Lemma 6.5 (`HeatCountStatement`, explicit hypothesis until its proof is integrated) applied to
the stopped trial potential at `σ = 0`, plus the scalar margin `e_h > e_0 + ν`. -/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace AndersonAC.AgentS6

open AndersonAC.S6

universe u

/-- Scalar part: the restart tail at `n_h` is below a third of the target. -/
theorem count_scalar (d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 ≤ heatLimit t ∧
      2 * Real.exp (-Real.log 2 * (heatLimit t : ℝ) /
        (⌈10 * coreCap d t / leverageScale t⌉₊ : ℝ)) ≤
        (1 / 3) * Real.exp (-t ^ (-clearingExponent d)) := by
  have hκ := clearingExponent_pos d hd
  have hu : Tendsto (fun t : ℝ => t ^ (-clearingExponent d)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have hnu0 := nu_nonneg d
  filter_upwards [heat_limit_margin d hd, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    hu.eventually (eventually_ge_atTop 8)] with t hmarg ht hu8
  obtain ⟨ht0, ht1⟩ := ht
  set u := t ^ (-clearingExponent d) with hudef
  set N : ℝ := (heatLimit t : ℝ)
  set l := leverageScale t
  set rr := coreCap d t
  have hl : 0 < l := Real.rpow_pos_of_pos ht0 _
  have hl1 : l ≤ 1 := Real.rpow_le_one ht0.le ht1.le (by unfold e0 delta; norm_num)
  have hrr1 : 1 ≤ rr := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1.le (by linarith)
  set X := rr / l with hX
  have hX1 : 1 ≤ X := by rw [hX, le_div_iff₀ hl]; linarith
  have hu4 : t ^ (-(eh - e0 - nu d)) = u ^ 4 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    congr 1; unfold clearingExponent; push_cast; ring
  have hNX : u ^ 4 / 2 ≤ N / X := by
    have : N * l / rr = N / X := by rw [hX]; field_simp
    rw [← this]; linarith [hmarg]
  have hX0 : 0 < X := by linarith
  have hu4' : 8 * 8 * 8 * u ≤ u ^ 4 := by
    have h1 : 8 ≤ u := hu8
    nlinarith [mul_le_mul h1 h1 (by norm_num) (by linarith), sq_nonneg u]
  have hN : 256 * u * X ≤ N := by
    have := (le_div_iff₀ hX0).mp hNX
    nlinarith
  refine ⟨?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ (heatLimit t : ℝ) := by nlinarith
    exact_mod_cast h1
  · set Q : ℝ := (⌈10 * rr / l⌉₊ : ℝ)
    have hQ1 : Q < 10 * rr / l + 1 := Nat.ceil_lt_add_one (by positivity)
    have hQ0 : 10 * rr / l ≤ Q := Nat.le_ceil _
    have h10 : 10 * rr / l = 10 * X := by rw [hX]; ring
    have hQpos : 0 < Q := by linarith
    have hQX : Q ≤ 11 * X := by linarith
    have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hlog6 : Real.log 6 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num); linarith
    have hkey : u + Real.log 6 ≤ Real.log 2 * N / Q := by
      rw [le_div_iff₀ hQpos]
      have h1 : Real.log 2 * (256 * u * X) ≤ Real.log 2 * N :=
        mul_le_mul_of_nonneg_left hN (by linarith)
      have h2 : (u + Real.log 6) * Q ≤ (u + 5) * (11 * X) :=
        mul_le_mul (by linarith) hQX hQpos.le (by linarith)
      have hux : 0 ≤ u * X := by positivity
      have h3 : (0.69 : ℝ) * (u * X) ≤ Real.log 2 * (u * X) :=
        mul_le_mul_of_nonneg_right hlog2.le hux
      have h4 : 8 * X ≤ u * X := mul_le_mul_of_nonneg_right hu8 hX0.le
      have h5 : (u + 5) * (11 * X) ≤ Real.log 2 * (256 * u * X) := by nlinarith
      linarith
    have hexp : Real.exp (-Real.log 2 * N / Q) ≤ Real.exp (-(u + Real.log 6)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_mul, neg_div]; linarith
    have hsplit : Real.exp (-(u + Real.log 6)) = Real.exp (-u) / 6 := by
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 6), Real.exp_log (by norm_num)]
      ring
    rw [hsplit] at hexp
    linarith

/-- The heat-limit failure mode, given Lemma 6.5. -/
theorem countTail_of_heatCount (hHC : AndersonAC.SolS6.HeatCountStatement.{u})
    {Ω : Type u} [MeasurableSpace Ω] (d : ℕ) (hd : 3 ≤ d) (c K Cloc cConc : ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (qlag ε : ℝ → ℝ)
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0)) (hεpos : ∀ t, 0 ≤ ε t) :
    ModeTail d c K Cloc cConc μ qlag ε countMode := by
  intro _hWard
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ε t ≤ 1 / 20 ∧ (1 ≤ heatLimit t ∧
      2 * Real.exp (-Real.log 2 * (heatLimit t : ℝ) /
        (⌈10 * coreCap d t / leverageScale t⌉₊ : ℝ)) ≤
        (1 / 3) * Real.exp (-t ^ (-clearingExponent d))) := by
    filter_upwards [hε.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 20 by norm_num)),
      count_scalar d hd] with t h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨t0, ht0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨t0, ht0, ?_⟩
  intro n core t r g0 order q dist collapsed ell htt hyp
  obtain ⟨hεt, hN1, hscal⟩ := hsub ⟨hyp.t_pos, htt⟩
  have hl : 0 < leverageScale t := Real.rpow_pos_of_pos hyp.t_pos _
  have hrr : 0 < coreCap d t := Real.rpow_pos_of_pos hyp.t_pos _
  have hinput := stoppedPotential q hyp (hεpos t) hεt
  have hσ : IsStoppingTime q.history (fun ω => (((fun _ : Ω => (0 : ℕ)) ω : ℕ) : WithTop ℕ)) :=
    isStoppingTime_const q.history 0
  have hcount := hHC Ω μ q.history (leverageScale t) (coreCap d t) (heatLimit t) q.stop
    (fun _ => 0) (phi q (leverageScale t)) hl hrr hinput hσ
  have htail := hcount.2 (heatLimit t) hN1
  have hms : hσ.measurableSpace = q.history 0 := IsStoppingTime.measurableSpace_const _ _
  refine ⟨{ω | heatLimit t ≤ q.stop ω}, ?_, fun ω h => le_of_eq h.symm, ?_⟩
  · have hm := q.history.le (heatLimit t - 1) _ (q.stopping (heatLimit t - 1)).compl
    convert hm using 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro h h'
      have := (WithTop.coe_le_coe.mp h' : q.stop ω ≤ heatLimit t - 1); omega
    · intro h
      by_contra h''
      exact h (WithTop.coe_le_coe.mpr (show q.stop ω ≤ heatLimit t - 1 by omega))
  · rw [hms] at htail
    filter_upwards [htail] with ω hω
    simp only [Nat.sub_zero] at hω
    exact hω.trans hscal

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.count_scalar
#print axioms AndersonAC.AgentS6.countTail_of_heatCount
