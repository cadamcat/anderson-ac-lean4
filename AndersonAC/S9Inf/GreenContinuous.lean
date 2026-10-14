import AndersonAC.S9Inf.Nonvanishing

/-! Strong operator continuity gives continuity of the nonreal resolvent. -/

noncomputable section

open Filter OAI.Anderson
open scoped Topology

namespace AndersonAC.SolS9Inf

section Hilbert

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem inverse_difference_apply (A B : K →L[ℂ] K) (hA : IsUnit A) (hB : IsUnit B)
    (v : K) :
    Ring.inverse A v - Ring.inverse B v =
      Ring.inverse A ((B - A) (Ring.inverse B v)) := by
  apply unit_injective A hA
  rw [map_sub, unit_inverse_apply_left A hA, unit_inverse_apply_left A hA]
  simp only [ContinuousLinearMap.sub_apply, unit_inverse_apply_left B hB]

theorem continuous_green_of_strong {Ω : Type*} [TopologicalSpace Ω]
    (T : Ω → K →L[ℂ] K) (hT : ∀ ω, IsSelfAdjoint (T ω))
    (hstrong : ∀ v : K, Continuous (fun ω => T ω v))
    (z : Ω → ℂ) (hz : Continuous z) (hpos : ∀ ω, 0 < (z ω).im) (v : K) :
    Continuous (fun ω => green (T ω) (z ω) v) := by
  rw [continuous_iff_continuousAt]
  intro ω₀
  let q := green (T ω₀) (z ω₀) v
  let f := fun ω => (T ω₀ q - z ω₀ • q) - (T ω q - z ω • q)
  have hf : Continuous f :=
    continuous_const.sub ((hstrong q).sub (hz.smul continuous_const))
  have hlim : Tendsto (fun ω => ‖f ω‖ / (z ω).im) (𝓝 ω₀) (𝓝 0) := by
    have hn : Tendsto (fun ω => ‖f ω‖) (𝓝 ω₀) (𝓝 0) := by
      simpa [f] using hf.norm.tendsto ω₀
    have hi : Tendsto (fun ω => (z ω).im) (𝓝 ω₀) (𝓝 (z ω₀).im) :=
      (Complex.continuous_im.comp hz).tendsto ω₀
    convert hn.div hi (hpos ω₀).ne' using 1 <;> simp
  have hdiff (ω : Ω) : green (T ω) (z ω) v - q = green (T ω) (z ω) (f ω) := by
    simpa [green, q, f] using inverse_difference_apply
      (T ω - z ω • (1 : K →L[ℂ] K))
      (T ω₀ - z ω₀ • (1 : K →L[ℂ] K))
      (shifted_isUnit _ (hT ω) _ (hpos ω).ne')
      (shifted_isUnit _ (hT ω₀) _ (hpos ω₀).ne') v
  have hzero : Tendsto (fun ω => green (T ω) (z ω) v - q) (𝓝 ω₀) (𝓝 0) := by
    apply squeeze_zero_norm (fun ω => ?_) hlim
    rw [hdiff]
    exact norm_green_apply_le _ (hT ω) _ (hpos ω) _
  change Tendsto _ (𝓝 ω₀) (𝓝 _)
  simpa only [q] using (tendsto_sub_nhds_zero_iff.mp hzero)

end Hilbert

end AndersonAC.SolS9Inf
