import AndersonAC.S78.Contraction
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open scoped Topology
open MeasureTheory Filter
set_option autoImplicit false

namespace AndersonAC.SolS78

/-- Jointly measurable contractions have a measurable fixed point in their
common closed ball. Measurability follows from their iterates from the center. -/
theorem measurable_fixedPoint_closedBall {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Ω → E → E) (r : E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hT : Measurable (Function.uncurry T))
    (hball : ∀ ω z, ‖z - r‖ ≤ ρ → ‖T ω z - r‖ ≤ ρ)
    (hcontract : ∀ ω z w, ‖z - r‖ ≤ ρ → ‖w - r‖ ≤ ρ →
      ‖T ω z - T ω w‖ ≤ (1 / 2 : ℝ) * ‖z - w‖) :
    ∃ ζ : Ω → E, Measurable ζ ∧ ∀ ω, ‖ζ ω - r‖ ≤ ρ ∧ T ω (ζ ω) = ζ ω := by
  have hex : ∀ ω, ∃ z, ‖z - r‖ ≤ ρ ∧ T ω z = z ∧
      Tendsto (fun n : ℕ => (T ω)^[n] r) atTop (𝓝 z) :=
    fun ω => fixedPoint_closedBall_with_iterates (T ω) r ρ hρ (hball ω) (hcontract ω)
  choose ζ hζ hfixed hlim using hex
  have hiter : ∀ n : ℕ, Measurable (fun ω => (T ω)^[n] r) := by
    intro n
    induction n with
    | zero => simpa only [Function.iterate_zero_apply] using (measurable_const : Measurable (fun _ : Ω => r))
    | succ n hn =>
        simpa only [Function.iterate_succ_apply', Function.comp_def, Function.uncurry, id_eq] using hT.comp (measurable_id.prodMk hn)
  have hm : Measurable ζ := measurable_of_tendsto_metrizable hiter (tendsto_pi_nhds.mpr hlim)
  exact ⟨ζ, hm, fun ω => ⟨hζ ω, hfixed ω⟩⟩

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.measurable_fixedPoint_closedBall
