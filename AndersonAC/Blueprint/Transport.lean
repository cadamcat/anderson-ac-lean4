import AndersonAC.Blueprint.SpectralInputs

noncomputable section
open MeasureTheory OAI.Anderson

namespace AndersonAC.Blueprint

def conjugate {d : ℕ} (U : StateSpace d ≃ₗᵢ[ℂ] StateSpace d) (T : Operator d) : Operator d :=
  U.toLinearIsometry.toContinuousLinearMap * T * U.symm.toLinearIsometry.toContinuousLinearMap

/-- An affine image is iid uniform on `[a,b]`; embedding permits almost-everywhere
transport even before measurability of the AC spectral event is established. -/
def LawTransportInput : Prop :=
  ∀ (d : ℕ) (a b : ℝ), a < b →
    MeasurableEmbedding (affineConfiguration (d := d) a b) ∧
    (disorderLaw d).map (affineConfiguration a b) = intervalLaw d a b

/-- The parity unitary is the same for all intervals and configurations.
The operator on the right is built directly from the transported potential. -/
def SignTransportInput : Prop :=
  ∀ d : ℕ, ∃ U : StateSpace d ≃ₗᵢ[ℂ] StateSpace d,
    ∀ (a b : ℝ) (ω : Configuration d), ∃ (M : ℝ) (hM : 0 ≤ M)
      (hV : ∀ x, |affineConfiguration a b ω x| ≤ M),
      simonHamiltonian (affineConfiguration a b ω) M hM hV =
        conjugate U (shiftedHamiltonian a b ω)

/-- A scalar shift translates the real spectrum, projections, and scalar
measures; unitary conjugation transports vectors and the AC subspace. -/
def SpectralTransportInput : Prop :=
  ∀ (d : ℕ) (T : Operator d), IsSelfAdjoint T →
    ∀ (c : ℝ) (U : StateSpace d ≃ₗᵢ[ℂ] StateSpace d) (I : Set ℝ),
      ACRegion T I →
        ACRegion (conjugate U (T + (c : ℂ) • (1 : Operator d))) (translateWindow c I)

theorem energyWindow_bounded (d : ℕ) (e₂ : ℝ) :
    Bornology.IsBounded (energyWindow d e₂) := by
  unfold energyWindow higherDimWindow
  split_ifs <;> exact Metric.isBounded_Ioo _ _

theorem translateWindow_Ioo (c a b : ℝ) :
    translateWindow c (Set.Ioo a b) = Set.Ioo (c + a) (c + b) := by
  ext E
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨by linarith [hF.1], by linarith [hF.2]⟩
  · intro hE
    exact ⟨E - c, ⟨by linarith [hE.1], by linarith [hE.2]⟩, by ring⟩

theorem translateWindow_energyWindow_open (d : ℕ) (e₂ c : ℝ) :
    IsOpen (translateWindow c (energyWindow d e₂)) := by
  unfold energyWindow higherDimWindow
  split_ifs <;> rw [translateWindow_Ioo] <;> exact isOpen_Ioo

theorem translateWindow_energyWindow_nonempty (d : ℕ) {e₂ : ℝ} (he : 0 < e₂) (c : ℝ) :
    (translateWindow c (energyWindow d e₂)).Nonempty :=
  (energyWindow_nonempty he).image _

theorem energyWindow_eq_Ioo (d : ℕ) {e₂ : ℝ} (he : 0 < e₂) :
    ∃ E₁ E₂ : ℝ, E₁ < E₂ ∧ energyWindow d e₂ = Set.Ioo E₁ E₂ := by
  unfold energyWindow higherDimWindow
  split_ifs
  · exact ⟨_, _, by linarith, rfl⟩
  · exact ⟨_, _, by norm_num, rfl⟩

end AndersonAC.Blueprint
