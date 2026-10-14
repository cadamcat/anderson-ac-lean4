import AndersonAC.Blueprint.Transport

/-!
The assembly is conditional and contains no holes. Its only mathematical
hypotheses are the named package contracts. It does not import Interfaces,
so its axiom audit is independent of the allowed interface holes there.
-/

noncomputable section
open MeasureTheory OAI.Anderson

namespace AndersonAC.Blueprint

theorem dimensionThreshold {d : ℕ} {e₂ : ℝ}
    (hcert : ∃ k : ℕ, windowThreshold d e₂ k) :
    ∃ bound : ℝ, 0 < bound ∧ (4 ≤ d → finiteBoxThreshold d bound) ∧
      ∀ coupling : ℝ, 0 < coupling → coupling < bound →
        WeakCertificates d coupling (energyWindow d e₂) := by
  obtain ⟨k, hk⟩ := hcert
  by_cases hd : 4 ≤ d
  · have hex : ∃ j : ℕ, thresholdCriterion d j :=
      ⟨k, (windowThreshold_iff_of_four_le hd e₂ k).mp hk⟩
    obtain ⟨bound, hbound⟩ := (finiteBoxThreshold_exists_iff d).mpr hex
    refine ⟨bound, finiteBoxThreshold_pos hbound, fun _ => hbound, ?_⟩
    obtain ⟨j, hj, heq⟩ := hbound
    intro coupling hc hb
    apply weakCertificates_of_windowThreshold
      ((windowThreshold_iff_of_four_le hd e₂ j).mpr hj.1) hc
    simpa only [heq] using hb
  · refine ⟨Real.sqrt 3 / (2 : ℝ) ^ k, by positivity, ?_, ?_⟩
    · intro h4
      exact False.elim (hd h4)
    · intro coupling hc hb
      exact weakCertificates_of_windowThreshold hk hc hb

/-- Exact Theorem 1.1 assembly from true-variable certificate and §9 contracts. -/
theorem paperTheorem_of_packages {e₂ : ℝ} (he : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100))
    (hcert : CertificateFamily e₂) (hsp : SpectralInput) (hbd : BoundaryInput)
    (hav : AveragingInput) (hread : ReadoutInput) (hpure : PurityInput) :
    PaperTheorem := by
  refine ⟨e₂, he, ?_⟩
  intro d hd
  obtain ⟨bound, hb, hintrinsic, hc⟩ := dimensionThreshold (hcert d hd)
  refine ⟨bound, hb, hintrinsic, ?_⟩
  intro coupling hcoupling hsmall
  have hopen := energyWindow_open d e₂
  have hnonempty := energyWindow_nonempty (d := d) he.1
  have hbounded := energyWindow_bounded d e₂
  have hpositive := hread hsp hbd hav d hd coupling hcoupling (energyWindow d e₂)
    hopen hnonempty hbounded (hc coupling hcoupling hsmall)
  exact hpure hsp hbd hav d hd coupling hcoupling (energyWindow d e₂)
    hopen hnonempty hbounded hpositive

theorem ae_map_of_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → β} (hf : MeasurableEmbedding f) {p : β → Prop}
    (h : ∀ᵐ x ∂μ, p (f x)) : ∀ᵐ y ∂μ.map f, p y := by
  rw [ae_iff] at h ⊢
  rw [hf.map_apply]
  exact h

/-- Law, operator, and spectral transports close Simon's positive-hopping,
unscaled uniform `[a,b]` formulation for every d≥3 and every positive width
below `2*bound`. The interval is translated only by the scalar center. -/
theorem simonProblem_of_paper (hpaper : PaperTheorem) (hlaw : LawTransportInput)
    (hsign : SignTransportInput) (htransport : SpectralTransportInput) :
    SimonProblem := by
  obtain ⟨e₂, he, hdim⟩ := hpaper
  intro d hd
  obtain ⟨bound, hb, _, hcoupling⟩ := hdim d hd
  obtain ⟨E₁, E₂, hE, hwin⟩ := energyWindow_eq_Ioo d he.1
  refine ⟨2 * bound, E₁, E₂, by positivity, hE, ?_⟩
  rw [← hwin]
  intro a b hab hwidth
  have hcouplingPos : 0 < intervalCoupling a b := by unfold intervalCoupling; linarith
  have hcouplingSmall : intervalCoupling a b < bound := by unfold intervalCoupling; linarith
  obtain ⟨U, hU⟩ := hsign d
  obtain ⟨hembed, hmap⟩ := hlaw d a b hab
  rw [← hmap]
  apply ae_map_of_embedding hembed
  filter_upwards [hcoupling (intervalCoupling a b) hcouplingPos hcouplingSmall] with ω hAC
  obtain ⟨M, hM, hV, hop⟩ := hU a b ω
  refine ⟨M, hM, hV, ?_⟩
  rw [hop]
  exact htransport d (hamiltonian (intervalCoupling a b) ω)
    (hamiltonian_isSelfAdjoint _ _) (intervalCenter a b) U (energyWindow d e₂) hAC

end AndersonAC.Blueprint
