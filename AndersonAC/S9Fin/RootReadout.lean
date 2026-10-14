import AndersonAC.S9Fin.Torus

noncomputable section
open MeasureTheory OAI.Anderson AndersonAC.S9
open scoped ENNReal

namespace AndersonAC.SolS9

/-- The final c*/8 arithmetic, with the two still-needed finite estimates
exposed as hypotheses. Translation invariance is already proved. -/
lemma finite_root_readout_of_estimates (d m : ℕ) (coupling E η ε : ℝ)
    (hcoupling : 0 < coupling) (hη : 0 < η) (b : CertificateBounds)
    (hε : 0 < ε) (hεsmall : ε ≤ min 1 (columnConstant b * coupling / 64))
    (hcert : (1 / 2 : ℝ≥0∞) ≤ torusLaw d m (trueCertificateEvent d m coupling E η b))
    (hH : ∀ ω : TorusConfiguration d m, (periodicHamiltonian coupling ω).IsHermitian)
    (hAverage :
      columnConstant b / 2 * (torusLaw d m (trueCertificateEvent d m coupling E η b)).toReal -
        8 * (∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E (ε * η) : ℝ)
          ∂torusLaw d m) / (η * Fintype.card (Torus d m)) ≤
        ∫ ω, (∑ i, truncatedReadout b ε (scalarQ (periodicHamiltonian coupling ω) E η i)) /
          Fintype.card (Torus d m) ∂torusLaw d m)
    (hWegner :
      (∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E (ε * η) : ℝ)
        ∂torusLaw d m) ≤ (Fintype.card (Torus d m) : ℝ) * (ε * η) / coupling) :
    columnConstant b / 8 ≤ ∫ ω, truncatedReadout b ε
      (scalarQ (periodicHamiltonian coupling ω) E η 0) ∂torusLaw d m := by
  let p := (torusLaw d m (trueCertificateEvent d m coupling E η b)).toReal
  let N : ℝ := Fintype.card (Torus d m)
  let R := ∫ ω, (windowRank (periodicHamiltonian coupling ω) (hH ω) E (ε * η) : ℝ)
    ∂torusLaw d m
  have hp : (1 / 2 : ℝ) ≤ p := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hcert
    simpa using hh
  have hN : 0 < N := by
    change 0 < (Fintype.card (Torus d m) : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Torus d m))
  have hc := columnConstant_pos_proof b
  have hP : columnConstant b / 4 ≤ columnConstant b / 2 * p := by
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ columnConstant b / 2)]
  have hR : 8 * R / (η * N) ≤ 8 * ε / coupling := by
    calc
      8 * R / (η * N) ≤ 8 * (N * (ε * η) / coupling) / (η * N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hWegner (by norm_num))
          (mul_pos hη hN).le
      _ = 8 * ε / coupling := by field_simp [hcoupling.ne', hη.ne', hN.ne']
  have hεC : 8 * ε / coupling ≤ columnConstant b / 8 := by
    apply (div_le_iff₀ hcoupling).mpr
    have hs := hεsmall.trans (min_le_right 1 (columnConstant b * coupling / 64))
    nlinarith
  rw [torus_root_expectation_proof] at hAverage
  change columnConstant b / 2 * p - 8 * R / (η * N) ≤ _ at hAverage
  linarith

end AndersonAC.SolS9
