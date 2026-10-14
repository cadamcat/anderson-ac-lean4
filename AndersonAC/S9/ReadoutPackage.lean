import AndersonAC.S9Inf.AllSitesProof
import AndersonAC.S9Basis.Join
import AndersonAC.S9Kern.CompactMomentKernel
import AndersonAC.Blueprint.Interfaces

noncomputable section

open MeasureTheory Filter OAI.Anderson
open scoped Topology ENNReal

namespace AndersonAC.SolS9

noncomputable def resolvedAnderson (S : AndersonAC.Blueprint.SpectralInput)
    (d : ℕ) (coupling : ℝ) : AndersonAC.S9.ResolvedAnderson d coupling where
  resolved ω := (S d (hamiltonian coupling ω)
    (hamiltonian_isSelfAdjoint coupling ω)).some
  measure_measurable x A hA :=
    BasisMeasureMeasurableJoin_proof CompactMomentKernelInput_proof d coupling
      (fun ω => (S d (hamiltonian coupling ω)
        (hamiltonian_isSelfAdjoint coupling ω)).some.spectral) x A hA

private def normalizedBounds (k : ℕ) (hk : 0 < k) : AndersonAC.S9.CertificateBounds where
  B := k
  pMin := 1 / (k : ℝ)
  pMax := k
  qMin := 1 / (k : ℝ)
  B_nonneg := Nat.cast_nonneg k
  pMin_pos := one_div_pos.mpr (by exact_mod_cast hk)
  pMin_le_pMax := by
    have h : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_of_lt hk)
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one h)).mpr
    nlinarith
  qMin_pos := one_div_pos.mpr (by exact_mod_cast hk)

theorem scaleHeight_comparable_proof (u : ℝ) (hu : 0 < u) :
    AndersonAC.S9.comparableHeights (fun m => scaleHeight m u) := by
  refine ⟨fun m => div_pos hu (by positivity), u, u, hu, hu, ?_⟩
  exact Eventually.of_forall fun m => ⟨le_rfl, le_rfl⟩

theorem weakCertificates_half (d : ℕ) (coupling : ℝ) (I : Set ℝ)
    (h : AndersonAC.Blueprint.WeakCertificates d coupling I) :
    AndersonAC.S9.halfProbabilityCertificates d coupling I := by
  obtain ⟨k, n₀, u, hk, hu, heq, hcert⟩ := h
  refine ⟨normalizedBounds k hk, fun m => scaleHeight m u,
    scaleHeight_comparable_proof u (lt_trans (by norm_num) hu.1), ?_⟩
  intro E hE
  filter_upwards [hcert E hE] with m hm
  apply hm.trans (measure_mono ?_)
  intro ω hω
  obtain ⟨A, r, G, hcard, hr, hl, hh, hq⟩ := hω
  refine ⟨A, r, G, hcard, ?_, ?_, ?_, hq⟩
  · intro i hi
    refine ⟨(hr i hi).1, (hr i hi).2, ?_⟩
    exact (Complex.im_le_norm _).trans (hr i hi).1
  · simpa only [AndersonAC.S9.matrixCertificate, certificateMatrix, diagonalOn, heq] using hl
  · simpa only [AndersonAC.S9.matrixCertificate, certificateMatrix, diagonalOn, heq] using hh

open AndersonAC.S9 AndersonAC.SolS9Inf

theorem all_sites_positive_general (d : ℕ) (hd : 3 ≤ d) (coupling : ℝ) (hcoupling : 0 < coupling)
    (I : Set ℝ) (hI : MeasurableSet I) (R : ResolvedAnderson d coupling) (B : BoundaryTheory)
    (hcertificate : halfProbabilityCertificates d coupling I) :
    ∀ᵐ E ∂volume.restrict I,
      ∀ᵐ ω ∂disorderLaw d, allSitesPositive coupling E ω := by
  obtain ⟨bounds, η, hη, hcert⟩ := hcertificate
  let ε := min 1 (columnConstant bounds * coupling / 64)
  have hε : 0 < ε := lt_min (by norm_num)
    (div_pos (mul_pos (columnConstant_pos_proof bounds) hcoupling) (by norm_num))
  have hinfinite (E : ℝ) (hE : E ∈ I) :
      columnConstant bounds / 8 ≤ liminf (fun m => ∫ ω,
        truncatedReadout bounds ε (diagonalGreen coupling ω 0
          ((E : ℂ) + η m * Complex.I)).im ∂disorderLaw d) atTop := by
    apply infinite_root_readout_proof d hd coupling E ε bounds η hη hε
    filter_upwards [hcert E hE] with m hm
    exact finite_root_readout_proof d m coupling E (η m) ε hcoupling (hη.1 m)
      bounds hε le_rfl hm
  have hroot : ∀ᵐ E ∂volume.restrict I,
      0 < disorderLaw d {ω | positiveScalarBoundary coupling E 0 ω} := by
    filter_upwards [ae_restrict_mem hI,
      ae_restrict_of_ae (s := I) (boundaryGood_ae_energy coupling R.resolved B)]
      with E hE hgood
    exact boundary_positive_probability_proof d coupling E ε bounds η hη hε
      (hgood.mono (fun ω hω => hω.1 0)) (hinfinite E hE)
  exact all_sites_positive_ae_energy_of_root_probability (by omega) coupling hcoupling
    R.resolved B I hroot


end AndersonAC.SolS9

namespace AndersonAC.Blueprint.Packages

theorem readout : ReadoutInput := by
  intro S B A d hd coupling hc I hI hn hb hcert
  exact AndersonAC.SolS9.all_sites_positive_general d hd coupling hc I hI.measurableSet
    (AndersonAC.SolS9.resolvedAnderson S d coupling) B
    (AndersonAC.SolS9.weakCertificates_half d coupling I hcert)


end AndersonAC.Blueprint.Packages
