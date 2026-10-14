import AndersonAC.S78.Definitions
import AndersonAC.S78Abort.Abort

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace AndersonAC.SolS78

open AndersonAC.S78

private lemma continuous_certificate_matrix (d n₀ m : ℕ) (u E : ℝ)
    (A : Finset (Torus d m)) :
    Continuous (fun p : OAI.Anderson.TorusConfiguration d m × (Torus d m → ℂ) ×
      Matrix (Torus d m) (Torus d m) ℂ =>
        OAI.Anderson.certificateMatrix n₀ m u E p.1 A p.2.1) := by
  unfold OAI.Anderson.certificateMatrix
  exact ((OAI.Anderson.continuous_periodicHamiltonian d m _).comp continuous_fst).sub
    continuous_const |>.sub
      (((OAI.Anderson.continuous_diagonalOn A).comp
        (continuous_fst.comp continuous_snd)).const_smul
          (OAI.Anderson.scaleHeight m u : ℂ))

/-- The event allowing arbitrary uniform bounds on the certificate witnesses is
measurable, by the same sigma-compact projection argument as OAI's event. -/
theorem bounded_certificate_event_measurable_proof
    (d n₀ m : ℕ) (u E Cr cp cg : ℝ) :
    MeasurableSet (boundedCertificateEvent d n₀ m u E Cr cp cg) := by
  classical
  let X := OAI.Anderson.TorusConfiguration d m × (Torus d m → ℂ) ×
    Matrix (Torus d m) (Torus d m) ℂ
  have : CompactSpace OAI.Anderson.SingleSite :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have : SigmaCompactSpace X := by
    change SigmaCompactSpace (OAI.Anderson.TorusConfiguration d m ×
      (Torus d m → ℂ) × (Torus d m → Torus d m → ℂ))
    infer_instance
  let C (A : Finset (Torus d m)) : Set X := {p |
    (∀ i ∈ A, ‖p.2.1 i‖ ≤ Cr ∧ cp ≤ (p.2.1 i).im) ∧
    OAI.Anderson.certificateMatrix n₀ m u E p.1 A p.2.1 * p.2.2 = 1 ∧
    p.2.2 * OAI.Anderson.certificateMatrix n₀ m u E p.1 A p.2.1 = 1 ∧
    (∀ i ∈ A, cg ≤ (p.2.2 i i).im)}
  have hClosed (A : Finset (Torus d m)) : IsClosed (C A) := by
    have hB : Continuous (fun p : X =>
        OAI.Anderson.certificateMatrix n₀ m u E p.1 A p.2.1) := by
      exact continuous_certificate_matrix d n₀ m u E A
    have hr : IsClosed {p : X | ∀ i ∈ A,
        ‖p.2.1 i‖ ≤ Cr ∧ cp ≤ (p.2.1 i).im} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro _
      have h₁ : IsClosed {p : X | ‖p.2.1 i‖ ≤ Cr} :=
        isClosed_le (by fun_prop) continuous_const
      have h₂ : IsClosed {p : X | cp ≤ (p.2.1 i).im} :=
        isClosed_le continuous_const (by fun_prop)
      exact h₁.inter h₂
    have hG : IsClosed {p : X | ∀ i ∈ A, cg ≤ (p.2.2 i i).im} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro _
      exact isClosed_le continuous_const (by fun_prop)
    have hGcont : Continuous (fun p : X => p.2.2) :=
      continuous_snd.comp continuous_snd
    exact hr.inter ((isClosed_eq (hB.mul hGcont) continuous_const).inter
      ((isClosed_eq (hGcont.mul hB) continuous_const).inter hG))
  have hProjection (A : Finset (Torus d m)) :
      MeasurableSet (Prod.fst '' C A) := by
    have hs : IsSigmaCompact (C A) :=
      isSigmaCompact_univ.of_isClosed_subset (hClosed A) (Set.subset_univ _)
    obtain ⟨K, hK, hEq⟩ := hs.image continuous_fst
    rw [← hEq]
    exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)
  have hEq : boundedCertificateEvent d n₀ m u E Cr cp cg =
      ⋃ A : Finset (Torus d m), ⋃ (_ : Fintype.card (Torus d m) ≤ 2 * A.card),
        Prod.fst '' C A := by
    ext ω
    simp only [boundedCertificateEvent, Set.mem_iUnion,
      Set.mem_image, Prod.exists, C]
    constructor
    · rintro ⟨A, r, G, hA, hr, hBG, hGB, hG⟩
      exact ⟨A, hA, ω, r, G, ⟨hr, hBG, hGB, hG⟩, rfl⟩
    · rintro ⟨A, hA, ω', r, G, ⟨hr, hBG, hGB, hG⟩, rfl⟩
      exact ⟨A, r, G, hA, hr, hBG, hGB, hG⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun A =>
    MeasurableSet.iUnion fun _ => hProjection A

/-- Quantitative certificate completion from measurable success, its pointwise
final certificate inclusion, the true marginal law, and the uniform abort
estimate. -/
theorem certificate_completion_proof {Ω : Type} [MeasurableSpace Ω]
    (d : ℕ) (hd : 3 ≤ d) (e₂ q C Cr cp cg : ℝ) (cutoff : ℕ)
    (hq : 0 < q) (hC : 0 ≤ C) (hcp : 0 < cp) (hcg : 0 < cg)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (trueConfig : ∀ m : ℕ, Ω → OAI.Anderson.TorusConfiguration d m)
    (hmap : ∀ m, Measurable (trueConfig m))
    (hlaw : ∀ m, μ.map (trueConfig m) = OAI.Anderson.torusLaw d m)
    (success : ℕ → ℕ → ℝ → ℝ → Set Ω)
    (hmeas : ∀ n₀ m u E, MeasurableSet (success n₀ m u E))
    (hfinal : ∀ n₀ m u E, cutoff ≤ n₀ → 4 * n₀ ≤ m →
      u ∈ Set.Ioc (1 / 4 : ℝ) 1 → E ∈ OAI.Anderson.energyWindow d e₂ →
      success n₀ m u E ⊆ (trueConfig m) ⁻¹'
        boundedCertificateEvent d n₀ m u E Cr cp cg)
    (habort : ∀ n₀ m u E, cutoff ≤ n₀ → 4 * n₀ ≤ m →
      u ∈ Set.Ioc (1 / 4 : ℝ) 1 → E ∈ OAI.Anderson.energyWindow d e₂ →
      μ (success n₀ m u E)ᶜ ≤ ENNReal.ofReal (abortBound d m q C)) :
    UniformCertificateInput d e₂ := by
  have _hd := hd
  obtain ⟨Nabort, hNabort⟩ :=
    AndersonAC.SolS78.uniform_abort_bound_proof d q C hq hC
  obtain ⟨Nexp, hNexp⟩ := exists_nat_gt (Real.log 2)
  refine ⟨max cutoff (max Nabort Nexp), Cr, cp, cg, hcp, hcg, ?_⟩
  intro n₀ m hn₀ hm u hu E hE
  have hcutoff : cutoff ≤ n₀ := by omega
  have habortN : Nabort ≤ n₀ := by omega
  have hexpN : Nexp ≤ n₀ := by omega
  have hnm : n₀ ≤ m := by omega
  have hlogN : Real.log 2 < (n₀ : ℝ) :=
    lt_of_lt_of_le hNexp (by exact_mod_cast hexpN)
  have hlogm : Real.log 2 < (m : ℝ) :=
    lt_of_lt_of_le hlogN (by exact_mod_cast hnm)
  have hExpHalf : Real.exp (-(m : ℝ)) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-(m : ℝ)) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hAbortHalf : abortBound d m q C ≤ (1 / 2 : ℝ) := by
    exact (hNabort n₀ m habortN hm).trans hExpHalf
  let S := success n₀ m u E
  let ev := boundedCertificateEvent d n₀ m u E Cr cp cg
  have hSmeas : MeasurableSet S := hmeas n₀ m u E
  have hScompl : μ S + μ Sᶜ = 1 := MeasureTheory.prob_add_prob_compl hSmeas
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hScomplHalf : μ Sᶜ ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      μ Sᶜ ≤ ENNReal.ofReal (abortBound d m q C) :=
        habort n₀ m u E hcutoff hm hu hE
      _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hAbortHalf
  have hhalfadd : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hScompl' : μ Sᶜ + μ S = 1 := by simpa [add_comm] using hScompl
  have hSprob : (1 / 2 : ENNReal) ≤ μ S := by
    rw [← hhalf]
    have hle : (1 : ENNReal) ≤ ENNReal.ofReal (1 / 2 : ℝ) + μ S := by
      calc
        (1 : ENNReal) = μ Sᶜ + μ S := hScompl'.symm
        _ ≤ ENNReal.ofReal (1 / 2 : ℝ) + μ S := add_le_add_left hScomplHalf _
    have hleft : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) ≤
        ENNReal.ofReal (1 / 2 : ℝ) + μ S := by
      calc
        ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := hhalfadd
        _ ≤ ENNReal.ofReal (1 / 2 : ℝ) + μ S := hle
    exact (ENNReal.add_le_add_iff_left
      (a := ENNReal.ofReal (1 / 2 : ℝ)) ENNReal.ofReal_ne_top).mp hleft
  have hevmeas : MeasurableSet ev :=
    bounded_certificate_event_measurable_proof d n₀ m u E Cr cp cg
  have hproject : μ ((trueConfig m) ⁻¹' ev) = OAI.Anderson.torusLaw d m ev := by
    rw [← hlaw m]
    exact (Measure.map_apply (hmap m) hevmeas).symm
  calc
    (1 / 2 : ENNReal) ≤ μ S := hSprob
    _ ≤ μ ((trueConfig m) ⁻¹' ev) := measure_mono (hfinal n₀ m u E hcutoff hm hu hE)
    _ = OAI.Anderson.torusLaw d m ev := hproject

end AndersonAC.SolS78
