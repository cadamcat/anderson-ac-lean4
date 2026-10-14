import AndersonAC.S78.Definitions
import AndersonAC.Blueprint.Certificate

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace AndersonAC.SolS78

private theorem boundedCertificateEvent_subset_certificateEvent
    (d n₀ m k : ℕ) (u E Cr cp cg : ℝ)
    (hCr : Cr ≤ (k : ℝ)) (hcp : 1 / (k : ℝ) ≤ cp) (hcg : 1 / (k : ℝ) ≤ cg) :
    AndersonAC.S78.boundedCertificateEvent d n₀ m u E Cr cp cg ⊆
      OAI.Anderson.certificateEvent d k n₀ m u E := by
  intro ω hω
  rcases hω with ⟨A, r, G, hcard, hbounds, hBG, hGB, hG⟩
  refine ⟨A, r, G, hcard, ?_, hBG, hGB, ?_⟩
  · intro i hi
    exact ⟨(hbounds i hi).1.trans hCr, hcp.trans (hbounds i hi).2⟩
  · intro i hi
    exact hcg.trans (hG i hi)

/-- Convert uniform finite-box certificates into OAI's indexed threshold. -/
theorem window_threshold_nonempty_proof (d : ℕ) (hd : 3 ≤ d) (e₂ : ℝ)
    (hengine : AndersonAC.S78.UniformCertificateInput d e₂) :
    ∃ k, AndersonAC.Blueprint.windowThreshold d e₂ k := by
  rcases hengine with ⟨cutoff, Cr, cp, cg, hcpPos, hcgPos, hprob⟩
  let x : ℝ := max Cr (max cp⁻¹ cg⁻¹)
  obtain ⟨n, hn⟩ := exists_nat_gt x
  let k : ℕ := max (max cutoff 10) n
  have hcutoff : cutoff ≤ k := by
    dsimp [k]
    exact le_trans (Nat.le_max_left cutoff 10) (Nat.le_max_left (max cutoff 10) n)
  have hten : 10 ≤ k := by
    dsimp [k]
    exact le_trans (Nat.le_max_right cutoff 10) (Nat.le_max_left (max cutoff 10) n)
  have hnle : n ≤ k := by
    dsimp [k]
    exact Nat.le_max_right (max cutoff 10) n
  have hxk : x ≤ (k : ℝ) := by
    dsimp [x]
    exact (le_of_lt hn).trans (by exact_mod_cast hnle)
  have hCr : Cr ≤ (k : ℝ) := by
    exact (le_max_left Cr (max cp⁻¹ cg⁻¹)).trans hxk
  have hcpInv : cp⁻¹ ≤ (k : ℝ) := by
    calc
      cp⁻¹ ≤ max cp⁻¹ cg⁻¹ := le_max_left _ _
      _ ≤ max Cr (max cp⁻¹ cg⁻¹) := le_max_right _ _
      _ ≤ (k : ℝ) := hxk
  have hcgInv : cg⁻¹ ≤ (k : ℝ) := by
    calc
      cg⁻¹ ≤ max cp⁻¹ cg⁻¹ := le_max_right _ _
      _ ≤ max Cr (max cp⁻¹ cg⁻¹) := le_max_right _ _
      _ ≤ (k : ℝ) := hxk
  have hkPos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (show 0 < k by omega)
  have hcpLower : 1 / (k : ℝ) ≤ cp := by
    rw [div_le_iff₀ hkPos]
    calc
      1 = cp * cp⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt hcpPos)]
      _ ≤ cp * (k : ℝ) := mul_le_mul_of_nonneg_left hcpInv hcpPos.le
  have hcgLower : 1 / (k : ℝ) ≤ cg := by
    rw [div_le_iff₀ hkPos]
    calc
      1 = cg * cg⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt hcgPos)]
      _ ≤ cg * (k : ℝ) := mul_le_mul_of_nonneg_left hcgInv hcgPos.le
  refine ⟨k, ?_⟩
  change 10 ≤ k ∧ ∀ n₀ : ℕ, k ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m →
    ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 →
      ∀ E : ℝ, E ∈ OAI.Anderson.energyWindow d e₂ →
        (1 / 2 : ℝ≥0∞) ≤ OAI.Anderson.torusLaw d m
          (OAI.Anderson.certificateEvent d k n₀ m u E)
  refine ⟨hten, ?_⟩
  intro n₀ hn₀ m hm u hu E hE
  have hprob' := hprob n₀ m (le_trans hcutoff hn₀) hm u hu E hE
  exact hprob'.trans (measure_mono (boundedCertificateEvent_subset_certificateEvent
    d n₀ m k u E Cr cp cg hCr hcpLower hcgLower))

theorem threshold_nonempty_proof (d : ℕ) (hd : 4 ≤ d) (e₂ : ℝ)
    (hengine : AndersonAC.S78.UniformCertificateInput d e₂) :
    ∃ k, AndersonAC.S78.thresholdCriterion d k := by
  obtain ⟨k, hk⟩ := window_threshold_nonempty_proof d (by omega) e₂ hengine
  exact ⟨k, (AndersonAC.Blueprint.windowThreshold_iff_of_four_le hd e₂ k).mp hk⟩

theorem threshold_exists_positive_proof (d : ℕ) (hd : 4 ≤ d) (e₂ : ℝ)
    (hengine : AndersonAC.S78.UniformCertificateInput d e₂) :
    ∃ lambda : ℝ, AndersonAC.S78.finiteBoxThreshold d lambda ∧ 0 < lambda := by
  obtain ⟨k, hk⟩ := threshold_nonempty_proof d hd e₂ hengine
  obtain ⟨lambda, hlambda⟩ :=
    (OAI.Anderson.finiteBoxThreshold_exists_iff d).2 ⟨k, hk⟩
  exact ⟨lambda, hlambda, OAI.Anderson.finiteBoxThreshold_pos hlambda⟩

theorem threshold_probability_proof {d k : ℕ}
    (hk : IsLeast {n : ℕ | AndersonAC.S78.thresholdCriterion d n} k)
    {coupling : ℝ} (hc : 0 < coupling)
    (hsmall : coupling < Real.sqrt 3 / (2 : ℝ) ^ k) :
    ∃ n₀ : ℕ, k ≤ n₀ ∧ ∃ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 ∧
      OAI.Anderson.scaleCoupling n₀ u = coupling ∧ ∀ m, 4 * n₀ ≤ m →
        ∀ E ∈ OAI.Anderson.higherDimWindow d,
          (1 / 2 : ℝ≥0∞) ≤
            OAI.Anderson.torusLaw d m (OAI.Anderson.certificateEvent d k n₀ m u E) := by
  obtain ⟨n₀, hn₀, u, hu, hscale⟩ :=
    OAI.Anderson.coupling_parametrization hc hsmall
  refine ⟨n₀, hn₀, u, hu, hscale, ?_⟩
  intro m hm E hE
  exact hk.1.2 n₀ hn₀ m hm u hu E hE

theorem intrinsic_threshold_spec_proof (d : ℕ)
    (hne : ∃ k, AndersonAC.S78.thresholdCriterion d k) :
    IsLeast {k | AndersonAC.S78.thresholdCriterion d k}
      (AndersonAC.S78.thresholdIndex d hne) ∧
    AndersonAC.S78.finiteBoxThreshold d (AndersonAC.S78.intrinsicThreshold d hne) ∧
      0 < AndersonAC.S78.intrinsicThreshold d hne := by
  classical
  have hleast : IsLeast {k : ℕ | AndersonAC.S78.thresholdCriterion d k}
      (AndersonAC.S78.thresholdIndex d hne) := by
    constructor
    · exact Nat.find_spec hne
    · intro n hn
      exact Nat.find_min' hne hn
  have hfinite : AndersonAC.S78.finiteBoxThreshold d (AndersonAC.S78.intrinsicThreshold d hne) := by
    refine ⟨AndersonAC.S78.thresholdIndex d hne, hleast, ?_⟩
    rfl
  exact ⟨hleast, hfinite, OAI.Anderson.finiteBoxThreshold_pos hfinite⟩

theorem certificate_family_of_uniform_input_proof (e₂ : ℝ)
    (hengine : ∀ d : ℕ, 3 ≤ d → AndersonAC.S78.UniformCertificateInput d e₂) :
    AndersonAC.Blueprint.CertificateFamily e₂ := by
  intro d hd
  exact window_threshold_nonempty_proof d hd e₂ (hengine d hd)

end AndersonAC.SolS78
