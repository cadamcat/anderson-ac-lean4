import AndersonAC.S9Fin.Core

noncomputable section

open MeasureTheory Filter OAI.Anderson AndersonAC.S9
open scoped Topology ComplexConjugate

namespace AndersonAC.SolS9

theorem columnConstant_pos_proof (b : CertificateBounds) : 0 < columnConstant b := by
  have hC : 0 < comparisonConstant b := by
    unfold comparisonConstant
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (by linarith [b.B_nonneg]) b.pMin_pos.le)
  exact div_pos b.qMin_pos
    (mul_pos (lt_of_lt_of_le b.pMin_pos b.pMin_le_pMax) (sq_pos_of_pos hC))

theorem periodicHamiltonian_isHermitian_proof (d m : ℕ) (coupling : ℝ)
    (ω : TorusConfiguration d m) : (periodicHamiltonian coupling ω).IsHermitian := by
  classical
  ext x y
  change star (periodicHamiltonian coupling ω y x) = periodicHamiltonian coupling ω x y
  have hplus (j : Fin d) : (x = y + torusBasisVector j) ↔
      (y = x - torusBasisVector j) := by
    constructor <;> intro h <;> simp [h]
  have hminus (j : Fin d) : (x = y - torusBasisVector j) ↔
      (y = x + torusBasisVector j) := by
    constructor <;> intro h <;> simp [h]
  have hstar (p : Prop) [Decidable p] (a b : ℂ) :
      star (if p then a else b) = if p then star a else star b := by
    split_ifs <;> rfl
  simp only [periodicHamiltonian, star_add, star_neg, star_sum, hstar,
    star_one, star_zero, Complex.star_def, hplus, hminus]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact add_comm _ _
  · by_cases h : x = y <;> simp [h, eq_comm]

theorem trueCertificateEvent_measurable_proof (d m : ℕ) (coupling E η : ℝ)
    (b : CertificateBounds) : MeasurableSet (trueCertificateEvent d m coupling E η b) := by
  classical
  let X := TorusConfiguration d m ×
    (Torus d m → ℂ) × Matrix (Torus d m) (Torus d m) ℂ
  have : CompactSpace SingleSite := isCompact_iff_compactSpace.mp isCompact_Icc
  have : SigmaCompactSpace X := by
    change SigmaCompactSpace (TorusConfiguration d m ×
      (Torus d m → ℂ) × (Torus d m → Torus d m → ℂ))
    infer_instance
  let M (A : Finset (Torus d m)) (p : X) :=
    periodicHamiltonian coupling p.1 - (E : ℂ) • 1 - (η : ℂ) • diagonalOn A p.2.1
  let C (A : Finset (Torus d m)) : Set X := {p |
    (∀ i ∈ A, ‖p.2.1 i‖ ≤ b.B ∧ b.pMin ≤ (p.2.1 i).im ∧ (p.2.1 i).im ≤ b.pMax) ∧
    M A p * p.2.2 = 1 ∧ p.2.2 * M A p = 1 ∧
    (∀ i ∈ A, b.qMin ≤ (p.2.2 i i).im)}
  have hc (A : Finset (Torus d m)) : IsClosed (C A) := by
    have hM : Continuous (M A) := by
      exact ((continuous_periodicHamiltonian d m _).comp continuous_fst).sub
        continuous_const |>.sub
        (((continuous_diagonalOn A).comp (continuous_fst.comp continuous_snd)).const_smul (η : ℂ))
    have hr : IsClosed {p : X | ∀ i ∈ A,
        ‖p.2.1 i‖ ≤ b.B ∧ b.pMin ≤ (p.2.1 i).im ∧ (p.2.1 i).im ≤ b.pMax} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro _
      have h₁ : IsClosed {p : X | ‖p.2.1 i‖ ≤ b.B} :=
        isClosed_le (by fun_prop) continuous_const
      have h₂ : IsClosed {p : X | b.pMin ≤ (p.2.1 i).im} :=
        isClosed_le continuous_const (by fun_prop)
      have h₃ : IsClosed {p : X | (p.2.1 i).im ≤ b.pMax} :=
        isClosed_le (by fun_prop) continuous_const
      exact h₁.inter (h₂.inter h₃)
    have hG : IsClosed {p : X | ∀ i ∈ A, b.qMin ≤ (p.2.2 i i).im} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro _
      exact isClosed_le continuous_const (by fun_prop)
    have hGcont : Continuous (fun p : X => p.2.2) := continuous_snd.comp continuous_snd
    exact hr.inter ((isClosed_eq (hM.mul hGcont) continuous_const).inter
      ((isClosed_eq (hGcont.mul hM) continuous_const).inter hG))
  have hm (A : Finset (Torus d m)) : MeasurableSet (Prod.fst '' C A) := by
    have hs : IsSigmaCompact (C A) :=
      isSigmaCompact_univ.of_isClosed_subset (hc A) (Set.subset_univ _)
    obtain ⟨K, hK, hEq⟩ := hs.image continuous_fst
    rw [← hEq]
    exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)
  have heq : trueCertificateEvent d m coupling E η b =
      ⋃ A : Finset (Torus d m), ⋃ (_ : Fintype.card (Torus d m) ≤ 2 * A.card),
        Prod.fst '' C A := by
    ext ω
    simp only [trueCertificateEvent, matrixCertificate, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_image, Prod.exists, C, M, diagonalOn]
    constructor
    · rintro ⟨A, r, G, hA, hr, hBG, hGB, hG⟩
      exact ⟨A, hA, ω, r, G, ⟨hr, hBG, hGB, hG⟩, rfl⟩
    · rintro ⟨A, hA, ω', r, G, ⟨hr, hBG, hGB, hG⟩, rfl⟩
      exact ⟨A, r, G, hA, hr, hBG, hGB, hG⟩
  rw [heq]
  exact MeasurableSet.iUnion fun A => MeasurableSet.iUnion fun _ => hm A

end AndersonAC.SolS9
