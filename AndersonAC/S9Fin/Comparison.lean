import AndersonAC.S9Fin.Scalar
import AndersonAC.S9Fin.CertificateSchur

noncomputable section
open AndersonAC.S9

namespace AndersonAC.SolS9

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma columnNormSq_sub_bound (G C : Matrix n n ℂ) (i : n) :
    columnNormSq G i ≤ 2 * columnNormSq C i + 2 * columnNormSq (G - C) i := by
  unfold columnNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have htri : ‖G j i‖ ≤ ‖C j i‖ + ‖(G - C) j i‖ := by
    simpa only [Matrix.sub_apply, add_sub_cancel] using
      norm_add_le (C j i) (G j i - C j i)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htri
  nlinarith [sq_nonneg (‖C j i‖ - ‖(G - C) j i‖)]

/-- The scalar truncation retains the column lower bound up to the squared
error. No spectral projection or certificate selection enters this step. -/
lemma truncatedReadout_column_bound (b : CertificateBounds) (η ε q c d : ℝ)
    (hη : 0 ≤ η) (hd : 0 ≤ d)
    (hcert : columnConstant b ≤ 2 * η * c + 2 * η * d)
    (hcut : η * c ≤ cutMultiplier ε * q) :
    columnConstant b - 2 * η * d ≤ truncatedReadout b ε q := by
  unfold truncatedReadout
  apply le_min
  · linarith
  · exact sub_le_self _ (by positivity)

/-- Sum the active-column estimates, account for the full cutoff rank,
and include the nonnegative inactive readouts. -/
theorem finite_cut_comparison_of_columns [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hη : 0 < η) (b : CertificateBounds)
    (hprincipal : allPrincipalInvertible H E) (A : Finset n)
    (hcard : Fintype.card n ≤ 2 * A.card)
    (hcolumn : ∀ i : A, columnConstant b ≤ η * columnNormSq
      (dampingFunction η (compress A ((H - (E : ℂ) • 1)⁻¹))) i)
    (hcut : ∀ i : A, η * columnNormSq
      (dampingFunction η (compress A (cutInverse H hH E η ε))) i ≤
      cutMultiplier ε * scalarQ H E η i)
    (hε : 0 < ε) :
    columnConstant b / 2 - 8 * (windowRank H hH E (ε * η) : ℝ) /
      (η * Fintype.card n) ≤
      (∑ i, truncatedReadout b ε (scalarQ H E η i)) / Fintype.card n := by
  let G := dampingFunction η (compress A ((H - (E : ℂ) • 1)⁻¹))
  let C := dampingFunction η (compress A (cutInverse H hH E η ε))
  let D := G - C
  let f (i : n) := truncatedReadout b ε (scalarQ H E η i)
  have hc : 0 < columnConstant b := columnConstant_pos_proof b
  have hf : ∀ i : n, 0 ≤ f i := by
    intro i
    exact le_min (mul_nonneg (by unfold cutMultiplier; positivity)
      (scalarQ_nonneg H hH E η hη i)) hc.le
  have hpoint : ∀ i : A, columnConstant b - 2 * η * columnNormSq D i ≤ f i := by
    intro i
    apply truncatedReadout_column_bound b η ε _ (columnNormSq C i) (columnNormSq D i) hη.le
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
    · have ht := mul_le_mul_of_nonneg_left (columnNormSq_sub_bound G C i) hη.le
      have hi := hcolumn i
      change columnConstant b ≤ η * columnNormSq G i at hi
      linarith
    · exact hcut i
  have hsum : (A.card : ℝ) * columnConstant b - 2 * η * hilbertSchmidtSq D ≤
      ∑ i : A, f i := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset A)) => hpoint i)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul, ← Finset.mul_sum, hilbertSchmidtSq] using hs
  have hsub : (∑ i : A, f i) ≤ ∑ i : n, f i := by
    calc
      (∑ i : A, f i) = ∑ i ∈ A, f i := by
        simpa only [Finset.attach_eq_univ] using Finset.sum_attach A f
      _ ≤ ∑ i : n, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _ => hf i)
  have hhs : hilbertSchmidtSq D ≤
      4 * (windowRank H hH E (ε * η) : ℝ) / η ^ 2 :=
    (cut_rank_hilbertSchmidt_proof H hH E η ε hη hε hprincipal A).2.2
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hA : (Fintype.card n : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hcard
  have hcardC : (Fintype.card n : ℝ) * (columnConstant b / 2) ≤
      (A.card : ℝ) * columnConstant b := by nlinarith
  have herr : 2 * η * hilbertSchmidtSq D ≤
      8 * (windowRank H hH E (ε * η) : ℝ) / η := by
    calc
      2 * η * hilbertSchmidtSq D ≤
          2 * η * (4 * (windowRank H hH E (ε * η) : ℝ) / η ^ 2) :=
        mul_le_mul_of_nonneg_left hhs (by positivity)
      _ = 8 * (windowRank H hH E (ε * η) : ℝ) / η := by
        field_simp [hη.ne'] <;> ring
  apply (le_div_iff₀ hN).mpr
  have heq : (columnConstant b / 2 -
      8 * (windowRank H hH E (ε * η) : ℝ) / (η * Fintype.card n)) *
      Fintype.card n = (Fintype.card n : ℝ) * (columnConstant b / 2) -
      8 * (windowRank H hH E (ε * η) : ℝ) / η := by
    field_simp [hη.ne', hN.ne'] <;> ring
  rw [heq]
  change _ ≤ ∑ i : n, f i
  linarith

/-- The remaining matrix input is precisely the outside-cut column estimate.
The certificate witnesses are used pointwise, with no selection requirement. -/
theorem finite_cut_comparison_of_cut_columns [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ε : ℝ) (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (b : CertificateBounds) (hprincipal : allPrincipalInvertible H E)
    (hcert : matrixCertificate H E η b)
    (hcut : ∀ (A : Finset n) (i : A),
      η * columnNormSq (dampingFunction η (compress A (cutInverse H hH E η ε))) i ≤
        cutMultiplier ε * scalarQ H E η i) :
    columnConstant b / 2 - 8 * (windowRank H hH E (ε * η) : ℝ) /
      (η * Fintype.card n) ≤
      (∑ i, truncatedReadout b ε (scalarQ H E η i)) / Fintype.card n := by
  obtain ⟨A, r, G, hcard, hr, hMG, _, hq⟩ := hcert
  have hInv := certified_active_inverse H E η A r G hMG hprincipal
  have hq' : ∀ i : A, b.qMin ≤
      ((activeSchur H E A - (η : ℂ) • Matrix.diagonal (fun j : A => r j))⁻¹ i i).im := by
    intro i
    rw [← hInv]
    exact hq i i.property
  have hcolumn := certified_subset_column_proof H hH E η hη b hprincipal A r hr hq'
  rw [active_resolvent_compression_proof H hH E η hη hprincipal A] at hcolumn
  exact finite_cut_comparison_of_columns H hH E η ε hη b hprincipal A hcard
    hcolumn (hcut A) hε.1

end AndersonAC.SolS9
