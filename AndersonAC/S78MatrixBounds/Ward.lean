import AndersonAC.S2.WardAlgebra
import AndersonAC.S78.Definitions

open scoped BigOperators ComplexConjugate

noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78 AndersonAC.S2 AndersonAC.SolS2

/-- A diagonal Ward identity controls the normalized inverse's squared row
sum by the imaginary part of the diagonal entry. -/
theorem rowTwo_normalized_le_diagonal_im {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (p : ι → ℝ) (t c : ℝ) (i : ι)
    (ht : 0 < t) (hc : 0 < c) (hp : ∀ j, c ≤ p j)
    (hward : (t : ℂ) • (G * Matrix.diagonal (fun j => (p j : ℂ)) * G.conjTranspose) =
      hermitianImaginary G) :
    rowTwo ((Real.sqrt t : ℂ) • G) i ≤ (G i i).im / c := by
  have hentry :
      ((t * ∑ j, p j * ‖G i j‖ ^ 2 : ℝ) : ℂ) = ((G i i).im : ℂ) := by
    have h := congrArg (fun A : Matrix ι ι ℂ => A i i) hward
    have hkernel :
        (G * Matrix.diagonal (fun j => (p j : ℂ)) * G.conjTranspose) i i =
          ((∑ j, p j * ‖G i j‖ ^ 2 : ℝ) : ℂ) := by
      calc
        _ = ∑ j, G i j * (p j : ℂ) * star (G i j) := by
          simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
        _ = ∑ j, ((p j * ‖G i j‖ ^ 2 : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Complex.star_def]
          calc
            G i j * (p j : ℂ) * conj (G i j) =
                (p j : ℂ) * (G i j * conj (G i j)) := by ring
            _ = (p j : ℂ) * (‖G i j‖ ^ 2 : ℂ) := by rw [Complex.mul_conj']
            _ = ((p j * ‖G i j‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
        _ = ((∑ j, p j * ‖G i j‖ ^ 2 : ℝ) : ℂ) := by norm_cast
    have hleft :
        ((t : ℂ) • (G * Matrix.diagonal (fun j => (p j : ℂ)) * G.conjTranspose)) i i =
          ((t * ∑ j, p j * ‖G i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.smul_apply, smul_eq_mul, hkernel]
      push_cast
      ring
    have hrhs : hermitianImaginary G i i = ((G i i).im : ℂ) := by
      simpa [hermitianImaginary, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
        Matrix.conjTranspose_apply, Complex.star_def] using complex_imaginary_difference (G i i)
    rw [hleft, hrhs] at h
    exact h
  have hsum : t * ∑ j, p j * ‖G i j‖ ^ 2 = (G i i).im := by
    exact Complex.ofReal_injective hentry
  have hweighted : c * rowTwo ((Real.sqrt t : ℂ) • G) i ≤ (G i i).im := by
    have hnorm (j : ι) :
        ‖((Real.sqrt t : ℂ) • G) i j‖ ^ 2 = t * ‖G i j‖ ^ 2 := by
      calc
        ‖((Real.sqrt t : ℂ) • G) i j‖ ^ 2 =
            (Real.sqrt t * ‖G i j‖) ^ 2 := by
              simp [Matrix.smul_apply, norm_smul, Complex.norm_real,
                abs_of_nonneg (Real.sqrt_nonneg _)]
        _ = t * ‖G i j‖ ^ 2 := by
              rw [show (Real.sqrt t * ‖G i j‖) ^ 2 =
                (Real.sqrt t) ^ 2 * ‖G i j‖ ^ 2 by ring, Real.sq_sqrt ht.le]
  
    rw [rowTwo]
    calc
      c * (∑ j, ‖((Real.sqrt t : ℂ) • G) i j‖ ^ 2) =
          t * ∑ j, c * ‖G i j‖ ^ 2 := by
            simp_rw [hnorm]
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ ≤ t * ∑ j, p j * ‖G i j‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hp j) (sq_nonneg _))
            exact ht.le
      _ = (G i i).im := hsum
  rw [le_div_iff₀ hc]
  simpa [mul_comm] using hweighted

/-- Apply the finite Ward identity to the active principal inverse and then
extend its row sum by zero to the ambient torus. -/
theorem endpoint_rowTwo_le_diagonal_im {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Endpoint ι) (r : ι → ℂ) (t c : ℝ)
    (ht : 0 < t) (hc : 0 < c) (hr : ∀ i, c ≤ (r i).im)
    (hphys : IsDampedEndpoint s r t) :
    ∀ i ∈ s.active, rowTwo (normalizedInverse s t) i ≤ (s.g i i).im / c := by
  classical
  rcases hphys with ⟨hMphysical, hsupport, hinverse⟩
  rcases hinverse with ⟨hBG, hGB⟩
  let A : Type := {i : ι // i ∈ s.active}
  let M : Matrix A A ℝ := fun i j => (s.M i.val j.val).re
  let G : Matrix A A ℂ := fun i j => s.g i.val j.val
  let rho : A → ℂ := fun i => r i.val
  have hMsymm : M.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact (congrArg Complex.re (hMphysical i.val j.val).1).symm
  have hreal : S2.realMatrix M = s.M.submatrix (fun i : A => i.val) (fun i : A => i.val) := by
    ext i j
    apply Complex.ext
    · simp [S2.realMatrix, M]
    · simpa [S2.realMatrix, M] using (hMphysical i.val j.val).2.symm
  have hB : S2.dampedMatrix M t rho =
      s.M.submatrix (fun i : A => i.val) (fun i : A => i.val) -
        (t : ℂ) • Matrix.diagonal rho := by
    ext i j
    simp [S2.dampedMatrix, hreal]
  have hBG' : S2.dampedMatrix M t rho * G = 1 := by
    rw [hB]
    exact hBG
  have hGB' : G * S2.dampedMatrix M t rho = 1 := by
    rw [hB]
    exact hGB
  have hres : S2.resolvent M t rho = G := by
    unfold S2.resolvent
    rw [hB]
    exact Matrix.inv_eq_left_inv hGB
  have hward := unnormalized_ward M hMsymm ht rho (fun i => lt_of_lt_of_le hc (hr i.val))
  rw [hres] at hward
  intro i hi
  let ii : A := ⟨i, hi⟩
  have hsub := rowTwo_normalized_le_diagonal_im G (fun j => (rho j).im)
    t c ii ht hc (fun j => hr j.val) hward
  have hzero : ∀ j, j ∉ s.active →
      ‖normalizedInverse s t i j‖ ^ 2 = 0 := by
    intro j hj
    have hg := hsupport i j (Or.inr hj)
    simp [normalizedInverse, hg]
  have hsum : (∑ j, ‖normalizedInverse s t i j‖ ^ 2) =
      ∑ j : A, ‖((Real.sqrt t : ℂ) • G) ii j‖ ^ 2 := by
    calc
      (∑ j, ‖normalizedInverse s t i j‖ ^ 2) =
          ∑ j ∈ s.active, ‖normalizedInverse s t i j‖ ^ 2 := by
            rw [← Finset.sum_subset (Finset.subset_univ s.active)]
            intro j hj hjnot
            exact hzero j hjnot
      _ = ∑ j : A, ‖((Real.sqrt t : ℂ) • G) ii j‖ ^ 2 := by
            rw [← Finset.sum_attach]
            have hattach : s.active.attach = (Finset.univ : Finset A) := by
              ext j
              simp [A]
            rw [hattach]
            change (∑ j : A, ‖(Real.sqrt t : ℂ) * s.g i j.val‖ ^ 2) =
              ∑ j : A, ‖(Real.sqrt t : ℂ) * s.g i j.val‖ ^ 2
            rfl
  change rowTwo (normalizedInverse s t) i ≤ (s.g i i).im / c
  unfold rowTwo
  calc
    (∑ j, ‖normalizedInverse s t i j‖ ^ 2) =
        ∑ j : A, ‖((Real.sqrt t : ℂ) • G) ii j‖ ^ 2 := hsum
    _ ≤ (s.g i i).im / c := by simpa [rowTwo, G, ii] using hsub

/-- The ambient endpoint inverse is symmetric: on the active subtype it is
the inverse of a symmetric damped matrix, and it is zero off that subtype. -/
theorem endpoint_inverse_symmetric {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Endpoint ι) (r : ι → ℂ) (t : ℝ)
    (hphys : IsDampedEndpoint s r t) : s.g.IsSymm := by
  classical
  rcases hphys with ⟨hMphysical, hsupport, hinverse⟩
  rcases hinverse with ⟨hBG, hGB⟩
  let A : Type := {i : ι // i ∈ s.active}
  let M : Matrix A A ℝ := fun i j => (s.M i.val j.val).re
  let G : Matrix A A ℂ := fun i j => s.g i.val j.val
  let rho : A → ℂ := fun i => r i.val
  have hMsymm : M.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact (congrArg Complex.re (hMphysical i.val j.val).1).symm
  have hreal : S2.realMatrix M = s.M.submatrix (fun i : A => i.val) (fun i : A => i.val) := by
    ext i j
    apply Complex.ext
    · simp [S2.realMatrix, M]
    · simpa [S2.realMatrix, M] using (hMphysical i.val j.val).2.symm
  have hB : S2.dampedMatrix M t rho =
      s.M.submatrix (fun i : A => i.val) (fun i : A => i.val) -
        (t : ℂ) • Matrix.diagonal rho := by
    ext i j
    simp [S2.dampedMatrix, hreal]
  have hGB' : G * S2.dampedMatrix M t rho = 1 := by
    rw [hB]
    exact hGB
  have hres : S2.resolvent M t rho = G := by
    unfold S2.resolvent
    rw [hB]
    exact Matrix.inv_eq_left_inv hGB
  have hGsym := (AndersonAC.S2.resolvent_symmetric M hMsymm t rho).1
  rw [hres] at hGsym
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hi : i ∈ s.active
  · by_cases hj : j ∈ s.active
    · exact hGsym.apply ⟨i, hi⟩ ⟨j, hj⟩
    · have hij := hsupport i j (Or.inr hj)
      have hji := hsupport j i (Or.inl hj)
      simp [hij, hji]
  · have hij := hsupport i j (Or.inl hi)
    have hji := hsupport j i (Or.inr hi)
    simp [hij, hji]

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.rowTwo_normalized_le_diagonal_im
#print axioms AndersonAC.SolS78.endpoint_rowTwo_le_diagonal_im
#print axioms AndersonAC.SolS78.endpoint_inverse_symmetric
