import AndersonAC.S78.Definitions

set_option autoImplicit false
noncomputable section
namespace AndersonAC.SolS78
open AndersonAC.S78

/-- Symmetry of the actual padded inverse follows from its active two-sided
inverse equations; no statement about the inactive ambient block is used. -/
theorem damped_endpoint_symmetric {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Endpoint ι) (r : ι → ℂ) (t : ℝ) (hs : IsDampedEndpoint s r t) :
    ∀ i j, s.g i j = s.g j i := by
  rcases hs with ⟨hM, hzero, hInv⟩
  let B := s.M.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val) -
    (t : ℂ) • Matrix.diagonal (fun i : s.active => r i.val)
  let G := s.g.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val)
  have hB : B.transpose = B := by
    dsimp [B]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.diagonal_transpose]
    congr 1
    ext i j
    exact (hM j.val i.val).1
  have hG : G = B⁻¹ := (Matrix.inv_eq_right_inv hInv.1).symm
  have hSym : G.transpose = G := by
    rw [hG, Matrix.transpose_nonsing_inv, hB]
  intro i j
  by_cases hi : i ∈ s.active
  · by_cases hj : j ∈ s.active
    · exact (congrArg (fun K : Matrix s.active s.active ℂ => K ⟨i, hi⟩ ⟨j, hj⟩) hSym).symm
    · rw [hzero i j (Or.inr hj), hzero j i (Or.inl hj)]
  · rw [hzero i j (Or.inl hi), hzero j i (Or.inr hi)]

theorem normalized_endpoint_symmetric {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Endpoint ι) (r : ι → ℂ) (t : ℝ) (hs : IsDampedEndpoint s r t) :
    ∀ i j, normalizedInverse s t i j = normalizedInverse s t j i := by
  intro i j
  unfold normalizedInverse
  simp only [Matrix.smul_apply, damped_endpoint_symmetric s r t hs i j]

theorem survivor_difference_symmetric {ι : Type} [Fintype ι] [DecidableEq ι]
    (old next : Endpoint ι) (r : ι → ℂ) (t : ℝ)
    (hold : IsDampedEndpoint old r t) (hnext : IsDampedEndpoint next r t) :
    ∀ i j, survivorDifference old next t i j = survivorDifference old next t j i := by
  intro i j
  unfold survivorDifference
  rw [normalized_endpoint_symmetric old r t hold i j,
    normalized_endpoint_symmetric next r t hnext i j]
  simp only [and_comm]

/-- The normalized endpoint update is exactly old plus the survivor
difference on every retained pair. -/
theorem survivor_difference_identity {ι : Type} [DecidableEq ι]
    (old next : Endpoint ι) (t : ℝ) (B : Finset ι) (hB : B ⊆ next.active) :
    ∀ i ∈ B, ∀ j ∈ B, normalizedInverse next t i j =
      (normalizedInverse old t + survivorDifference old next t) i j := by
  intro i hi j hj
  simp only [Matrix.add_apply, survivorDifference]
  split_ifs with hmem
  · ring
  · exact False.elim (hmem ⟨hB hi, hB hj⟩)

end AndersonAC.SolS78

#print axioms AndersonAC.SolS78.damped_endpoint_symmetric
#print axioms AndersonAC.SolS78.survivor_difference_symmetric
