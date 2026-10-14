import AndersonAC.S9Fin.SchurStatements

noncomputable section

open AndersonAC.S9

namespace AndersonAC.S9Schur

universe u

/-- Reindexing by the active plus eliminated coordinates. -/
def activeEquiv {n : Type u} [Fintype n] [DecidableEq n] (A : Finset n) :
    (↥A ⊕ ↥(Finset.univ \ A)) ≃ n :=
  Equiv.ofBijective
    (Sum.elim (fun i : ↥A => (i : n)) (fun j : ↥(Finset.univ \ A) => (j : n))) ⟨by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [Sum.elim_inl] at h
        have : a.val = b.val := h
        exact congrArg Sum.inl (Subtype.ext this)
      | inr b =>
        simp only [Sum.elim_inl, Sum.elim_inr] at h
        exfalso
        have ha : (a.val : n) ∈ A := a.property
        have hb : (b.val : n) ∈ Finset.univ \ A := b.property
        rw [Finset.mem_sdiff] at hb
        rw [h] at ha
        exact hb.2 ha
    | inr a =>
      cases b with
      | inl b =>
        simp only [Sum.elim_inr, Sum.elim_inl] at h
        exfalso
        have ha : (a.val : n) ∈ Finset.univ \ A := a.property
        have hb : (b.val : n) ∈ A := b.property
        rw [Finset.mem_sdiff] at ha
        rw [← h] at hb
        exact ha.2 hb
      | inr b =>
        simp only [Sum.elim_inr] at h
        have : a.val = b.val := h
        exact congrArg Sum.inr (Subtype.ext this), by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · have hxU : x ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      exact ⟨Sum.inr ⟨x, hxU⟩, rfl⟩⟩

@[simp]
theorem activeEquiv_inl {n : Type u} [Fintype n] [DecidableEq n] (A : Finset n)
    (i : ↥A) : activeEquiv A (Sum.inl i) = (i : n) :=
  rfl

@[simp]
theorem activeEquiv_inr {n : Type u} [Fintype n] [DecidableEq n] (A : Finset n)
    (j : ↥(Finset.univ \ A)) : activeEquiv A (Sum.inr j) = (j : n) :=
  rfl

end AndersonAC.S9Schur

namespace AndersonAC.SolS9

universe u

theorem schurCompression_proof : SchurCompressionStatement.{u} := by
  unfold SchurCompressionStatement
  intro n _ _ H E A hH hAc
  let e := AndersonAC.S9Schur.activeEquiv A
  let H0 : Matrix n n ℂ := H - (E : ℂ) • 1
  let A11 : Matrix ↥A ↥A ℂ := compress A H0
  let B : Matrix ↥A ↥(Finset.univ \ A) ℂ :=
    H0.submatrix (fun i : ↥A => (i : n)) (fun j : ↥(Finset.univ \ A) => (j : n))
  let C : Matrix ↥(Finset.univ \ A) ↥A ℂ :=
    H0.submatrix (fun j : ↥(Finset.univ \ A) => (j : n)) (fun i : ↥A => (i : n))
  let D : Matrix ↥(Finset.univ \ A) ↥(Finset.univ \ A) ℂ :=
    compress (Finset.univ \ A) H0
  have hM_eq : H0.submatrix e e = Matrix.fromBlocks A11 B C D := by
    ext (i | i) (j | j) <;> rfl
  have hM : IsUnit (H0.submatrix e e) := (Matrix.isUnit_submatrix_equiv e e).mpr hH
  have hM' : IsUnit (Matrix.fromBlocks A11 B C D) := hM_eq ▸ hM
  have hD : IsUnit D := hAc
  haveI := hD.invertible
  have hSchur : IsUnit (A11 - B * ⅟D * C) :=
    Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mp hM'
  haveI := hSchur.invertible
  haveI := hM'.invertible
  have hInvEq_D : ⅟D = D⁻¹ := Matrix.invOf_eq_nonsing_inv D
  have hS_eq : (A11 - B * ⅟D * C) = activeSchur H E A := by
    rw [hInvEq_D]
    unfold activeSchur compress
    rfl
  have hS_unit : IsUnit (activeSchur H E A) := hS_eq ▸ hSchur
  have hInvOf := Matrix.invOf_fromBlocks₂₂_eq A11 B C D
  have h11_of : (⅟(Matrix.fromBlocks A11 B C D)).toBlocks₁₁ = ⅟(A11 - B * ⅟D * C) := by
    rw [hInvOf]
    rfl
  have h11 : ((Matrix.fromBlocks A11 B C D)⁻¹).toBlocks₁₁ = (A11 - B * ⅟D * C)⁻¹ := by
    have h1 : (Matrix.fromBlocks A11 B C D)⁻¹ = ⅟(Matrix.fromBlocks A11 B C D) :=
      (Matrix.invOf_eq_nonsing_inv _).symm
    have h2 : (A11 - B * ⅟D * C)⁻¹ = ⅟(A11 - B * ⅟D * C) :=
      (Matrix.invOf_eq_nonsing_inv _).symm
    rw [h1, h2]
    exact h11_of
  have hM_inv : (H0.submatrix e e)⁻¹ = (H0⁻¹).submatrix e e :=
    Matrix.inv_submatrix_equiv H0 e e
  have hToBlocks : ((H0.submatrix e e)⁻¹).toBlocks₁₁ = compress A (H0⁻¹) := by
    rw [hM_inv]
    ext i j
    rfl
  have hCombine : ((Matrix.fromBlocks A11 B C D)⁻¹).toBlocks₁₁ = compress A (H0⁻¹) := by
    rw [← hM_eq]
    exact hToBlocks
  have hInv : (activeSchur H E A)⁻¹ = compress A (H0⁻¹) := by
    have hEq : (A11 - B * ⅟D * C)⁻¹ = compress A (H0⁻¹) := by
      rw [← h11, hCombine]
    rw [← hEq, hS_eq]
  exact ⟨hS_unit, hInv⟩

end AndersonAC.SolS9
