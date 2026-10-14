import AndersonAC.S78.PhysicalCertificate

/-!
# The Schur determinant step

agent-s78phase2 (DISPATCH 04:08:18 (B), route R2). For a matrix `B` and an active set `A ∋ p`, the
block on the complement of `A.erase p` has determinant `det B_{Aᶜ} · (activeSchur B A)_{pp}`
whenever `B_{Aᶜ}` is invertible. Hence the sequential Schur pivot at `p` is nonzero as soon as the
two principal blocks are invertible (on `ω ∉ exceptionalSet`, every principal block of the true
matrix is).
-/

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- The block of `B` on the complement of `A`. -/
def offB {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (A : Finset ι) :
    Matrix {i // i ∉ A} {i // i ∉ A} ℂ :=
  B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val)

/-- The complement of `A.erase p` as the complement of `A` plus `p`. -/
def eraseEquiv {ι : Type} [DecidableEq ι] (A : Finset ι) (p : ι) (hp : p ∈ A) :
    {i // i ∉ A} ⊕ Unit ≃ {i // i ∉ A.erase p} where
  toFun := Sum.elim (fun t => ⟨t.1, fun h => t.2 (Finset.mem_of_mem_erase h)⟩)
    (fun _ => ⟨p, Finset.notMem_erase p A⟩)
  invFun s := if h : s.1 = p then Sum.inr () else
    Sum.inl ⟨s.1, fun h' => s.2 (Finset.mem_erase.mpr ⟨h, h'⟩)⟩
  left_inv x := by
    cases x with
    | inl t =>
      have : t.1 ≠ p := fun h => t.2 (h ▸ hp)
      simp [this]
    | inr u => simp
  right_inv s := by
    by_cases h : s.1 = p
    · simp only [h, dif_pos]; ext; simp [h]
    · simp [h]

/-- **The Schur determinant step.** -/
theorem det_offB_erase {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (A : Finset ι)
    (p : ι) (hp : p ∈ A) (hT : IsUnit (offB B A).det) :
    (offB B (A.erase p)).det =
      (offB B A).det * SolS78.activeSchur B A ⟨p, hp⟩ ⟨p, hp⟩ := by
  classical
  haveI : Invertible (offB B A) := Matrix.invertibleOfIsUnitDet _ hT
  have hblk : (offB B (A.erase p)).submatrix (eraseEquiv A p hp) (eraseEquiv A p hp) =
      Matrix.fromBlocks (offB B A)
        (Matrix.of fun (t : {i // i ∉ A}) (_ : Unit) => B t.1 p)
        (Matrix.of fun (_ : Unit) (t : {i // i ∉ A}) => B p t.1)
        (Matrix.of fun (_ : Unit) (_ : Unit) => B p p) := by
    ext a b
    cases a <;> cases b <;> rfl
  rw [← Matrix.det_submatrix_equiv_self (eraseEquiv A p hp), hblk, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv]
  congr 1
  rw [Matrix.det_unique]
  simp only [SolS78.activeSchur, Matrix.sub_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    offB, Matrix.of_apply]

/-- A nonzero pivot from two invertible principal blocks. -/
theorem activeSchur_pivot_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (A : Finset ι) (p : ι) (hp : p ∈ A) (hT : IsUnit (offB B A).det)
    (hT' : IsUnit (offB B (A.erase p)).det) : SolS78.activeSchur B A ⟨p, hp⟩ ⟨p, hp⟩ ≠ 0 := by
  intro h0
  rw [det_offB_erase B A p hp hT, h0, mul_zero] at hT'
  exact not_isUnit_zero hT'

end AndersonAC.AgentS78

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Adding `ξ` at a diagonal entry `p ∈ A` adds `ξ` to the active Schur complement there. -/
theorem activeSchur_add_single {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (A : Finset ι) (p : ι) (hp : p ∈ A) (ξ : ℂ) :
    SolS78.activeSchur (B + Matrix.diagonal (Pi.single p ξ)) A ⟨p, hp⟩ ⟨p, hp⟩ =
      SolS78.activeSchur B A ⟨p, hp⟩ ⟨p, hp⟩ + ξ := by
  have hout : ∀ i : {i // i ∉ A}, i.val ≠ p := fun i h => i.2 (h ▸ hp)
  have h1 : (B + Matrix.diagonal (Pi.single p ξ)).submatrix (fun i : {i // i ∉ A} => i.val)
      (fun i : {i // i ∉ A} => i.val) =
      B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : {i // i ∉ A} => i.val) := by
    ext a b
    simp [Matrix.diagonal_apply, Pi.single_apply, hout a]
  have h2 : (B + Matrix.diagonal (Pi.single p ξ)).submatrix (fun i : A => i.val)
      (fun i : {i // i ∉ A} => i.val) =
      B.submatrix (fun i : A => i.val) (fun i : {i // i ∉ A} => i.val) := by
    ext a b
    have : a.val ≠ b.val := fun h => b.2 (h ▸ a.2)
    simp [Matrix.diagonal_apply, this]
  have h3 : (B + Matrix.diagonal (Pi.single p ξ)).submatrix (fun i : {i // i ∉ A} => i.val)
      (fun i : A => i.val) =
      B.submatrix (fun i : {i // i ∉ A} => i.val) (fun i : A => i.val) := by
    ext a b
    have : a.val ≠ b.val := fun h => a.2 (h ▸ b.2)
    simp [Matrix.diagonal_apply, this]
  unfold SolS78.activeSchur
  rw [h1, h2, h3]
  simp [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply]
  ring

end AndersonAC.AgentS78
