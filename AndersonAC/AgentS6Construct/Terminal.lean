import AndersonAC.S6.Definitions

/-! Principal-minor inheritance for one Schur heat. -/

noncomputable section

open scoped BigOperators

namespace AndersonAC.AgentS6Construct

def schurEntry {α : Type*} (M : Matrix α α ℝ) (ξ : α → ℝ) (x i j : α) : ℝ :=
  M i j - M i x * M x j / (M x x + ξ x)

def schurShifted {α : Type*} [DecidableEq α] (M : Matrix α α ℝ) (ξ : α → ℝ)
    (x : α) (U : Finset α) : Matrix {i // i ∈ U} {i // i ∈ U} ℝ :=
  fun i j => schurEntry M ξ x i j + if i = j then ξ i else 0

def insertIndexMap {α : Type*} [DecidableEq α] (x : α) (U : Finset α) :
    Unit ⊕ {i // i ∈ U} → {i // i ∈ insert x U}
  | Sum.inl _ => ⟨x, Finset.mem_insert_self x U⟩
  | Sum.inr i => ⟨i.1, Finset.mem_insert_of_mem i.2⟩

def insertIndexEquiv {α : Type*} [DecidableEq α] (x : α) (U : Finset α)
    (hxU : x ∉ U) : Unit ⊕ {i // i ∈ U} ≃ {i // i ∈ insert x U} :=
  Equiv.ofBijective (insertIndexMap x U) ⟨by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => rfl
      | inr b =>
        have hv : x = b.1 := by
          have h := congrArg (fun z : {i // i ∈ insert x U} => (z : α)) hab
          simpa [insertIndexMap] using h
        exact False.elim (hxU (hv ▸ b.2))
    | inr a =>
      cases b with
      | inl b =>
        have hv : a.1 = x := by
          have h := congrArg (fun z : {i // i ∈ insert x U} => (z : α)) hab
          simpa [insertIndexMap] using h
        exact False.elim (hxU (hv ▸ a.2))
      | inr b =>
        have hv : a.1 = b.1 := by
          have h := congrArg (fun z : {i // i ∈ insert x U} => (z : α)) hab
          simpa [insertIndexMap] using h
        exact congrArg Sum.inr (Subtype.ext hv)
  , by
    intro s
    rcases Finset.mem_insert.mp s.2 with hxs | hsU
    · refine ⟨Sum.inl (), ?_⟩
      apply Subtype.ext
      exact hxs.symm
    · refine ⟨Sum.inr ⟨s.1, hsU⟩, ?_⟩
      apply Subtype.ext
      rfl⟩

theorem schur_principal_det_unit {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℝ) (ξ : α → ℝ) (x : α) (U : Finset α) (hxU : x ∉ U)
    (hden : M x x + ξ x ≠ 0)
    (hprincipal : ∀ T : Finset α,
      IsUnit (((M + Matrix.diagonal ξ).submatrix
        (fun i : {i // i ∈ T} => (i : α)) (fun i : {i // i ∈ T} => (i : α))).det)) :
    IsUnit (schurShifted M ξ x U).det := by
  classical
  let S := insert x U
  let e : Unit ⊕ {i // i ∈ U} ≃ {i // i ∈ S} := insertIndexEquiv x U hxU
  have he : ∀ z, e z = insertIndexMap x U z := by
    intro z
    rfl
  let P := M + Matrix.diagonal ξ
  let Psub : Matrix {i // i ∈ S} {i // i ∈ S} ℝ :=
    P.submatrix (fun i : {i // i ∈ S} => (i : α)) (fun i => (i : α))
  let A : Matrix Unit Unit ℝ := fun _ _ => M x x + ξ x
  let B : Matrix Unit {i // i ∈ U} ℝ := fun _ j => M x j
  let C : Matrix {i // i ∈ U} Unit ℝ := fun i _ => M i x
  let D : Matrix {i // i ∈ U} {i // i ∈ U} ℝ :=
    P.submatrix (fun i : {i // i ∈ U} => (i : α)) (fun i => (i : α))
  have hBlock :
      Psub.submatrix e e = Matrix.fromBlocks A B C D := by
    ext i j
    change Psub (e i) (e j) = (Matrix.fromBlocks A B C D) i j
    rw [he i, he j]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [Psub, A, P, insertIndexMap, Matrix.fromBlocks, Matrix.diagonal_apply]
      | inr j =>
        have hj : x ≠ j.1 := fun h => hxU (h ▸ j.2)
        simp [Psub, B, P, insertIndexMap, Matrix.fromBlocks, Matrix.diagonal_apply, hj]
    | inr i =>
      cases j with
      | inl j =>
        have hi : x ≠ i.1 := fun h => hxU (h ▸ i.2)
        simp [Psub, C, P, insertIndexMap, Matrix.fromBlocks, Matrix.diagonal_apply,
          Ne.symm hi]
      | inr j =>
        simp [Psub, D, P, insertIndexMap, Matrix.fromBlocks, Matrix.diagonal_apply]
  have hdetS : IsUnit
      Psub.det := by
    exact hprincipal S
  have hdetBlock : IsUnit
      ((Psub.submatrix e e).det) := by
    rw [Matrix.det_submatrix_equiv_self]
    exact hdetS
  have hA : IsUnit A := by
    apply (Matrix.isUnit_iff_isUnit_det A).2
    have hdetA : A.det = M x x + ξ x := by
      calc
        A.det = A default default := Matrix.det_unique A
        _ = M x x + ξ x := rfl
    rw [hdetA, isUnit_iff_ne_zero]
    exact hden
  letI : Invertible A := hA.invertible
  have hBlockUnit : IsUnit (Matrix.fromBlocks A B C D) := by
    have hUnitReindex : IsUnit (Psub.submatrix e e) :=
      (Matrix.isUnit_iff_isUnit_det _).2 hdetBlock
    rw [← hBlock]
    exact hUnitReindex
  have hSchurUnit : IsUnit (D - C * ⅟A * B) :=
    (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁).1 hBlockUnit
  have hInvMatrix : A⁻¹ = fun _ _ => (M x x + ξ x)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    ext i j
    change (∑ k : Unit, (M x x + ξ x) * (M x x + ξ x)⁻¹) = 1
    simp
    field_simp [hden]
  have hInvEntry : (⅟A) () () = (M x x + ξ x)⁻¹ := by
    rw [Matrix.invOf_eq_nonsing_inv, hInvMatrix]
  have hInvFun : ⅟A = fun _ _ => (M x x + ξ x)⁻¹ := by
    rw [Matrix.invOf_eq_nonsing_inv, hInvMatrix]
  have hSchurEq : D - C * ⅟A * B = schurShifted M ξ x U := by
    ext i j
    have hprod : (C * ⅟A * B) i j = M i x * (⅟A () ()) * M x j := by
      change (∑ k : Unit, (∑ l : Unit, M i x * ⅟A l k) * M x j) = _
      simp
    simp only [Matrix.sub_apply]
    rw [hprod, hInvEntry]
    simp [D, P, schurShifted, schurEntry, Matrix.diagonal, Matrix.diagonal_apply]
    field_simp [hden]
    ring
  rw [← hSchurEq]
  exact (Matrix.isUnit_iff_isUnit_det _).1 hSchurUnit

end AndersonAC.AgentS6Construct
