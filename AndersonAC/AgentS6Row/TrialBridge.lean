import AndersonAC.AgentS6Row.Bounds
import AndersonAC.S6.Statements
import AndersonAC.L64.Heat
import AndersonAC.AgentS6.RunningPrestate

open Matrix ComplexConjugate MeasureTheory

namespace AndersonAC.AgentS6Row

open AndersonAC.L64
open AndersonAC.S6

variable {R U : Type*} [Fintype R] [DecidableEq R] [Fintype U] [DecidableEq U]

lemma inv_fromBlocks₂₂_topLeft (A : Matrix R R ℂ) (B : Matrix R U ℂ)
    (C : Matrix U R ℂ) (D : Matrix U U ℂ)
    [Invertible D] [Invertible (A - B * ⅟D * C)] :
    ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₁₁ = (A - B * ⅟D * C)⁻¹ := by
  letI : Invertible (Matrix.fromBlocks A B C D) := Matrix.fromBlocks₂₂Invertible A B C D
  have h := Matrix.invOf_fromBlocks₂₂_eq A B C D
  rw [← invOf_eq_nonsing_inv, h]
  simp only [Matrix.toBlocks_fromBlocks₁₁, invOf_eq_nonsing_inv]

lemma inv_reindex_sum_topLeft {α R : Type*} [Fintype α] [DecidableEq α]
    [Fintype R] [DecidableEq R] (e : α ≃ R ⊕ Unit) (N : Matrix α α ℂ)
    (A : Matrix R R ℂ) (B : Matrix R Unit ℂ) (C : Matrix Unit R ℂ)
    (D : Matrix Unit Unit ℂ)
    (hBlock : Matrix.reindex e e N = Matrix.fromBlocks A B C D)
    (hD : IsUnit D) (hS : IsUnit (A - B * D⁻¹ * C)) :
    ∀ i j, N⁻¹ (e.symm (Sum.inl i)) (e.symm (Sum.inl j)) =
      (A - B * D⁻¹ * C)⁻¹ i j := by
  haveI : Invertible D := hD.nonempty_invertible.some
  have hS' : IsUnit (A - B * ⅟D * C) := by
    have hS'' := hS
    rw [← invOf_eq_nonsing_inv] at hS''
    exact hS''
  haveI : Invertible (A - B * ⅟D * C) := hS'.nonempty_invertible.some
  have hTop := inv_fromBlocks₂₂_topLeft A B C D
  have hN : (Matrix.fromBlocks A B C D)⁻¹ = Matrix.reindex e e N⁻¹ := by
    rw [← hBlock, Matrix.inv_reindex]
  rw [hN] at hTop
  intro i j
  have h := congrFun (congrFun hTop i) j
  simpa [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.of_apply,
    invOf_eq_nonsing_inv] using h

noncomputable def deleteSumEquiv {ι : Type*} [DecidableEq ι] (x : ι) :
    ι ≃ ({i : ι // i ≠ x} ⊕ Unit) where
  toFun i := if hi : i ≠ x then Sum.inl ⟨i, hi⟩ else Sum.inr ()
  invFun
    | Sum.inl i => i.1
    | Sum.inr _ => x
  left_inv i := by
    by_cases hi : i = x
    · subst i; simp
    · simp [hi]
  right_inv i := by
    cases i with
    | inl j => simp [j.2]
    | inr u => cases u; simp

def eraseSubtypeEquiv {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι) (hx : x ∈ s) :
    {i : ι // i ∈ s.erase x} ≃ {i : {i : ι // i ∈ s} // i ≠ ⟨x, hx⟩} where
  toFun i := by
    let hi : i.1 ≠ x := (Finset.mem_erase.mp i.2).1
    let a : {i : ι // i ∈ s} := ⟨i.1, (Finset.mem_erase.mp i.2).2⟩
    refine ⟨a, ?_⟩
    intro h
    apply hi
    exact congrArg Subtype.val h
  invFun i := by
    have hi : x ≠ i.1.1 := by
      intro h
      apply i.2
      apply Subtype.ext
      exact h.symm
    exact ⟨i.1.1, Finset.mem_erase.mpr ⟨hi.symm, i.1.2⟩⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; apply Subtype.ext; rfl

lemma damped_schur_inverse_minor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ) (x : ι) (ξ : ℝ)
    (M' : Matrix {i : ι // i ≠ x} {i : ι // i ≠ x} ℝ)
    (hM' : M'.IsSymm) (ht : 0 < t) (hp : ∀ i, 0 < (r i).im)
    (hden : M x x + ξ ≠ 0)
    (hupdate : ∀ i j, M' i j = M i.1 j.1 - M i.1 x * M x j.1 / (M x x + ξ)) :
    ∀ i j, (damped M' t (fun i => r i.1))⁻¹ i j =
      (dampedPost M t r x ξ)⁻¹ i.1 j.1 := by
  let e := deleteSumEquiv x
  let N : Matrix ι ι ℂ := dampedPost M t r x ξ
  let N' := Matrix.reindex e e N
  let A : Matrix {i : ι // i ≠ x} {i : ι // i ≠ x} ℂ := N'.toBlocks₁₁
  let B : Matrix {i : ι // i ≠ x} Unit ℂ := N'.toBlocks₁₂
  let C : Matrix Unit {i : ι // i ≠ x} ℂ := N'.toBlocks₂₁
  let D : Matrix Unit Unit ℂ := fun _ _ => ((M x x + ξ : ℝ) : ℂ)
  have hblock : N' = Matrix.fromBlocks A B C D := by
    have hD : N'.toBlocks₂₂ = D := by
      ext u v
      cases u
      cases v
      simp [D, N', N, Matrix.toBlocks₂₂, Matrix.reindex_apply, e, deleteSumEquiv,
        dampedPost, damped, Matrix.diagonal_apply, Pi.single_apply]
    calc
      N' = Matrix.fromBlocks N'.toBlocks₁₁ N'.toBlocks₁₂ N'.toBlocks₂₁ N'.toBlocks₂₂ :=
        N'.fromBlocks_toBlocks.symm
      _ = Matrix.fromBlocks A B C D := by rw [hD]
  have hDunit : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hd : IsUnit ((M x x + ξ : ℝ) : ℂ) :=
      isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hden)
    have hdet : D.det = ((M x x + ξ : ℝ) : ℂ) := by
      have hdet' := Matrix.det_unique D
      simpa [D, Complex.ofReal_add] using hdet'
    rw [hdet]
    exact hd
  have hDinverse : D⁻¹ = fun _ _ => ((M x x + ξ : ℝ) : ℂ)⁻¹ := by
    ext u v
    rw [Matrix.inv_subsingleton]
    simp [D]
  have hSchur : A - B * D⁻¹ * C = damped M' t (fun i => r i.1) := by
    ext i j
    have hA : A i j = N i.1 j.1 := by
      simp [A, N', Matrix.toBlocks₁₁, Matrix.reindex_apply, e, deleteSumEquiv]
    have hB : B i () = N i.1 x := by
      simp [B, N', Matrix.toBlocks₁₂, Matrix.reindex_apply, e, deleteSumEquiv]
    have hC : C () j = N x j.1 := by
      simp [C, N', Matrix.toBlocks₂₁, Matrix.reindex_apply, e, deleteSumEquiv]
    have hBD : (B * D⁻¹) i () = B i () * D⁻¹ () () := by
      simp [Matrix.mul_apply]
    have hprod : (B * D⁻¹ * C) i j =
        N i.1 x * (((M x x + ξ : ℝ) : ℂ)⁻¹) * N x j.1 := by
      rw [Matrix.mul_apply]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hBD, hB, hDinverse, hC]
    have hNij : N i.1 j.1 =
        (M i.1 j.1 : ℂ) - (if i = j then (t : ℂ) * r i.1 else 0) := by
      simp [N, dampedPost, damped, Matrix.diagonal_apply, Matrix.one_apply,
        i.property, j.property, Subtype.ext_iff]
    have hNix : N i.1 x = (M i.1 x : ℂ) := by
      simp [N, dampedPost, damped, Matrix.diagonal_apply, Matrix.one_apply,
        i.property, Ne.symm i.property]
    have hNxj : N x j.1 = (M x j.1 : ℂ) := by
      simp [N, dampedPost, damped, Matrix.diagonal_apply, Matrix.one_apply,
        j.property, Ne.symm j.property]
    have hM'entry : damped M' t (fun i => r i.1) i j =
        (M' i j : ℂ) - (if i = j then (t : ℂ) * r i.1 else 0) := by
      simp [damped, Matrix.diagonal_apply, Matrix.one_apply]
    rw [Matrix.sub_apply, hA, hprod, hNij, hNix, hNxj, hM'entry, hupdate i j]
    push_cast
    field_simp [hden]
    ring
  have hSunit : IsUnit (A - B * D⁻¹ * C) := by
    rw [hSchur]
    exact (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_det_damped M' t (fun i => r i.1) hM' ht (fun i => hp i.1))
  intro i j
  have h := inv_reindex_sum_topLeft e N A B C D hblock hDunit hSunit i j
  rw [hSchur] at h
  exact h.symm

theorem stoppedTrial_active_iff_pivots_avoided
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
    (q : StoppedTrial (Ω := Ω) core t r g0 order) :
    ∀ k ω, k ≤ q.stop ω → ∀ i,
      (i ∈ (q.state k ω).active ↔ ∀ j, j < k → q.pivot j ω ≠ i) := by
  classical
  intro k
  induction k with
  | zero =>
      intro ω hk i
      simp [q.initial_active]
  | succ k ih =>
      intro ω hk i
      have hrun : k < q.stop ω := by omega
      rcases q.heat k ω hrun with ⟨hx, hxcore, hactive, hden, hM, hhat⟩
      have hkprev : k ≤ q.stop ω := by omega
      rw [hactive, Finset.mem_erase]
      rw [ih ω hkprev i]
      constructor
      · rintro ⟨hlast, hprev⟩ j hj
        rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hjk | rfl
        · exact hprev j hjk
        · exact hlast.symm
      · intro hall
        refine ⟨?_, ?_⟩
        · exact (hall k (Nat.lt_succ_iff_lt_or_eq.mpr (Or.inr rfl))).symm
        · intro j hj
          exact hall j (Nat.lt_succ_iff_lt_or_eq.mpr (Or.inl hj))

theorem stoppedTrial_running_active_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {core : Finset (Fin n)} {t : ℝ}
    {r : Ω → Fin n → ℂ} {g0 : Ω → Matrix (Fin n) (Fin n) ℂ}
    {order : Fin n ≃ Fin (Fintype.card (Fin n))}
    [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]
    (q : StoppedTrial (Ω := Ω) core t r g0 order) (k : ℕ) (i : Fin n) :
    MeasurableSet[q.history k] {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active} := by
  classical
  have hrun : MeasurableSet[q.history k] {ω | k < q.stop ω} := by
    have hle := q.stopping.measurableSet_le k
    have heq : {ω | k < q.stop ω} = {ω | ¬ (q.stop ω : WithTop ℕ) ≤ k} := by
      ext ω
      simp
    rw [heq]
    exact hle.compl
  have hpivots : MeasurableSet[q.history k] {ω | ∀ j < k, q.pivot j ω ≠ i} := by
    have hP : {ω | ∀ j < k, q.pivot j ω ≠ i} =
        ⋂ j ∈ Finset.range k, {ω | q.pivot j ω ≠ i} := by
      ext ω
      simp
    rw [hP]
    apply Finset.measurableSet_biInter
    intro j hj
    have hp : Measurable[q.history k] (q.pivot j) :=
      (q.pivot_predictable j).mono (q.history.mono (Nat.le_of_lt (Finset.mem_range.mp hj))) le_rfl
    have hEq : MeasurableSet[q.history k] {ω | q.pivot j ω = i} :=
      hp (MeasurableSet.singleton i)
    have hNe : {ω | q.pivot j ω ≠ i} = {ω | q.pivot j ω = i}ᶜ := by
      ext ω
      simp
    rw [hNe]
    exact hEq.compl
  have hEq : {ω | k < q.stop ω ∧ i ∈ (q.state k ω).active} =
      {ω | k < q.stop ω} ∩ {ω | ∀ j < k, q.pivot j ω ≠ i} := by
    ext ω
    by_cases hk : k < q.stop ω
    · simp [hk, stoppedTrial_active_iff_pivots_avoided q k ω (Nat.le_of_lt hk) i]
    · simp [hk]
  rw [hEq]
  exact hrun.inter hpivots

end AndersonAC.AgentS6Row
