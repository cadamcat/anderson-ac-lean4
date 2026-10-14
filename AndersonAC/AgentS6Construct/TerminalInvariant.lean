import AndersonAC.AgentS6Construct.Core
import AndersonAC.AgentS6Construct.Terminal

noncomputable section

namespace AndersonAC.AgentS6Construct

open AndersonAC.S6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finsetImageEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (s : Finset α) :
    {x // x ∈ s} ≃ {y // y ∈ s.image f} :=
  Equiv.ofBijective
    (fun x => ⟨f x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact hf (congrArg Subtype.val h)
    , by
      intro y
      rcases Finset.mem_image.mp y.2 with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy⟩

def allPrincipalMinorUnits {core : Finset ι} (s : TrialState core)
    (ξ : {i // i ∈ s.active} → ℝ) : Prop :=
  ∀ T : Finset {i // i ∈ s.active},
    IsUnit (((s.M + Matrix.diagonal (fun i => ξ i)).submatrix
      (fun i : {i // i ∈ T} => (i : {i // i ∈ s.active}))
      (fun i : {i // i ∈ T} => (i : {i // i ∈ s.active}))).det)

theorem initialState_allPrincipalMinorUnits (core : Finset ι) (M : Matrix ι ι ℝ)
    (G : Matrix ι ι ℂ) (hM : M.IsSymm) (ξ : ι → ℝ)
    (hterminal : ∀ T : Finset ι,
      IsUnit (((M + Matrix.diagonal ξ).submatrix
        (fun i : {i // i ∈ T} => (i : ι))
        (fun i : {i // i ∈ T} => (i : ι))).det)) :
    allPrincipalMinorUnits (initialState core M G hM) (fun i => ξ i.1) := by
  classical
  let s := initialState core M G hM
  change allPrincipalMinorUnits s (fun i => ξ i.1)
  unfold allPrincipalMinorUnits
  intro T
  let f : {i // i ∈ s.active} → ι := fun i => i.1
  let U := T.image f
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext hij
  let e := finsetImageEquiv f hf T
  have heval (i : {i // i ∈ T}) : (e i).1 = i.1.1 := rfl
  have hmat :
      (((s.M + Matrix.diagonal (fun i : {i // i ∈ s.active} => ξ i.1)).submatrix
        (fun i : {i // i ∈ T} => i.1) (fun i : {i // i ∈ T} => i.1))) =
      ((M + Matrix.diagonal ξ).submatrix
        (fun i : {i // i ∈ U} => (i : ι)) (fun i : {i // i ∈ U} => (i : ι))).submatrix e e := by
    ext i j
    change M (i.1.1) (j.1.1) +
        (if i.1 = j.1 then ξ i.1.1 else 0) =
      M ((e i).1) ((e j).1) +
        (if (e i).1 = (e j).1 then ξ (e i).1 else 0)
    rw [heval i, heval j]
    simp only [Subtype.ext_iff]
  rw [hmat, Matrix.det_submatrix_equiv_self]
  exact hterminal U

theorem heatState_allPrincipalMinorUnits {core : Finset ι} (s : TrialState core)
    (t : ℝ) (r : ι → ℂ) (ξ : ι → ℝ) (x : ι)
    (hx : x ∈ s.active) (hxc : x ∉ core)
    (hden : s.M ⟨x, hx⟩ ⟨x, hx⟩ + ξ x ≠ 0)
    (hs : allPrincipalMinorUnits s (fun i => ξ i.1)) :
    allPrincipalMinorUnits (heatState t r s x hx hxc (ξ x)) (fun i => ξ i.1) := by
  classical
  let s' := heatState t r s x hx hxc (ξ x)
  let oldIndex := {i // i ∈ s.active}
  let newIndex := {i // i ∈ s'.active}
  let x' : oldIndex := ⟨x, hx⟩
  let ξold : oldIndex → ℝ := fun i => ξ i.1
  let ξnew : newIndex → ℝ := fun i => ξ i.1
  let f : newIndex → oldIndex := fun i =>
    ⟨i.1, (Finset.mem_erase.mp (by simpa [s', heatState] using i.2)).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hv : i.1 = j.1 := congrArg (fun z : oldIndex => z.1) hij
    exact Subtype.ext hv
  intro T
  let U := T.image f
  let e := finsetImageEquiv f hf T
  have hxU : x' ∉ U := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, hi, hix⟩
    have hval : i.1 = x := congrArg Subtype.val hix
    have hi' : i.1 ∈ s.active.erase x := by simpa [s', heatState] using i.2
    exact (Finset.mem_erase.mp hi').1 hval
  have hprincipal : ∀ V : Finset oldIndex,
      IsUnit (((s.M + Matrix.diagonal ξold).submatrix
        (fun i : {i // i ∈ V} => (i : oldIndex))
        (fun i : {i // i ∈ V} => (i : oldIndex))).det) := by
    intro V
    exact hs V
  have hden' : s.M x' x' + ξold x' ≠ 0 := by simpa [x', ξold] using hden
  have hminor := schur_principal_det_unit s.M ξold x' U hxU hden' hprincipal
  have hmat :
      ((s'.M + Matrix.diagonal ξnew).submatrix
        (fun i : {i // i ∈ T} => (i : newIndex))
        (fun i : {i // i ∈ T} => (i : newIndex))) =
      (schurShifted s.M ξold x' U).submatrix e e := by
    ext i j
    have hiErase : i.1.1 ∈ s.active.erase x := by
      change i.1.1 ∈ s.active.erase x
      simpa [s', heatState] using i.1.2
    have hjErase : j.1.1 ∈ s.active.erase x := by
      change j.1.1 ∈ s.active.erase x
      simpa [s', heatState] using j.1.2
    have hei : (e i).1 = (⟨i.1.1, Finset.mem_of_mem_erase hiErase⟩ : oldIndex) := rfl
    have hej : (e j).1 = (⟨j.1.1, Finset.mem_of_mem_erase hjErase⟩ : oldIndex) := rfl
    change heatMatrix s x hx (ξ x) i.1 j.1 +
        (if i.1 = j.1 then ξ i.1.1 else 0) =
      schurShifted s.M ξold x' U (e i) (e j)
    simp only [schurShifted, schurEntry]
    rw [hei, hej]
    simp [heatMatrix, ξold, ξnew, x']
  change IsUnit (((s'.M + Matrix.diagonal ξnew).submatrix
    (fun i : {i // i ∈ T} => (i : newIndex))
    (fun i : {i // i ∈ T} => (i : newIndex))).det)
  rw [hmat, Matrix.det_submatrix_equiv_self]
  exact hminor

theorem pivot_denominator_ne_zero {core : Finset ι} (s : TrialState core)
    (ξ : {i // i ∈ s.active} → ℝ) (x : {i // i ∈ s.active})
    (hminor : allPrincipalMinorUnits s ξ) :
    s.M x x + ξ x ≠ 0 := by
  classical
  let T : Finset {i // i ∈ s.active} := {x}
  let I := {i // i ∈ T}
  letI : Subsingleton I := ⟨fun a b => by
    apply Subtype.ext
    have ha : a.1 = x := Finset.mem_singleton.mp a.2
    have hb : b.1 = x := Finset.mem_singleton.mp b.2
    exact ha.trans hb.symm⟩
  have hunit := hminor T
  have hdet :
      (((s.M + Matrix.diagonal ξ).submatrix
        (fun i : I => (i : {i // i ∈ s.active}))
        (fun i : I => (i : {i // i ∈ s.active}))).det) = s.M x x + ξ x := by
    rw [Matrix.det_eq_elem_of_subsingleton
      (A := (s.M + Matrix.diagonal ξ).submatrix
        (fun i : I => (i : {i // i ∈ s.active}))
        (fun i : I => (i : {i // i ∈ s.active}))) ⟨x, Finset.mem_singleton_self _⟩]
    simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.diagonal_apply]
  rw [hdet] at hunit
  exact isUnit_iff_ne_zero.mp hunit

end AndersonAC.AgentS6Construct
