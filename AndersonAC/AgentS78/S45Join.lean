import AndersonAC.S45.Definitions
import AndersonAC.S78.Definitions

/-!
Transport between the §§4–5 matrix state (`S45.State κ`, indexed by the active
sites through an equivalence `e : κ ≃ s.active`, e.g. `κ = Fin n`) and the
§§7–8 ambient endpoint (`S78.Endpoint ι` with active set `s.active`).

Under the §4 state hypotheses `g.IsSymm` and `ward t` (both required of `old`
by `S45.ordinary_sweep_endpoint`), the S78 endpoint energy is the S45 quadratic
form of `D`, the S78 variational inverse energy is the S45 dual form `X`
(for every charge, no neutrality needed), and the S78 fourth-row sums are the
S45 fourth rows.
-/

open scoped BigOperators
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The S45 state carried by the active block of an S78 endpoint. -/
def toS45 (s : AndersonAC.S78.Endpoint ι) (r : ι → ℂ) (e : κ ≃ s.active) : AndersonAC.S45.State κ where
  g := fun i j => s.g (e i).val (e j).val
  r := fun i => r (e i).val

theorem sum_active_equiv (A : Finset ι) (e : κ ≃ A) (F : ι → ℝ) :
    ∑ i : κ, F (e i).val = ∑ x ∈ A, F x := by
  rw [Equiv.sum_comp e (fun a : A => F a.val), Finset.sum_coe_sort A F]

/-- Ward row identity of an S45 state: `q_i = Σ_j p_j |h_ij|²`. -/
theorem S45_ward_row (st : AndersonAC.S45.State κ) (t : ℝ) (hw : st.ward t) (i : κ) :
    st.q i = ∑ j, st.p j * ‖st.h t i j‖ ^ 2 := by
  have h := congrFun (congrFun hw i) i
  simp only [AndersonAC.S45.matrixIm, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.re_sum] at hre
  unfold AndersonAC.S45.State.q
  rw [← hre]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (st.h t i j) _, mul_assoc, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The S45 quadratic form of `D` is the Ward edge energy (Ward + symmetry). -/
theorem S45_qform_D (st : AndersonAC.S45.State κ) (t : ℝ) (hsym : st.g.IsSymm) (hw : st.ward t)
    (f : κ → ℝ) :
    AndersonAC.S45.qform (st.D t) f =
      (1 / 2) * ∑ i, ∑ j, st.p i * st.p j * ‖st.h t i j‖ ^ 2 * (f i - f j) ^ 2 := by
  have hsymh : ∀ i j, ‖st.h t i j‖ = ‖st.h t j i‖ := by
    intro i j
    have : st.g j i = st.g i j := by
      have := congrFun (congrFun hsym i) j
      simpa [Matrix.transpose_apply] using this
    simp [AndersonAC.S45.State.h, this]
  have hrow := S45_ward_row st t hw
  set w : κ → κ → ℝ := fun i j => st.p i * st.p j * ‖st.h t i j‖ ^ 2 with hwdef
  have h1 : ∑ i, ∑ j, w i j * f i ^ 2 = ∑ i, st.p i * st.q i * f i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow i, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hwdef]; ring
  have h2 : ∑ i, ∑ j, w i j * f j ^ 2 = ∑ j, st.p j * st.q j * f j ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrow j, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hwdef]; rw [hsymh i j]; ring
  have hR : (1 / 2) * ∑ i, ∑ j, w i j * (f i - f j) ^ 2 =
      ∑ i, st.p i * st.q i * f i ^ 2 - ∑ i, ∑ j, w i j * (f i * f j) := by
    have e : ∀ i j, w i j * (f i - f j) ^ 2 =
        w i j * f i ^ 2 + w i j * f j ^ 2 - 2 * (w i j * (f i * f j)) := by intro i j; ring
    simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
    ring
  have hL : AndersonAC.S45.qform (st.D t) f =
      ∑ i, st.p i * st.q i * f i ^ 2 - ∑ i, ∑ j, w i j * (f i * f j) := by
    unfold AndersonAC.S45.qform AndersonAC.S45.State.D
    simp only [Matrix.sub_mulVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mulVec_diagonal]; ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hwdef, AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare, Finset.sum_ite_eq',
        Finset.sum_ite_eq, Matrix.diagonal_apply]
      ring
  rw [hL, ← hR]

/-- The S78 endpoint energy is the S45 form of `D` on the active block. -/
theorem endpointEnergy_eq_S45 (s : AndersonAC.S78.Endpoint ι) (r : ι → ℂ) (t : ℝ) (e : κ ≃ s.active)
    (hsym : (toS45 s r e).g.IsSymm) (hw : (toS45 s r e).ward t) (f : ι → ℝ) :
    AndersonAC.S78.endpointEnergy s r t f =
      AndersonAC.S45.qform ((toS45 s r e).D t) (fun i => f (e i).val) := by
  rw [S45_qform_D _ t hsym hw]
  unfold AndersonAC.S78.endpointEnergy AndersonAC.S78.wardEnergy
  congr 1
  rw [← sum_active_equiv s.active e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_active_equiv s.active e]
  rfl

/-- The S78 variational inverse energy is the S45 dual form, for every charge. -/
theorem inverseEnergy_eq_S45X (s : AndersonAC.S78.Endpoint ι) (r : ι → ℂ) (t : ℝ) (e : κ ≃ s.active)
    (hsym : (toS45 s r e).g.IsSymm) (hw : (toS45 s r e).ward t) (y : ι → ℝ) :
    AndersonAC.S78.inverseEnergy s.active (AndersonAC.S78.endpointEnergy s r t) y =
      (toS45 s r e).X t (fun i => y (e i).val) := by
  unfold AndersonAC.S78.inverseEnergy AndersonAC.S45.State.X AndersonAC.S45.dualForm
  congr 1
  ext a
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨fun i => f (e i).val, ?_⟩
    rw [endpointEnergy_eq_S45 s r t e hsym hw f, sum_active_equiv s.active e (fun x => y x * f x)]
  · rintro ⟨g, rfl⟩
    classical
    let f : ι → ℝ := fun x => if hx : x ∈ s.active then g (e.symm ⟨x, hx⟩) else 0
    have hf : (fun i => f (e i).val) = g := by
      funext i
      simp [f, (e i).property]
    refine ⟨f, ?_⟩
    rw [endpointEnergy_eq_S45 s r t e hsym hw f, hf,
      ← sum_active_equiv s.active e (fun x => y x * f x)]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show f (e i).val = g i from congrFun hf i]

/-- Neutral S78 charges on the active set restrict to neutral S45 charges. -/
theorem neutral_to_S45 (A : Finset ι) (e : κ ≃ A) (y : ι → ℝ) (hy : AndersonAC.S78.neutral A y) :
    AndersonAC.S45.neutral (fun i => y (e i).val) := by
  unfold AndersonAC.S45.neutral
  rw [sum_active_equiv A e y]
  exact hy.2

/-- The S78 fourth row on an active site is the S45 fourth row of the active block. -/
theorem rowFour_eq_S45 (s : AndersonAC.S78.Endpoint ι) (r : ι → ℂ) (t : ℝ) (e : κ ≃ s.active)
    (hzero : ∀ i j, i ∉ s.active ∨ j ∉ s.active → s.g i j = 0) (i : κ) :
    AndersonAC.S78.rowFour (AndersonAC.S78.normalizedInverse s t) (e i).val =
      (toS45 s r e).fourthRow t Finset.univ i := by
  unfold AndersonAC.S78.rowFour AndersonAC.S45.State.fourthRow
  rw [← Finset.sum_subset (Finset.subset_univ s.active), ← sum_active_equiv s.active e]
  · rfl
  · intro x _ hx
    simp [AndersonAC.S78.normalizedInverse, hzero _ _ (Or.inr hx)]

/-- Off the active set the S78 fourth row vanishes. -/
theorem rowFour_inactive (s : AndersonAC.S78.Endpoint ι) (t : ℝ)
    (hzero : ∀ i j, i ∉ s.active ∨ j ∉ s.active → s.g i j = 0) (i : ι) (hi : i ∉ s.active) :
    AndersonAC.S78.rowFour (AndersonAC.S78.normalizedInverse s t) i = 0 := by
  unfold AndersonAC.S78.rowFour
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [AndersonAC.S78.normalizedInverse, hzero _ _ (Or.inl hi)]

end AndersonAC.AgentS78
