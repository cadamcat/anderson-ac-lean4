import AndersonAC.L64.Resolvent
import AndersonAC.L64.Cancellation

/-!
# Lemma 6.4: the heat update

A heat at `x` changes the damped diagonal at `x` by `ξ + t r_x` (paper l.381–389). The new
active inverse is the `A ∖ {x}` block of `(M - t diag r + (ξ + t r_x) e_x e_xᵀ)⁻¹`, given by the
Sherman–Morrison identity (eq. `clearing-heat-update`):
`g'_{ij} = g_{ij} - a g_{ix} g_{xj} / (1 + a g_{xx})`, `a = ξ + t r_x`.
On surviving exterior rows the cross block becomes `𝒞'_i = 𝒞_i + c_x v_i 𝒞_x` with
`c_x = -a/(√t (1 + a g_xx))` and `v_i = h_{ix} √(p_i/p_x)` (eq. `clearing-cross-update`).
-/

open Matrix Finset ComplexConjugate Complex

set_option linter.unusedSectionVars false

namespace AndersonAC.L64

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mul_vecMulVec_apply (M : Matrix ι ι ℂ) (u v : ι → ℂ) (i j : ι) :
    (M * vecMulVec u v) i j = (M *ᵥ u) i * v j := by
  simp only [mul_apply, vecMulVec_apply, mulVec, dotProduct, sum_mul]
  exact sum_congr rfl fun k _ => by ring

/-- Sherman–Morrison for a rank-one diagonal update at `x`. -/
lemma sherman_morrison (Dm : Matrix ι ι ℂ) (hD : IsUnit Dm.det) (x : ι) (a : ℂ)
    (ha : 1 + a * Dm⁻¹ x x ≠ 0) :
    (Dm + diagonal (Pi.single x a))⁻¹
      = Dm⁻¹ - (a / (1 + a * Dm⁻¹ x x)) • vecMulVec (fun i => Dm⁻¹ i x) (fun j => Dm⁻¹ x j) := by
  apply Matrix.inv_eq_right_inv
  have h1 : Dm * Dm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD
  have hcol : Dm *ᵥ (fun i => Dm⁻¹ i x) = Pi.single x 1 := by
    ext i
    have := congrFun (congrFun h1 i) x
    simp only [mul_apply, Matrix.one_apply] at this
    simp only [mulVec, dotProduct, this, Pi.single_apply]
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_smul, h1]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, mul_vecMulVec_apply, hcol,
    diagonal_mul, smul_eq_mul, vecMulVec_apply, Matrix.one_apply, Pi.single_apply]
  by_cases hi : i = x
  · subst hi
    simp only [if_true]
    field_simp
    split_ifs <;> ring
  · simp [hi]

section Post

variable (M : Matrix ι ι ℝ) (t : ℝ) (r : ι → ℂ)

/-- the post-heat damped matrix `M - t diag r + (ξ + t r_x) e_x e_xᵀ`. -/
noncomputable def dampedPost (x : ι) (ξ : ℝ) : Matrix ι ι ℂ :=
  damped M t r + diagonal (Pi.single x ((ξ : ℂ) + (t : ℂ) * r x))

/-- the heat coefficient `c_x = -(ξ + t r_x)/(√t (1 + (ξ + t r_x) g_xx))`. -/
noncomputable def heatCoeff (x : ι) (ξ : ℝ) : ℂ :=
  -((ξ : ℂ) + (t : ℂ) * r x)
    / (((√t : ℝ) : ℂ) * (1 + ((ξ : ℂ) + (t : ℂ) * r x) * (damped M t r)⁻¹ x x))

/-- `v_i = h_{ix} √(p_i/p_x)`, `h = √t g`. -/
noncomputable def heatVec (x : ι) (i : ι) : ℂ :=
  ((√t : ℝ) : ℂ) * (damped M t r)⁻¹ i x * ((√((r i).im / (r x).im) : ℝ) : ℂ)

variable {M t r}

/-- the imaginary parts `p = Im r`. -/
abbrev pim (r : ι → ℂ) : ι → ℝ := fun i => (r i).im

lemma heatVec_eq (ht : 0 < t) (hp : ∀ i, 0 < (r i).im) (x : ι) {i : ι} (hix : i ≠ x) :
    heatVec M t r x i
      = (1 / (2 * I * ((√t : ℝ) : ℂ) * (((r x).im : ℝ) : ℂ))) * scat t (pim r) (damped M t r)⁻¹ i x := by
  rw [scat_apply_ne _ _ _ hix, heatVec]
  have hpx := hp x
  have hsx : (√((r x).im) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpx).ne'
  have hst : (√t : ℝ) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have e1 : √((r i).im / (r x).im) = √((r i).im) / √((r x).im) :=
    Real.sqrt_div' _ hpx.le
  have e2 : ((t : ℝ) : ℂ) = ((√t : ℝ) : ℂ) * ((√t : ℝ) : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt ht.le]
  have e3 : (((r x).im : ℝ) : ℂ) = ((√((r x).im) : ℝ) : ℂ) * ((√((r x).im) : ℝ) : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt hpx.le]
  have hsx' : ((√((r x).im) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsx
  have hst' : ((√t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hst
  rw [e1, e2, e3]
  simp only [pim]
  push_cast
  field_simp

/-- The post-heat cross rows, eq. `clearing-cross-update`: `𝒞'_i = 𝒞_i + c_x v_i 𝒞_x`. -/
lemma post_crossRow (ht : 0 < t) (hp : ∀ i, 0 < (r i).im) (hD : IsUnit (damped M t r).det)
    {B : Finset ι} {x : ι} (hx : x ∉ B) (ξ : ℝ)
    (ha : 1 + ((ξ : ℂ) + (t : ℂ) * r x) * (damped M t r)⁻¹ x x ≠ 0)
    {i : ι} (hi : i ∈ Bᶜ.erase x) :
    crossRow (scat t (pim r) (dampedPost M t r x ξ)⁻¹) B i
      = crossRow (scat t (pim r) (damped M t r)⁻¹) B i
        + (heatCoeff M t r x ξ * heatVec M t r x i) • crossRow (scat t (pim r) (damped M t r)⁻¹) B x := by
  have hiB : i ∉ B := mem_compl.mp (mem_of_mem_erase hi)
  have hix : i ≠ x := ne_of_mem_erase hi
  ext b
  have hib : i ≠ (b : ι) := fun h => hiB (h ▸ b.2)
  have hxb : x ≠ (b : ι) := fun h => hx (h ▸ b.2)
  simp only [crossRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [scat_apply_ne _ _ _ hib, scat_apply_ne _ _ _ hib, scat_apply_ne _ _ _ hxb, dampedPost,
    sherman_morrison _ hD x _ ha]
  simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, heatCoeff,
    heatVec, pim]
  have hpx := hp x
  have hsx : (√((r x).im) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpx).ne'
  have hst : (√t : ℝ) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have e1 : √((r i).im / (r x).im) = √((r i).im) / √((r x).im) := Real.sqrt_div' _ hpx.le
  have hsx' : ((√((r x).im) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsx
  have hst' : ((√t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hst
  rw [e1]
  push_cast
  field_simp
  ring

end Post

end AndersonAC.L64
