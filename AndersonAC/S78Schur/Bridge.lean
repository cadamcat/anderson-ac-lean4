import Mathlib

open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace AndersonAC.SolS78

/-- Ward Dirichlet energy on a finite set, definitionally equal to
`AndersonAC.S78.wardEnergy`. -/
def wardEnergy {ι : Type} (A : Finset ι) (p : ι → ℝ) (h : Matrix ι ι ℂ)
    (f : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2

/-- Schur variational energy: infimum of `D` over extensions of `f` off `A`,
definitionally equal to `AndersonAC.S78.schurEnergy`. -/
def schurEnergy {ι : Type} (A : Finset ι) (D : (ι → ℝ) → ℝ) (f : ι → ℝ) : ℝ :=
  sInf (D '' {F : ι → ℝ | ∀ i ∈ A, F i = f i})

/-- Each Ward summand is nonnegative for nonnegative weights. -/
theorem wardTerm_nonneg {ι : Type} (p : ι → ℝ) (h : Matrix ι ι ℂ) (F : ι → ℝ)
    (A : Finset ι) (hp : ∀ i ∈ A, 0 ≤ p i) (i j : ι) (hi : i ∈ A) (hj : j ∈ A) :
    0 ≤ p i * p j * ‖h i j‖ ^ 2 * (F i - F j) ^ 2 :=
  mul_nonneg (mul_nonneg (mul_nonneg (hp i hi) (hp j hj)) (sq_nonneg _)) (sq_nonneg _)

/-- `wardEnergy` on `B` depends only on the values on `B`. -/
theorem wardEnergy_congr_on {ι : Type} (B : Finset ι) (p : ι → ℝ) (h : Matrix ι ι ℂ)
    (F₁ F₂ : ι → ℝ) (heq : ∀ i ∈ B, F₁ i = F₂ i) :
    wardEnergy B p h F₁ = wardEnergy B p h F₂ := by
  unfold wardEnergy
  congr 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [heq i hi, heq j hj]

/-- Restricting an extension to `B` recovers `D_B`, and the dropped
`A × A ∖ B × B` terms are nonnegative. -/
theorem wardEnergy_mono_of_subset {ι : Type} [DecidableEq ι] (A B : Finset ι)
    (hBA : B ⊆ A) (p : ι → ℝ) (h : Matrix ι ι ℂ) (f F : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) (heq : ∀ i ∈ B, F i = f i) :
    wardEnergy B p h f ≤ wardEnergy A p h F := by
  have hBB : wardEnergy B p h f = wardEnergy B p h F :=
    (wardEnergy_congr_on B p h f F (fun i hi => (heq i hi).symm))
  rw [hBB]
  unfold wardEnergy
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ i ∈ B, ∑ j ∈ B, p i * p j * ‖h i j‖ ^ 2 * (F i - F j) ^ 2
      ≤ ∑ i ∈ B, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F i - F j) ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg hBA fun j hjA _ =>
          wardTerm_nonneg p h F A hp i j (hBA hi) hjA
    _ ≤ ∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F i - F j) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hBA fun i hiA _ => ?_
        exact Finset.sum_nonneg fun j hjA =>
          wardTerm_nonneg p h F A hp i j hiA hjA

/-- Variational Schur bridge inequality: the Schur minimum over extensions off
`B` exceeds `D_B` by at most the crossing-edge energy of the constant
extension. Has the same type as `AndersonAC.S78.schur_bridge_trial`. -/
theorem schur_bridge_trial_proof {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hBA : B ⊆ A) (p : ι → ℝ) (hp : ∀ i ∈ A, 0 ≤ p i)
    (h : Matrix ι ι ℂ) (hsym : ∀ i j, h i j = h j i) (f : ι → ℝ) (c : ℝ) :
    0 ≤ schurEnergy B (wardEnergy A p h) f - wardEnergy B p h f ∧
    schurEnergy B (wardEnergy A p h) f - wardEnergy B p h f ≤
      ∑ i ∈ B, ∑ x ∈ A \ B, p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2 := by
  have hmem : ∀ F : ι → ℝ, (∀ i ∈ B, F i = f i) →
      wardEnergy A p h F ∈
        wardEnergy A p h '' {F : ι → ℝ | ∀ i ∈ B, F i = f i} :=
    fun F hF => ⟨F, hF, rfl⟩
  have hne : (wardEnergy A p h '' {F : ι → ℝ | ∀ i ∈ B, F i = f i}).Nonempty :=
    ⟨wardEnergy A p h f, f, (fun i _ => rfl), rfl⟩
  have hlb : ∀ b ∈ wardEnergy A p h '' {F : ι → ℝ | ∀ i ∈ B, F i = f i},
      wardEnergy B p h f ≤ b := by
    rintro b ⟨F, hF, rfl⟩
    exact wardEnergy_mono_of_subset A B hBA p h f F hp hF
  have hbdd : BddBelow
      (wardEnergy A p h '' {F : ι → ℝ | ∀ i ∈ B, F i = f i}) :=
    ⟨wardEnergy B p h f, hlb⟩
  have hlower : wardEnergy B p h f ≤ schurEnergy B (wardEnergy A p h) f := by
    unfold schurEnergy
    exact le_csInf hne hlb
  -- Constant extension: `f` on `B`, `c` elsewhere.
  set F₀ : ι → ℝ := fun i => if i ∈ B then f i else c with hF₀def
  have hFB : ∀ i ∈ B, F₀ i = f i := by
    intro i hi
    simp only [hF₀def, hi, ite_true]
  have hFc : ∀ (x : ι), x ∉ B → F₀ x = c := by
    intro x hx
    simp only [hF₀def, hx, ite_false]
  have hF₀mem : F₀ ∈ {F : ι → ℝ | ∀ i ∈ B, F i = f i} := fun i hi => hFB i hi
  have hupper : schurEnergy B (wardEnergy A p h) f ≤ wardEnergy A p h F₀ := by
    unfold schurEnergy
    exact csInf_le hbdd ⟨F₀, hF₀mem, rfl⟩
  -- Termwise values of the constant extension on the four blocks.
  have hBB : ∀ i ∈ B, ∀ j ∈ B,
      p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2
        = p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2 := by
    intro i hi j hj
    rw [hFB i hi, hFB j hj]
  have hBc : ∀ i ∈ B, ∀ x ∈ A \ B,
      p i * p x * ‖h i x‖ ^ 2 * (F₀ i - F₀ x) ^ 2
        = p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2 := by
    intro i hi x hx
    have hxB : x ∉ B := (Finset.mem_sdiff.mp hx).2
    rw [hFB i hi, hFc x hxB]
  have hcB : ∀ x ∈ A \ B, ∀ i ∈ B,
      p x * p i * ‖h x i‖ ^ 2 * (F₀ x - F₀ i) ^ 2
        = p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2 := by
    intro x hx i hi
    have hxB : x ∉ B := (Finset.mem_sdiff.mp hx).2
    rw [hFc x hxB, hFB i hi, hsym x i]
    ring
  have hcc : ∀ x ∈ A \ B, ∀ y ∈ A \ B,
      p x * p y * ‖h x y‖ ^ 2 * (F₀ x - F₀ y) ^ 2 = 0 := by
    intro x hx y hy
    have hxB : x ∉ B := (Finset.mem_sdiff.mp hx).2
    have hyB : y ∉ B := (Finset.mem_sdiff.mp hy).2
    rw [hFc x hxB, hFc y hyB, sub_self, zero_pow two_ne_zero, mul_zero]
  -- Split each inner sum over `A = B ∪ (A \ B)`.
  have hsplit_inner : ∀ i ∈ A,
      (∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
        = (∑ j ∈ B, p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
          + (∑ x ∈ A \ B, p i * p x * ‖h i x‖ ^ 2 * (F₀ i - F₀ x) ^ 2) := by
    intro i _
    have h := Finset.sum_sdiff hBA
      (f := fun j => p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
    linarith
  have hsplit_outer :
      (∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
        = (∑ i ∈ B, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
          + (∑ w ∈ A \ B, ∑ j ∈ A,
              p w * p j * ‖h w j‖ ^ 2 * (F₀ w - F₀ j) ^ 2) := by
    have h := Finset.sum_sdiff hBA
      (f := fun i => ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
    linarith
  have hexpandB : ∀ i ∈ B,
      (∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
        = (∑ j ∈ B, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2)
          + (∑ x ∈ A \ B, p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2) := by
    intro i hi
    rw [hsplit_inner i (hBA hi)]
    congr 1
    · exact Finset.sum_congr rfl (fun j hj => hBB i hi j hj)
    · exact Finset.sum_congr rfl (fun x hx => hBc i hi x hx)
  have hexpandC : ∀ w ∈ A \ B,
      (∑ j ∈ A, p w * p j * ‖h w j‖ ^ 2 * (F₀ w - F₀ j) ^ 2)
        = (∑ i ∈ B, p i * p w * ‖h i w‖ ^ 2 * (f i - c) ^ 2) + 0 := by
    intro w hw
    rw [hsplit_inner w (Finset.mem_sdiff.mp hw).1]
    congr 1
    · exact Finset.sum_congr rfl (fun i hi => hcB w hw i hi)
    · exact Finset.sum_eq_zero (fun y hy => hcc w hw y hy)
  have e1 : (∑ i ∈ B, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
      = (∑ i ∈ B, ∑ j ∈ B, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2)
        + (∑ i ∈ B, ∑ x ∈ A \ B, p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => hexpandB i hi)
  have e2 : (∑ w ∈ A \ B, ∑ j ∈ A, p w * p j * ‖h w j‖ ^ 2 * (F₀ w - F₀ j) ^ 2)
      = (∑ i ∈ B, ∑ x ∈ A \ B, p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2) := by
    calc _ = ∑ w ∈ A \ B,
            ((∑ i ∈ B, p i * p w * ‖h i w‖ ^ 2 * (f i - c) ^ 2) + 0) :=
          Finset.sum_congr rfl (fun w hw => hexpandC w hw)
      _ = ∑ w ∈ A \ B, ∑ i ∈ B, p i * p w * ‖h i w‖ ^ 2 * (f i - c) ^ 2 :=
          Finset.sum_congr rfl (fun w _ => add_zero _)
      _ = _ := Finset.sum_comm
  have htotal : (∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (F₀ i - F₀ j) ^ 2)
      = (∑ i ∈ B, ∑ j ∈ B, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2)
        + 2 * (∑ i ∈ B, ∑ x ∈ A \ B,
          p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2) := by
    rw [hsplit_outer, e1, e2]
    ring
  have hexact : wardEnergy A p h F₀ = wardEnergy B p h f +
      (∑ i ∈ B, ∑ x ∈ A \ B, p i * p x * ‖h i x‖ ^ 2 * (f i - c) ^ 2) := by
    unfold wardEnergy
    rw [htotal]
    ring
  constructor <;> linarith

end AndersonAC.SolS78
