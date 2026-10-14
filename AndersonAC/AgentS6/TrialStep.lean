import AndersonAC.S6.Statements
import AndersonAC.L64.Resolvent

/-! One real heat step of the trial (06-clearing.tex:428–434, 805–821): exposing `ξ` at the
pivot `x` and eliminating `x` by a true real Schur complement gives the surviving active inverse
by the Sherman–Morrison formula `g' = g - a g_{·x} g_{x·}/(1 + a g_xx)`, `a = ξ + t r_x`;
the denominator is nonzero. Stated for an abstract finite active set and for `HeatTransition`. -/

noncomputable section
open scoped BigOperators Matrix

namespace AndersonAC.AgentS6

open AndersonAC.S6

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The eliminated real matrix on `{i // i ≠ x}`. -/
def schurElim (M : Matrix A A ℝ) (x : A) (ξ : ℝ) : Matrix {i // i ≠ x} {i // i ≠ x} ℝ :=
  fun i j => M i j - M i x * M x j / (M x x + ξ)

theorem schurElim_symm (M : Matrix A A ℝ) (hM : M.IsSymm) (x : A) (ξ : ℝ) :
    (schurElim M x ξ).IsSymm := by
  have hs : ∀ i j, M i j = M j i := fun i j => by
    have := congrFun (congrFun hM j) i; simpa [Matrix.transpose_apply] using this
  ext i j
  simp only [Matrix.transpose_apply, schurElim, hs i j, hs (i : A) x, hs x (j : A)]
  ring

theorem damped_isUnit (M : Matrix A A ℝ) (hM : M.IsSymm) {t : ℝ} (ht : 0 < t) (r : A → ℂ)
    (hr : ∀ i, 0 < (r i).im) : IsUnit (dampedMatrix M t r).det :=
  AndersonAC.L64.isUnit_det_damped (M := M) (t := t) (r := r) hM ht hr

theorem damped_apply (M : Matrix A A ℝ) (t : ℝ) (r : A → ℂ) (i j : A) :
    dampedMatrix M t r i j = (M i j : ℂ) - if i = j then (t : ℂ) * r i else 0 := by
  by_cases h : i = j <;> simp [dampedMatrix, Matrix.diagonal_apply, h]

/-- Abstract heat step. -/
theorem heat_step (M : Matrix A A ℝ) (hM : M.IsSymm) {t : ℝ} (ht : 0 < t) (r : A → ℂ)
    (hr : ∀ i, 0 < (r i).im) (x : A) (ξ : ℝ) (hP : M x x + ξ ≠ 0) :
    1 + ((ξ : ℂ) + (t : ℂ) * r x) * (dampedMatrix M t r)⁻¹ x x ≠ 0 ∧
    (dampedMatrix (schurElim M x ξ) t (fun i => r i))⁻¹ = Matrix.of fun i j : {i // i ≠ x} =>
      (dampedMatrix M t r)⁻¹ (i : A) (j : A) - ((ξ : ℂ) + (t : ℂ) * r x) *
        (dampedMatrix M t r)⁻¹ (i : A) x * (dampedMatrix M t r)⁻¹ x (j : A) /
          (1 + ((ξ : ℂ) + (t : ℂ) * r x) * (dampedMatrix M t r)⁻¹ x x) := by
  set D := dampedMatrix M t r with hDdef
  set g := D⁻¹ with hg
  set a : ℂ := (ξ : ℂ) + (t : ℂ) * r x with ha
  set P : ℂ := ((M x x + ξ : ℝ) : ℂ) with hPdef
  have hP' : P ≠ 0 := by rw [hPdef]; exact_mod_cast hP
  have hDu := damped_isUnit M hM ht r hr
  have hDg : D * g = 1 := Matrix.mul_nonsing_inv D hDu
  have hs : ∀ i j, M i j = M j i := fun i j => by
    have := congrFun (congrFun hM j) i; simpa [Matrix.transpose_apply] using this
  -- row identities of D g = 1, split at x
  have hrow : ∀ i j : A, D i x * g x j + ∑ k : {k // k ≠ x}, D i k * g k j =
      if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hDg i) j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ x, Matrix.one_apply] at this
    exact this
  have hDoff : ∀ i k : A, i ≠ k → D i k = (M i k : ℂ) := by
    intro i k hik; rw [hDdef, damped_apply, if_neg hik, sub_zero]
  have hDxx : D x x = (M x x : ℂ) - (t : ℂ) * r x := by rw [hDdef, damped_apply, if_pos rfl]
  have hPd : P = D x x + a := by rw [hDxx, hPdef, ha]; push_cast; ring
  set N := schurElim M x ξ
  set S := dampedMatrix N t (fun i : {i // i ≠ x} => r i)
  have hSu : IsUnit S.det := damped_isUnit N (schurElim_symm M hM x ξ) ht _ (fun i => hr i)
  have hS : ∀ i k : {i // i ≠ x}, S i k = D i k - (M i x : ℂ) * (M x k : ℂ) / P := by
    intro i k
    simp only [S, damped_apply, N, schurElim, hDdef, Subtype.ext_iff, hPdef]
    push_cast
    ring
  -- q ≠ 0
  have hq : 1 + a * g x x ≠ 0 := by
    intro hq0
    set u : {i // i ≠ x} → ℂ := fun k => g k x
    have hSu0 : S *ᵥ u = 0 := by
      funext i
      have h1 := hrow i x
      have h2 := hrow x x
      rw [if_neg i.2] at h1
      rw [if_pos rfl] at h2
      simp only [Matrix.mulVec, dotProduct, hS, Pi.zero_apply, u]
      have hix : D i x = (M i x : ℂ) := hDoff i x i.2
      have hxk : ∀ k : {k // k ≠ x}, D x k = (M x k : ℂ) := fun k => hDoff x k (Ne.symm k.2)
      simp only [hxk] at h2
      simp only [sub_mul, Finset.sum_sub_distrib]
      have e : ∑ k : {k // k ≠ x}, (M i x : ℂ) * (M x k : ℂ) / P * g k x =
          (M i x : ℂ) / P * ∑ k : {k // k ≠ x}, (M x k : ℂ) * g k x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [e]
      have h2' : ∑ k : {k // k ≠ x}, (M x k : ℂ) * g k x = 1 - D x x * g x x := by
        linear_combination h2
      rw [h2']
      have hgx : g x x * a = -1 := by linear_combination hq0
      rw [hix] at h1
      have : ∑ k : {k // k ≠ x}, D i k * g k x = -((M i x : ℂ) * g x x) := by
        linear_combination h1
      rw [this]
      field_simp
      linear_combination (-(M i x : ℂ)) * hq0 + (-(M i x : ℂ) * g x x) * hPd
    have hu0 : u = 0 := by
      have := congrArg (fun v => S⁻¹ *ᵥ v) hSu0
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hSu] using this
    have h2 := hrow x x
    rw [if_pos rfl] at h2
    have : ∀ k : {k // k ≠ x}, g k x = 0 := fun k => congrFun hu0 k
    simp only [this, mul_zero, Finset.sum_const_zero, add_zero] at h2
    have hgx : g x x * a = -1 := by linear_combination hq0
    have : D x x * g x x = 1 := h2
    have hgx0 : g x x ≠ 0 := by intro h0; rw [h0, mul_zero] at this; exact zero_ne_one this
    -- D x x = 1 / g x x and a = -1 / g x x, so P = D x x + a = 0
    apply hP'
    rw [hPd]
    have e1 : D x x = 1 / g x x := by field_simp; linear_combination this
    have e2 : a = -1 / g x x := by field_simp; linear_combination hgx
    rw [e1, e2]; ring
  refine ⟨hq, ?_⟩
  -- right inverse
  apply Matrix.inv_eq_right_inv
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, hS]
  have h1 := hrow i j
  have h3 := hrow i x
  have h2 := hrow x j
  have h4 := hrow x x
  rw [if_neg i.2] at h3
  rw [if_pos rfl] at h4
  have hxj : (x = (j : A)) = False := by simp [Ne.symm j.2]
  rw [if_neg (Ne.symm j.2)] at h2
  have hix : D i x = (M i x : ℂ) := hDoff i x i.2
  have hxk : ∀ k : {k // k ≠ x}, D x k = (M x k : ℂ) := fun k => hDoff x k (Ne.symm k.2)
  simp only [hxk] at h2 h4
  rw [hix] at h1 h3
  have hij : ((i : A) = (j : A)) ↔ i = j := Subtype.ext_iff.symm
  have hite : (if (i : A) = (j : A) then (1 : ℂ) else 0) = if i = j then 1 else 0 := by
    by_cases h : i = j
    · rw [if_pos h, if_pos (hij.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hij.mp h'))]
  rw [hite] at h1
  -- expand the sum
  have expand : ∑ k : {k // k ≠ x}, (D i k - (M i x : ℂ) * (M x k : ℂ) / P) *
      (g k j - a * g k x * g x j / (1 + a * g x x)) =
      (∑ k : {k // k ≠ x}, D i k * g k j) -
        a * g x j / (1 + a * g x x) * (∑ k : {k // k ≠ x}, D i k * g k x) -
        (M i x : ℂ) / P * (∑ k : {k // k ≠ x}, (M x k : ℂ) * g k j) +
        (M i x : ℂ) / P * (a * g x j / (1 + a * g x x)) *
          (∑ k : {k // k ≠ x}, (M x k : ℂ) * g k x) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [expand]
  have s1 : ∑ k : {k // k ≠ x}, D i k * g k j = (if i = j then 1 else 0) - (M i x : ℂ) * g x j := by
    linear_combination h1
  have s2 : ∑ k : {k // k ≠ x}, D i k * g k x = -((M i x : ℂ) * g x x) := by
    linear_combination h3
  have s3 : ∑ k : {k // k ≠ x}, (M x k : ℂ) * g k j = -(D x x * g x j) := by
    linear_combination h2
  have s4 : ∑ k : {k // k ≠ x}, (M x k : ℂ) * g k x = 1 - D x x * g x x := by
    linear_combination h4
  rw [s1, s2, s3, s4]
  field_simp
  rw [hPd]
  ring

/-- The trial heat step: `HeatTransition` gives the surviving active inverse by Sherman–Morrison
from the prestate active inverse, with nonzero denominator. -/
theorem trial_heat_step {ι : Type*} [Fintype ι] [DecidableEq ι] {core : Finset ι} {t : ℝ}
    (ht : 0 < t) (r : ι → ℂ) (hr : ∀ i, 0 < (r i).im) {s s' : TrialState core} {x : ι}
    {ξ : ℝ} (h : HeatTransition t r s s' x ξ) :
    ∃ hx : x ∈ s.active,
      1 + ((ξ : ℂ) + (t : ℂ) * r x) * trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩ ≠ 0 ∧
      ∀ (i j : {i // i ∈ s'.active}) (hi : (i : ι) ∈ s.active) (hj : (j : ι) ∈ s.active),
        trialInverse t r s' i j = trialInverse t r s ⟨i, hi⟩ ⟨j, hj⟩ -
          ((ξ : ℂ) + (t : ℂ) * r x) * trialInverse t r s ⟨i, hi⟩ ⟨x, hx⟩ *
            trialInverse t r s ⟨x, hx⟩ ⟨j, hj⟩ /
              (1 + ((ξ : ℂ) + (t : ℂ) * r x) * trialInverse t r s ⟨x, hx⟩ ⟨x, hx⟩) := by
  obtain ⟨hx, -, hact, hP, hM', -⟩ := h
  set xA : {i // i ∈ s.active} := ⟨x, hx⟩
  obtain ⟨hq, hinv⟩ := heat_step s.M s.symmetric ht (fun i : {i // i ∈ s.active} => r i)
    (fun i => hr i) xA ξ hP
  refine ⟨hx, hq, fun i j hi hj => ?_⟩
  have hmem : ∀ k : {i // i ∈ s'.active}, (k : ι) ∈ s.active ∧ (k : ι) ≠ x := by
    intro k
    have h2 : (k : ι) ∈ s.active.erase x := by rw [← hact]; exact k.2
    rw [Finset.mem_erase] at h2
    exact ⟨h2.2, h2.1⟩
  let e : {i // i ∈ s'.active} ≃ {k : {i // i ∈ s.active} // k ≠ xA} :=
    { toFun := fun k => ⟨⟨k, (hmem k).1⟩, fun h' => (hmem k).2 (congrArg Subtype.val h')⟩
      invFun := fun k => ⟨k.1.1, by
        rw [hact, Finset.mem_erase]
        exact ⟨fun h' => k.2 (Subtype.ext h'), k.1.2⟩⟩
      left_inv := fun k => rfl
      right_inv := fun k => rfl }
  have hD : dampedMatrix s'.M t (fun i : {i // i ∈ s'.active} => r i) =
      (dampedMatrix (schurElim s.M xA ξ) t (fun i => r i)).submatrix e e := by
    ext a b
    rw [Matrix.submatrix_apply, damped_apply, damped_apply]
    have hab : (a = b) ↔ (e a = e b) := e.injective.eq_iff.symm
    have hM2 := hM' a b (hmem a).1 (hmem b).1
    simp only [schurElim]
    by_cases hab' : a = b
    · rw [if_pos hab', if_pos (hab.mp hab'), hM2]; subst hab'; rfl
    · rw [if_neg hab', if_neg (fun h'' => hab' (hab.mpr h'')), hM2]; rfl
  have hT : trialInverse t r s' = (dampedMatrix s'.M t (fun i : {i // i ∈ s'.active} => r i))⁻¹ :=
    rfl
  rw [hT, hD, Matrix.inv_submatrix_equiv, Matrix.submatrix_apply, hinv]
  rfl

end AndersonAC.AgentS6

#print axioms AndersonAC.AgentS6.heat_step
#print axioms AndersonAC.AgentS6.trial_heat_step
