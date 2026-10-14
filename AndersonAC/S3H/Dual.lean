import AndersonAC.S3.Definitions

/-! S3-dual: Lemma 3.1 dual comparison forms + order (paper 03-initialization.tex:29–72).
    Imports Definitions only (never Statements). -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
open Matrix

attribute [local instance] Classical.propDecidable

namespace AndersonAC.S3H

variable {d L : ℕ} [NeZero L]

/-! ## Basic pairing / form / norm identities -/

theorem pairing_add_right {A : Type*} [Fintype A] (y f g : A → ℂ) :
    AndersonAC.S3.pairing y (f + g)
      = AndersonAC.S3.pairing y f + AndersonAC.S3.pairing y g := by
  simp only [AndersonAC.S3.pairing, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, Complex.add_re]

theorem pairing_add_left {A : Type*} [Fintype A] (y z f : A → ℂ) :
    AndersonAC.S3.pairing (y + z) f
      = AndersonAC.S3.pairing y f + AndersonAC.S3.pairing z f := by
  simp only [AndersonAC.S3.pairing, Pi.add_apply, star_add, add_mul,
    Finset.sum_add_distrib, Complex.add_re]

theorem pairing_neg_right {A : Type*} [Fintype A] (y f : A → ℂ) :
    AndersonAC.S3.pairing y (-f) = -AndersonAC.S3.pairing y f := by
  simp [AndersonAC.S3.pairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem pairing_neg_left {A : Type*} [Fintype A] (y f : A → ℂ) :
    AndersonAC.S3.pairing (-y) f = -AndersonAC.S3.pairing y f := by
  simp [AndersonAC.S3.pairing, Pi.neg_apply, star_neg, neg_mul,
    Finset.sum_neg_distrib]

theorem pairing_zero_right {A : Type*} [Fintype A] (y : A → ℂ) :
    AndersonAC.S3.pairing y 0 = 0 := by
  simp [AndersonAC.S3.pairing]

theorem pairing_zero_left {A : Type*} [Fintype A] (f : A → ℂ) :
    AndersonAC.S3.pairing 0 f = 0 := by
  simp [AndersonAC.S3.pairing]

/-- Pairing is symmetric (real parts of conjugates). -/
theorem pairing_comm {A : Type*} [Fintype A] (y f : A → ℂ) :
    AndersonAC.S3.pairing y f = AndersonAC.S3.pairing f y := by
  unfold AndersonAC.S3.pairing
  have h : (∑ i, star (f i) * y i) = star (∑ i, star (y i) * f i) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [star_mul, star_star, mul_comm]
  rw [h]
  simp

/-- Real scaling in the second argument. -/
theorem pairing_real_smul_right {A : Type*} [Fintype A] (y f : A → ℂ) (t : ℝ) :
    AndersonAC.S3.pairing y (fun i => (t : ℂ) * f i)
      = t * AndersonAC.S3.pairing y f := by
  have h1 : ∀ x, star (y x) * ((t : ℂ) * f x) = (t : ℂ) * (star (y x) * f x) := by
    intro x
    ring
  simp only [AndersonAC.S3.pairing]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem pairing_real_smul_left {A : Type*} [Fintype A] (y f : A → ℂ) (t : ℝ) :
    AndersonAC.S3.pairing (fun i => (t : ℂ) * y i) f
      = t * AndersonAC.S3.pairing y f := by
  rw [pairing_comm _ f, pairing_comm y f]
  exact pairing_real_smul_right _ _ _

theorem pairing_sub_right {A : Type*} [Fintype A] (y f g : A → ℂ) :
    AndersonAC.S3.pairing y (f - g)
      = AndersonAC.S3.pairing y f - AndersonAC.S3.pairing y g := by
  rw [sub_eq_add_neg, pairing_add_right, pairing_neg_right, sub_eq_add_neg]

theorem pairing_sub_left {A : Type*} [Fintype A] (y z f : A → ℂ) :
    AndersonAC.S3.pairing (y - z) f
      = AndersonAC.S3.pairing y f - AndersonAC.S3.pairing z f := by
  rw [sub_eq_add_neg, pairing_add_left, pairing_neg_left, sub_eq_add_neg]

/-- Norm squared is nonnegative. -/
theorem normSq_nonneg {A : Type*} [Fintype A] (v : A → ℂ) :
    0 ≤ AndersonAC.S3.normSq v :=
  Finset.sum_nonneg fun _ _ => pow_two_nonneg _

/-- Squared norm via real/imaginary parts. -/
theorem norm_sq_eq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, pow_two, pow_two]

/-- Pointwise parallelogram law for `ℂ`. -/
theorem complex_parallelogram (a b : ℂ) :
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  rw [norm_sq_eq_re_im, norm_sq_eq_re_im, norm_sq_eq_re_im, norm_sq_eq_re_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- Parallelogram law for `normSq`. -/
theorem normSq_parallelogram {A : Type*} [Fintype A] (f g : A → ℂ) :
    AndersonAC.S3.normSq (f + g) + AndersonAC.S3.normSq (f - g)
      = 2 * AndersonAC.S3.normSq f + 2 * AndersonAC.S3.normSq g := by
  unfold AndersonAC.S3.normSq
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply]
  exact complex_parallelogram _ _

/-- Complex homogeneity of `normSq`. -/
theorem normSq_smul {A : Type*} [Fintype A] (z : ℂ) (f : A → ℂ) :
    AndersonAC.S3.normSq (z • f) = ‖z‖ ^ 2 * AndersonAC.S3.normSq f := by
  unfold AndersonAC.S3.normSq
  simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]

theorem normSq_zero {A : Type*} [Fintype A] :
    AndersonAC.S3.normSq (0 : A → ℂ) = 0 := by
  simp [AndersonAC.S3.normSq]

/-! ## Gradient energy identities -/

theorem gradientEnergy_nonneg (v : AndersonAC.S3.Torus d L → ℂ) :
    0 ≤ AndersonAC.S3.gradientEnergy v :=
  Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => pow_two_nonneg _

theorem gradientEnergy_zero :
    AndersonAC.S3.gradientEnergy (0 : AndersonAC.S3.Torus d L → ℂ) = 0 := by
  simp [AndersonAC.S3.gradientEnergy]

theorem gradientEnergy_smul (z : ℂ) (v : AndersonAC.S3.Torus d L → ℂ) :
    AndersonAC.S3.gradientEnergy (z • v)
      = ‖z‖ ^ 2 * AndersonAC.S3.gradientEnergy v := by
  unfold AndersonAC.S3.gradientEnergy
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_sub, norm_mul, mul_pow]

/-- Adding a constant does not change differences. -/
theorem gradientEnergy_add_const (v : AndersonAC.S3.Torus d L → ℂ) (c : ℂ) :
    AndersonAC.S3.gradientEnergy (v + fun _ => c)
      = AndersonAC.S3.gradientEnergy v := by
  unfold AndersonAC.S3.gradientEnergy
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply]
  rw [add_sub_add_right_eq_sub]

theorem gradientEnergy_parallelogram (v w : AndersonAC.S3.Torus d L → ℂ) :
    AndersonAC.S3.gradientEnergy (v + w) + AndersonAC.S3.gradientEnergy (v - w)
      = 2 * AndersonAC.S3.gradientEnergy v
        + 2 * AndersonAC.S3.gradientEnergy w := by
  unfold AndersonAC.S3.gradientEnergy
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply, Pi.sub_apply]
  have h1 : (v (x + AndersonAC.S3.basisStep j) + w (x + AndersonAC.S3.basisStep j)
        - (v x + w x))
      = (v (x + AndersonAC.S3.basisStep j) - v x)
        + (w (x + AndersonAC.S3.basisStep j) - w x) := by
    ring
  have h2 : (v (x + AndersonAC.S3.basisStep j) - w (x + AndersonAC.S3.basisStep j)
        - (v x - w x))
      = (v (x + AndersonAC.S3.basisStep j) - v x)
        - (w (x + AndersonAC.S3.basisStep j) - w x) := by
    ring
  rw [h1, h2]
  have h := complex_parallelogram
    (v (x + AndersonAC.S3.basisStep j) - v x)
    (w (x + AndersonAC.S3.basisStep j) - w x)
  linarith

/-! ## Laplacian: Hermitian + energy identity -/

/-- `(star z * z).re = ‖z‖^2`. -/
theorem star_mul_self_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_re]
  simp
  rw [norm_sq_eq_re_im]
  ring

/-! ## Torus translations and connectivity -/

/-- Translation by a fixed element preserves finite sums. -/
theorem sum_add_right {M : Type*} [AddCommMonoid M] (f : AndersonAC.S3.Torus d L → M)
    (c : AndersonAC.S3.Torus d L) :
    ∑ x, f (x + c) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight c) f

theorem sum_add_left {M : Type*} [AddCommMonoid M] (f : AndersonAC.S3.Torus d L → M)
    (c : AndersonAC.S3.Torus d L) :
    ∑ x, f (c + x) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addLeft c) f

/-- A single nearest-neighbor step preserves `v` implies `n`-fold steps do too. -/
theorem step_nsmul_preserved (v : AndersonAC.S3.Torus d L → ℂ)
    (h : ∀ x (j : Fin d), v (x + AndersonAC.S3.basisStep j) = v x)
    (y : AndersonAC.S3.Torus d L) (n : ℕ) (j : Fin d) :
    v (y + n • AndersonAC.S3.basisStep j) = v y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : y + (n + 1) • AndersonAC.S3.basisStep j
        = (y + n • AndersonAC.S3.basisStep j)
          + AndersonAC.S3.basisStep j := by
      rw [add_nsmul, one_nsmul, add_assoc]
    rw [this, h _ j, ih]

/-- `Pi.single` preserves addition in the value. -/
theorem pi_single_add (j : Fin d) (a b : ZMod L) :
    Pi.single (M := fun _ => ZMod L) j (a + b)
      = Pi.single (M := fun _ => ZMod L) j a
        + Pi.single (M := fun _ => ZMod L) j b := by
  funext i
  by_cases h : i = j
  · subst h
    simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

/-- `Pi.single` preserves `ℕ`-scaling. -/
theorem pi_single_nsmul (j : Fin d) (n : ℕ) (a : ZMod L) :
    n • Pi.single (M := fun _ => ZMod L) j a
      = Pi.single (M := fun _ => ZMod L) j (n • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul, ih, pi_single_add]

/-- Every site coordinate is an `ℕ`-multiple of `1`. -/
theorem zmod_eq_nsmul_one (a : ZMod L) : a.val • (1 : ZMod L) = a := by
  have h : ((a.val : ℕ) : ZMod L) = a := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have h2 : ((a.val : ℕ) : ZMod L) = a.val • (1 : ZMod L) := by
    rw [nsmul_one]
  rw [← h2, h]

/-- Each `Pi.single` fiber equals a multiple of a basis step. -/
theorem pi_single_eq_nsmul_basis (x : AndersonAC.S3.Torus d L) (j : Fin d) :
    Pi.single (M := fun _ => ZMod L) j (x j)
      = (x j).val • AndersonAC.S3.basisStep j := by
  unfold AndersonAC.S3.basisStep
  rw [pi_single_nsmul, zmod_eq_nsmul_one]

/-- Every torus point is the sum of its single-coordinate fibers. -/
theorem torus_eq_sum_single (x : AndersonAC.S3.Torus d L) :
    (∑ j, Pi.single (M := fun _ => ZMod L) j (x j)) = x := by
  funext i
  rw [Finset.sum_apply]
  exact Fintype.sum_pi_single i x

/-- Step-invariance in all directions forces constancy. -/
theorem const_of_step_invariant (v : AndersonAC.S3.Torus d L → ℂ)
    (h : ∀ x (j : Fin d), v (x + AndersonAC.S3.basisStep j) = v x) :
    ∃ c : ℂ, v = fun _ => c := by
  use v 0
  funext x
  have hdecomp : x = ∑ j, ((x j).val • AndersonAC.S3.basisStep j) := by
    conv_lhs => rw [← torus_eq_sum_single x]
    apply Finset.sum_congr rfl
    intro j _
    exact pi_single_eq_nsmul_basis x j
  have hsum : ∀ t : Finset (Fin d),
      v (Finset.sum t (fun j => ((x j).val • AndersonAC.S3.basisStep j))) = v 0 := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | insert a s has ihs =>
      rw [Finset.sum_insert has]
      have hstep := step_nsmul_preserved v h
        (Finset.sum s (fun j => ((x j).val • AndersonAC.S3.basisStep j)))
        ((x a).val) a
      rw [add_comm
        (Finset.sum s (fun j => ((x j).val • AndersonAC.S3.basisStep j)))
        ((x a).val • AndersonAC.S3.basisStep a)] at hstep
      rw [hstep, ihs]
  rw [hdecomp]
  exact hsum Finset.univ

/-! ## Free hopping symmetry + Hermitian -/

theorem step_iff_sub (x y : AndersonAC.S3.Torus d L) (j : Fin d) :
    (y = x + AndersonAC.S3.basisStep j)
      ↔ (x = y - AndersonAC.S3.basisStep j) := by
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    rw [h]
    abel

theorem step_iff_add (x y : AndersonAC.S3.Torus d L) (j : Fin d) :
    (y = x - AndersonAC.S3.basisStep j)
      ↔ (x = y + AndersonAC.S3.basisStep j) := by
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    rw [h]
    abel

theorem freeHopping_symm (x y : AndersonAC.S3.Torus d L) :
    AndersonAC.S3.freeHopping (d := d) (L := L) x y
      = AndersonAC.S3.freeHopping (d := d) (L := L) y x := by
  unfold AndersonAC.S3.freeHopping
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have e1 := step_iff_sub x y j
  have e2 := step_iff_add x y j
  simp only [e1, e2, add_comm]

/-- Entries of `freeHopping` are fixed by `star` (they are `0`, `-1`, `-2`). -/
theorem freeHopping_star (x y : AndersonAC.S3.Torus d L) :
    star (AndersonAC.S3.freeHopping (d := d) (L := L) x y)
      = AndersonAC.S3.freeHopping (d := d) (L := L) x y := by
  unfold AndersonAC.S3.freeHopping
  rw [star_neg]
  congr 1
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [star_add]
  congr 1
  · by_cases h : y = x + AndersonAC.S3.basisStep j <;> simp [h]
  · by_cases h : y = x - AndersonAC.S3.basisStep j <;> simp [h]

theorem freeHopping_hermitian :
    (AndersonAC.S3.freeHopping (d := d) (L := L)).conjTranspose
      = AndersonAC.S3.freeHopping (d := d) (L := L) := by
  funext x y
  simp only [Matrix.conjTranspose_apply]
  rw [freeHopping_symm y x]
  exact freeHopping_star x y

theorem laplacian_hermitian :
    (AndersonAC.S3.laplacian (d := d) (L := L)).conjTranspose
      = AndersonAC.S3.laplacian (d := d) (L := L) := by
  unfold AndersonAC.S3.laplacian
  rw [Matrix.conjTranspose_add, freeHopping_hermitian]
  congr 1
  have hreal : star (2 * ((d : ℕ) : ℂ)) = 2 * ((d : ℕ) : ℂ) := by
    simp
  rw [Matrix.conjTranspose_smul, hreal, Matrix.conjTranspose_one]

/-! ## Energy identity: `gradientEnergy = form laplacian` -/

/-- `mulVec` of `freeHopping` sums the two neighbors. -/
theorem mulVec_freeHopping (v : AndersonAC.S3.Torus d L → ℂ)
    (x : AndersonAC.S3.Torus d L) :
    (AndersonAC.S3.freeHopping (d := d) (L := L) *ᵥ v) x
      = -∑ j : Fin d, (v (x + AndersonAC.S3.basisStep j)
        + v (x - AndersonAC.S3.basisStep j)) := by
  have hite_add (j : Fin d) :
      (∑ y, (if y = x + AndersonAC.S3.basisStep j then (1 : ℂ) else 0) * v y)
        = v (x + AndersonAC.S3.basisStep j) := by
    have h1 : ∀ y, (if y = x + AndersonAC.S3.basisStep j then (1 : ℂ) else 0) * v y
        = (if y = x + AndersonAC.S3.basisStep j then v y else 0) := by
      intro y
      by_cases hy : y = x + AndersonAC.S3.basisStep j <;> simp [hy]
    rw [Finset.sum_congr rfl (fun y _ => h1 y)]
    rw [Finset.sum_ite_eq']
    simp
  have hite_sub (j : Fin d) :
      (∑ y, (if y = x - AndersonAC.S3.basisStep j then (1 : ℂ) else 0) * v y)
        = v (x - AndersonAC.S3.basisStep j) := by
    have h1 : ∀ y, (if y = x - AndersonAC.S3.basisStep j then (1 : ℂ) else 0) * v y
        = (if y = x - AndersonAC.S3.basisStep j then v y else 0) := by
      intro y
      by_cases hy : y = x - AndersonAC.S3.basisStep j <;> simp [hy]
    rw [Finset.sum_congr rfl (fun y _ => h1 y)]
    rw [Finset.sum_ite_eq']
    simp
  unfold AndersonAC.S3.freeHopping
  simp only [Matrix.mulVec, dotProduct]
  have hsum : ∀ y : AndersonAC.S3.Torus d L,
      (-∑ j : Fin d, ((if y = x + AndersonAC.S3.basisStep j then (1 : ℂ) else 0) +
        (if y = x - AndersonAC.S3.basisStep j then (1 : ℂ) else 0))) * v y
      = -∑ j : Fin d, (((if y = x + AndersonAC.S3.basisStep j then (1 : ℂ) else 0) * v y) +
        ((if y = x - AndersonAC.S3.basisStep j then (1 : ℂ) else 0) * v y)) := by
    intro y
    rw [neg_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [add_mul]
  rw [Finset.sum_congr rfl (fun y _ => hsum y)]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_add_distrib]
  congr 1
  · exact hite_add j
  · exact hite_sub j

/-- `pairing v v = normSq v`. -/
theorem pairing_self_eq_normSq {A : Type*} [Fintype A] (v : A → ℂ) :
    AndersonAC.S3.pairing v v = AndersonAC.S3.normSq v := by
  have hre_sum : ∀ (s : Finset A) (f : A → ℂ),
      (Finset.sum s f).re = Finset.sum s (fun i => (f i).re) := by
    intro s f
    induction s using Finset.induction with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, Complex.add_re, ih]
  unfold AndersonAC.S3.pairing AndersonAC.S3.normSq
  rw [hre_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact star_mul_self_re _

/-- Pointwise expansion of `‖a - b‖^2`. -/
theorem norm_sub_sq (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (star b * a).re := by
  have h1 : (star (a - b) * (a - b)).re = ‖a - b‖ ^ 2 :=
    star_mul_self_re _
  have hstar : star (a - b) = star a - star b := by
    simp [star_sub]
  rw [hstar] at h1
  have hexpand : ((star a - star b) * (a - b)).re
      = ‖a‖ ^ 2 + ‖b‖ ^ 2 - (star a * b).re - (star b * a).re := by
    rw [sub_mul, mul_sub, mul_sub]
    simp only [Complex.sub_re]
    rw [star_mul_self_re, star_mul_self_re]
    ring
  have hsymm : (star a * b).re = (star b * a).re := by
    have h : star a * b = star (star b * a) := by
      rw [star_mul, star_star, mul_comm]
    rw [h]
    simp
  rw [hexpand, hsymm] at h1
  linarith [h1]

/-- Symmetry of `(star a * b).re`. -/
theorem star_dot_symm (a b : ℂ) : (star a * b).re = (star b * a).re := by
  have h : star a * b = star (star b * a) := by
    rw [star_mul, star_star, mul_comm]
  rw [h]
  simp

/-- Shifted norm sums agree. -/
theorem normSq_shift (v : AndersonAC.S3.Torus d L → ℂ)
    (c : AndersonAC.S3.Torus d L) :
    (∑ x, ‖v (x + c)‖ ^ 2) = AndersonAC.S3.normSq v := by
  unfold AndersonAC.S3.normSq
  exact sum_add_right (fun x => ‖v x‖ ^ 2) c

/-- The two neighbor dot-sums have equal real parts. -/
theorem dot_sum_sub_eq_add (v : AndersonAC.S3.Torus d L → ℂ) (j : Fin d) :
    (∑ x, (star (v x) * v (x - AndersonAC.S3.basisStep j)).re)
      = (∑ x, (star (v x) * v (x + AndersonAC.S3.basisStep j)).re) := by
  have htrans : (∑ x, (star (v (x + AndersonAC.S3.basisStep j)) * v x).re)
      = (∑ x, (star (v x) * v (x - AndersonAC.S3.basisStep j)).re) := by
    have hfun : ∀ x, (star (v (x + AndersonAC.S3.basisStep j)) * v x).re
        = (fun y => (star (v y)
          * v (y - AndersonAC.S3.basisStep j)).re)
          (x + AndersonAC.S3.basisStep j) := by
      intro x
      have hcancel : (x + AndersonAC.S3.basisStep j)
          - AndersonAC.S3.basisStep j = x := by abel
      show (star (v (x + AndersonAC.S3.basisStep j)) * v x).re
        = (star (v (x + AndersonAC.S3.basisStep j))
          * v ((x + AndersonAC.S3.basisStep j) - AndersonAC.S3.basisStep j)).re
      rw [hcancel]
    rw [Finset.sum_congr rfl (fun x _ => hfun x)]
    exact sum_add_right
      (fun y => (star (v y) * v (y - AndersonAC.S3.basisStep j)).re)
      (AndersonAC.S3.basisStep j)
  rw [← htrans]
  apply Finset.sum_congr rfl
  intro x _
  exact star_dot_symm _ _

/-- `form` of a scalar identity matrix. -/
theorem form_smul_one_eq (v : AndersonAC.S3.Torus d L → ℂ) :
    AndersonAC.S3.form ((2 * ((d : ℕ) : ℂ)) • (1 : Matrix _ _ ℂ)) v
      = 2 * (d : ℝ) * AndersonAC.S3.normSq v := by
  have hmul : (((2 * ((d : ℕ) : ℂ)) • (1 : Matrix _ _ ℂ)) *ᵥ v)
      = fun i => ((2 * (d : ℝ) : ℝ) : ℂ) * v i := by
    funext i
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    push_cast
    ring
  unfold AndersonAC.S3.form
  rw [hmul]
  rw [pairing_real_smul_right]
  rw [pairing_self_eq_normSq]

/-- Moving `.re` inside a finite sum. -/
theorem sum_re_eq {A : Type*} [Fintype A] (s : Finset A) (f : A → ℂ) :
    (Finset.sum s f).re = Finset.sum s (fun i => (f i).re) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, Complex.add_re, ih]

/-- `form` of `freeHopping` as neighbor dot-sums. -/
theorem form_freeHopping_eq (v : AndersonAC.S3.Torus d L → ℂ) :
    AndersonAC.S3.form AndersonAC.S3.freeHopping v
      = -(∑ j : Fin d, (∑ x, (star (v x)
        * v (x + AndersonAC.S3.basisStep j)).re
        + ∑ x, (star (v x) * v (x + AndersonAC.S3.basisStep j)).re)) := by
  have hmv : ∀ x, (AndersonAC.S3.freeHopping *ᵥ v) x
      = -∑ j : Fin d, (v (x + AndersonAC.S3.basisStep j)
        + v (x - AndersonAC.S3.basisStep j)) :=
    fun x => mulVec_freeHopping v x
  have hpoint : ∀ x, (star (v x)
      * (AndersonAC.S3.freeHopping *ᵥ v) x).re
      = -∑ j : Fin d, (((star (v x)
        * v (x + AndersonAC.S3.basisStep j)).re)
        + ((star (v x) * v (x - AndersonAC.S3.basisStep j)).re)) := by
    intro x
    rw [hmv x, mul_neg, Finset.mul_sum]
    rw [Complex.neg_re, sum_re_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_add, Complex.add_re]
  unfold AndersonAC.S3.form AndersonAC.S3.pairing
  rw [sum_re_eq]
  rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_add_distrib]
  have hsub := dot_sum_sub_eq_add v j
  rw [hsub]

/-- `form` splits over matrix addition. -/
theorem form_add {A : Type*} [Fintype A] [DecidableEq A]
    (M N : Matrix A A ℂ) (v : A → ℂ) :
    AndersonAC.S3.form (M + N) v
      = AndersonAC.S3.form M v + AndersonAC.S3.form N v := by
  unfold AndersonAC.S3.form
  rw [Matrix.add_mulVec]
  exact pairing_add_right _ _ _

/-- Main energy identity. -/
theorem gradientEnergy_eq_form (v : AndersonAC.S3.Torus d L → ℂ) :
    AndersonAC.S3.gradientEnergy v
      = AndersonAC.S3.form AndersonAC.S3.laplacian v := by
  have hlap : AndersonAC.S3.laplacian (d := d) (L := L)
      = (2 * ((d : ℕ) : ℂ)) • (1 : Matrix _ _ ℂ)
        + AndersonAC.S3.freeHopping := rfl
  rw [hlap, form_add, form_smul_one_eq, form_freeHopping_eq]
  have hgrad : ∀ j : Fin d, (∑ x, ‖v (x + AndersonAC.S3.basisStep j) - v x‖ ^ 2)
      = 2 * AndersonAC.S3.normSq v
        - 2 * (∑ x, (star (v x) * v (x + AndersonAC.S3.basisStep j)).re) := by
    intro j
    have hexpand : ∀ x, ‖v (x + AndersonAC.S3.basisStep j) - v x‖ ^ 2
        = (‖v (x + AndersonAC.S3.basisStep j)‖ ^ 2 + ‖v x‖ ^ 2)
          - 2 * (star (v x) * v (x + AndersonAC.S3.basisStep j)).re := by
      intro x
      exact norm_sub_sq _ _
    rw [Finset.sum_congr rfl (fun x _ => hexpand x)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [normSq_shift v (AndersonAC.S3.basisStep j)]
    have hmul : (∑ x, 2 * (star (v x)
        * v (x + AndersonAC.S3.basisStep j)).re)
        = 2 * (∑ x, (star (v x) * v (x + AndersonAC.S3.basisStep j)).re) := by
      rw [Finset.mul_sum]
    rw [hmul]
    unfold AndersonAC.S3.normSq
    ring
  have hswap : (∑ x, ∑ j : Fin d, ‖v (x + AndersonAC.S3.basisStep j) - v x‖ ^ 2)
      = (∑ j : Fin d, ∑ x, ‖v (x + AndersonAC.S3.basisStep j) - v x‖ ^ 2) :=
    Finset.sum_comm
  have hsum_const : (∑ _j : Fin d, (2 * AndersonAC.S3.normSq v))
      = 2 * (d : ℝ) * AndersonAC.S3.normSq v := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
    ring
  have hform : (∑ j : Fin d, (∑ x, (star (v x)
      * v (x + AndersonAC.S3.basisStep j)).re
      + ∑ x, (star (v x) * v (x + AndersonAC.S3.basisStep j)).re))
      = 2 * (∑ j : Fin d, ∑ x, (star (v x)
        * v (x + AndersonAC.S3.basisStep j)).re) := by
    rw [Finset.sum_add_distrib]
    ring
  unfold AndersonAC.S3.gradientEnergy
  rw [hswap]
  rw [Finset.sum_congr rfl (fun j _ => hgrad j)]
  rw [Finset.sum_sub_distrib]
  rw [hsum_const]
  rw [hform]
  rw [← Finset.mul_sum]
  ring

/-- `gradientEnergy` vanishes iff constant (using connectivity). -/
theorem gradientEnergy_eq_zero_iff (v : AndersonAC.S3.Torus d L → ℂ) :
    AndersonAC.S3.gradientEnergy v = 0 ↔ ∃ c : ℂ, v = fun _ => c := by
  constructor
  · intro h0
    have hinner_nonneg : ∀ x ∈ (Finset.univ : Finset (AndersonAC.S3.Torus d L)),
        0 ≤ ∑ j : Fin d, ‖v (x + AndersonAC.S3.basisStep j) - v x‖ ^ 2 :=
      fun _ _ => Finset.sum_nonneg fun _ _ => pow_two_nonneg _
    have houter := (Finset.sum_eq_zero_iff_of_nonneg hinner_nonneg).mp h0
    have hstep : ∀ x (j : Fin d),
        v (x + AndersonAC.S3.basisStep j) = v x := by
      intro x j
      have hx := houter x (Finset.mem_univ x)
      have hpt_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin d)),
          0 ≤ ‖v (x + AndersonAC.S3.basisStep j) - v x‖ ^ 2 :=
        fun _ _ => pow_two_nonneg _
      have hpt := (Finset.sum_eq_zero_iff_of_nonneg hpt_nonneg).mp hx
      have hzero := hpt j (Finset.mem_univ j)
      have hnorm : ‖v (x + AndersonAC.S3.basisStep j) - v x‖ = 0 := by
        by_contra hne
        have hpos : 0 < ‖v (x + AndersonAC.S3.basisStep j) - v x‖ :=
          lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
        have hpos2 : 0 < ‖v (x + AndersonAC.S3.basisStep j) - v x‖ ^ 2 :=
          pow_pos hpos 2
        rw [hzero] at hpos2
        exact lt_irrefl _ hpos2
      have hdiff : v (x + AndersonAC.S3.basisStep j) - v x = 0 :=
        norm_eq_zero.mp hnorm
      exact sub_eq_zero.mp hdiff
    exact const_of_step_invariant v hstep
  · rintro ⟨c, rfl⟩
    have hconst : (fun _ : AndersonAC.S3.Torus d L => c)
        = (0 : AndersonAC.S3.Torus d L → ℂ) + fun _ => c := by
      simp
    rw [hconst, gradientEnergy_add_const, gradientEnergy_zero]

/-- The Laplacian is a connected Laplacian (no `L ≥ 4` needed, only `NeZero`). -/
theorem laplacian_connected :
    AndersonAC.S3.connectedLaplacian
      (AndersonAC.S3.laplacian (d := d) (L := L)) := by
  constructor
  · exact laplacian_hermitian
  · intro f
    rw [← gradientEnergy_eq_form]
    constructor
    · exact gradientEnergy_nonneg _
    · exact gradientEnergy_eq_zero_iff _

/-! ## General pseudoinverse for `connectedLaplacian` -/

/-- Hermitian cross-term symmetry: `pairing δ (M g) = pairing g (M δ)`. -/
theorem pairing_hermitian_symm {A : Type*} [Fintype A] [DecidableEq A]
    (M : Matrix A A ℂ) (hH : M.conjTranspose = M)
    (x y : A → ℂ) :
    AndersonAC.S3.pairing x (M *ᵥ y)
      = AndersonAC.S3.pairing y (M *ᵥ x) := by
  have hentry : ∀ i j, M i j = star (M j i) := by
    intro i j
    have h := congrFun (congrFun hH i) j
    simp only [Matrix.conjTranspose_apply] at h
    exact h.symm
  have hexpand : ∀ (a b : A → ℂ),
      AndersonAC.S3.pairing a (M *ᵥ b)
        = Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun j => (star (a i) * (M i j * b j)).re)) := by
    intro a b
    unfold AndersonAC.S3.pairing
    rw [sum_re_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [sum_re_eq]
  rw [hexpand, hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hconj : star (y j) * (M j i * x i)
      = star (star (x i) * (M i j * y j)) := by
    simp only [star_mul, star_star, hentry i j]
    ring
  rw [hconj]
  simp
  ring

/-- First-order condition: a minimizer of a positive Hermitian form is in the kernel.
    If `0 ≤ form M` everywhere and `form M g = 0`, then `M *ᵥ g = 0`. -/
theorem hermitian_form_min_kernel {A : Type*} [Fintype A] [DecidableEq A]
    (M : Matrix A A ℂ) (hH : M.conjTranspose = M)
    (hpos : ∀ f, 0 ≤ AndersonAC.S3.form M f)
    (g : A → ℂ) (hmin : AndersonAC.S3.form M g = 0) :
    M *ᵥ g = 0 := by
  have hmul_add : ∀ (a b : A → ℂ), M *ᵥ (a + b) = M *ᵥ a + M *ᵥ b := by
    intro a b
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
    calc ∑ x, M i x * (a x + b x)
        = ∑ x, (M i x * a x + M i x * b x) :=
          Finset.sum_congr rfl (fun _ _ => mul_add _ _ _)
      _ = (∑ x, M i x * a x) + (∑ x, M i x * b x) :=
          Finset.sum_add_distrib
  have hmul_real : ∀ (d : A → ℂ) (t : ℝ),
      M *ᵥ (fun i => (t : ℂ) * d i) = fun i => (t : ℂ) * (M *ᵥ d) i := by
    intro d t
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hexpand : ∀ (d : A → ℂ) (t : ℝ),
      AndersonAC.S3.form M (g + fun i => (t : ℂ) * d i)
        = AndersonAC.S3.form M g
          + t * (2 * AndersonAC.S3.pairing d (M *ᵥ g))
          + t ^ 2 * AndersonAC.S3.form M d := by
    intro d t
    have hMu : M *ᵥ (g + fun i => (t : ℂ) * d i)
        = M *ᵥ g + fun i => (t : ℂ) * (M *ᵥ d) i := by
      rw [hmul_add, hmul_real]
    unfold AndersonAC.S3.form
    rw [hMu]
    rw [pairing_add_left, pairing_add_right, pairing_add_right]
    rw [pairing_real_smul_left, pairing_real_smul_right,
      pairing_real_smul_left, pairing_real_smul_right]
    have hsymm : AndersonAC.S3.pairing g (M *ᵥ d)
        = AndersonAC.S3.pairing d (M *ᵥ g) :=
      pairing_hermitian_symm M hH g d
    rw [hsymm]
    ring
  have hpair_zero : ∀ d : A → ℂ,
      AndersonAC.S3.pairing d (M *ᵥ g) = 0 := by
    intro d
    have hb : 0 ≤ AndersonAC.S3.form M d := hpos d
    have hg : ∀ t : ℝ, 0 ≤ t * (2 * AndersonAC.S3.pairing d (M *ᵥ g))
        + t ^ 2 * AndersonAC.S3.form M d := by
      intro t
      have h := hpos (g + fun i => (t : ℂ) * d i)
      rw [hexpand, hmin, zero_add] at h
      exact h
    by_contra hne
    have ha : 2 * AndersonAC.S3.pairing d (M *ᵥ g) ≠ 0 := by
      intro h0
      apply hne
      linarith
    set a := 2 * AndersonAC.S3.pairing d (M *ᵥ g) with ha_def
    set b := AndersonAC.S3.form M d with hb_def
    have hb_nonneg : 0 ≤ b := hb
    have ha_ne : a ≠ 0 := ha
    have hb1_pos : 0 < b + 1 := by linarith
    set t0 := -a / (2 * (b + 1)) with ht0_def
    have hgt0 : 0 ≤ t0 * a + t0 ^ 2 * b := hg t0
    have hD_pos : 0 < 4 * (b + 1) ^ 2 := by positivity
    have hprod_nonneg : 0 ≤ (t0 * a + t0 ^ 2 * b) * (4 * (b + 1) ^ 2) :=
      mul_nonneg hgt0 (le_of_lt hD_pos)
    have hcalc : (t0 * a + t0 ^ 2 * b) * (4 * (b + 1) ^ 2)
        = -(a ^ 2 * (b + 2)) := by
      rw [ht0_def]
      field_simp
      ring
    rw [hcalc] at hprod_nonneg
    have ha2_pos : 0 < a ^ 2 := sq_pos_of_ne_zero ha_ne
    have hb2_pos : 0 < b + 2 := by linarith
    have hneg : -(a ^ 2 * (b + 2)) < 0 := by
      have : 0 < a ^ 2 * (b + 2) := mul_pos ha2_pos hb2_pos
      linarith
    linarith
  have hself : AndersonAC.S3.pairing (M *ᵥ g) (M *ᵥ g) = 0 :=
    hpair_zero _
  rw [pairing_self_eq_normSq] at hself
  have hzero : ∀ i, (M *ᵥ g) i = 0 := by
    intro i
    have hsum0 : AndersonAC.S3.normSq (M *ᵥ g) = 0 := hself
    unfold AndersonAC.S3.normSq at hsum0
    have hnonneg : ∀ j ∈ (Finset.univ : Finset A),
        0 ≤ ‖(M *ᵥ g) j‖ ^ 2 := fun _ _ => pow_two_nonneg _
    have hpt := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0
    have hi := hpt i (Finset.mem_univ i)
    have hnorm : ‖(M *ᵥ g) i‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖(M *ᵥ g) i‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have hpos2 : 0 < ‖(M *ᵥ g) i‖ ^ 2 := pow_pos hpos 2
      rw [hi] at hpos2
      exact lt_irrefl _ hpos2
    exact norm_eq_zero.mp hnorm
  funext i
  simp [hzero i]

/-! ## Mean projection and `D` killing constants -/

theorem meanProjection_hermitian (A : Type*) [Fintype A] :
    (AndersonAC.S3.meanProjection A).conjTranspose
      = AndersonAC.S3.meanProjection A := by
  funext x y
  simp only [Matrix.conjTranspose_apply, AndersonAC.S3.meanProjection]
  have hreal : star (((Fintype.card A : ℕ) : ℂ)⁻¹)
      = (((Fintype.card A : ℕ) : ℂ)⁻¹) := by
    simp
  exact hreal

/-- `D` kills the constant-one vector (minimizer argument). -/
theorem connectedLaplacian_mulVec_one {A : Type*} [Fintype A] [DecidableEq A]
    (D : Matrix A A ℂ) (hD : AndersonAC.S3.connectedLaplacian D) :
    D *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  have hpos : ∀ f, 0 ≤ AndersonAC.S3.form D f := fun f => (hD.2 f).1
  have hzero : AndersonAC.S3.form D (fun _ => (1 : ℂ)) = 0 := by
    have hker := (hD.2 (fun _ => (1 : ℂ))).2
    rw [hker]
    exact ⟨1, rfl⟩
  exact hermitian_form_min_kernel D hD.1 hpos _ hzero

/-- `D` kills every constant vector. -/
theorem connectedLaplacian_mulVec_const {A : Type*} [Fintype A] [DecidableEq A]
    (D : Matrix A A ℂ) (hD : AndersonAC.S3.connectedLaplacian D)
    (c : ℂ) : D *ᵥ (fun _ : A => c) = 0 := by
  have h1 := connectedLaplacian_mulVec_one D hD
  have hconst : (fun _ : A => c) = c • (fun _ : A => (1 : ℂ)) := by
    funext i
    simp [smul_eq_mul]
  rw [hconst, Matrix.mulVec_smul, h1, smul_zero]

/-- `meanProjection` applied to a vector gives the constant mean. -/
theorem meanProjection_mulVec {A : Type*} [Fintype A]
    (v : A → ℂ) :
    (AndersonAC.S3.meanProjection A *ᵥ v)
      = fun _ => ((Fintype.card A : ℂ)⁻¹ * ∑ i, v i) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, AndersonAC.S3.meanProjection]
  rw [Finset.mul_sum]

/-- `form` of `meanProjection` is `n⁻¹‖∑‖² ≥ 0`. -/
theorem form_meanProjection_nonneg {A : Type*} [Fintype A]
    (v : A → ℂ) : 0 ≤ AndersonAC.S3.form (AndersonAC.S3.meanProjection A) v := by
  have hPv := meanProjection_mulVec v
  unfold AndersonAC.S3.form AndersonAC.S3.pairing
  rw [hPv]
  have hreal : (((Fintype.card A : ℕ) : ℂ)⁻¹
      = (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ)) := by
    push_cast
    rfl
  have hsum : (∑ i, star (v i) * (((Fintype.card A : ℂ)⁻¹ * ∑ j, v j))).re
      = ((Fintype.card A : ℝ)⁻¹ * ‖∑ i, v i‖ ^ 2) := by
    rw [hreal]
    have hstep : ∀ i, star (v i) * (((((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) * ∑ j, v j))
        = ((((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ)
          * (star (v i) * (∑ j, v j))) := by
      intro i
      ring
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    rw [← Finset.mul_sum]
    have hstar_sum : (∑ i, star (v i) * (∑ j, v j))
        = star (∑ i, v i) * (∑ j, v j) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [star_sum]
    rw [hstar_sum]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [star_mul_self_re]
  rw [hsum]
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact pow_two_nonneg _

/-- `P` applied to a constant returns it (when nonempty). -/
theorem meanProjection_mulVec_const {A : Type*} [Fintype A] [Nonempty A]
    (c : ℂ) :
    (AndersonAC.S3.meanProjection A *ᵥ (fun _ : A => c)) = fun _ => c := by
  funext x
  simp only [Matrix.mulVec, dotProduct, AndersonAC.S3.meanProjection]
  rw [Finset.sum_const, Finset.card_univ]
  simp [nsmul_eq_mul]

/-- `P * P = P` (nonempty; empty is `0=0`). -/
theorem meanProjection_mul_self (A : Type*) [Fintype A] [DecidableEq A]
    [Nonempty A] :
    AndersonAC.S3.meanProjection A * AndersonAC.S3.meanProjection A
      = AndersonAC.S3.meanProjection A := by
  funext x y
  simp only [Matrix.mul_apply, AndersonAC.S3.meanProjection]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : ((Fintype.card A : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- `D * P = 0` for connected `D` (nonempty; empty vacuous). -/
theorem connected_mul_meanProj {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (D : Matrix A A ℂ)
    (hD : AndersonAC.S3.connectedLaplacian D) :
    D * AndersonAC.S3.meanProjection A = 0 := by
  funext x y
  simp only [Matrix.mul_apply, Matrix.zero_apply, AndersonAC.S3.meanProjection]
  have hcol : ∀ k, D x k = D x k := fun k => rfl
  have hD1 : D *ᵥ (fun _ : A => (1 : ℂ)) = 0 :=
    connectedLaplacian_mulVec_one D hD
  have hrow : ∑ k, D x k = 0 := by
    have h := congrFun hD1 x
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h
    simpa using h
  calc ∑ k, D x k * ((Fintype.card A : ℂ)⁻¹)
      = (∑ k, D x k) * ((Fintype.card A : ℂ)⁻¹) := by rw [Finset.sum_mul]
    _ = 0 * _ := by rw [hrow]
    _ = 0 := zero_mul _

/-- `P * D = 0` from `D * P = 0` + Hermitian. -/
theorem meanProj_mul_connected {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (D : Matrix A A ℂ)
    (hD : AndersonAC.S3.connectedLaplacian D) :
    AndersonAC.S3.meanProjection A * D = 0 := by
  have hDP := connected_mul_meanProj D hD
  have hPh : (AndersonAC.S3.meanProjection A).conjTranspose
      = AndersonAC.S3.meanProjection A :=
    meanProjection_hermitian A
  have hDh : D.conjTranspose = D := hD.1
  have h : (D * AndersonAC.S3.meanProjection A).conjTranspose = (0 : Matrix _ _ ℂ) := by
    rw [hDP, Matrix.conjTranspose_zero]
  rw [Matrix.conjTranspose_mul, hPh, hDh] at h
  -- `h : P * D = 0` after rewriting `(D*P)ᴴ = Pᴴ*Dᴴ`
  exact h

/-- `D + P` is invertible for connected `D` (empty case vacuous). -/
theorem isUnit_D_add_P {A : Type*} [Fintype A] [DecidableEq A]
    (D : Matrix A A ℂ) (hD : AndersonAC.S3.connectedLaplacian D) :
    IsUnit (D + AndersonAC.S3.meanProjection A) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have hsub : (D + AndersonAC.S3.meanProjection A) *ᵥ (a - b) = 0 := by
    have h1 : (D + AndersonAC.S3.meanProjection A) *ᵥ a
        = (D + AndersonAC.S3.meanProjection A) *ᵥ b := hab
    have h2 : (D + AndersonAC.S3.meanProjection A) *ᵥ (a - b)
        = (D + AndersonAC.S3.meanProjection A) *ᵥ a
          - (D + AndersonAC.S3.meanProjection A) *ᵥ b := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
      calc ∑ x, (D + AndersonAC.S3.meanProjection A) i x * (a x - b x)
          = ∑ x, ((D + AndersonAC.S3.meanProjection A) i x * a x
            - (D + AndersonAC.S3.meanProjection A) i x * b x) :=
            Finset.sum_congr rfl (fun _ _ => mul_sub _ _ _)
        _ = (∑ x, (D + AndersonAC.S3.meanProjection A) i x * a x)
            - (∑ x, (D + AndersonAC.S3.meanProjection A) i x * b x) :=
            Finset.sum_sub_distrib _ _
    rw [h2, h1, sub_self]
  have hker : a - b = 0 := by
    rcases isEmpty_or_nonempty A with hempty | hempty
    · funext i
      exact IsEmpty.elim hempty i
    · haveI := hempty
      have hform0 : AndersonAC.S3.form (D + AndersonAC.S3.meanProjection A) (a - b) = 0 := by
        unfold AndersonAC.S3.form
        rw [hsub]
        exact pairing_zero_right _
      have hsplit := form_add D (AndersonAC.S3.meanProjection A) (a - b)
      rw [hform0] at hsplit
      -- `hsplit : 0 = form D + form P`; both nonneg so both zero
      have hD_nonneg := (hD.2 (a - b)).1
      have hP_nonneg := form_meanProjection_nonneg (a - b)
      have hboth : AndersonAC.S3.form D (a - b) = 0
          ∧ AndersonAC.S3.form (AndersonAC.S3.meanProjection A) (a - b) = 0 := by
        have h := hsplit.symm
        -- `h : form D + form P = 0`
        have := (add_eq_zero_iff_of_nonneg hD_nonneg hP_nonneg).mp h
        exact this
      obtain ⟨hDz, hPz⟩ := hboth
      obtain ⟨c, hc⟩ := (hD.2 (a - b)).2.mp hDz
      -- `form P = r*‖S‖² = 0 → S = 0`
      have hsum_zero : ∑ i, (a - b) i = 0 := by
        have hform_eq : AndersonAC.S3.form (AndersonAC.S3.meanProjection A) (a - b)
            = ((Fintype.card A : ℝ)⁻¹ * ‖∑ i, (a - b) i‖ ^ 2) := by
          have hPv := meanProjection_mulVec (a - b)
          unfold AndersonAC.S3.form AndersonAC.S3.pairing
          rw [hPv]
          have hreal : (((Fintype.card A : ℕ) : ℂ)⁻¹
              = (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ)) := by
            push_cast
            rfl
          have hsum : (∑ i, star ((a - b) i)
              * (((Fintype.card A : ℂ)⁻¹ * ∑ j, (a - b) j))).re
              = ((Fintype.card A : ℝ)⁻¹ * ‖∑ i, (a - b) i‖ ^ 2) := by
            rw [hreal]
            have hstep : ∀ i, star ((a - b) i)
                * (((((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) * ∑ j, (a - b) j))
                = ((((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ)
                  * (star ((a - b) i) * (∑ j, (a - b) j))) := by
              intro i
              ring
            rw [Finset.sum_congr rfl (fun i _ => hstep i)]
            rw [← Finset.mul_sum]
            have hstar_sum : (∑ i, star ((a - b) i) * (∑ j, (a - b) j))
                = star (∑ i, (a - b) i) * (∑ j, (a - b) j) := by
              rw [← Finset.sum_mul]
              congr 1
              rw [star_sum]
            rw [hstar_sum]
            rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              zero_mul, sub_zero]
            rw [star_mul_self_re]
          exact hsum
        rw [hform_eq] at hPz
        have hr_ne : ((Fintype.card A : ℝ)⁻¹ : ℝ) ≠ 0 := by
          apply inv_ne_zero
          apply ne_of_gt
          apply Nat.cast_pos.mpr
          exact Fintype.card_pos
        have hnorm2 : ‖∑ i, (a - b) i‖ ^ 2 = 0 := by
          have h := (mul_eq_zero.mp hPz)
          rcases h with h | h
          · exact absurd h hr_ne
          · exact h
        have hnorm : ‖∑ i, (a - b) i‖ = 0 := by
          by_contra hne
          have hpos : 0 < ‖∑ i, (a - b) i‖ :=
            lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
          have hpos2 : 0 < ‖∑ i, (a - b) i‖ ^ 2 := pow_pos hpos 2
          rw [hnorm2] at hpos2
          exact lt_irrefl _ hpos2
        exact norm_eq_zero.mp hnorm
      -- `const c` with sum zero → `c = 0`
      have hc0 : c = 0 := by
        have hsum_c : ∑ _i : A, c = (Fintype.card A : ℂ) * c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hS : ∑ i, (a - b) i = ∑ _i : A, c := by
          rw [Finset.sum_congr rfl (fun i _ => congrFun hc i)]
        rw [hsum_zero] at hS
        rw [hsum_c] at hS
        have hn : ((Fintype.card A : ℕ) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        have h := (mul_eq_zero.mp hS.symm)
        rcases h with h | h
        · exact absurd h hn
        · exact h
      rw [hc, hc0]
      funext i
      rfl
  exact sub_eq_zero.mp hker

/-! ## Pseudoinverse `X` for nonempty `connectedLaplacian` -/

/-- `P * (D + P) = P` (nonempty). -/
theorem meanProj_mul_D_add_P {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : AndersonAC.S3.connectedLaplacian D) :
    AndersonAC.S3.meanProjection A * (D + AndersonAC.S3.meanProjection A)
      = AndersonAC.S3.meanProjection A := by
  rw [Matrix.mul_add, meanProj_mul_connected D hD,
    meanProjection_mul_self A, zero_add]

/-- `(D + P) * P = P` (nonempty). -/
theorem D_add_P_mul_meanProj {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : AndersonAC.S3.connectedLaplacian D) :
    (D + AndersonAC.S3.meanProjection A) * AndersonAC.S3.meanProjection A
      = AndersonAC.S3.meanProjection A := by
  rw [Matrix.add_mul, connected_mul_meanProj D hD,
    meanProjection_mul_self A, zero_add]

/-- `P * (D+P)⁻¹ = P` from `P*(D+P)=P` + IsUnit. -/
theorem meanProj_mul_inv {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : AndersonAC.S3.connectedLaplacian D) :
    AndersonAC.S3.meanProjection A * (D + AndersonAC.S3.meanProjection A)⁻¹
      = AndersonAC.S3.meanProjection A := by
  have hU := isUnit_D_add_P D hD
  have hdet : IsUnit (D + AndersonAC.S3.meanProjection A).det :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hPP := meanProj_mul_D_add_P D hD
  calc AndersonAC.S3.meanProjection A * (D + AndersonAC.S3.meanProjection A)⁻¹
      = (AndersonAC.S3.meanProjection A * (D + AndersonAC.S3.meanProjection A))
        * (D + AndersonAC.S3.meanProjection A)⁻¹ := by
        rw [hPP]
    _ = AndersonAC.S3.meanProjection A
        * ((D + AndersonAC.S3.meanProjection A)
          * (D + AndersonAC.S3.meanProjection A)⁻¹) := by
        rw [Matrix.mul_assoc]
    _ = AndersonAC.S3.meanProjection A * 1 := by
        rw [Matrix.mul_nonsing_inv _ hdet]
    _ = AndersonAC.S3.meanProjection A := Matrix.mul_one _

/-- `(D+P)⁻¹ * P = P` symmetrically. -/
theorem inv_mul_meanProj {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : AndersonAC.S3.connectedLaplacian D) :
    (D + AndersonAC.S3.meanProjection A)⁻¹ * AndersonAC.S3.meanProjection A
      = AndersonAC.S3.meanProjection A := by
  have hU := isUnit_D_add_P D hD
  have hdet : IsUnit (D + AndersonAC.S3.meanProjection A).det :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hPP := D_add_P_mul_meanProj D hD
  calc (D + AndersonAC.S3.meanProjection A)⁻¹ * AndersonAC.S3.meanProjection A
      = (D + AndersonAC.S3.meanProjection A)⁻¹
        * ((D + AndersonAC.S3.meanProjection A) * AndersonAC.S3.meanProjection A) := by
        rw [hPP]
    _ = ((D + AndersonAC.S3.meanProjection A)⁻¹
        * (D + AndersonAC.S3.meanProjection A))
        * AndersonAC.S3.meanProjection A := by
        rw [← Matrix.mul_assoc]
    _ = 1 * AndersonAC.S3.meanProjection A := by
        rw [Matrix.nonsing_inv_mul _ hdet]
    _ = AndersonAC.S3.meanProjection A := Matrix.one_mul _

/-- `P *ᵥ y = 0` iff `neutral y` (nonempty). -/
theorem meanProj_mulVec_eq_zero_iff {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (y : A → ℂ) :
    AndersonAC.S3.meanProjection A *ᵥ y = 0 ↔ AndersonAC.S3.neutral y := by
  have hP := meanProjection_mulVec y
  constructor
  · intro h
    unfold AndersonAC.S3.neutral
    have hn : ((Fintype.card A : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hmean : ((Fintype.card A : ℂ)⁻¹ * ∑ i, y i) = 0 := by
      have h0 := congrFun h (Classical.arbitrary A)
      rw [hP] at h0
      simpa using h0
    have hS : (∑ i, y i) = 0 := by
      have h := (mul_eq_zero.mp hmean)
      rcases h with h | h
      · exfalso
        apply hn
        have : ((Fintype.card A : ℂ)⁻¹)⁻¹ = (Fintype.card A : ℂ) := inv_inv _
        rw [← this, h]
        simp
      · exact h
    exact hS
  · intro h
    unfold AndersonAC.S3.neutral at h
    rw [hP]
    funext i
    simp [h]

/-- `D *ᵥ (X *ᵥ y) = y` for neutral `y` (nonempty). Here `X` is `inverseOnConstants`. -/
theorem pseudoinv_mulVec {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : AndersonAC.S3.connectedLaplacian D)
    (y : A → ℂ) (hy : AndersonAC.S3.neutral y) :
    D *ᵥ ((AndersonAC.S3.inverseOnConstants D) *ᵥ y) = y := by
  have hU := isUnit_D_add_P D hD
  have hdet : IsUnit (D + AndersonAC.S3.meanProjection A).det :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hPinv := meanProj_mul_inv D hD
  have hPy : AndersonAC.S3.meanProjection A *ᵥ y = 0 :=
    (meanProj_mulVec_eq_zero_iff y).mpr hy
  have hXy : (AndersonAC.S3.inverseOnConstants D) *ᵥ y
      = (D + AndersonAC.S3.meanProjection A)⁻¹ *ᵥ y := by
    unfold AndersonAC.S3.inverseOnConstants
    rw [Matrix.sub_mulVec, hPy, sub_zero]
  rw [hXy]
  have hDPinv : (D + AndersonAC.S3.meanProjection A)
      *ᵥ ((D + AndersonAC.S3.meanProjection A)⁻¹ *ᵥ y) = y := by
    have hmat : (D + AndersonAC.S3.meanProjection A)
        * (D + AndersonAC.S3.meanProjection A)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hdet
    have hvec := congrArg (· *ᵥ y) hmat
    simp only [Matrix.one_mulVec] at hvec
    rw [← Matrix.mulVec_mulVec] at hvec
    exact hvec
  have hPinv_y : AndersonAC.S3.meanProjection A
      *ᵥ ((D + AndersonAC.S3.meanProjection A)⁻¹ *ᵥ y) = 0 := by
    have hvec := congrArg (· *ᵥ y) hPinv
    rw [← Matrix.mulVec_mulVec] at hvec
    rw [hvec, hPy]
  have hsplit : (D + AndersonAC.S3.meanProjection A)
      *ᵥ ((D + AndersonAC.S3.meanProjection A)⁻¹ *ᵥ y)
      = D *ᵥ ((D + AndersonAC.S3.meanProjection A)⁻¹ *ᵥ y)
        + AndersonAC.S3.meanProjection A
          *ᵥ ((D + AndersonAC.S3.meanProjection A)⁻¹ *ᵥ y) := by
    rw [Matrix.add_mulVec]
  rw [hDPinv, hPinv_y, add_zero] at hsplit
  exact hsplit.symm

/-- Pairing a constant against a neutral charge vanishes (left). -/
theorem pairing_const_neutral_left {A : Type*} [Fintype A]
    (c : ℂ) (w : A → ℂ) (hw : AndersonAC.S3.neutral w) :
    AndersonAC.S3.pairing (fun _ : A => c) w = 0 := by
  unfold AndersonAC.S3.pairing AndersonAC.S3.neutral at *
  have hsum : (∑ i, star c * w i) = star c * (∑ i, w i) := by
    rw [Finset.mul_sum]
  rw [hsum, hw, mul_zero]
  rfl

/-- Pairing a neutral charge against a constant vanishes (right, via comm). -/
theorem pairing_neutral_const_right {A : Type*} [Fintype A]
    (y : A → ℂ) (hy : AndersonAC.S3.neutral y) (c : ℂ) :
    AndersonAC.S3.pairing y (fun _ : A => c) = 0 := by
  rw [pairing_comm]
  exact pairing_const_neutral_left c y hy

open AndersonAC.S3

/-- Completion of squares for a connected Laplacian and its pseudoinverse. -/
theorem young_D_X {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : connectedLaplacian D)
    (f y : A → ℂ) (hy : neutral y) :
    2 * pairing y f ≤ form D f + form (inverseOnConstants D) y := by
  have h := (hD.2 (f - inverseOnConstants D *ᵥ y)).1
  have hDy := pseudoinv_mulVec D hD y hy
  have hcross := pairing_hermitian_symm D hD.1 f (inverseOnConstants D *ᵥ y)
  rw [hDy] at hcross
  have hdiag : pairing (inverseOnConstants D *ᵥ y) y = form (inverseOnConstants D) y :=
    pairing_comm _ _
  unfold form at h
  rw [Matrix.mulVec_sub, hDy, pairing_sub_left,
    pairing_sub_right, pairing_sub_right, ← hcross, hdiag, pairing_comm f y] at h
  change 2 * pairing y f ≤ pairing f (D *ᵥ f) + form (inverseOnConstants D) y
  linarith

/-- The inverse value is attained in the dual variational principle. -/
theorem dual_D_attains {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : connectedLaplacian D)
    (y : A → ℂ) (hy : neutral y) :
    2 * pairing y (inverseOnConstants D *ᵥ y)
      - form D (inverseOnConstants D *ᵥ y) = form (inverseOnConstants D) y := by
  unfold form
  rw [pseudoinv_mulVec D hD y hy, pairing_comm (inverseOnConstants D *ᵥ y) y]
  ring

/-- The image of a connected Laplacian is neutral. -/
theorem connected_image_neutral {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : connectedLaplacian D) (f : A → ℂ) :
    neutral (D *ᵥ f) := by
  apply (meanProj_mulVec_eq_zero_iff _).mp
  rw [Matrix.mulVec_mulVec, meanProj_mul_connected D hD, Matrix.zero_mulVec]

/-- A connected pseudoinverse gives a nonnegative value on neutral charges. -/
theorem pseudoinv_nonneg {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : connectedLaplacian D)
    (y : A → ℂ) (hy : neutral y) : 0 ≤ form (inverseOnConstants D) y := by
  have h := (hD.2 (inverseOnConstants D *ᵥ y)).1
  simpa only [form, pseudoinv_mulVec D hD y hy, pairing_comm] using h

/-- Left inverse identity modulo constants. -/
theorem pseudoinv_left_mulVec {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : connectedLaplacian D) (f : A → ℂ) :
    inverseOnConstants D *ᵥ (D *ᵥ f) = f - meanProjection A *ᵥ f := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_D_add_P D hD)
  have hmat : (D + meanProjection A)⁻¹ * D = 1 - meanProjection A := by
    have h := Matrix.nonsing_inv_mul (D + meanProjection A) hdet
    rw [Matrix.mul_add, inv_mul_meanProj D hD] at h
    exact eq_sub_of_add_eq h
  unfold inverseOnConstants
  rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    meanProj_mul_connected D hD, Matrix.zero_mulVec, sub_zero, hmat,
    Matrix.sub_mulVec, Matrix.one_mulVec]

/-- The primal value is attained in the neutral dual variational principle. -/
theorem bidual_D_attains {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : connectedLaplacian D) (f : A → ℂ) :
    2 * pairing (D *ᵥ f) f - form (inverseOnConstants D) (D *ᵥ f) = form D f := by
  have hn := connected_image_neutral D hD f
  unfold form
  rw [pseudoinv_left_mulVec D hD f, pairing_sub_right,
    meanProjection_mulVec, pairing_neutral_const_right _ hn, sub_zero,
    pairing_comm (D *ᵥ f) f]
  ring

/-- Least squares data space, with the energy encoded in extra coordinates. -/
abbrev CostSpace (A : Type*) (d L : ℕ) :=
  EuclideanSpace ℂ (A ⊕ (Torus d L × Fin d))

def costEmbed {A : Type*} [Fintype A] : (A → ℂ) →ₗ[ℂ] CostSpace A d L where
  toFun f := WithLp.toLp 2 (Sum.elim f (fun _ => 0))
  map_add' f g := by ext i; cases i <;> simp
  map_smul' z f := by ext i; cases i <;> simp

def costFit {A : Type*} [Fintype A] (π : A → Torus d L) (b : ℝ) :
    (Torus d L → ℂ) →ₗ[ℂ] CostSpace A d L where
  toFun v := WithLp.toLp 2 (Sum.elim (fun x => v (π x))
    (fun p => (Real.sqrt b⁻¹ : ℂ) * (v (p.1 + basisStep p.2) - v p.1)))
  map_add' v w := by
    ext i
    cases i with
    | inl x => rfl
    | inr p =>
        change (Real.sqrt b⁻¹ : ℂ) * ((v (p.1 + basisStep p.2) + w (p.1 + basisStep p.2)) - (v p.1 + w p.1))
          = (Real.sqrt b⁻¹ : ℂ) * (v (p.1 + basisStep p.2) - v p.1)
            + (Real.sqrt b⁻¹ : ℂ) * (w (p.1 + basisStep p.2) - w p.1)
        ring
  map_smul' z v := by
    ext i
    cases i with
    | inl x => rfl
    | inr p =>
        change (Real.sqrt b⁻¹ : ℂ) * (z * v (p.1 + basisStep p.2) - z * v p.1)
          = z * ((Real.sqrt b⁻¹ : ℂ) * (v (p.1 + basisStep p.2) - v p.1))
        ring

theorem comparisonCost_norm {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) (v : Torus d L → ℂ) :
    comparisonCost π b f v = ‖costEmbed (d := d) (L := L) f - costFit π b v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  unfold comparisonCost normSq gradientEnergy
  congr 1
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change b⁻¹ * ‖v (x + basisStep j) - v x‖ ^ 2 =
    ‖(0 : ℂ) - ((Real.sqrt b⁻¹ : ℂ) * (v (x + basisStep j) - v x))‖ ^ 2
  rw [zero_sub, norm_neg, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt (inv_pos.mpr hb))]

def costResidual {A : Type*} [Fintype A] (π : A → Torus d L) (b : ℝ) :
    (A → ℂ) →ₗ[ℂ] CostSpace A d L :=
  ((LinearMap.range (costFit π b))ᗮ.starProjection : CostSpace A d L →ₗ[ℂ] CostSpace A d L).comp costEmbed

set_option maxHeartbeats 1000000 in
theorem comparison_minimizer {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) :
    ∃ v, (∀ w, comparisonCost π b f v ≤ comparisonCost π b f w) ∧
      comparisonW π b f = comparisonCost π b f v ∧
      comparisonW π b f = ‖costResidual π b f‖ ^ 2 := by
  let K := LinearMap.range (costFit π b)
  have hm : K.starProjection (costEmbed f) ∈ K := K.starProjection_apply_mem _
  obtain ⟨v, hv⟩ := hm
  have hle : ∀ w, comparisonCost π b f v ≤ comparisonCost π b f w := by
    intro w
    rw [comparisonCost_norm π b hb, comparisonCost_norm π b hb, hv]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    rw [Submodule.starProjection_minimal]
    exact ciInf_le (show BddBelow (Set.range (fun u : K => ‖costEmbed (d := d) (L := L) f - (u : CostSpace A d L)‖)) from
      ⟨0, fun _ hr => by obtain ⟨i, rfl⟩ := hr; exact norm_nonneg _⟩)
      (⟨costFit π b w, ⟨w, rfl⟩⟩ : K)
  have hW : comparisonW π b f = comparisonCost π b f v := by
    apply IsLeast.csInf_eq
    exact ⟨⟨v, rfl⟩, fun _ hr => by obtain ⟨w, rfl⟩ := hr; exact hle w⟩
  refine ⟨v, hle, hW, ?_⟩
  rw [hW, comparisonCost_norm π b hb, hv]
  change ‖costEmbed f - K.starProjection (costEmbed f)‖ ^ 2 = ‖Kᗮ.starProjection (costEmbed f)‖ ^ 2
  rw [K.starProjection_orthogonal_val]

theorem comparisonW_norm {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) :
    comparisonW π b f = ‖costResidual π b f‖ ^ 2 := by
  obtain ⟨v, _, _, h⟩ := comparison_minimizer π b hb f
  exact h

theorem comparisonW_le_cost {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) (v : Torus d L → ℂ) :
    comparisonW π b f ≤ comparisonCost π b f v := by
  obtain ⟨w, hw, hW, _⟩ := comparison_minimizer π b hb f
  rw [hW]
  exact hw v

theorem normSq_eq_zero_iff {A : Type*} [Fintype A] (f : A → ℂ) :
    normSq f = 0 ↔ f = 0 := by
  constructor
  · intro h
    funext x
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (i : A) (_ : i ∈ Finset.univ) => sq_nonneg ‖f i‖)).mp h x (Finset.mem_univ x)
    simpa only [sq_eq_zero_iff, norm_eq_zero, Pi.zero_apply] using hx
  · rintro rfl
    exact normSq_zero

theorem comparisonW_nonneg_kernel {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) :
    0 ≤ comparisonW π b f ∧ (comparisonW π b f = 0 ↔ ∃ c : ℂ, f = fun _ => c) := by
  constructor
  · rw [comparisonW_norm π b hb]
    positivity
  · constructor
    · intro h
      obtain ⟨v, _, hW, _⟩ := comparison_minimizer π b hb f
      rw [hW] at h
      have hparts := (add_eq_zero_iff_of_nonneg
        (normSq_nonneg (fun x => f x - v (π x)))
        (mul_nonneg (le_of_lt (inv_pos.mpr hb)) (gradientEnergy_nonneg v))).mp h
      have he : gradientEnergy v = 0 := (mul_eq_zero.mp hparts.2).resolve_left
        (ne_of_gt (inv_pos.mpr hb))
      obtain ⟨c, hc⟩ := (gradientEnergy_eq_zero_iff v).mp he
      have hz := (normSq_eq_zero_iff _).mp hparts.1
      refine ⟨c, ?_⟩
      funext x
      have hx := congrFun hz x
      simp only [Pi.zero_apply] at hx
      simpa [hc] using sub_eq_zero.mp hx
    · rintro ⟨c, rfl⟩
      have hle := comparisonW_le_cost π b hb (fun _ => c) (fun _ => c)
      have hz : comparisonCost π b (fun _ => c) (fun _ => c) = 0 := by
        simp [comparisonCost, normSq, gradientEnergy]
      rw [hz] at hle
      exact le_antisymm hle (by rw [comparisonW_norm π b hb]; positivity)

theorem costResidual_const {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (c : ℂ) : costResidual π b (fun _ => c) = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [← comparisonW_norm π b hb]
  exact (comparisonW_nonneg_kernel π b hb (fun _ => c)).2.mpr ⟨c, rfl⟩

theorem comparisonW_shift {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) (c : ℂ) :
    comparisonW π b (fun x => f x + c) = comparisonW π b f := by
  rw [comparisonW_norm π b hb, comparisonW_norm π b hb]
  rw [show (fun x => f x + c) = f + (fun _ : A => c) from rfl,
    map_add, costResidual_const π b hb, add_zero]

theorem comparisonW_parallelogram {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f g : A → ℂ) :
    comparisonW π b (f + g) + comparisonW π b (f - g) =
      2 * comparisonW π b f + 2 * comparisonW π b g := by
  simp only [comparisonW_norm π b hb, map_add, map_sub]
  have h := parallelogram_law_with_norm ℂ (costResidual π b f) (costResidual π b g)
  linarith

theorem comparisonW_smul {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) (z : ℂ) :
    comparisonW π b (z • f) = ‖z‖ ^ 2 * comparisonW π b f := by
  simp only [comparisonW_norm π b hb, map_smul, norm_smul, mul_pow]

theorem pairing_siteSum {A : Type*} [Fintype A] (π : A → Torus d L)
    (y : A → ℂ) (v : Torus d L → ℂ) : pairing (siteSum π y) v = pairing y (fun x => v (π x)) := by
  unfold pairing
  congr 1
  simp only [siteSum, star_sum, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [apply_ite]

theorem siteSum_neutral {A : Type*} [Fintype A] (π : A → Torus d L)
    (y : A → ℂ) (hy : neutral y) : neutral (siteSum π y) := by
  unfold neutral siteSum at *
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simpa using hy

theorem neutral_real_smul {A : Type*} [Fintype A] (y : A → ℂ) (hy : neutral y) (t : ℝ) :
    neutral (fun i => (t : ℂ) * y i) := by
  unfold neutral at *
  rw [← Finset.mul_sum, hy, mul_zero]

theorem form_real_smul {A : Type*} [Fintype A] [DecidableEq A]
    (M : Matrix A A ℂ) (f : A → ℂ) (t : ℝ) :
    form M (fun i => (t : ℂ) * f i) = t ^ 2 * form M f := by
  have hM : M *ᵥ (fun i => (t : ℂ) * f i) = fun i => (t : ℂ) * (M *ᵥ f) i :=
    Matrix.mulVec_smul M (t : ℂ) f
  unfold form
  rw [hM, pairing_real_smul_left, pairing_real_smul_right]
  ring

theorem young_scaled_D_X {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (D : Matrix A A ℂ) (hD : connectedLaplacian D)
    (q : ℝ) (hq : 0 < q) (f y : A → ℂ) (hy : neutral y) :
    2 * pairing y f ≤ q⁻¹ * form D f + q * form (inverseOnConstants D) y := by
  have h := young_D_X D hD f (fun i => (q : ℂ) * y i) (neutral_real_smul y hy q)
  rw [pairing_real_smul_left, form_real_smul] at h
  apply (mul_le_mul_iff_right₀ hq).mp
  calc q * (2 * pairing y f) ≤ form D f + q ^ 2 * form (inverseOnConstants D) y := by nlinarith [h]
    _ = q * (q⁻¹ * form D f + q * form (inverseOnConstants D) y) := by
      field_simp <;> ring

theorem normSq_young {A : Type*} [Fintype A] (y f : A → ℂ) :
    2 * pairing y f ≤ normSq y + normSq f := by
  have h := normSq_nonneg (f - y)
  rw [← pairing_self_eq_normSq, pairing_sub_left, pairing_sub_right,
    pairing_sub_right, pairing_self_eq_normSq, pairing_self_eq_normSq, pairing_comm f y] at h
  linarith

theorem comparison_young {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f y : A → ℂ) (hy : neutral y) :
    2 * pairing y f ≤ comparisonW π b f + comparisonWStar π b y := by
  obtain ⟨v, _, hW, _⟩ := comparison_minimizer π b hb f
  have ha := normSq_young y (f - fun x => v (π x))
  have hv := young_scaled_D_X laplacian laplacian_connected b hb v (siteSum π y) (siteSum_neutral π y hy)
  rw [pairing_siteSum, ← gradientEnergy_eq_form] at hv
  rw [pairing_sub_right] at ha
  rw [hW]
  unfold comparisonCost comparisonWStar
  change 2 * pairing y f ≤ normSq (f - fun x => v (π x)) + b⁻¹ * gradientEnergy v +
    (normSq y + b * form (inverseOnConstants laplacian) (siteSum π y))
  linarith

/-- A witness for the dual maximum of the comparison form. -/
theorem comparison_dual_witness {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (y : A → ℂ) (hy : neutral y) :
    ∃ f, pairing y f = comparisonWStar π b y ∧ comparisonW π b f = comparisonWStar π b y := by
  let u := laplacianPlus *ᵥ siteSum π y
  let v := fun i => (b : ℂ) * u i
  let f := y + fun x => v (π x)
  have hn := siteSum_neutral π y hy
  have hLu : laplacian *ᵥ u = siteSum π y := pseudoinv_mulVec laplacian laplacian_connected _ hn
  have henergy : gradientEnergy v = b ^ 2 * form laplacianPlus (siteSum π y) := by
    rw [gradientEnergy_eq_form, form_real_smul]
    congr 1
    change pairing u (laplacian *ᵥ u) = pairing (siteSum π y) u
    rw [hLu, pairing_comm]
  have hpair : pairing y f = normSq y + b * form laplacianPlus (siteSum π y) := by
    rw [pairing_add_right, pairing_self_eq_normSq, ← pairing_siteSum]
    change normSq y + pairing (siteSum π y) (fun i => (b : ℂ) * u i) = _
    rw [pairing_real_smul_right]
    rfl
  have hcost : comparisonCost π b f v = comparisonWStar π b y := by
    unfold comparisonCost comparisonWStar
    have hr : (fun x => f x - v (π x)) = y := by funext x; dsimp [f]; ring
    rw [hr, henergy]
    field_simp
  have hp : pairing y f = comparisonWStar π b y := hpair
  refine ⟨f, hp, le_antisymm ?_ ?_⟩
  · exact (comparisonW_le_cost π b hb f v).trans_eq hcost
  · have h := comparison_young π b hb f y hy
    rw [hp] at h
    linarith

theorem comparison_dual_attains {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (y : A → ℂ) (hy : neutral y) :
    ∃ f, 2 * pairing y f - comparisonW π b f = comparisonWStar π b y := by
  obtain ⟨f, hp, hW⟩ := comparison_dual_witness π b hb y hy
  exact ⟨f, by rw [hp, hW]; ring⟩

theorem comparison_dual {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (y : A → ℂ) (hy : neutral y) :
    convexDual (comparisonW π b) y = comparisonWStar π b y := by
  obtain ⟨f, hf⟩ := comparison_dual_attains π b hb y hy
  apply IsGreatest.csSup_eq
  refine ⟨⟨f, hf.symm⟩, ?_⟩
  rintro r ⟨g, rfl⟩
  have h := comparison_young π b hb g y hy
  linarith

theorem normSq_add_real {A : Type*} [Fintype A] (f g : A → ℂ) (t : ℝ) :
    normSq (f + fun i => (t : ℂ) * g i) =
      normSq f + 2 * t * pairing f g + t ^ 2 * normSq g := by
  rw [← pairing_self_eq_normSq, pairing_add_left, pairing_add_right, pairing_add_right,
    pairing_real_smul_left, pairing_real_smul_right, pairing_real_smul_left,
    pairing_real_smul_right, pairing_comm g f, pairing_self_eq_normSq, pairing_self_eq_normSq]
  ring

theorem form_add_real {A : Type*} [Fintype A] [DecidableEq A]
    (M : Matrix A A ℂ) (hH : M.conjTranspose = M) (f g : A → ℂ) (t : ℝ) :
    form M (f + fun i => (t : ℂ) * g i) =
      form M f + 2 * t * pairing g (M *ᵥ f) + t ^ 2 * form M g := by
  have hM : M *ᵥ (fun i => (t : ℂ) * g i) = fun i => (t : ℂ) * (M *ᵥ g) i :=
    Matrix.mulVec_smul M (t : ℂ) g
  unfold form
  rw [Matrix.mulVec_add, hM, pairing_add_left, pairing_add_right, pairing_add_right,
    pairing_real_smul_left, pairing_real_smul_right, pairing_real_smul_left,
    pairing_real_smul_right, pairing_hermitian_symm M hH f g]
  ring

theorem linear_coeff_zero (a B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 ≤ t * a + t ^ 2 * B) : a = 0 := by
  by_contra ha
  have hB1 : B + 1 ≠ 0 := ne_of_gt (by linarith)
  have ht := h (-a / (2 * (B + 1)))
  have hp := mul_nonneg ht (sq_nonneg (2 * (B + 1)))
  have heq : (-a / (2 * (B + 1)) * a + (-a / (2 * (B + 1))) ^ 2 * B)
      * (2 * (B + 1)) ^ 2 = -(a ^ 2 * (B + 2)) := by
    field_simp <;> ring
  rw [heq] at hp
  have ha2 := sq_pos_of_ne_zero ha
  have hB2 : 0 < B + 2 := by linarith
  have := mul_pos ha2 hB2
  linarith

theorem comparisonCost_perturb {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (f : A → ℂ) (v w : Torus d L → ℂ) (t : ℝ) :
    comparisonCost π b f (v + fun i => (t : ℂ) * w i) = comparisonCost π b f v
      + t * (2 * b⁻¹ * pairing w (laplacian *ᵥ v)
        - 2 * pairing (f - fun x => v (π x)) (fun x => w (π x)))
      + t ^ 2 * (normSq (fun x => w (π x)) + b⁻¹ * gradientEnergy w) := by
  have hr : (fun x => f x - (v + fun i => (t : ℂ) * w i) (π x)) =
      (f - fun x => v (π x)) + fun x => ((-t : ℝ) : ℂ) * w (π x) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Complex.ofReal_neg]
    ring
  have hn := normSq_add_real (f - fun x => v (π x)) (fun x => w (π x)) (-t)
  have he := form_add_real laplacian laplacian_hermitian v w t
  simp only [← gradientEnergy_eq_form] at he
  unfold comparisonCost
  rw [hr, hn, he]
  change normSq (f - fun x => v (π x)) + 2 * (-t) * pairing (f - fun x => v (π x)) (fun x => w (π x))
      + (-t) ^ 2 * normSq (fun x => w (π x)) + b⁻¹ * (gradientEnergy v +
        2 * t * pairing w (laplacian *ᵥ v) + t ^ 2 * gradientEnergy w) =
    normSq (f - fun x => v (π x)) + b⁻¹ * gradientEnergy v +
      t * (2 * b⁻¹ * pairing w (laplacian *ᵥ v) - 2 * pairing (f - fun x => v (π x)) (fun x => w (π x))) +
      t ^ 2 * (normSq (fun x => w (π x)) + b⁻¹ * gradientEnergy w)
  ring

/-- Normal equation for any attained minimum. -/
theorem comparison_normal {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) (v : Torus d L → ℂ)
    (hv : ∀ w, comparisonCost π b f v ≤ comparisonCost π b f w) :
    siteSum π (f - fun x => v (π x)) = fun i => ((b⁻¹ : ℝ) : ℂ) * (laplacian *ᵥ v) i := by
  let y := f - fun x => v (π x)
  have hpair : ∀ w : Torus d L → ℂ,
      pairing (siteSum π y) w = b⁻¹ * pairing w (laplacian *ᵥ v) := by
    intro w
    have hpos : 0 ≤ normSq (fun x => w (π x)) + b⁻¹ * gradientEnergy w :=
      add_nonneg (normSq_nonneg _) (mul_nonneg (le_of_lt (inv_pos.mpr hb)) (gradientEnergy_nonneg _))
    have hzero := linear_coeff_zero
      (2 * b⁻¹ * pairing w (laplacian *ᵥ v) - 2 * pairing y (fun x => w (π x)))
      (normSq (fun x => w (π x)) + b⁻¹ * gradientEnergy w) hpos (fun t => by
        have h := hv (v + fun i => (t : ℂ) * w i)
        rw [comparisonCost_perturb] at h
        dsimp only [y]
        linarith)
    rw [pairing_siteSum]
    linarith
  let r := (fun i => ((b⁻¹ : ℝ) : ℂ) * (laplacian *ᵥ v) i) - siteSum π y
  have hz : normSq r = 0 := by
    rw [← pairing_self_eq_normSq]
    change pairing r ((fun i => ((b⁻¹ : ℝ) : ℂ) * (laplacian *ᵥ v) i) - siteSum π y) = 0
    rw [pairing_sub_right, pairing_real_smul_right, pairing_comm r (siteSum π y), hpair]
    ring
  exact (sub_eq_zero.mp ((normSq_eq_zero_iff r).mp hz)).symm

theorem siteSum_sum {A : Type*} [Fintype A] (π : A → Torus d L) (y : A → ℂ) :
    ∑ i, siteSum π y i = ∑ x, y x := by
  unfold siteSum
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The minimum residual attains the primal variational principle. -/
theorem comparison_bidual_witness {A : Type*} [Fintype A] (π : A → Torus d L)
    (b : ℝ) (hb : 0 < b) (f : A → ℂ) :
    ∃ y, neutral y ∧ pairing y f = comparisonW π b f ∧ comparisonWStar π b y = comparisonW π b f := by
  obtain ⟨v, hv, hW, _⟩ := comparison_minimizer π b hb f
  let y := f - fun x => v (π x)
  have heq : siteSum π y = fun i => ((b⁻¹ : ℝ) : ℂ) * (laplacian *ᵥ v) i := comparison_normal π b hb f v hv
  have hn : neutral y := by
    have h := neutral_real_smul (laplacian *ᵥ v)
      (connected_image_neutral laplacian laplacian_connected v) b⁻¹
    rw [← heq] at h
    unfold neutral at *
    rwa [siteSum_sum] at h
  have hX : form laplacianPlus (laplacian *ᵥ v) = gradientEnergy v := by
    have h := bidual_D_attains laplacian laplacian_connected v
    have hp : pairing (laplacian *ᵥ v) v = form laplacian v := pairing_comm _ _
    rw [hp] at h
    simp only [← gradientEnergy_eq_form] at h
    change 2 * gradientEnergy v - form laplacianPlus (laplacian *ᵥ v) = gradientEnergy v at h
    linarith
  have hs : comparisonWStar π b y = comparisonW π b f := by
    unfold comparisonWStar
    rw [heq, form_real_smul, hX, hW]
    change normSq y + b * ((b⁻¹) ^ 2 * gradientEnergy v) = normSq y + b⁻¹ * gradientEnergy v
    field_simp <;> ring
  have hp : pairing y f = comparisonW π b f := by
    have hf : f = y + fun x => v (π x) := by dsimp [y]; abel
    calc pairing y f = pairing y (y + fun x => v (π x)) := congrArg (pairing y) hf
      _ = normSq y + b⁻¹ * gradientEnergy v := by
        rw [pairing_add_right, pairing_self_eq_normSq, ← pairing_siteSum, heq, pairing_real_smul_left,
          pairing_comm (laplacian *ᵥ v) v]
        change normSq y + b⁻¹ * form laplacian v = _
        rw [gradientEnergy_eq_form]
      _ = comparisonW π b f := hW.symm
  exact ⟨y, hn, hp, hs⟩

end AndersonAC.S3H

namespace AndersonAC.S3
open AndersonAC.S3H
variable {d L : ℕ} [NeZero L]

theorem dual_comparison_forms_proof (hL : 4 ≤ L) {A : Type*} [Fintype A]
    (π : A → Torus d L) (b : ℝ) (hb : 0 < b) :
    (∀ f, ∃ v, comparisonW π b f = comparisonCost π b f v) ∧
    (∀ f c, comparisonW π b (fun x => f x + c) = comparisonW π b f) ∧
    (∀ f, 0 ≤ comparisonW π b f ∧
      (comparisonW π b f = 0 ↔ ∃ c : ℂ, f = fun _ => c)) ∧
    (∀ f g, comparisonW π b (f + g) + comparisonW π b (f - g) =
      2 * comparisonW π b f + 2 * comparisonW π b g) ∧
    (∀ (f : A → ℂ) (z : ℂ), comparisonW π b (z • f) = ‖z‖ ^ 2 * comparisonW π b f) ∧
    (∀ y, neutral y → convexDual (comparisonW π b) y = comparisonWStar π b y) := by
  exact ⟨fun f => by obtain ⟨v, _, h, _⟩ := comparison_minimizer π b hb f; exact ⟨v, h⟩,
    comparisonW_shift π b hb, comparisonW_nonneg_kernel π b hb,
    comparisonW_parallelogram π b hb, comparisonW_smul π b hb, comparison_dual π b hb⟩

/-- Scalar algebra used in reversing the two quadratic comparisons. -/
private theorem reverse_lower (q a B x : ℝ) (hq : 0 < q)
    (h : 2 * q⁻¹ * a ≤ B + q⁻¹ ^ 2 * x) (hx : x ≤ q * a) : q⁻¹ * a ≤ B := by
  have heq : q⁻¹ ^ 2 * q = q⁻¹ := by field_simp <;> ring
  have hx' : q⁻¹ ^ 2 * x ≤ q⁻¹ * a := by
    calc q⁻¹ ^ 2 * x ≤ q⁻¹ ^ 2 * (q * a) := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ = q⁻¹ * a := by rw [← mul_assoc, heq]
  linarith

private theorem reverse_upper (q a B z : ℝ) (hq : 0 < q)
    (h : 2 * q⁻¹ * a ≤ q⁻¹ ^ 2 * B + z) (hz : q * z ≤ a) : a ≤ q⁻¹ * B := by
  have hz' : z ≤ q⁻¹ * a := (le_inv_mul_iff₀ hq).mpr hz
  have hmid : q⁻¹ * a ≤ q⁻¹ ^ 2 * B := by linarith
  calc a = q * (q⁻¹ * a) := by field_simp
    _ ≤ q * (q⁻¹ ^ 2 * B) := mul_le_mul_of_nonneg_left hmid (le_of_lt hq)
    _ = q⁻¹ * B := by field_simp <;> ring

theorem dual_comparison_order_proof (hL : 4 ≤ L) {A : Type*} [Fintype A] [DecidableEq A]
    (π : A → Torus d L) (b c C : ℝ) (hb : 0 < b) (hc : 0 < c) (hC : 0 < C)
    (D : Matrix A A ℂ) (hD : connectedLaplacian D) :
    (∀ y, neutral y → c * comparisonWStar π b y ≤ form (inverseOnConstants D) y ∧
      form (inverseOnConstants D) y ≤ C * comparisonWStar π b y) ↔
    (∀ f, C⁻¹ * comparisonW π b f ≤ form D f ∧
      form D f ≤ c⁻¹ * comparisonW π b f) := by
  classical
  rcases isEmpty_or_nonempty A with hempty | hne
  · haveI := hempty
    have hW : ∀ f : A → ℂ, comparisonW π b f = 0 := fun f =>
      (comparisonW_nonneg_kernel π b hb f).2.mpr ⟨0, by ext x; exact isEmptyElim x⟩
    simp [hW, comparisonWStar, normSq, form, pairing, siteSum]
  · haveI := hne
    constructor
    · intro h f
      constructor
      · obtain ⟨y, hy, hp, hs⟩ := comparison_bidual_witness π b hb f
        have hx := (h y hy).2
        rw [hs] at hx
        have hY := young_D_X D hD f (fun i => ((C⁻¹ : ℝ) : ℂ) * y i) (neutral_real_smul y hy C⁻¹)
        rw [pairing_real_smul_left, form_real_smul, hp] at hY
        exact reverse_lower C (comparisonW π b f) (form D f) (form (inverseOnConstants D) y) hC (by nlinarith [hY]) hx
      · let y := D *ᵥ f
        have hy := connected_image_neutral D hD f
        have hX : form (inverseOnConstants D) y = form D f := by
          have ht := bidual_D_attains D hD f
          have hp : pairing (D *ᵥ f) f = form D f := pairing_comm _ _
          rw [hp] at ht
          dsimp only [y]
          linarith
        have hx := (h y hy).1
        rw [hX] at hx
        have hY := comparison_young π b hb (fun i => ((c⁻¹ : ℝ) : ℂ) * f i) y hy
        rw [pairing_real_smul_right] at hY
        have hscale : comparisonW π b (fun i => ((c⁻¹ : ℝ) : ℂ) * f i) = c⁻¹ ^ 2 * comparisonW π b f := by
          have ht := comparisonW_smul π b hb f ((c⁻¹ : ℝ) : ℂ)
          simpa only [Pi.smul_def, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hc)] using ht
        have hp : pairing y f = form D f := pairing_comm _ _
        rw [hscale, hp] at hY
        exact reverse_upper c (form D f) (comparisonW π b f) (comparisonWStar π b y) hc (by nlinarith [hY]) hx
    · intro h y hy
      constructor
      · obtain ⟨f, hp, hs⟩ := comparison_dual_witness π b hb y hy
        have hDupper := (h f).2
        rw [hs] at hDupper
        have hY := young_D_X D hD (fun i => (c : ℂ) * f i) y hy
        rw [pairing_real_smul_right, form_real_smul, hp] at hY
        have hbound : c ^ 2 * form D f ≤ c * comparisonWStar π b y := by
          calc c ^ 2 * form D f ≤ c ^ 2 * (c⁻¹ * comparisonWStar π b y) :=
              mul_le_mul_of_nonneg_left hDupper (sq_nonneg c)
            _ = c * comparisonWStar π b y := by field_simp <;> ring
        linarith
      · let f := inverseOnConstants D *ᵥ y
        have hDf : form D f = form (inverseOnConstants D) y := by
          change pairing f (D *ᵥ f) = pairing y f
          rw [pseudoinv_mulVec D hD y hy, pairing_comm]
        have hp : pairing y f = form (inverseOnConstants D) y := rfl
        have hDlower := (h f).1
        rw [hDf] at hDlower
        have hW : comparisonW π b f ≤ C * form (inverseOnConstants D) y :=
          (inv_mul_le_iff₀ hC).mp hDlower
        have hY := comparison_young π b hb (fun i => ((C⁻¹ : ℝ) : ℂ) * f i) y hy
        rw [pairing_real_smul_right, hp] at hY
        have hscale : comparisonW π b (fun i => ((C⁻¹ : ℝ) : ℂ) * f i) = C⁻¹ ^ 2 * comparisonW π b f := by
          have ht := comparisonW_smul π b hb f ((C⁻¹ : ℝ) : ℂ)
          simpa only [Pi.smul_def, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hC)] using ht
        rw [hscale] at hY
        apply (inv_mul_le_iff₀ hC).mp
        exact reverse_lower C (form (inverseOnConstants D) y) (comparisonWStar π b y)
          (comparisonW π b f) hC (by nlinarith [hY]) hW

end AndersonAC.S3
