import AndersonAC.S45.Definitions
import AndersonAC.S45.HelperStatements2
import AndersonAC.S45.OverlapLemmas
import AndersonAC.S45.LaplacianShift
import AndersonAC.S45.LocalTransferProof

/-! Energy-form part of the local-transfer estimate (Lemma 5.5). -/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace AndersonAC.AgentS45

open AndersonAC.S45

theorem real_sq_norm_mulVec_le {P : Type*} [Fintype P] [DecidableEq P]
    (M : RMat P) (x : P → ℝ) :
    (∑ i, ‖(M *ᵥ x) i‖ ^ 2) ≤ ‖M‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec M ((WithLp.equiv 2 (P → ℝ)).symm x)
  have e1 : ∀ y : P → ℝ, ‖(WithLp.equiv 2 (P → ℝ)).symm y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
    intro y
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have h2 : ‖(WithLp.equiv 2 (P → ℝ)).symm (M *ᵥ x)‖ ≤
      ‖M‖ * ‖(WithLp.equiv 2 (P → ℝ)).symm x‖ := by
    simpa using h
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, e1, e1] at h3
  exact h3

theorem qform_abs_le_opNorm {P : Type*} [Fintype P] [DecidableEq P]
    (M : RMat P) (x : P → ℝ) : |qform M x| ≤ ‖M‖ * l2sq x := by
  have hx : 0 ≤ l2sq x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (M *ᵥ x)
  have hcs : (qform M x) ^ 2 ≤ l2sq x * l2sq (M *ᵥ x) := by
    simpa [qform, l2sq, Matrix.mulVec, dotProduct, Real.norm_eq_abs, sq_abs] using hcs0
  have hm := real_sq_norm_mulVec_le M x
  have hsq : (qform M x) ^ 2 ≤ ‖M‖ ^ 2 * (l2sq x) ^ 2 := by
    calc (qform M x) ^ 2 ≤ l2sq x * l2sq (M *ᵥ x) := hcs
      _ ≤ l2sq x * (‖M‖ ^ 2 * l2sq x) := mul_le_mul_of_nonneg_left hm hx
      _ = ‖M‖ ^ 2 * (l2sq x) ^ 2 := by ring
  have hn : 0 ≤ ‖M‖ * l2sq x := mul_nonneg (norm_nonneg _) hx
  have ha : |qform M x| ^ 2 = (qform M x) ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|qform M x| - ‖M‖ * l2sq x)]

theorem qform_pullback {P H : Type*} [Fintype P] [Fintype H]
    (B : Matrix P H ℝ) (L : RMat P) (w : H → ℝ) :
    qform (pullback B L) w = qform L (B *ᵥ w) := by
  change dotProduct w ((Bᵀ * L * B) *ᵥ w) = dotProduct (B *ᵥ w) (L *ᵥ (B *ᵥ w))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp [Matrix.vecMul_transpose]

theorem qform_shift_of_row_sum {P : Type*} [Fintype P] [DecidableEq P]
    (M : RMat P) (hM : M.IsSymm) (hrow : ∀ i, ∑ j, M i j = 0)
    (f : P → ℝ) (a : ℝ) :
    qform M (fun i => f i + a) = qform M f := by
  have hcol : ∀ j, ∑ i, M i j = 0 := by
    intro j
    calc ∑ i, M i j = ∑ i, M j i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have h := congrFun (congrFun hM i) j
          simpa [Matrix.transpose_apply] using h.symm
      _ = 0 := hrow j
  have hMv : M *ᵥ (fun i => f i + a) = M *ᵥ f := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    calc ∑ j, M i j * (f j + a) = ∑ j, (M i j * f j + M i j * a) := by
          congr 1
          funext j
          ring
      _ = ∑ j, M i j * f j + a * ∑ j, M i j := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          ring
      _ = ∑ j, M i j * f j := by rw [hrow i, mul_zero, add_zero]
  have hsum : ∑ i, (M *ᵥ f) i = 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, M i j * f j = ∑ j, (∑ i, M i j) * f j := by
          congr 1
          funext j
          rw [Finset.sum_mul]
      _ = 0 := by simp [hcol]
  unfold qform
  rw [hMv]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero]

theorem qform_laplacian_sub_const {P : Type*} [Fintype P] [DecidableEq P]
    (edge : RMat P) (hedge : edge.IsSymm) (f : P → ℝ) (a : ℝ) :
    qform (laplacian edge) (fun i => f i - a) = qform (laplacian edge) f := by
  simpa [sub_eq_add_neg] using qform_laplacian_shift edge hedge f (-a)

theorem qform_eq_neg_half_diff_sum {P : Type*} [Fintype P] [DecidableEq P]
    (M : RMat P) (hM : M.IsSymm) (hrow : ∀ i, ∑ j, M i j = 0) (f : P → ℝ) :
    qform M f = -(1 / 2 : ℝ) * ∑ i, ∑ j, M i j * (f i - f j) ^ 2 := by
  classical
  have hcol : ∀ j, ∑ i, M i j = 0 := by
    intro j
    calc ∑ i, M i j = ∑ i, M j i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have h := congrFun (congrFun hM i) j
          simpa [Matrix.transpose_apply] using h.symm
      _ = 0 := hrow j
  have hA : ∑ i, ∑ j, M i j * (f i) ^ 2 = ∑ i, (f i) ^ 2 * ∑ j, M i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ j, M i j * (f i) ^ 2 = (∑ j, M i j) * (f i) ^ 2 := by rw [Finset.sum_mul]
      _ = (f i) ^ 2 * ∑ j, M i j := by ring
  have hC : ∑ i, ∑ j, M i j * (f j) ^ 2 = ∑ j, (f j) ^ 2 * ∑ i, M i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc ∑ i, M i j * (f j) ^ 2 = (∑ i, M i j) * (f j) ^ 2 := by rw [Finset.sum_mul]
      _ = (f j) ^ 2 * ∑ i, M i j := by ring
  have hcross : ∑ i, ∑ j, M i j * f i * f j = qform M f := by
    unfold qform
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ j, M i j * f i * f j = ∑ j, (M i j * f j) * f i := by
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = (∑ j, M i j * f j) * f i := by rw [Finset.sum_mul]
      _ = f i * ∑ j, M i j * f j := by ring
  have hlin :
      (∑ i, ∑ j, M i j * (f i - f j) ^ 2) =
        (∑ i, ∑ j, M i j * (f i) ^ 2) -
          2 * (∑ i, ∑ j, M i j * f i * f j) +
          (∑ i, ∑ j, M i j * (f j) ^ 2) := by
    calc
      _ = ∑ i, ∑ j,
            (M i j * (f i) ^ 2 - 2 * (M i j * f i * f j) + M i j * (f j) ^ 2) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
      _ = ∑ i, ((∑ j, M i j * (f i) ^ 2) -
            2 * (∑ j, M i j * f i * f j) + (∑ j, M i j * (f j) ^ 2)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = _ := by
              simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hA, hcross, hC] at hlin
  simp only [hrow, hcol, mul_zero, Finset.sum_const_zero, zero_sub] at hlin
  nlinarith [hlin]

theorem qform_sum {P T : Type*} [Fintype P] [Fintype T] [DecidableEq P]
    (M : T → RMat P) (f : P → ℝ) :
    qform (∑ t, M t) f = ∑ t, qform (M t) f := by
  classical
  simp only [qform, Matrix.mulVec, dotProduct, Matrix.sum_apply]
  have hInner (i : P) :
      ∑ j, (∑ t, M t i j) * f j = ∑ t, ∑ j, M t i j * f j := by
    calc
      ∑ j, (∑ t, M t i j) * f j = ∑ j, ∑ t, M t i j * f j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
      _ = ∑ t, ∑ j, M t i j * f j := Finset.sum_comm
  calc
    _ = ∑ i, f i * ∑ t, ∑ j, M t i j * f j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hInner]
    _ = ∑ i, ∑ t, f i * ∑ j, M t i j * f j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    _ = ∑ t, ∑ i, f i * ∑ j, M t i j * f j := Finset.sum_comm

theorem qform_finset_sum {P : Type*} [Fintype P] [DecidableEq P]
    (K : Finset ℕ) (M : ℕ → RMat P) (f : P → ℝ) :
    qform (∑ k ∈ K, M k) f = ∑ k ∈ K, qform (M k) f := by
  classical
  calc
    qform (∑ k ∈ K, M k) f = qform (∑ k : K, M k.1) f := by
      congr 1
      exact (Finset.sum_coe_sort K M).symm
    _ = ∑ k : K, qform (M k.1) f := qform_sum (fun k : K => M k.1) f
    _ = ∑ k ∈ K, qform (M k) f := Finset.sum_coe_sort K (fun k => qform (M k) f)

theorem qform_difference_abs_le_masked {P : Type*} [Fintype P] [DecidableEq P]
    (M : RMat P) (hM : M.IsSymm) (hrow : ∀ i, ∑ j, M i j = 0)
    (f g : P → ℝ) (S : Finset P)
    (hagree : ∀ i ∈ S, ∀ j ∈ S, f i - f j = g i - g j) :
    |qform M f - qform M g| ≤ (1 / 2 : ℝ) *
      ∑ i, ∑ j, if i ∈ S ∧ j ∈ S then 0 else
        |M i j| * ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
  have hform : qform M f - qform M g = -(1 / 2 : ℝ) *
      ∑ i, ∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2) := by
    have hsum :
        (∑ i, ∑ j, M i j * (f i - f j) ^ 2) -
            (∑ i, ∑ j, M i j * (g i - g j) ^ 2) =
          ∑ i, ∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [qform_eq_neg_half_diff_sum M hM hrow f, qform_eq_neg_half_diff_sum M hM hrow g]
    rw [← hsum]
    ring
  have hsum :
      |∑ i, ∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| ≤
        ∑ i, ∑ j, if i ∈ S ∧ j ∈ S then 0 else
          |M i j| * ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
    calc
          |∑ i, ∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)|
          ≤ ∑ i, |∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| := by
            calc
              |∑ i, ∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| =
                  ‖∑ i, ∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)‖ := by
                    rw [Real.norm_eq_abs]
              _ ≤ ∑ i, ‖∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)‖ := norm_sum_le _ _
              _ = ∑ i, |∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| := by
                    simp [Real.norm_eq_abs]
      _ ≤ ∑ i, ∑ j, if i ∈ S ∧ j ∈ S then 0 else
            |M i j| * ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc
            |∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)|
                ≤ ∑ j, |M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| := by
                  calc
                    |∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| =
                        ‖∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)‖ := by
                          rw [Real.norm_eq_abs]
                    _ ≤ ∑ j, ‖M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)‖ := norm_sum_le _ _
                    _ = ∑ j, |M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| := by
                          simp [Real.norm_eq_abs]
            _ ≤ ∑ j, if i ∈ S ∧ j ∈ S then 0 else
                  |M i j| * ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
                refine Finset.sum_le_sum fun j _ => ?_
                by_cases hp : i ∈ S ∧ j ∈ S
                · have hd := hagree i hp.1 j hp.2
                  simp [hp, hd]
                · simp only [if_neg hp]
                  calc
                    |M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| =
                        |M i j| * |(f i - f j) ^ 2 - (g i - g j) ^ 2| := abs_mul _ _
                    _ ≤ |M i j| * (|(f i - f j) ^ 2| + |(g i - g j) ^ 2|) :=
                      mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
                    _ = |M i j| * ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
                      rw [abs_of_nonneg (sq_nonneg (f i - f j)),
                        abs_of_nonneg (sq_nonneg (g i - g j))]
  calc
    |qform M f - qform M g| = (1 / 2 : ℝ) *
        |∑ i, ∑ j, M i j * ((f i - f j) ^ 2 - (g i - g j) ^ 2)| := by
          rw [hform, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

theorem exp_buffer_factor {P : Type*} [Fintype P] {d : ℕ} {C : ℝ}
    (dist : P → P → ℝ) (shell : ShellBounds (P := P) d C dist)
    (u R : ℝ) (hu : 0 < u) (i j x : P)
    (hbuf : R ≤ dist i x + dist j x) :
    Real.exp (-(2 * u) * (dist i x + dist j x)) ≤
      Real.exp (-u * R) * Real.exp (-(u / 2) * dist i j) *
        Real.exp (-(u / 2) * dist i x) := by
  have htri : dist i j ≤ dist i x + dist j x := by
    calc dist i j ≤ dist i x + dist x j := shell.triangle i x j
      _ = dist i x + dist j x := congrArg (fun y => dist i x + y) (shell.symmetric x j)
  have hix : 0 ≤ dist i x := shell.nonneg i x
  have hixle : dist i x ≤ dist i x + dist j x := by linarith [shell.nonneg j x]
  have hexponent : -(2 * u) * (dist i x + dist j x) ≤
      -u * R - (u / 2) * dist i j - (u / 2) * dist i x := by
    have hR := mul_le_mul_of_nonneg_left hbuf (le_of_lt hu)
    have hD := mul_le_mul_of_nonneg_left htri (le_of_lt (by positivity : 0 < u / 2))
    have hI := mul_le_mul_of_nonneg_left hixle (le_of_lt (by positivity : 0 < u / 2))
    have huv : u = 2 * (u / 2) := by ring
    nlinarith
  calc
    Real.exp (-(2 * u) * (dist i x + dist j x)) ≤
        Real.exp (-u * R - (u / 2) * dist i j - (u / 2) * dist i x) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-u * R) * Real.exp (-(u / 2) * dist i j) *
        Real.exp (-(u / 2) * dist i x) := by
      rw [show -u * R - (u / 2) * dist i j - (u / 2) * dist i x =
        (-u * R - (u / 2) * dist i j) + (-(u / 2) * dist i x) by ring,
        Real.exp_add]
      rw [show -u * R - (u / 2) * dist i j =
        (-u * R) + (-(u / 2) * dist i j) by ring, Real.exp_add]

theorem step_tail_weighted {P : Type*} [Fintype P] [DecidableEq P]
    {d : ℕ} {C : ℝ} (dist : P → P → ℝ) (shell : ShellBounds d C dist)
    (M : RMat P) (hM : M.IsSymm) (hrow : ∀ i, ∑ j, M i j = 0)
    (f g : P → ℝ) (S : Finset P)
    (hagree : ∀ i ∈ S, ∀ j ∈ S, f i - f j = g i - g j)
    (A u R : ℝ) (hA : 0 ≤ A) (hu : 0 < u) (x : P)
    (hbuf : ∀ i j, (i ∉ S ∨ j ∉ S) → R ≤ dist i x + dist j x)
    (htail : ∀ i j, i ≠ j → |M i j| ≤ A *
      Real.exp (-(2 * u) * (dist i x + dist j x))) :
    |qform M f - qform M g| ≤ A * Real.exp (-u * R) *
      ((1 / 2 : ℝ) * ∑ i, ∑ j,
        Real.exp (-(u / 2) * dist i j) * Real.exp (-(u / 2) * dist i x) *
          ((f i - f j) ^ 2 + (g i - g j) ^ 2)) := by
  have hpoint (i j : P) :
      (if i ∈ S ∧ j ∈ S then 0 else |M i j| *
        ((f i - f j) ^ 2 + (g i - g j) ^ 2)) ≤
      A * Real.exp (-u * R) * Real.exp (-(u / 2) * dist i j) *
        Real.exp (-(u / 2) * dist i x) *
        ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · simp [hi, hj]
        positivity
      · have hsep : R ≤ dist i x + dist j x := hbuf i j (Or.inr hj)
        by_cases hij : i = j
        · subst j
          exact False.elim (hj hi)
        · have ht := htail i j hij
          have he := exp_buffer_factor dist shell u R hu i j x hsep
          have hD : 0 ≤ (f i - f j) ^ 2 + (g i - g j) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
          have hnot : ¬ (i ∈ S ∧ j ∈ S) := fun hp => hj hp.2
          rw [if_neg hnot]
          calc
            |M i j| * ((f i - f j) ^ 2 + (g i - g j) ^ 2) ≤
                (A * Real.exp (-(2 * u) * (dist i x + dist j x))) *
                  ((f i - f j) ^ 2 + (g i - g j) ^ 2) :=
              mul_le_mul_of_nonneg_right ht hD
            _ ≤ (A * (Real.exp (-u * R) * Real.exp (-(u / 2) * dist i j) *
                  Real.exp (-(u / 2) * dist i x))) *
                  ((f i - f j) ^ 2 + (g i - g j) ^ 2) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left he hA) hD
            _ = _ := by ring
    · have hsep : R ≤ dist i x + dist j x := hbuf i j (Or.inl hi)
      by_cases hij : i = j
      · subst j
        simp
      · have ht := htail i j hij
        have he := exp_buffer_factor dist shell u R hu i j x hsep
        have hD : 0 ≤ (f i - f j) ^ 2 + (g i - g j) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
        have hnot : ¬ (i ∈ S ∧ j ∈ S) := fun hp => hi hp.1
        rw [if_neg hnot]
        calc
          |M i j| * ((f i - f j) ^ 2 + (g i - g j) ^ 2) ≤
              (A * Real.exp (-(2 * u) * (dist i x + dist j x))) *
                ((f i - f j) ^ 2 + (g i - g j) ^ 2) :=
            mul_le_mul_of_nonneg_right ht hD
          _ ≤ (A * (Real.exp (-u * R) * Real.exp (-(u / 2) * dist i j) *
                Real.exp (-(u / 2) * dist i x))) *
                ((f i - f j) ^ 2 + (g i - g j) ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left he hA) hD
          _ = _ := by ring
  have hsum :
      (∑ i : P, ∑ j : P, (if i ∈ S ∧ j ∈ S then (0 : ℝ) else |M i j| *
          ((f i - f j) ^ 2 + (g i - g j) ^ 2))) ≤
        A * Real.exp (-u * R) * ∑ i : P, ∑ j : P,
          Real.exp (-(u / 2) * dist i j) * Real.exp (-(u / 2) * dist i x) *
            ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
    calc
      _ ≤ ∑ i, ∑ j, A * Real.exp (-u * R) * Real.exp (-(u / 2) * dist i j) *
          Real.exp (-(u / 2) * dist i x) *
          ((f i - f j) ^ 2 + (g i - g j) ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
      _ = _ := by
        have hfactor : ∀ i j,
            A * Real.exp (-u * R) * Real.exp (-(u / 2) * dist i j) *
                Real.exp (-(u / 2) * dist i x) *
                ((f i - f j) ^ 2 + (g i - g j) ^ 2) =
              (A * Real.exp (-u * R)) *
                (Real.exp (-(u / 2) * dist i j) * Real.exp (-(u / 2) * dist i x) *
                  ((f i - f j) ^ 2 + (g i - g j) ^ 2)) := by
          intro i j
          ring
        simp_rw [hfactor]
        calc
          ∑ i, ∑ j, (A * Real.exp (-u * R)) *
              (Real.exp (-(u / 2) * dist i j) * Real.exp (-(u / 2) * dist i x) *
                ((f i - f j) ^ 2 + (g i - g j) ^ 2)) =
              ∑ i, (A * Real.exp (-u * R)) * ∑ j,
                Real.exp (-(u / 2) * dist i j) * Real.exp (-(u / 2) * dist i x) *
                  ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum]
          _ = A * Real.exp (-u * R) * ∑ i, ∑ j,
              Real.exp (-(u / 2) * dist i j) * Real.exp (-(u / 2) * dist i x) *
                ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by rw [← Finset.mul_sum]
  calc
    |qform M f - qform M g| ≤ (1 / 2 : ℝ) *
        ∑ i, ∑ j, if i ∈ S ∧ j ∈ S then 0 else |M i j| *
          ((f i - f j) ^ 2 + (g i - g j) ^ 2) :=
      qform_difference_abs_le_masked M hM hrow f g S hagree
    _ ≤ (1 / 2 : ℝ) * (A * Real.exp (-u * R) * ∑ i, ∑ j,
          Real.exp (-(u / 2) * dist i j) * Real.exp (-(u / 2) * dist i x) *
            ((f i - f j) ^ 2 + (g i - g j) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

def graphEnergy {P : Type*} [Fintype P] (dist : P → P → ℝ) (u : ℝ)
    (f : P → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, Real.exp (-u * dist i j) * (f i - f j) ^ 2

def weightedGraphEnergy {P : Type*} [Fintype P] (dist : P → P → ℝ) (u : ℝ)
    (x : P) (f : P → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j,
    Real.exp (-u * dist i j) * Real.exp (-u * dist i x) * (f i - f j) ^ 2

theorem weightedGraphEnergy_add {P : Type*} [Fintype P]
    (dist : P → P → ℝ) (u : ℝ) (x : P) (f g : P → ℝ) :
    weightedGraphEnergy dist u x f + weightedGraphEnergy dist u x g =
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        Real.exp (-u * dist i j) * Real.exp (-u * dist i x) *
          ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
  unfold weightedGraphEnergy
  have hsum :
      (∑ i, ∑ j, Real.exp (-u * dist i j) * Real.exp (-u * dist i x) *
          (f i - f j) ^ 2) +
        (∑ i, ∑ j, Real.exp (-u * dist i j) * Real.exp (-u * dist i x) *
          (g i - g j) ^ 2) =
      ∑ i, ∑ j, Real.exp (-u * dist i j) * Real.exp (-u * dist i x) *
        ((f i - f j) ^ 2 + (g i - g j) ^ 2) := by
    calc
      _ = ∑ i, ((∑ j, Real.exp (-u * dist i j) * Real.exp (-u * dist i x) *
            (f i - f j) ^ 2) +
          ∑ j, Real.exp (-u * dist i j) * Real.exp (-u * dist i x) *
            (g i - g j) ^ 2) := by rw [← Finset.sum_add_distrib]
      _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
  rw [← hsum]
  ring

theorem pivot_weighted_graph_sum_le {P : Type*} [Fintype P]
    {d : ℕ} {C : ℝ} (dist : P → P → ℝ) (shell : ShellBounds d C dist)
    (len : ℕ) (pv : ℕ → Option P)
    (hinj : ∀ k l, k < len → l < len → ∀ x, pv k = some x → pv l = some x → k = l)
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (f : P → ℝ) :
    (∑ k ∈ Finset.range len, (pv k).elim 0 (fun x => weightedGraphEnergy dist u x f)) ≤
      (C * power u (-(d : ℝ))) * graphEnergy dist u f := by
  classical
  have hpoint (k : ℕ) :
      (pv k).elim 0 (fun x => weightedGraphEnergy dist u x f) =
        (1 / 2 : ℝ) * ∑ i, ∑ j,
          Real.exp (-u * dist i j) * (f i - f j) ^ 2 *
            (pv k).elim 0 (fun x => Real.exp (-u * dist i x)) := by
    cases hpv : pv k with
    | none => simp [hpv, weightedGraphEnergy]
    | some x =>
      simp [hpv, weightedGraphEnergy, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  have hPivot (i : P) :
      (∑ k ∈ Finset.range len, (pv k).elim 0 (fun x => Real.exp (-u * dist i x))) ≤
        C * power u (-(d : ℝ)) := by
    calc
      _ ≤ ∑ x, Real.exp (-u * dist i x) :=
        pivot_sum len pv hinj _ (fun x => (Real.exp_pos _).le)
      _ ≤ C * power u (-(d : ℝ)) := shell.count u hu hu1 i
  calc
    (∑ k ∈ Finset.range len, (pv k).elim 0 (fun x => weightedGraphEnergy dist u x f))
        = (1 / 2 : ℝ) * ∑ k ∈ Finset.range len, ∑ i, ∑ j,
            Real.exp (-u * dist i j) * (f i - f j) ^ 2 *
              (pv k).elim 0 (fun x => Real.exp (-u * dist i x)) := by
          simp_rw [hpoint]
          rw [← Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j,
          Real.exp (-u * dist i j) * (f i - f j) ^ 2 *
            ∑ k ∈ Finset.range len, (pv k).elim 0 (fun x => Real.exp (-u * dist i x)) := by
          congr 1
          calc
            (∑ k ∈ Finset.range len, ∑ i, ∑ j,
                Real.exp (-u * dist i j) * (f i - f j) ^ 2 *
                  (pv k).elim 0 (fun x => Real.exp (-u * dist i x)))
                = ∑ i, ∑ k ∈ Finset.range len, ∑ j,
                    Real.exp (-u * dist i j) * (f i - f j) ^ 2 *
                      (pv k).elim 0 (fun x => Real.exp (-u * dist i x)) := by
                    rw [Finset.sum_comm]
            _ = ∑ i, ∑ j, ∑ k ∈ Finset.range len,
                    Real.exp (-u * dist i j) * (f i - f j) ^ 2 *
                      (pv k).elim 0 (fun x => Real.exp (-u * dist i x)) := by
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_comm]
            _ = ∑ i, ∑ j,
                  Real.exp (-u * dist i j) * (f i - f j) ^ 2 *
                    ∑ k ∈ Finset.range len, (pv k).elim 0 (fun x => Real.exp (-u * dist i x)) := by
                    refine Finset.sum_congr rfl fun i _ => ?_
                    refine Finset.sum_congr rfl fun j _ => ?_
                    rw [← Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) * ∑ i, ∑ j,
          Real.exp (-u * dist i j) * (f i - f j) ^ 2 * (C * power u (-(d : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (hPivot i)
            (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    _ = (C * power u (-(d : ℝ))) * graphEnergy dist u f := by
          simp [graphEnergy, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem local_coordinates_B_mulVec {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b : ℝ) (h : ℕ)
    (a : LocalCoordinates Q b h) (w : Fin h → ℝ) :
    a.B *ᵥ w = Q.extend (fun i => (a.alpha *ᵥ w) i) (fun i => (a.potential *ᵥ w) i) := by
  classical
  funext x
  by_cases hx : x ∈ Q.ports
  · simp [LocalCoordinates.B, LocalCube.extend, Matrix.mulVec, dotProduct, hx]
    have hmean :
        (∑ j, (Q.cutoff (Q.site x) * ∑ i : Q.outer, a.potential i j) *
            (Q.outer.card : ℝ)⁻¹ * w j) =
          Q.cutoff (Q.site x) * (Q.outer.card : ℝ)⁻¹ *
            ∑ i : Q.outer, ∑ j, a.potential i j * w j := by
      calc
        _ = Q.cutoff (Q.site x) *
              ∑ j, ((∑ i : Q.outer, a.potential i j) * (Q.outer.card : ℝ)⁻¹ * w j) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => ?_
                ring
        _ = Q.cutoff (Q.site x) *
              ∑ j, ((∑ i : Q.outer, a.potential i j * w j) * (Q.outer.card : ℝ)⁻¹) := by
                congr 1
                refine Finset.sum_congr rfl fun j _ => ?_
                calc
                  (∑ i : Q.outer, a.potential i j) * (Q.outer.card : ℝ)⁻¹ * w j =
                      ((∑ i : Q.outer, a.potential i j) * w j) * (Q.outer.card : ℝ)⁻¹ := by ring
                  _ = (∑ i : Q.outer, a.potential i j * w j) * (Q.outer.card : ℝ)⁻¹ := by
                      rw [Finset.sum_mul]
        _ = Q.cutoff (Q.site x) *
              ((∑ j, ∑ i : Q.outer, a.potential i j * w j) * (Q.outer.card : ℝ)⁻¹) := by
                rw [Finset.sum_mul]
        _ = Q.cutoff (Q.site x) *
              ((∑ i : Q.outer, ∑ j, a.potential i j * w j) * (Q.outer.card : ℝ)⁻¹) := by
                congr 2
                rw [Finset.sum_comm]
        _ = Q.cutoff (Q.site x) * (Q.outer.card : ℝ)⁻¹ *
              ∑ i : Q.outer, ∑ j, a.potential i j * w j := by ring
    have hExpand :
        (∑ j, (Q.cutoff (Q.site x) *
          (a.alpha ⟨x, hx⟩ j +
            a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j -
            (∑ i : Q.outer, a.potential i j) / Q.outer.card) * w j)) =
          (∑ j, Q.cutoff (Q.site x) * a.alpha ⟨x, hx⟩ j * w j) +
          (∑ j, Q.cutoff (Q.site x) * a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * w j) -
          (∑ j, Q.cutoff (Q.site x) * ((∑ i : Q.outer, a.potential i j) / Q.outer.card) * w j) := by
      calc
        _ = ∑ j, (Q.cutoff (Q.site x) * a.alpha ⟨x, hx⟩ j * w j +
            Q.cutoff (Q.site x) * a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * w j -
            Q.cutoff (Q.site x) * ((∑ i : Q.outer, a.potential i j) / Q.outer.card) * w j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hmeanDiv :
        (∑ j, Q.cutoff (Q.site x) * ((∑ i : Q.outer, a.potential i j) / Q.outer.card) * w j) =
          Q.cutoff (Q.site x) / Q.outer.card *
            ∑ i : Q.outer, ∑ j, a.potential i j * w j := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmean
    have hAlpha :
        (∑ j, Q.cutoff (Q.site x) * a.alpha ⟨x, hx⟩ j * w j) =
          Q.cutoff (Q.site x) * ∑ j, a.alpha ⟨x, hx⟩ j * w j := by
      calc
        _ = ∑ j, Q.cutoff (Q.site x) * (a.alpha ⟨x, hx⟩ j * w j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
        _ = _ := by rw [Finset.mul_sum]
    have hPotential :
        (∑ j, Q.cutoff (Q.site x) * a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * w j) =
          Q.cutoff (Q.site x) * ∑ j, a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * w j := by
      calc
        _ = ∑ j, Q.cutoff (Q.site x) *
              (a.potential ⟨Q.site x, (Finset.mem_filter.mp hx).2⟩ j * w j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
        _ = _ := by rw [Finset.mul_sum]
    have hattach :
        (∑ i : Q.outer, ∑ j, a.potential i j * w j) =
          ∑ i ∈ Q.outer.attach, ∑ j, a.potential i j * w j := by
      let F : I → ℝ := fun i => if hi : i ∈ Q.outer then
        ∑ j, a.potential ⟨i, hi⟩ j * w j else 0
      have h1 : (∑ i : Q.outer, ∑ j, a.potential i j * w j) =
          ∑ i ∈ Q.outer, F i := by
        simpa [F] using (Finset.sum_coe_sort Q.outer F)
      have h2 : (∑ i ∈ Q.outer.attach, ∑ j, a.potential i j * w j) =
          ∑ i ∈ Q.outer, F i := by
        simpa [F] using (Finset.sum_attach Q.outer F)
      exact h1.trans h2.symm
    calc
      _ = _ := hExpand
      _ = _ := by
        rw [hmeanDiv, hAlpha, hPotential, hattach]
        ring
  · simp [LocalCoordinates.B, LocalCube.extend, Matrix.mulVec, dotProduct, hx]

def localCubeMean {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (Q : LocalCube P I) (v : I → ℝ) : ℝ :=
  (∑ i : Q.outer, v i) / Q.outer.card

def localCubeCentered {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (Q : LocalCube P I) (v : I → ℝ) : Q.outer → ℝ :=
  fun i => v i - localCubeMean Q v

theorem localCubeCentered_neutral {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    (Q : LocalCube P I) (v : I → ℝ) : neutral (localCubeCentered Q v) := by
  classical
  have hconst : (∑ i : Q.outer, localCubeMean Q v) =
      (Q.outer.card : ℝ) * localCubeMean Q v := by
    simp [Finset.sum_const, nsmul_eq_mul]
  by_cases hcard : Q.outer.card = 0
  · have hempty : Q.outer = ∅ := Finset.card_eq_zero.mp hcard
    unfold neutral localCubeCentered
    rw [hempty]
    simp [localCubeMean]
  · have hcast : (Q.outer.card : ℝ) ≠ 0 := by exact_mod_cast hcard
    change (∑ i : Q.outer, (v i - localCubeMean Q v)) = 0
    rw [Finset.sum_sub_distrib, hconst]
    simp only [localCubeMean]
    rw [mul_div_cancel₀ _ hcast]
    ring

theorem local_cube_coordinates {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b : ℝ) (h : ℕ)
    (a : LocalCoordinates Q b h) (hedge : Q.edge.IsSymm)
    (α : Q.ports → ℝ) (v : I → ℝ) :
    ∃ w : Fin h → ℝ,
      a.B *ᵥ w = Q.extend α (localCubeCentered Q v) ∧
      l2sq w = Q.energy b α (fun i => v i) := by
  let vT : Q.outer → ℝ := localCubeCentered Q v
  have hneutral : neutral vT := localCubeCentered_neutral Q v
  obtain ⟨w, hα, hv⟩ := a.complete α vT hneutral
  have hB := local_coordinates_B_mulVec Q b h a w
  rw [hα, hv] at hB
  have hnorm := a.normalized w
  rw [hα, hv] at hnorm
  have hshift :
      qform (laplacian Q.edge) (localCubeCentered Q v) =
        qform (laplacian Q.edge) (fun i : Q.outer => v i) := by
    change qform (laplacian Q.edge) (fun i : Q.outer => v i - localCubeMean Q v) = _
    exact qform_laplacian_sub_const Q.edge hedge (fun i : Q.outer => v i)
      (localCubeMean Q v)
  have henergy : Q.energy b α vT = Q.energy b α (fun i => v i) := by
    simp only [LocalCube.energy]
    rw [hshift]
  refine ⟨w, hB, ?_⟩
  calc l2sq w = Q.energy b α vT := hnorm.symm
    _ = Q.energy b α (fun i => v i) := henergy

theorem local_block_form_bound {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] (Q : LocalCube P I) (b : ℝ) (h : ℕ)
    (a : LocalCoordinates Q b h) (hedge : Q.edge.IsSymm) (L : RMat P)
    (α : Q.ports → ℝ) (v : I → ℝ) (ε : ℝ)
    (hbudget : ‖pullback a.B L‖ ≤ ε) :
    |qform L (Q.extend α (localCubeCentered Q v))| ≤ ε * Q.energy b α (fun i => v i) := by
  obtain ⟨w, hB, henergy⟩ := local_cube_coordinates Q b h a hedge α v
  calc
    |qform L (Q.extend α (localCubeCentered Q v))| =
        |qform (pullback a.B L) w| := by rw [← hB, ← qform_pullback]
    _ ≤ ‖pullback a.B L‖ * l2sq w := qform_abs_le_opNorm _ _
    _ ≤ ε * l2sq w := mul_le_mul_of_nonneg_right hbudget
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = ε * Q.energy b α (fun i => v i) := by rw [henergy]

theorem local_extended_is_global_split {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cover : TileCover (P := P) (I := I) d t b C dist) (T : Fin cover.count)
    (α : P → ℝ) (v : I → ℝ) :
    ∀ x ∈ cover.inner T,
      (cover.cube T).extend (fun p => α p.1)
        (localCubeCentered (cover.cube T) v) x +
          localCubeMean (cover.cube T) v = α x + v (cover.site x) := by
  intro x hx
  let Q := cover.cube T
  have hxInner : x ∈ cover.inner T := hx
  have hxPort : x ∈ Q.ports := (cover.inside T).2 hxInner
  have hxOuter : Q.site x ∈ Q.outer := (Finset.mem_filter.mp hxPort).2
  have hsite : Q.site x = cover.site x := congrFun (cover.same_site T) x
  have hsumcenter : ∑ i : Q.outer, localCubeCentered Q v i = 0 := by
    simpa [neutral] using localCubeCentered_neutral Q v
  change Q.extend (fun p => α p.1) (localCubeCentered Q v) x +
    localCubeMean Q v = α x + v (cover.site x)
  rw [LocalCube.extend, dif_pos hxPort, cover.cutoff_one T x hxInner, one_mul]
  rw [hsumcenter]
  simp only [localCubeCentered, localCubeMean, Subtype.coe_mk]
  rw [hsite]
  ring

theorem tile_energy_nonneg {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cover : TileCover (P := P) (I := I) d t b C dist) (T : Fin cover.count)
    (α : P → ℝ) (v : I → ℝ) :
    0 ≤ (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
  obtain ⟨w, _, hnorm⟩ := local_cube_coordinates (cover.cube T) b (cover.dim T)
    (cover.coords T) (cover.edge_symm T) (fun p => α p.1) v
  rw [← hnorm]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cover_energy_nonneg {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cover : TileCover (P := P) (I := I) d t b C dist)
    (hC : 0 < C) (hb : 0 < b) (v : I → ℝ) : 0 ≤ cover.energy v := by
  have hsum : 0 ≤ ∑ T, (cover.cube T).energy b (fun _ => 0) (fun i => v i.1) :=
    Finset.sum_nonneg fun T _ => tile_energy_nonneg cover T (fun _ => 0) v
  have hlocal := cover.local_sum (fun _ => 0) v
  have hprod : 0 ≤ C * (cover.energy v / b) := by
    have h := hsum.trans hlocal
    simpa [l2sq] using h
  by_contra hnot
  have hneg : cover.energy v < 0 := lt_of_not_ge hnot
  have hdiv : cover.energy v / b < 0 := div_neg_of_neg_of_pos hneg hb
  have hprodNeg : C * (cover.energy v / b) < 0 := mul_neg_of_pos_of_neg hC hdiv
  exact (not_lt_of_ge hprod) hprodNeg

theorem power_neg_dim_le {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (d : ℕ) :
    power u (-(d : ℝ)) ≤ power u (-(d : ℝ) - 2) := by
  have hsplit : power u (-(d : ℝ)) =
      power u (-(d : ℝ) - 2) * power u 2 := by
    rw [← power_split hu]
    congr 1
    ring
  have hpow : power u 2 = u ^ 2 := by
    show u ^ (2 : ℝ) = u ^ 2
    exact_mod_cast Real.rpow_natCast u 2
  have hpow1 : power u 2 ≤ 1 := by
    rw [hpow]
    have hmul := mul_le_mul_of_nonneg_right hu1 hu.le
    nlinarith
  calc
    power u (-(d : ℝ)) = power u (-(d : ℝ) - 2) * power u 2 := hsplit
    _ ≤ power u (-(d : ℝ) - 2) * 1 :=
      mul_le_mul_of_nonneg_left hpow1 (Real.rpow_nonneg hu.le _)
    _ = power u (-(d : ℝ) - 2) := by ring

theorem kernel_graph_bound_split {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cover : TileCover (P := P) (I := I) d t b C dist)
    (hC : 0 < C) (hb : 0 < b) (hb1 : b ≤ 1)
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (α : P → ℝ) (v : I → ℝ) :
    graphEnergy dist u (fun x => α x + v (cover.site x)) ≤
      C * power u (-(d : ℝ) - 2) * (l2sq α + cover.energy v / b) := by
  have hE0 : 0 ≤ cover.energy v := cover_energy_nonneg cover hC hb v
  have hEdiv : cover.energy v ≤ cover.energy v / b := by
    apply (le_div_iff₀ hb).2
    have hmul := mul_le_mul_of_nonneg_left hb1 hE0
    nlinarith
  have hα0 : 0 ≤ l2sq α := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpower := power_neg_dim_le hu hu1 d
  have hkernel := cover.kernel_energy u hu hu1 α v
  have hkernel' : graphEnergy dist u (fun x => α x + v (cover.site x)) ≤
      C * (power u (-(d : ℝ)) * l2sq α +
        power u (-(d : ℝ) - 2) * cover.energy v) := by
    unfold graphEnergy
    calc
      (1 / 2 : ℝ) * ∑ i, ∑ j,
          Real.exp (-u * dist i j) * ((α i + v (cover.site i)) -
            (α j + v (cover.site j))) ^ 2 =
        (1 / 2 : ℝ) * ∑ i, ∑ j,
          Real.exp (-u * dist i j) *
            (α i + v (cover.site i) - α j - v (cover.site j)) ^ 2 := by
          apply congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ ≤ C * (power u (-(d : ℝ)) * l2sq α +
          power u (-(d : ℝ) - 2) * cover.energy v) := hkernel
  calc
    graphEnergy dist u (fun x => α x + v (cover.site x)) ≤
        C * (power u (-(d : ℝ)) * l2sq α +
          power u (-(d : ℝ) - 2) * cover.energy v) := hkernel'
    _ ≤ C * (power u (-(d : ℝ) - 2) * l2sq α +
          power u (-(d : ℝ) - 2) * (cover.energy v / b)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact add_le_add
          (mul_le_mul_of_nonneg_right hpower hα0)
          (mul_le_mul_of_nonneg_left hEdiv (Real.rpow_nonneg hu.le _))
    _ = C * power u (-(d : ℝ) - 2) *
          (l2sq α + cover.energy v / b) := by ring

theorem local_extension_graph_bound {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] {d : ℕ} {t b C : ℝ} {dist : P → P → ℝ}
    (cover : TileCover (P := P) (I := I) d t b C dist) (T : Fin cover.count)
    (hC : 0 < C) (hb : 0 < b) (hb1 : b ≤ 1)
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (α : P → ℝ) (v : I → ℝ) :
    graphEnergy dist u
      ((cover.cube T).extend (fun p => α p.1)
        (localCubeCentered (cover.cube T) v)) ≤
      C ^ 2 * power u (-(d : ℝ) - 2) *
        (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
  obtain ⟨w, hBw, henergy⟩ := local_cube_coordinates (cover.cube T) b
    (cover.dim T) (cover.coords T) (cover.edge_symm T) (fun p => α p.1) v
  obtain ⟨α', v', hdecomp, hcost⟩ := cover.local_split T w
  have hglobal : ∀ x,
      (cover.cube T).extend (fun p => α p.1)
        (localCubeCentered (cover.cube T) v) x = α' x + v' (cover.site x) := by
    intro x
    rw [← hBw]
    rw [hdecomp x]
  have hsplit := kernel_graph_bound_split cover hC hb hb1 u hu hu1 α' v'
  have hcost' : l2sq α' + cover.energy v' / b ≤
      C * (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
    calc
      l2sq α' + cover.energy v' / b ≤ C * l2sq w := hcost
      _ = C * (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by rw [henergy]
  have hcoef : 0 ≤ C * power u (-(d : ℝ) - 2) :=
    mul_nonneg hC.le (Real.rpow_pos_of_pos hu _).le
  calc
    graphEnergy dist u
        ((cover.cube T).extend (fun p => α p.1)
          (localCubeCentered (cover.cube T) v)) =
        graphEnergy dist u (fun x => α' x + v' (cover.site x)) := by
          congr 1
          funext x
          exact hglobal x
    _ ≤ C * power u (-(d : ℝ) - 2) * (l2sq α' + cover.energy v' / b) := hsplit
    _ ≤ C * power u (-(d : ℝ) - 2) *
          (C * (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1)) :=
        mul_le_mul_of_nonneg_left hcost' hcoef
    _ = C ^ 2 * power u (-(d : ℝ) - 2) *
          (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by ring

set_option maxHeartbeats 1000000 in
theorem local_transfer_decomposition_bound {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I] {d : ℕ} {C c t b : ℝ} {dist : P → P → ℝ}
    (cover : TileCover (P := P) (I := I) d t b C dist)
    (q : Sequence P) (blocks : Fin cover.count → Finset ℕ)
    (r : P → ℂ) (res : Finset P)
    (hC : 1 ≤ C) (hc : 0 < c) (ht : 0 < t) (ht1 : t ≤ 1)
    (hb : 0 < b) (hbt : b ≤ t)
    (shell : ShellBounds d C dist)
    (hblocks : ∀ k < q.length, ∃! T, k ∈ blocks T)
    (hblockSub : ∀ T, blocks T ⊆ Finset.range q.length)
    (htile : ∀ k < q.length, ∀ x, q.pivot k = some x → ∀ T, k ∈ blocks T → x ∈ cover.tile T)
    (hdistinct : ∀ k l, k < q.length → l < q.length → ∀ x y,
      q.pivot k = some x → q.pivot l = some y → cover.site x = cover.site y → k = l)
    (tails : TraceTails q t C c r res dist)
    (hstep : ∀ k < q.length,
      (q.stepL t r k).IsSymm ∧ q.stepL t r k *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hbudget : ∀ T, localBudget cover T (q.Jrecord t r (blocks T))
      (q.Lrecord t r (blocks T)) (q.lagRecord t r (blocks T))
      (q.rowRecord t r Finset.univ (blocks T)) (q.rowRecord t r res (blocks T)))
    (u : ℝ) (huDef : u = c * t ^ 3 / 2) (hu : 0 < u) (hu1 : u ≤ 1)
    (α : P → ℝ) (v : I → ℝ) :
    |qform (q.Lrecord t r (Finset.range q.length))
        (fun x => α x + v (cover.site x))| ≤
      (C * power t (delta / 8) +
        2 * C ^ 4 * power t (-C) * Real.exp (-u * power t (-6)) *
          power (u / 2) (-(d : ℝ)) * power (u / 2) (-(d : ℝ) - 2)) *
        (l2sq α + cover.energy v / b) := by
  classical
  let F : P → ℝ := fun x => α x + v (cover.site x)
  let G : Fin cover.count → P → ℝ := fun T =>
    (cover.cube T).extend (fun p => α p.1)
      (localCubeCentered (cover.cube T) v)
  let z := u / 2
  let A := power t (-C)
  let R := power t (-6)
  let S := C * power z (-(d : ℝ))
  let K := C * power z (-(d : ℝ) - 2)
  let far := A * Real.exp (-u * R)
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hR : 0 < R := by
    dsimp [R, power]
    exact Real.rpow_pos_of_pos ht _
  have hA : 0 ≤ A := by
    dsimp [A, power]
    exact (Real.rpow_pos_of_pos ht _).le
  have hfar : 0 ≤ far := by dsimp [far]; positivity
  have hS : 0 ≤ S := by
    dsimp [S, power]
    exact mul_nonneg hC0.le (Real.rpow_pos_of_pos hz _).le
  have hK : 0 ≤ K := by
    dsimp [K, power]
    exact mul_nonneg hC0.le (Real.rpow_pos_of_pos hz _).le
  have hcost : 0 ≤ l2sq α + cover.energy v / b := by
    have hE := cover_energy_nonneg cover hC0 hb v
    have hα : 0 ≤ l2sq α := Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact add_nonneg hα (div_nonneg hE hb.le)
  have hdecay : -c * t ^ 3 = -(2 * u) := by rw [huDef]; ring
  have hstepTail (T : Fin cover.count) (k : ℕ) (hkT : k ∈ blocks T) :
      |qform (q.stepL t r k) F - qform (q.stepL t r k) (G T)| ≤
        far * ((q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F) +
          (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) := by
    have hk : k < q.length := Finset.mem_range.1 (hblockSub T hkT)
    cases hpv : q.pivot k with
    | none =>
      simp [Sequence.stepL, hpv, F, G, qform]
    | some x =>
      have hxT := htile k hk x hpv T hkT
      have hagree : ∀ i ∈ cover.inner T, ∀ j ∈ cover.inner T,
          F i - F j = G T i - G T j := by
        intro i hi j hj
        change (α i + v (cover.site i)) - (α j + v (cover.site j)) =
          G T i - G T j
        have ei := local_extended_is_global_split cover T α v i hi
        have ej := local_extended_is_global_split cover T α v j hj
        have ei' : G T i + localCubeMean (cover.cube T) v = F i := by simpa [F] using ei
        have ej' : G T j + localCubeMean (cover.cube T) v = F j := by simpa [F] using ej
        calc
          F i - F j = (G T i + localCubeMean (cover.cube T) v) -
              (G T j + localCubeMean (cover.cube T) v) := by rw [← ei', ← ej']
          _ = G T i - G T j := by ring
      have hbuf : ∀ i j, (i ∉ cover.inner T ∨ j ∉ cover.inner T) →
          R ≤ dist i x + dist j x := by
        intro i j hout
        rcases hout with hi | hj
        · have h := cover.buffer T x hxT i hi
          have hn := shell.nonneg j x
          linarith
        · have h := cover.buffer T x hxT j hj
          have hn := shell.nonneg i x
          linarith
      have hrow : ∀ i, ∑ j, q.stepL t r k i j = 0 := by
        intro i
        have hi := congrFun (hstep k hk).2 i
        simpa [Matrix.mulVec, dotProduct] using hi
      have htail : ∀ i j, i ≠ j → |q.stepL t r k i j| ≤
          A * Real.exp (-(2 * u) * (dist i x + dist j x)) := by
        intro i j hij
        have h := tails.L k hk x hpv i j hij
        rw [hdecay] at h
        simpa [A] using h
      have h := step_tail_weighted dist shell (q.stepL t r k) (hstep k hk).1 hrow
        F (G T) (cover.inner T) hagree A u R hA hu x hbuf htail
      rw [← weightedGraphEnergy_add] at h
      simpa [far] using h
  have hlocalT (T : Fin cover.count) :
      |qform (q.Lrecord t r (blocks T)) (G T)| ≤
        power t (delta / 8) *
          (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
    exact local_block_form_bound (cover.cube T) b (cover.dim T) (cover.coords T)
      (cover.edge_symm T) (q.Lrecord t r (blocks T)) (fun p => α p.1) v
      (power t (delta / 8)) ((hbudget T).2.2.2)
  have hlocalSum :
      (∑ T, |qform (q.Lrecord t r (blocks T)) (G T)|) ≤
        power t (delta / 8) * C * (l2sq α + cover.energy v / b) := by
    calc
      (∑ T, |qform (q.Lrecord t r (blocks T)) (G T)|) ≤
          ∑ T, power t (delta / 8) *
            (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) :=
        Finset.sum_le_sum fun T _ => hlocalT T
      _ = power t (delta / 8) *
            ∑ T, (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
        rw [Finset.mul_sum]
      _ ≤ power t (delta / 8) * (C * (l2sq α + cover.energy v / b)) :=
        mul_le_mul_of_nonneg_left (cover.local_sum α v)
          (Real.rpow_pos_of_pos ht _).le
      _ = _ := by ring
  have hinj : ∀ k l, k < q.length → l < q.length → ∀ x,
      q.pivot k = some x → q.pivot l = some x → k = l := by
    intro k l hk hl x hx hy
    exact hdistinct k l hk hl x x hx hy rfl
  have hFpartition :
      (∑ T, ∑ k ∈ blocks T,
        (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F)) =
      ∑ k ∈ Finset.range q.length,
        (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F) :=
    partition_sum q.length blocks hblocks hblockSub _
  have hFpivot :
      (∑ k ∈ Finset.range q.length,
        (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F)) ≤
      S * graphEnergy dist z F := by
    simpa [S, z] using pivot_weighted_graph_sum_le dist shell q.length q.pivot
      hinj z hz hz1 F
  have hGpivot :
      (∑ T, ∑ k ∈ blocks T,
        (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) ≤
      S * ∑ T, graphEnergy dist z (G T) := by
    calc
      (∑ T, ∑ k ∈ blocks T,
          (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) ≤
        ∑ T, S * graphEnergy dist z (G T) := by
          refine Finset.sum_le_sum fun T _ => ?_
          let pvT : ℕ → Option P := fun k => if k ∈ blocks T then q.pivot k else none
          have hsumTle :
              (∑ k ∈ blocks T,
                (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) ≤
              ∑ k ∈ Finset.range q.length,
                (pvT k).elim 0 (fun x => weightedGraphEnergy dist z x (G T)) := by
            calc
              _ = ∑ k ∈ blocks T,
                    (pvT k).elim 0 (fun x => weightedGraphEnergy dist z x (G T)) := by
                      refine Finset.sum_congr rfl fun k hk => ?_
                      simp [pvT, hk]
              _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (hblockSub T) fun k hk hknot => by
                    simp [pvT, hknot]
          have hinjT : ∀ k l, k < q.length → l < q.length → ∀ x,
              pvT k = some x → pvT l = some x → k = l := by
            intro k l hk hl x hx hy
            have hx' : k ∈ blocks T ∧ q.pivot k = some x := by simpa [pvT] using hx
            have hy' : l ∈ blocks T ∧ q.pivot l = some x := by simpa [pvT] using hy
            exact hdistinct k l hk hl x x hx'.2 hy'.2 rfl
          calc
            (∑ k ∈ blocks T,
                (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) ≤
              ∑ k ∈ Finset.range q.length,
                (pvT k).elim 0 (fun x => weightedGraphEnergy dist z x (G T)) := hsumTle
            _ ≤ S * graphEnergy dist z (G T) := by
              simpa [S, z] using pivot_weighted_graph_sum_le dist shell q.length pvT
                hinjT z hz hz1 (G T)
      _ = S * ∑ T, graphEnergy dist z (G T) := by rw [Finset.mul_sum]
  have hFkernel := kernel_graph_bound_split cover hC0 hb (hbt.trans ht1) z hz hz1 α v
  have hGkernel :
      (∑ T, graphEnergy dist z (G T)) ≤
        C ^ 2 * power z (-(d : ℝ) - 2) *
          ∑ T, (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
    calc
      (∑ T, graphEnergy dist z (G T)) ≤
          ∑ T, C ^ 2 * power z (-(d : ℝ) - 2) *
            (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) :=
        Finset.sum_le_sum fun T _ => local_extension_graph_bound cover T hC0 hb
          (hbt.trans ht1) z hz hz1 α v
      _ = C ^ 2 * power z (-(d : ℝ) - 2) *
          ∑ T, (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := by
            rw [Finset.mul_sum]
  have hGkernel' :
      (∑ T, graphEnergy dist z (G T)) ≤
        C ^ 3 * power z (-(d : ℝ) - 2) * (l2sq α + cover.energy v / b) := by
    calc
      (∑ T, graphEnergy dist z (G T)) ≤
          C ^ 2 * power z (-(d : ℝ) - 2) *
            ∑ T, (cover.cube T).energy b (fun p => α p.1) (fun i => v i.1) := hGkernel
      _ ≤ C ^ 2 * power z (-(d : ℝ) - 2) *
            (C * (l2sq α + cover.energy v / b)) :=
        mul_le_mul_of_nonneg_left (cover.local_sum α v)
          (mul_nonneg (sq_nonneg C) (Real.rpow_pos_of_pos hz _).le)
      _ = _ := by ring
  have hFkernel' : graphEnergy dist z F ≤
      C * power z (-(d : ℝ) - 2) * (l2sq α + cover.energy v / b) := by
    have h := hFkernel
    simpa [F] using h
  have htailSum :
      (∑ T, |qform (q.Lrecord t r (blocks T)) F -
          qform (q.Lrecord t r (blocks T)) (G T)|) ≤
        2 * C ^ 4 * far * power z (-(d : ℝ)) * power z (-(d : ℝ) - 2) *
          (l2sq α + cover.energy v / b) := by
    have hblock (T : Fin cover.count) :
        |qform (q.Lrecord t r (blocks T)) F -
          qform (q.Lrecord t r (blocks T)) (G T)| ≤
        far * ((∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F)) +
          ∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) := by
      have hformula :
          qform (q.Lrecord t r (blocks T)) F -
              qform (q.Lrecord t r (blocks T)) (G T) =
            ∑ k ∈ blocks T,
              (qform (q.stepL t r k) F - qform (q.stepL t r k) (G T)) := by
        change qform (∑ k ∈ blocks T, q.stepL t r k) F -
          qform (∑ k ∈ blocks T, q.stepL t r k) (G T) = _
        rw [qform_finset_sum, qform_finset_sum, ← Finset.sum_sub_distrib]
      calc
        |qform (q.Lrecord t r (blocks T)) F -
            qform (q.Lrecord t r (blocks T)) (G T)| =
          |∑ k ∈ blocks T,
              (qform (q.stepL t r k) F - qform (q.stepL t r k) (G T))| := by rw [hformula]
        _ ≤ ∑ k ∈ blocks T,
              |qform (q.stepL t r k) F - qform (q.stepL t r k) (G T)| := by
          calc
            |∑ k ∈ blocks T,
                (qform (q.stepL t r k) F - qform (q.stepL t r k) (G T))| =
              ‖∑ k ∈ blocks T,
                (qform (q.stepL t r k) F - qform (q.stepL t r k) (G T))‖ := by
                  rw [Real.norm_eq_abs]
            _ ≤ ∑ k ∈ blocks T,
                ‖qform (q.stepL t r k) F - qform (q.stepL t r k) (G T)‖ := norm_sum_le _ _
            _ = _ := by simp [Real.norm_eq_abs]
        _ ≤ ∑ k ∈ blocks T,
              far * ((q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F) +
                (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) :=
          Finset.sum_le_sum fun k hk => hstepTail T k hk
        _ = far * ((∑ k ∈ blocks T,
              (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F)) +
            ∑ k ∈ blocks T,
              (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have hsumBlocks :
        (∑ T, |qform (q.Lrecord t r (blocks T)) F -
            qform (q.Lrecord t r (blocks T)) (G T)|) ≤
          ∑ T, far * ((∑ k ∈ blocks T,
              (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F)) +
            ∑ k ∈ blocks T,
              (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) :=
      Finset.sum_le_sum fun T _ => hblock T
    have hFpart := hFpartition
    have hGpart := hGpivot
    calc
      (∑ T, |qform (q.Lrecord t r (blocks T)) F -
          qform (q.Lrecord t r (blocks T)) (G T)|) ≤
        far * ((∑ T, ∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F)) +
          ∑ T, ∑ k ∈ blocks T,
            (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) := by
          calc
            _ ≤ ∑ T, far * ((∑ k ∈ blocks T,
                (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x F)) +
              ∑ k ∈ blocks T,
                (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) := hsumBlocks
            _ = _ := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ far * (S * graphEnergy dist z F +
          S * (C ^ 3 * power z (-(d : ℝ) - 2) *
            (l2sq α + cover.energy v / b))) := by
          rw [hFpart]
          apply mul_le_mul_of_nonneg_left _ hfar
          have hGbound :
              (∑ T, ∑ k ∈ blocks T,
                (q.pivot k).elim 0 (fun x => weightedGraphEnergy dist z x (G T))) ≤
              S * (C ^ 3 * power z (-(d : ℝ) - 2) *
                (l2sq α + cover.energy v / b)) :=
            hGpivot.trans (mul_le_mul_of_nonneg_left hGkernel' hS)
          exact add_le_add hFpivot hGbound
      _ ≤ 2 * C ^ 4 * far * power z (-(d : ℝ)) * power z (-(d : ℝ) - 2) *
            (l2sq α + cover.energy v / b) := by
          have hSdef : S = C * power z (-(d : ℝ)) := rfl
          rw [hSdef]
          have hC2 : 1 ≤ C ^ 2 := by
            have h := mul_le_mul hC hC (by norm_num) hC0.le
            nlinarith
          have hCpower : C ^ 2 + C ^ 4 ≤ 2 * C ^ 4 := by
            have h := mul_le_mul_of_nonneg_right hC2 (sq_nonneg C)
            nlinarith
          have hprod : 0 ≤ power z (-(d : ℝ)) *
              power z (-(d : ℝ) - 2) * (l2sq α + cover.energy v / b) := by
            exact mul_nonneg
              (mul_nonneg (Real.rpow_pos_of_pos hz _).le
                (Real.rpow_pos_of_pos hz _).le) hcost
          have hcoef' : (C ^ 2 + C ^ 4) * power z (-(d : ℝ)) *
                power z (-(d : ℝ) - 2) ≤
              2 * C ^ 4 * power z (-(d : ℝ)) * power z (-(d : ℝ) - 2) := by
            calc
              (C ^ 2 + C ^ 4) * power z (-(d : ℝ)) *
                  power z (-(d : ℝ) - 2) ≤
                (2 * C ^ 4 * power z (-(d : ℝ))) *
                  power z (-(d : ℝ) - 2) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hCpower
                    (Real.rpow_pos_of_pos hz _).le)
                  (Real.rpow_pos_of_pos hz _).le
              _ = _ := by ring
          calc
            far * (C * power z (-(d : ℝ)) * graphEnergy dist z F +
              C * power z (-(d : ℝ)) *
                (C ^ 3 * power z (-(d : ℝ) - 2) *
                  (l2sq α + cover.energy v / b))) ≤
              far * ((C ^ 2 + C ^ 4) * power z (-(d : ℝ)) *
                power z (-(d : ℝ) - 2) * (l2sq α + cover.energy v / b)) := by
                  calc
                    _ ≤ far * (C * power z (-(d : ℝ)) *
                        (C * power z (-(d : ℝ) - 2) *
                          (l2sq α + cover.energy v / b)) +
                      C * power z (-(d : ℝ)) *
                        (C ^ 3 * power z (-(d : ℝ) - 2) *
                          (l2sq α + cover.energy v / b))) := by
                        apply mul_le_mul_of_nonneg_left _ hfar
                        apply add_le_add
                        · exact mul_le_mul_of_nonneg_left hFkernel'
                            (mul_nonneg hC0.le (Real.rpow_pos_of_pos hz _).le)
                        · exact le_of_eq rfl
                    _ = _ := by ring
            _ ≤ far * (2 * C ^ 4 * power z (-(d : ℝ)) *
                power z (-(d : ℝ) - 2) * (l2sq α + cover.energy v / b)) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hcoef' hcost) hfar
            _ = 2 * C ^ 4 * far * power z (-(d : ℝ)) *
                power z (-(d : ℝ) - 2) * (l2sq α + cover.energy v / b) := by ring
  have hpartition :
      q.Lrecord t r (Finset.range q.length) =
        ∑ T, q.Lrecord t r (blocks T) := by
    ext i j
    simp only [Sequence.Lrecord, Matrix.sum_apply]
    exact (partition_sum q.length blocks hblocks hblockSub
      (fun k => q.stepL t r k i j)).symm
  have hformPartition :
      qform (q.Lrecord t r (Finset.range q.length)) F =
        ∑ T, qform (q.Lrecord t r (blocks T)) F := by
    calc
      _ = qform (∑ T, q.Lrecord t r (blocks T)) F := by rw [hpartition]
      _ = _ := qform_sum (fun T => q.Lrecord t r (blocks T)) F
  have htriangle (T : Fin cover.count) :
      |qform (q.Lrecord t r (blocks T)) F| ≤
        |qform (q.Lrecord t r (blocks T)) (G T)| +
          |qform (q.Lrecord t r (blocks T)) F -
            qform (q.Lrecord t r (blocks T)) (G T)| := by
    calc
      |qform (q.Lrecord t r (blocks T)) F| =
          |(qform (q.Lrecord t r (blocks T)) F -
            qform (q.Lrecord t r (blocks T)) (G T)) +
              qform (q.Lrecord t r (blocks T)) (G T)| := by congr 1 <;> ring
      _ ≤ _ := by
        calc
          |(qform (q.Lrecord t r (blocks T)) F -
              qform (q.Lrecord t r (blocks T)) (G T)) +
                qform (q.Lrecord t r (blocks T)) (G T)| =
              ‖(qform (q.Lrecord t r (blocks T)) F -
                qform (q.Lrecord t r (blocks T)) (G T)) +
                  qform (q.Lrecord t r (blocks T)) (G T)‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖qform (q.Lrecord t r (blocks T)) F -
                qform (q.Lrecord t r (blocks T)) (G T)‖ +
              ‖qform (q.Lrecord t r (blocks T)) (G T)‖ := norm_add_le _ _
          _ = _ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]; ring
  calc
    |qform (q.Lrecord t r (Finset.range q.length)) F| ≤
      ∑ T, |qform (q.Lrecord t r (blocks T)) F| := by
        rw [hformPartition]
        calc
          |∑ T, qform (q.Lrecord t r (blocks T)) F| =
              ‖∑ T, qform (q.Lrecord t r (blocks T)) F‖ := by rw [Real.norm_eq_abs]
          _ ≤ ∑ T, ‖qform (q.Lrecord t r (blocks T)) F‖ := norm_sum_le _ _
          _ = _ := by simp [Real.norm_eq_abs]
    _ ≤ ∑ T, (|qform (q.Lrecord t r (blocks T)) (G T)| +
          |qform (q.Lrecord t r (blocks T)) F -
            qform (q.Lrecord t r (blocks T)) (G T)|) :=
        Finset.sum_le_sum fun T _ => htriangle T
    _ = (∑ T, |qform (q.Lrecord t r (blocks T)) (G T)|) +
          ∑ T, |qform (q.Lrecord t r (blocks T)) F -
            qform (q.Lrecord t r (blocks T)) (G T)| := Finset.sum_add_distrib
    _ ≤ power t (delta / 8) * C * (l2sq α + cover.energy v / b) +
          2 * C ^ 4 * far * power z (-(d : ℝ)) * power z (-(d : ℝ) - 2) *
            (l2sq α + cover.energy v / b) := add_le_add hlocalSum htailSum
    _ = (C * power t (delta / 8) +
          2 * C ^ 4 * power t (-C) * Real.exp (-u * power t (-6)) *
            power (u / 2) (-(d : ℝ)) * power (u / 2) (-(d : ℝ) - 2)) *
          (l2sq α + cover.energy v / b) := by
          dsimp [far, A, R, z]
          ring

theorem tail_transfer_coefficient_small {d : ℕ} {C c : ℝ}
    (hC : 1 ≤ C) (hc : 0 < c) :
    ∃ t0 > 0, ∀ t, 0 < t → t < t0 →
      2 * C ^ 4 * power t (-C) * Real.exp (-(c * t ^ 3 / 2) * power t (-6)) *
        power (c * t ^ 3 / 4) (-(d : ℝ)) *
        power (c * t ^ 3 / 4) (-(d : ℝ) - 2) ≤ t := by
  let Kc := power (c / 4) (-2)
  let Ctail := 2 * C ^ 2 * (1 + Kc)
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  obtain ⟨t0, ht0, hsmall⟩ := tail_small (C + 6) Ctail (c / 2) d (by positivity)
  refine ⟨t0, ht0, fun t ht htt => ?_⟩
  let z := c * t ^ 3 / 4
  let R := power t (-6)
  let A := power t (-C)
  let pd := power z (-(d : ℝ))
  have hz : 0 < z := by dsimp [z]; positivity
  have hR : 0 < R := by dsimp [R, power]; exact Real.rpow_pos_of_pos ht _
  have hA : 0 < A := by dsimp [A, power]; exact Real.rpow_pos_of_pos ht _
  have hKc : 0 < Kc := by dsimp [Kc, power]; exact Real.rpow_pos_of_pos (by positivity) _
  have hCtail : 0 < Ctail := by dsimp [Ctail]; positivity
  have hzTail : c / 2 * t ^ 3 / 2 = z := by dsimp [z]; ring
  have hTR : power t (-(C + 6)) = A * R := by
    rw [show -(C + 6) = -C + -6 by ring, power_split ht]
  have hbase : power z (-2) = Kc * R := by
    have hzEq : z = (c / 4) * t ^ 3 := by dsimp [z]; ring
    have hpow : (t ^ 3) ^ (-2 : ℝ) = t ^ (-6 : ℝ) := by
      rw [← Real.rpow_natCast_mul ht.le 3 (-2)]
      norm_num
    rw [hzEq]
    dsimp [power, Kc, R]
    rw [Real.mul_rpow (by positivity) (by positivity), hpow]
  have hpd2 : power z (-(d : ℝ) - 2) = pd * power z (-2) := by
    rw [← power_split hz]
    congr 1
  have hsmall' : (A * R) * Real.exp (-z * R) * (Ctail * pd) ^ 2 ≤ t := by
    have h := hsmall t ht htt
    rw [hzTail, hTR] at h
    exact h
  have hCoeff : 2 * C ^ 4 * Kc ≤ Ctail ^ 2 := by
    have hKle : Kc ≤ (1 + Kc) ^ 2 := by nlinarith [sq_nonneg Kc]
    have hstep := mul_le_mul_of_nonneg_left hKle (by positivity : 0 ≤ 2 * C ^ 4)
    have hstep' : 2 * C ^ 4 * (1 + Kc) ^ 2 ≤ Ctail ^ 2 := by
      dsimp [Ctail]
      nlinarith
    calc
      2 * C ^ 4 * Kc ≤ 2 * C ^ 4 * (1 + Kc) ^ 2 := hstep
      _ ≤ Ctail ^ 2 := hstep'
  have hExp : Real.exp (-(c * t ^ 3 / 2) * R) ≤ Real.exp (-z * R) := by
    apply Real.exp_le_exp.mpr
    have huZ : c * t ^ 3 / 2 = 2 * z := by dsimp [z]; ring
    rw [huZ]
    nlinarith [mul_nonneg hR.le hz.le]
  have hpowpos : 0 ≤ pd ^ 2 := sq_nonneg pd
  have hcoefRest : 0 ≤ (A * R) * Real.exp (-(c * t ^ 3 / 2) * R) * pd ^ 2 := by positivity
  have hExpRest : (A * R) * Real.exp (-(c * t ^ 3 / 2) * R) * pd ^ 2 ≤
      (A * R) * Real.exp (-z * R) * pd ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hExp (mul_nonneg hA.le hR.le)) hpowpos
  calc
    2 * C ^ 4 * power t (-C) * Real.exp (-(c * t ^ 3 / 2) * power t (-6)) *
        power (c * t ^ 3 / 4) (-(d : ℝ)) *
        power (c * t ^ 3 / 4) (-(d : ℝ) - 2) =
      (2 * C ^ 4 * Kc) *
        ((A * R) * Real.exp (-(c * t ^ 3 / 2) * R) * pd ^ 2) := by
          rw [hpd2, hbase]
          dsimp [A, R, pd, z, Kc]
          ring
    _ ≤ Ctail ^ 2 * ((A * R) * Real.exp (-z * R) * pd ^ 2) := by
          exact mul_le_mul hCoeff hExpRest hcoefRest (sq_nonneg Ctail)
    _ = (A * R) * Real.exp (-z * R) * (Ctail * pd) ^ 2 := by ring
    _ ≤ t := hsmall'

set_option maxHeartbeats 1000000 in
theorem localTransferL_proof : LocalTransferL := by
  intro d C c hC hc
  obtain ⟨tTail, htTail, htailSmall⟩ := tail_transfer_coefficient_small (d := d) hC hc
  obtain ⟨tU, htU, hsmallU⟩ := power_small (e := 3) (by norm_num) (a := 2 / c) (by positivity)
  let C' := C * (C + 1)
  let t0 := min tTail (min tU 1)
  have hC' : 0 < C' := by dsimp [C']; positivity
  have ht0 : 0 < t0 := by dsimp [t0]; positivity
  refine ⟨C', hC', t0, ht0, ?_⟩
  intro n m t b θ dist r res cover q blocks D0 ht htt hb hbt hθlo hθhi shell hwf hlive
    hblocks hblockSub htile hdistinct tails hstep hcomp hu0 hrow0 hres0 hbudget
  change t < min tTail (min tU 1) at htt
  have httTail : t < tTail := lt_of_lt_of_le htt (min_le_left _ _)
  have httRest : t < min tU 1 := lt_of_lt_of_le htt (min_le_right _ _)
  have httU : t < tU := lt_of_lt_of_le httRest (min_le_left _ _)
  have httOne : t < 1 := lt_of_lt_of_le httRest (min_le_right _ _)
  have ht1 : t ≤ 1 := le_of_lt httOne
  let u := c * t ^ 3 / 2
  have hu : 0 < u := by dsimp [u]; positivity
  have huDef : u = c * t ^ 3 / 2 := rfl
  have hu1 : u ≤ 1 := by
    have hs := hsmallU t ht httU
    have hp3 : power t 3 = t ^ 3 := by
      show t ^ (3 : ℝ) = t ^ 3
      exact_mod_cast Real.rpow_natCast t 3
    rw [hp3] at hs
    have hm := mul_lt_mul_of_pos_left hs hc
    rw [mul_div_cancel₀ 2 (ne_of_gt hc)] at hm
    dsimp [u]
    linarith
  have htEps : t ≤ power t (delta / 8) :=
    le_power_of_le_one ht ht1 (by norm_num [delta])
  have htailT :
      2 * C ^ 4 * power t (-C) * Real.exp (-u * power t (-6)) *
        power (u / 2) (-(d : ℝ)) * power (u / 2) (-(d : ℝ) - 2) ≤
      power t (delta / 8) := by
    have h := htailSmall t ht httTail
    have huHalf : u / 2 = c * t ^ 3 / 4 := by dsimp [u]; ring
    have huFull : u = c * t ^ 3 / 2 := rfl
    calc
      _ ≤ t := by rw [huFull, huHalf]; exact h
      _ ≤ power t (delta / 8) := htEps
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hsplitBound (α : Fin n → ℝ) (v : Fin m → ℝ) :
      |qform (q.Lrecord t r (Finset.range q.length))
          (fun x => α x + v (cover.site x))| ≤
        (C + 1) * power t (delta / 8) *
          (l2sq α + cover.energy v / b) := by
    have hraw := local_transfer_decomposition_bound cover q blocks r res hC hc ht ht1 hb hbt
      shell hblocks hblockSub htile hdistinct tails hstep hbudget u huDef hu hu1 α v
    have hcost : 0 ≤ l2sq α + cover.energy v / b := by
      have hE := cover_energy_nonneg cover hC0 hb v
      have hα : 0 ≤ l2sq α := Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact add_nonneg hα (div_nonneg hE hb.le)
    have hcoef : C * power t (delta / 8) +
        2 * C ^ 4 * power t (-C) * Real.exp (-u * power t (-6)) *
          power (u / 2) (-(d : ℝ)) * power (u / 2) (-(d : ℝ) - 2) ≤
        (C + 1) * power t (delta / 8) := by
      nlinarith [htailT]
    calc
      |qform (q.Lrecord t r (Finset.range q.length))
          (fun x => α x + v (cover.site x))| ≤
        (C * power t (delta / 8) +
          2 * C ^ 4 * power t (-C) * Real.exp (-u * power t (-6)) *
            power (u / 2) (-(d : ℝ)) * power (u / 2) (-(d : ℝ) - 2)) *
            (l2sq α + cover.energy v / b) := hraw
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hcost
  have hB : 0 < (C + 1) * power t (delta / 8) := by
    apply mul_pos
    · linarith
    · exact Real.rpow_pos_of_pos ht _
  intro f
  let SpatialCosts : Set ℝ := {a | ∃ α : Fin n → ℝ, ∃ v : Fin m → ℝ,
    (∀ x, f x = α x + v (cover.site x)) ∧ a = l2sq α + cover.energy v / b}
  have hSpatialNonempty : SpatialCosts.Nonempty := by
    refine ⟨l2sq f + cover.energy (fun _ => 0) / b, f, (fun _ => 0), ?_⟩
    constructor
    · intro x
      simp
    · rfl
  have hSpatialLower : |qform (q.Lrecord t r (Finset.range q.length)) f| /
      ((C + 1) * power t (delta / 8)) ≤ spatialEnergy cover.site b cover.energy f := by
    change |qform (q.Lrecord t r (Finset.range q.length)) f| /
      ((C + 1) * power t (delta / 8)) ≤ sInf SpatialCosts
    apply le_csInf hSpatialNonempty
    intro a ha
    rcases ha with ⟨α, v, hsplit, rfl⟩
    have hdecomp := hsplitBound α v
    have hfun : f = fun x => α x + v (cover.site x) := funext hsplit
    rw [← hfun] at hdecomp
    exact (div_le_iff₀ hB).2 (by simpa [mul_comm] using hdecomp)
  have hformLower :
      spatialEnergy cover.site b cover.energy f / C ≤ qform D0 f := (hcomp f).1
  have hspatialCompare : spatialEnergy cover.site b cover.energy f ≤ C * qform D0 f := by
    have h := (div_le_iff₀ hC0).1 hformLower
    simpa [mul_comm] using h
  have hglobal : |qform (q.Lrecord t r (Finset.range q.length)) f| ≤
      (C + 1) * power t (delta / 8) * spatialEnergy cover.site b cover.energy f := by
    have h := (div_le_iff₀ hB).1 hSpatialLower
    simpa [mul_comm] using h
  have hnonnegB : 0 ≤ (C + 1) * power t (delta / 8) := hB.le
  have hfinal := hglobal.trans
    (mul_le_mul_of_nonneg_left hspatialCompare hnonnegB)
  have hCeq : (C + 1) * power t (delta / 8) * (C * qform D0 f) =
      C' * power t (delta / 8) * qform D0 f := by
    dsimp [C']
    ring
  rw [hCeq] at hfinal
  exact hfinal

end AndersonAC.AgentS45
