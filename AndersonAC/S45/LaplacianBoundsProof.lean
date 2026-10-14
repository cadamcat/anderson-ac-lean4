import AndersonAC.S45.LaplacianProof
import AndersonAC.S45.JFourthProof

/-! Lemma 4.5 (`AndersonAC.S45.laplacian_bounds`), 04-sweep.tex:527–790.
Imports only sorry-free proof modules (never `Statements`). -/

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators

noncomputable section

namespace AndersonAC.AgentS45

open AndersonAC.S45

section Structure

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Edge weights of a Laplacian increment on the full index set, with general
linear coefficient `a` and quadratic coefficient `b`; zero on edges at `x`. -/
def edgeG (t : ℝ) (s : State P) (x : P) (a : ℂ) (b : ℝ) : RMat P :=
  fun i j => if i ≠ x ∧ j ≠ x then
    s.p i * s.p j * (-2 * (a * star (s.h t i j) * s.h t i x * s.h t x j).re +
      b * s.F t i x * s.F t x j)
  else 0

/-- The deletion constant `c_x = p_x / (q_x - p_x F_xx)`. -/
def cx (t : ℝ) (s : State P) (x : P) : ℝ := s.p x / (s.q x - s.p x * s.F t x x)

lemma mem_survivors_iff (x k : P) : k ∈ survivors x ↔ k ≠ x := by
  simp [survivors]

lemma Linc_eq_laplacian_edgeG (t : ℝ) (s : State P) (x : P) (ξ : ℝ) :
    Linc t s x ξ = laplacian (edgeG t s x (gamma t s x ξ)
      (‖gamma t s x ξ‖ ^ 2 - cx t s x)) := by
  classical
  ext i j
  by_cases hi : i = x
  · subst hi
    have hz : ∀ k, edgeG t s i (gamma t s i ξ) (‖gamma t s i ξ‖ ^ 2 - cx t s i) i k = 0 := by
      intro k; simp [edgeG]
    simp [Linc, pad, survivors, laplacian, hz]
  · have hiS : i ∈ survivors x := (mem_survivors_iff x i).2 hi
    by_cases hj : j = x
    · subst hj
      have hij : i ≠ j := hi
      simp [Linc, pad, survivors, laplacian, hij, edgeG]
    · have hjS : j ∈ survivors x := (mem_survivors_iff x j).2 hj
      by_cases hij : i = j
      · subst hij
        simp only [Linc, pad, dif_pos hiS, laplacian, if_true]
        rw [← sum_dite_mem_eq_subtype (survivors x)
          (fun k hk => if (⟨k, hk⟩ : survivors x) = ⟨i, hiS⟩ then 0
            else Ledge t s x ξ ⟨i, hiS⟩ ⟨k, hk⟩)]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = x
        · subst hk
          simp [survivors, edgeG]
        · have hkS : k ∈ survivors x := (mem_survivors_iff x k).2 hk
          rw [dif_pos hkS]
          by_cases hki : k = i
          · subst hki; simp
          · have hne : (⟨k, hkS⟩ : survivors x) ≠ ⟨i, hiS⟩ := by
              intro h; exact hki (congrArg Subtype.val h)
            simp only [hne, hki, if_false]
            simp [Ledge, edgeG, hi, hk, cx]
      · have hne : (⟨i, hiS⟩ : survivors x) ≠ ⟨j, hjS⟩ := by
          intro h; exact hij (congrArg Subtype.val h)
        simp only [Linc, pad, dif_pos hiS, dif_pos hjS, laplacian, hne, hij, if_false]
        simp [Ledge, edgeG, hi, hj, cx]

end Structure

section Analytic

/-- The analytic prestate facts used by Lemma 4.5, transferred from `Fin n`
to an arbitrary finite index type. -/
lemma analytic_any (C : ℝ) (hC : 1 ≤ C) : ∃ A > 0, ∃ tA > 0,
    ∀ (P : Type) [Fintype P] [DecidableEq P] (t : ℝ) (s : State P)
      (Λplus Wstar : Form P), t < tA → Prestate t C Λplus Wstar s →
      (∀ i, (∑ j, s.F t i j) ≤ A ∧ ‖s.h t i i‖ ≤ A * Real.sqrt t ∧
        |s.q i - s.p i| ≤ A * power t beta) ∧
      (∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤ A * power t (delta / 2)) := by
  obtain ⟨A, hA, tA, htA, hF⟩ := analytic_prestate_proof C hC
  refine ⟨A, hA, tA, htA, ?_⟩
  intro P _ _ t s Λplus Wstar ht hPre
  let n := Fintype.card P
  let e : Fin n ≃ P := (Fintype.equivFin P).symm
  have hPreFin := prestate_reindex e t C Λplus Wstar s hPre
  obtain ⟨h1, h2, _⟩ := hF n t (State.reindex e s) (formReindex e Λplus)
    (formReindex e Wstar) ht hPreFin
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨_, hq, hrow, hdiag⟩ := h1 (e.symm i)
    refine ⟨?_, ?_, ?_⟩
    · have hsum : ∑ j, (State.reindex e s).F t (e.symm i) j = ∑ j, s.F t i j := by
        rw [State.reindex_F]
        simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
        exact Fintype.sum_equiv e _ _ (fun _ => rfl)
      linarith
    · have heq : (State.reindex e s).h t (e.symm i) (e.symm i) = s.h t i i := by
        rw [State.reindex_h]; simp
      rw [heq] at hdiag; exact hdiag
    · simpa [State.reindex, State.q, State.p] using hq
  · intro i
    have h := h2 (e.symm i)
    rw [State.reindex_diagonal_h, norm_submatrix_equiv] at h
    simpa using h

lemma exists_small_beta (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ t1 > 0, ∀ t, 0 < t → t < t1 → K * power t beta ≤ ε := by
  have hβ : 0 < S45.beta := by norm_num [S45.beta, delta]
  refine ⟨(ε / K) ^ S45.beta⁻¹, by positivity, ?_⟩
  intro t ht htl
  have hle : power t beta ≤ ((ε / K) ^ S45.beta⁻¹) ^ S45.beta :=
    Real.rpow_le_rpow ht.le htl.le hβ.le
  rw [Real.rpow_inv_rpow (by positivity) hβ.ne'] at hle
  calc K * power t beta ≤ K * (ε / K) := mul_le_mul_of_nonneg_left hle hK.le
    _ = ε := by field_simp

lemma t_le_power_beta {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : t ≤ power t beta := by
  have h1 := t_le_sqrt_mul_power_beta ht ht1
  have h2 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
  have h3 : 0 ≤ power t beta := Real.rpow_nonneg ht.le _
  nlinarith

lemma cx_bounds {P : Type*} [Fintype P] [DecidableEq P]
    (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hC : 1 ≤ C) (hsmall : C * power t beta ≤ 1 / 2)
    (hsmallq : 2 * (1 + C ^ 2) * power t beta ≤ 1 / (4 * C))
    (hsmallt : C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≤ 1 / (4 * C))
    (hp : Prestate t C Λplus Wstar s) (x : P) :
    0 ≤ cx t s x ∧ cx t s x ≤ 2 * C ^ 2 := by
  have hden := deletion_denominator_lower_of_prestate t C Λplus Wstar s hC
    hsmall hsmallq hsmallt hp x
  have hCpos : 0 < C := by linarith
  have hdpos : 0 < s.q x - s.p x * s.F t x x :=
    lt_of_lt_of_le (by positivity) hden
  have hpNon : 0 ≤ s.p x := by
    have hinv : 0 < 1 / C := by positivity
    linarith [(hp.broad x).2.1]
  have hrecip : 1 / (s.q x - s.p x * s.F t x x) ≤ 2 * C := by
    rw [div_le_iff₀ hdpos]
    have hmul := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 2 * C)
    have hleft : (2 * C) * (1 / (2 * C)) = 1 := by
      field_simp [ne_of_gt hCpos]
    linarith
  refine ⟨div_nonneg hpNon hdpos.le, ?_⟩
  unfold cx
  calc
    s.p x / (s.q x - s.p x * s.F t x x) =
        s.p x * (1 / (s.q x - s.p x * s.F t x x)) := by ring
    _ ≤ C * (2 * C) :=
      mul_le_mul (hp.broad x).2.2 hrecip (by positivity) hCpos.le
    _ = 2 * C ^ 2 := by ring

end Analytic

section Pointwise

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The vector `u^i_j = p_j (f_i - f_j) conj(h_ij)` of the linear output stack. -/
def ubar (t : ℝ) (s : State P) (f : P → ℝ) (i : P) : P → ℂ :=
  fun j => ((s.p j * (f i - f j) : ℝ) : ℂ) * star (s.h t i j)

lemma laplacian_mulVec_eq_sum (c : RMat P) (f : P → ℝ) (i : P) :
    (laplacian c *ᵥ f) i = ∑ j, c i j * (f i - f j) := by
  rw [laplacian_mulVec_eq_sum_diff]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

omit [Fintype P] [DecidableEq P] in
lemma F_eq_norm_sq (t : ℝ) (s : State P) (i j : P) : s.F t i j = ‖s.h t i j‖ ^ 2 := rfl

omit [Fintype P] [DecidableEq P] in
lemma F_nonneg (t : ℝ) (s : State P) (i j : P) : 0 ≤ s.F t i j := by
  rw [F_eq_norm_sq]; positivity

lemma sum_ite_ne_eq_sub {M : Type*} [AddCommGroup M] (φ : P → M) (x : P) :
    (∑ j, if j = x then 0 else φ j) = (∑ j, φ j) - φ x := by
  have h : ∀ j, φ j = (if j = x then 0 else φ j) + (if j = x then φ j else 0) := by
    intro j; by_cases hj : j = x <;> simp [hj]
  have hs : (∑ j, φ j) = (∑ j, if j = x then 0 else φ j) +
      ∑ j, (if j = x then φ j else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => h j)
  rw [hs]; simp

/-- Pointwise output bound for a Laplacian increment with coefficients
`|a| ≤ G`, `|b| ≤ K` (04-sweep.tex, linear output and quadratic output). -/
lemma edge_output_bound (t C G K : ℝ) (s : State P) (x : P) (a : ℂ) (b : ℝ)
    (f : P → ℝ) (i : P) (hC : 0 ≤ C) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hp0 : ∀ i, 0 ≤ s.p i) (hpC : ∀ i, s.p i ≤ C)
    (ha : ‖a‖ ≤ G) (hb : |b| ≤ K) :
    |(laplacian (edgeG t s x a b) *ᵥ f) i| ≤
      2 * C * G * (‖s.h t i x‖ * ‖(s.h t *ᵥ ubar t s f i) x‖) +
      2 * C ^ 2 * G * ‖s.h t x x‖ * (s.F t i x * |f i - f x|) +
      C ^ 2 * K * (s.F t i x * ∑ j, s.F t x j * |f i - f j|) := by
  classical
  have hF := F_nonneg t s
  have hR0 : 0 ≤ 2 * C * G * (‖s.h t i x‖ * ‖(s.h t *ᵥ ubar t s f i) x‖) +
      2 * C ^ 2 * G * ‖s.h t x x‖ * (s.F t i x * |f i - f x|) +
      C ^ 2 * K * (s.F t i x * ∑ j, s.F t x j * |f i - f j|) := by
    have : 0 ≤ ∑ j, s.F t x j * |f i - f j| :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hF x j) (abs_nonneg _))
    have := hF i x
    positivity
  rw [laplacian_mulVec_eq_sum]
  by_cases hi : i = x
  · have hz : ∀ j, edgeG t s x a b i j = 0 := by
      intro j; simp [edgeG, hi]
    simp only [hz, zero_mul, Finset.sum_const_zero, abs_zero]
    exact hR0
  -- split into linear and quadratic parts
  let W : ℂ := ∑ j, if j = x then 0 else s.h t x j * ubar t s f i j
  let T2 : P → ℝ := fun j => if j = x then 0 else
    s.p i * s.p j * b * s.F t i x * s.F t x j * (f i - f j)
  have hterm : ∀ j, edgeG t s x a b i j * (f i - f j) =
      (-2 * s.p i) * (a * s.h t i x *
        (if j = x then 0 else s.h t x j * ubar t s f i j)).re + T2 j := by
    intro j
    by_cases hj : j = x
    · simp [edgeG, hj, T2]
    · simp only [edgeG, ne_eq, hi, not_false_eq_true, hj, and_self, if_true, if_false, T2]
      have hc : a * s.h t i x * (s.h t x j * ubar t s f i j) =
          ((s.p j * (f i - f j) : ℝ) : ℂ) *
            (a * star (s.h t i j) * s.h t i x * s.h t x j) := by
        simp only [ubar]; ring
      rw [hc, Complex.re_ofReal_mul]
      ring
  have hsum : (∑ j, edgeG t s x a b i j * (f i - f j)) =
      (-2 * s.p i) * (a * s.h t i x * W).re + ∑ j, T2 j := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
    congr 1
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum]
  rw [hsum]
  -- linear part
  have hWeq : W = (s.h t *ᵥ ubar t s f i) x - s.h t x x * ubar t s f i x := by
    simp only [W]
    rw [sum_ite_ne_eq_sub (fun j => s.h t x j * ubar t s f i j) x]
    rfl
  have hux : ‖ubar t s f i x‖ ≤ C * |f i - f x| * ‖s.h t i x‖ := by
    simp only [ubar, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
    rw [abs_of_nonneg (hp0 x)]
    have := hpC x
    have : 0 ≤ |f i - f x| * ‖s.h t i x‖ := by positivity
    nlinarith
  have hW : ‖W‖ ≤ ‖(s.h t *ᵥ ubar t s f i) x‖ +
      ‖s.h t x x‖ * (C * |f i - f x| * ‖s.h t i x‖) := by
    rw [hWeq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    gcongr
  have hlin : |(-2 * s.p i) * (a * s.h t i x * W).re| ≤
      2 * C * G * (‖s.h t i x‖ * ‖(s.h t *ᵥ ubar t s f i) x‖) +
      2 * C ^ 2 * G * ‖s.h t x x‖ * (s.F t i x * |f i - f x|) := by
    have h1 : |(a * s.h t i x * W).re| ≤ G * ‖s.h t i x‖ * ‖W‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul]
      gcongr
    rw [abs_mul, abs_of_nonpos (by linarith [hp0 i] : -2 * s.p i ≤ 0)]
    have hFix : s.F t i x = ‖s.h t i x‖ ^ 2 := rfl
    have hpi := hpC i
    have hn1 : 0 ≤ ‖s.h t i x‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖s.h t x x‖ := norm_nonneg _
    have hn3 : 0 ≤ ‖(s.h t *ᵥ ubar t s f i) x‖ := norm_nonneg _
    have hW0 : 0 ≤ ‖W‖ := norm_nonneg _
    have hd : 0 ≤ |f i - f x| := abs_nonneg _
    calc -(-2 * s.p i) * |(a * s.h t i x * W).re|
        ≤ (2 * C) * (G * ‖s.h t i x‖ * (‖(s.h t *ᵥ ubar t s f i) x‖ +
            ‖s.h t x x‖ * (C * |f i - f x| * ‖s.h t i x‖))) := by
          apply mul_le_mul (by linarith) (h1.trans ?_) (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by rw [hFix]; ring
  -- quadratic part
  have hquad : |∑ j, T2 j| ≤ C ^ 2 * K * (s.F t i x * ∑ j, s.F t x j * |f i - f j|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = x
    · simp only [T2, hj, if_true, abs_zero]
      have := hF i x; have := hF x x
      positivity
    · simp only [T2, hj, if_false]
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hp0 i),
        abs_of_nonneg (hp0 j), abs_of_nonneg (hF i x), abs_of_nonneg (hF x j)]
      have h1 : s.p i * s.p j ≤ C ^ 2 := by
        nlinarith [hp0 i, hp0 j, hpC i, hpC j]
      have := hF i x; have := hF x j
      have hd := abs_nonneg (f i - f j)
      calc s.p i * s.p j * |b| * s.F t i x * s.F t x j * |f i - f j|
          = (s.p i * s.p j) * |b| * (s.F t i x * (s.F t x j * |f i - f j|)) := by ring
        _ ≤ C ^ 2 * K * (s.F t i x * (s.F t x j * |f i - f j|)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul h1 hb (abs_nonneg _) (by positivity)
  calc |(-2 * s.p i) * (a * s.h t i x * W).re + ∑ j, T2 j|
      ≤ |(-2 * s.p i) * (a * s.h t i x * W).re| + |∑ j, T2 j| := abs_add_le _ _
    _ ≤ _ := by linarith [hlin, hquad]

end Pointwise

section Generic

variable {P : Type*} [Fintype P]

/-- Unweighted energy `E(f) = Σ_i Σ_j F_ij (f_i - f_j)^2`. -/
def energyF (F : P → P → ℝ) (f : P → ℝ) : ℝ := ∑ i, ∑ j, F i j * (f i - f j) ^ 2

lemma energyF_nonneg (F : P → P → ℝ) (hF : ∀ i j, 0 ≤ F i j) (f : P → ℝ) :
    0 ≤ energyF F f :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hF i j) (sq_nonneg _)

lemma energyF_swap (F : P → P → ℝ) (f : P → ℝ) :
    (∑ x, ∑ i, F i x * (f i - f x) ^ 2) = energyF F f := by
  unfold energyF; rw [Finset.sum_comm]

lemma col_sum_le (F : P → P → ℝ) (hsym : ∀ i j, F i j = F j i) (A : ℝ)
    (hrow : ∀ i, (∑ j, F i j) ≤ A) (x : P) : (∑ i, F i x) ≤ A := by
  calc (∑ i, F i x) = ∑ i, F x i := Finset.sum_congr rfl (fun i _ => hsym i x)
    _ ≤ A := hrow x

/-- Weighted Cauchy–Schwarz: `(Σ w a)^2 ≤ (Σ w)(Σ w a^2)` for `w ≥ 0`. -/
lemma wcs (w a : P → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * a i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * a i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact hw i
  · intro i _; exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i _; nlinarith [hw i, sq_nonneg (a i)]

lemma sq_diff_split (a b c : ℝ) : (a - c) ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * (b - c) ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b + c)]

/-- Splitting a difference through the pivot `x`. -/
lemma pivot_split (W F : P → P → ℝ) (hW : ∀ x i, 0 ≤ W x i) (hF : ∀ i j, 0 ≤ F i j)
    (f : P → ℝ) :
    (∑ x, ∑ i, ∑ j, W x i * F x j * (f i - f j) ^ 2) ≤
      2 * (∑ x, ∑ i, W x i * (∑ j, F x j) * (f i - f x) ^ 2) +
      2 * (∑ x, (∑ i, W x i) * ∑ j, F x j * (f x - f j) ^ 2) := by
  have h1 : (∑ x, ∑ i, ∑ j, W x i * F x j * (f i - f j) ^ 2) ≤
      ∑ x, ∑ i, ∑ j, (2 * (W x i * F x j * (f i - f x) ^ 2) +
        2 * (W x i * F x j * (f x - f j) ^ 2)) := by
    gcongr with x _ i _ j _
    have := mul_nonneg (hW x i) (hF x j)
    nlinarith [sq_diff_split (f i) (f x) (f j)]
  refine h1.trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 2
  · apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, Finset.sum_mul]
  · apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring

lemma abs_sum_mul_le (F : P → P → ℝ) (hF : ∀ i j, 0 ≤ F i j) (A : ℝ)
    (hrow : ∀ i, (∑ j, F i j) ≤ A) (f : P → ℝ) (x i : P) :
    (∑ j, F x j * |f i - f j|) ^ 2 ≤ A * ∑ j, F x j * (f i - f j) ^ 2 := by
  have h := wcs (F x) (fun j => |f i - f j|) (hF x)
  simp only [sq_abs] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (hrow x)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hF x j) (sq_nonneg _))

/-- Quadratic output stack in `ℓ²`: `Σ_{x,i} Q_{xi}^2 ≤ 4 A² ε E`. -/
lemma Q_l2_stack (F : P → P → ℝ) (hF : ∀ i j, 0 ≤ F i j) (hsym : ∀ i j, F i j = F j i)
    (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε) (hrow : ∀ i, (∑ j, F i j) ≤ A)
    (hmax : ∀ i j, F i j ≤ ε) (f : P → ℝ) :
    (∑ x, ∑ i, (F i x * ∑ j, F x j * |f i - f j|) ^ 2) ≤ 4 * A ^ 2 * ε * energyF F f := by
  have hE := energyF_nonneg F hF f
  have step1 : (∑ x, ∑ i, (F i x * ∑ j, F x j * |f i - f j|) ^ 2) ≤
      A * ∑ x, ∑ i, ∑ j, F i x ^ 2 * F x j * (f i - f j) ^ 2 := by
    rw [Finset.mul_sum]
    gcongr with x _
    rw [Finset.mul_sum]
    gcongr with i _
    rw [mul_pow]
    have := abs_sum_mul_le F hF A hrow f x i
    calc F i x ^ 2 * (∑ j, F x j * |f i - f j|) ^ 2
        ≤ F i x ^ 2 * (A * ∑ j, F x j * (f i - f j) ^ 2) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = A * ∑ j, F i x ^ 2 * F x j * (f i - f j) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
  have hW : ∀ x i, 0 ≤ F i x ^ 2 := fun _ _ => sq_nonneg _
  have step2 := pivot_split (fun x i => F i x ^ 2) F hW hF f
  have hA1 : (∑ x, ∑ i, F i x ^ 2 * (∑ j, F x j) * (f i - f x) ^ 2) ≤
      A * ε * energyF F f := by
    rw [← energyF_swap, Finset.mul_sum]
    gcongr with x _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    have h1 : F i x ^ 2 ≤ ε * F i x := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hmax i x) (hF i x)
    have h2 := hrow x
    have h3 : 0 ≤ ∑ j, F x j := Finset.sum_nonneg fun j _ => hF x j
    have h4 := hF i x
    calc F i x ^ 2 * (∑ j, F x j) * (f i - f x) ^ 2
        ≤ (ε * F i x) * A * (f i - f x) ^ 2 := by
          gcongr
      _ = A * ε * (F i x * (f i - f x) ^ 2) := by ring
  have hA2 : (∑ x, (∑ i, F i x ^ 2) * ∑ j, F x j * (f x - f j) ^ 2) ≤
      A * ε * energyF F f := by
    unfold energyF
    rw [Finset.mul_sum]
    gcongr with x _
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hF x j) (sq_nonneg _)
    · calc (∑ i, F i x ^ 2) ≤ ∑ i, ε * F i x := by
            gcongr with i _
            rw [sq]; exact mul_le_mul_of_nonneg_right (hmax i x) (hF i x)
        _ = ε * ∑ i, F i x := by rw [Finset.mul_sum]
        _ ≤ ε * A := mul_le_mul_of_nonneg_left (col_sum_le F hsym A hrow x) hε
        _ = A * ε := by ring
  calc _ ≤ A * ∑ x, ∑ i, ∑ j, F i x ^ 2 * F x j * (f i - f j) ^ 2 := step1
    _ ≤ A * (2 * (A * ε * energyF F f) + 2 * (A * ε * energyF F f)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact step2.trans (by linarith)
    _ = 4 * A ^ 2 * ε * energyF F f := by ring

/-- Quadratic output stack in squared `ℓ¹`: `Σ_x (Σ_i Q_{xi})^2 ≤ 4 A³ E`. -/
lemma Q_l1_stack (F : P → P → ℝ) (hF : ∀ i j, 0 ≤ F i j) (hsym : ∀ i j, F i j = F j i)
    (A : ℝ) (hA : 0 ≤ A) (hrow : ∀ i, (∑ j, F i j) ≤ A) (f : P → ℝ) :
    (∑ x, (∑ i, F i x * ∑ j, F x j * |f i - f j|) ^ 2) ≤ 4 * A ^ 3 * energyF F f := by
  have hE := energyF_nonneg F hF f
  have step1 : (∑ x, (∑ i, F i x * ∑ j, F x j * |f i - f j|) ^ 2) ≤
      A ^ 2 * ∑ x, ∑ i, ∑ j, F i x * F x j * (f i - f j) ^ 2 := by
    rw [Finset.mul_sum]
    gcongr with x _
    have h := wcs (fun i => F i x) (fun i => ∑ j, F x j * |f i - f j|) (fun i => hF i x)
    refine h.trans ?_
    have hc := col_sum_le F hsym A hrow x
    have hin : (∑ i, F i x * (∑ j, F x j * |f i - f j|) ^ 2) ≤
        A * ∑ i, ∑ j, F i x * F x j * (f i - f j) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      calc F i x * (∑ j, F x j * |f i - f j|) ^ 2
          ≤ F i x * (A * ∑ j, F x j * (f i - f j) ^ 2) :=
            mul_le_mul_of_nonneg_left (abs_sum_mul_le F hF A hrow f x i) (hF i x)
        _ = A * ∑ j, F i x * F x j * (f i - f j) ^ 2 := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring
    have hnn : 0 ≤ ∑ i, F i x * (∑ j, F x j * |f i - f j|) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hF i x) (sq_nonneg _)
    calc (∑ i, F i x) * ∑ i, F i x * (∑ j, F x j * |f i - f j|) ^ 2
        ≤ A * (A * ∑ i, ∑ j, F i x * F x j * (f i - f j) ^ 2) :=
          mul_le_mul hc hin hnn hA
      _ = A ^ 2 * ∑ i, ∑ j, F i x * F x j * (f i - f j) ^ 2 := by ring
  have step2 := pivot_split (fun x i => F i x) F (fun x i => hF i x) hF f
  have hA1 : (∑ x, ∑ i, F i x * (∑ j, F x j) * (f i - f x) ^ 2) ≤ A * energyF F f := by
    rw [← energyF_swap, Finset.mul_sum]
    gcongr with x _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    have := hF i x
    calc F i x * (∑ j, F x j) * (f i - f x) ^ 2 ≤ F i x * A * (f i - f x) ^ 2 := by
          gcongr; exact hrow x
      _ = A * (F i x * (f i - f x) ^ 2) := by ring
  have hA2 : (∑ x, (∑ i, F i x) * ∑ j, F x j * (f x - f j) ^ 2) ≤ A * energyF F f := by
    unfold energyF
    rw [Finset.mul_sum]
    gcongr with x _
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hF x j) (sq_nonneg _)
    · exact col_sum_le F hsym A hrow x
  calc _ ≤ A ^ 2 * ∑ x, ∑ i, ∑ j, F i x * F x j * (f i - f j) ^ 2 := step1
    _ ≤ A ^ 2 * (2 * (A * energyF F f) + 2 * (A * energyF F f)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
        exact step2.trans (by linarith)
    _ = 4 * A ^ 3 * energyF F f := by ring

end Generic

section Stacks

variable {P : Type*} [Fintype P] [DecidableEq P]

lemma l2sq_mulVec_le_opNorm_sq' (A : CMat P) (u : P → ℂ) :
    l2sq (A *ᵥ u) ≤ ‖A‖ ^ 2 * l2sq u := by
  have hnormSq (x : P → ℂ) : ‖WithLp.toLp 2 x‖ ^ 2 = l2sq x := by
    rw [PiLp.norm_eq_of_L2]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (‖x i‖))]
    rfl
  have hnorm : ‖WithLp.toLp 2 (A *ᵥ u)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 u‖ := by
    have h :=
      (Matrix.toEuclideanCLM (n := P) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 u)
    simpa [Matrix.toEuclideanCLM_toLp, Matrix.l2_opNorm_toEuclideanCLM] using h
  calc
    l2sq (A *ᵥ u) = ‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 := (hnormSq _).symm
    _ ≤ (‖A‖ * ‖WithLp.toLp 2 u‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    _ = ‖A‖ ^ 2 * l2sq u := by rw [mul_pow, hnormSq]

lemma ubar_l2sq_le (t C : ℝ) (s : State P) (f : P → ℝ) (i : P)
    (hp0 : ∀ i, 0 ≤ s.p i) (hpC : ∀ i, s.p i ≤ C) :
    l2sq (ubar t s f i) ≤ C ^ 2 * ∑ j, s.F t i j * (f i - f j) ^ 2 := by
  unfold l2sq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  simp only [ubar, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
  rw [F_eq_norm_sq, mul_pow, mul_pow, sq_abs, sq_abs]
  have hpj : s.p j ^ 2 ≤ C ^ 2 := by
    have := hp0 j; have := hpC j; nlinarith
  have : 0 ≤ (f i - f j) ^ 2 * ‖s.h t i j‖ ^ 2 := by positivity
  nlinarith

lemma diag_mul_mulVec_apply (v : P → ℂ) (M : CMat P) (u : P → ℂ) (x : P) :
    ((diagonal v * M) *ᵥ u) x = v x * (M *ᵥ u) x := by
  rw [← Matrix.mulVec_mulVec, mulVec_diagonal]

/-- Linear output stack, `ℓ²` part (TeX eq. sweep-laplacian-linear-two). -/
lemma linear_l2_stack (t C Bop : ℝ) (s : State P) (f : P → ℝ)
    (hp0 : ∀ i, 0 ≤ s.p i) (hpC : ∀ i, s.p i ≤ C)
    (hop : ∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤ Bop) :
    (∑ x, ∑ i, (‖s.h t i x‖ * ‖(s.h t *ᵥ ubar t s f i) x‖) ^ 2) ≤
      Bop * C ^ 2 * energyF (s.F t) f := by
  rw [Finset.sum_comm]
  unfold energyF
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have hrow : (∑ x, (‖s.h t i x‖ * ‖(s.h t *ᵥ ubar t s f i) x‖) ^ 2) =
      l2sq ((diagonal (s.h t i) * s.h t) *ᵥ ubar t s f i) := by
    unfold l2sq
    apply Finset.sum_congr rfl; intro x _
    rw [diag_mul_mulVec_apply, norm_mul]
  rw [hrow]
  have hB : 0 ≤ Bop := le_trans (sq_nonneg _) (hop i)
  calc l2sq ((diagonal (s.h t i) * s.h t) *ᵥ ubar t s f i)
      ≤ ‖diagonal (s.h t i) * s.h t‖ ^ 2 * l2sq (ubar t s f i) :=
        l2sq_mulVec_le_opNorm_sq' _ _
    _ ≤ Bop * (C ^ 2 * ∑ j, s.F t i j * (f i - f j) ^ 2) :=
        mul_le_mul (hop i) (ubar_l2sq_le t C s f i hp0 hpC)
          (Finset.sum_nonneg fun j _ => sq_nonneg _) hB
    _ = Bop * C ^ 2 * ∑ j, s.F t i j * (f i - f j) ^ 2 := by ring

/-- Linear output stack, squared `ℓ¹` part. -/
lemma linear_l1_stack (t C A Hn : ℝ) (s : State P) (f : P → ℝ)
    (hp0 : ∀ i, 0 ≤ s.p i) (hpC : ∀ i, s.p i ≤ C) (hA : 0 ≤ A)
    (hcol : ∀ x, (∑ i, s.F t i x) ≤ A) (hh : ‖s.h t‖ ≤ Hn) :
    (∑ x, (∑ i, ‖s.h t i x‖ * ‖(s.h t *ᵥ ubar t s f i) x‖) ^ 2) ≤
      A * Hn ^ 2 * C ^ 2 * energyF (s.F t) f := by
  have step1 : (∑ x, (∑ i, ‖s.h t i x‖ * ‖(s.h t *ᵥ ubar t s f i) x‖) ^ 2) ≤
      A * ∑ i, l2sq (s.h t *ᵥ ubar t s f i) := by
    unfold l2sq
    rw [Finset.sum_comm (f := fun i x => ‖(s.h t *ᵥ ubar t s f i) x‖ ^ 2), Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    exact le_of_eq_of_le (Finset.sum_congr rfl fun i _ => (F_eq_norm_sq t s i x).symm) (hcol x)
  refine step1.trans ?_
  unfold energyF
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have hHn : 0 ≤ Hn := le_trans (norm_nonneg _) hh
  calc A * l2sq (s.h t *ᵥ ubar t s f i)
      ≤ A * (‖s.h t‖ ^ 2 * l2sq (ubar t s f i)) :=
        mul_le_mul_of_nonneg_left (l2sq_mulVec_le_opNorm_sq' _ _) hA
    _ ≤ A * (Hn ^ 2 * (C ^ 2 * ∑ j, s.F t i j * (f i - f j) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hh 2)
          (ubar_l2sq_le t C s f i hp0 hpC) (Finset.sum_nonneg fun j _ => sq_nonneg _)
          (sq_nonneg _)
    _ = A * Hn ^ 2 * C ^ 2 * ∑ j, s.F t i j * (f i - f j) ^ 2 := by ring

omit [DecidableEq P] in
lemma beta_l2_stack (F : P → P → ℝ) (hF : ∀ i j, 0 ≤ F i j) (ε : ℝ)
    (hmax : ∀ i j, F i j ≤ ε) (f : P → ℝ) :
    (∑ x, ∑ i, (F i x * |f i - f x|) ^ 2) ≤ ε * energyF F f := by
  rw [← energyF_swap, Finset.mul_sum]
  apply Finset.sum_le_sum; intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [mul_pow, sq_abs, sq]
  have := hF i x
  have := mul_le_mul_of_nonneg_right (hmax i x) (hF i x)
  nlinarith [sq_nonneg (f i - f x)]

omit [DecidableEq P] in
lemma beta_l1_stack (F : P → P → ℝ) (hF : ∀ i j, 0 ≤ F i j) (A : ℝ)
    (hcol : ∀ x, (∑ i, F i x) ≤ A) (f : P → ℝ) :
    (∑ x, (∑ i, F i x * |f i - f x|) ^ 2) ≤ A * energyF F f := by
  rw [← energyF_swap, Finset.mul_sum]
  apply Finset.sum_le_sum; intro x _
  have h := wcs (fun i => F i x) (fun i => |f i - f x|) (fun i => hF i x)
  simp only [sq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hcol x)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hF i x) (sq_nonneg _)))

lemma sq_add3_le (u v w : ℝ) : (u + v + w) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (u - w)]

end Stacks

section DetStacks

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Deterministic `ℓ²` and squared `ℓ¹` stacks of the Laplacian outputs for
arbitrary coefficients at the hypothetical pivots (04-sweep.tex, "linear
output stacks" and "quadratic output stacks"). -/
lemma det_stacks (t C G K A Hd Hn Bop ε : ℝ) (s : State P) (S : Finset P)
    (a : P → ℂ) (b : P → ℝ) (f : P → ℝ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 ≤ ε) (hHd : 0 ≤ Hd)
    (hp0 : ∀ i, 0 ≤ s.p i) (hpC : ∀ i, s.p i ≤ C)
    (hhsym : ∀ i j, s.h t j i = s.h t i j)
    (hrow : ∀ i, (∑ j, s.F t i j) ≤ A) (hdiag : ∀ x, ‖s.h t x x‖ ≤ Hd)
    (hop : ∀ i, ‖diagonal (s.h t i) * s.h t‖ ^ 2 ≤ Bop) (hh : ‖s.h t‖ ≤ Hn)
    (hmax : ∀ i j, s.F t i j ≤ ε)
    (ha : ∀ x ∈ S, ‖a x‖ ≤ G) (hb : ∀ x ∈ S, |b x| ≤ K) :
    (∑ x ∈ S, l2sq (laplacian (edgeG t s x (a x) (b x)) *ᵥ f)) ≤
      3 * ((2 * C * G) ^ 2 * (Bop * C ^ 2) + (2 * C ^ 2 * G * Hd) ^ 2 * ε +
        (C ^ 2 * K) ^ 2 * (4 * A ^ 2 * ε)) * energyF (s.F t) f ∧
    (∑ x ∈ S, l1 (laplacian (edgeG t s x (a x) (b x)) *ᵥ f) ^ 2) ≤
      3 * ((2 * C * G) ^ 2 * (A * Hn ^ 2 * C ^ 2) + (2 * C ^ 2 * G * Hd) ^ 2 * A +
        (C ^ 2 * K) ^ 2 * (4 * A ^ 3)) * energyF (s.F t) f := by
  classical
  have hF := F_nonneg t s
  have hFsym : ∀ i j, s.F t i j = s.F t j i := by
    intro i j; rw [F_eq_norm_sq, F_eq_norm_sq, hhsym]
  have hcol := col_sum_le (s.F t) hFsym A hrow
  set k1 := 2 * C * G with hk1
  set k2 := 2 * C ^ 2 * G * Hd with hk2
  set k3 := C ^ 2 * K with hk3
  let α : P → P → ℝ := fun x i => ‖s.h t i x‖ * ‖(s.h t *ᵥ ubar t s f i) x‖
  let β : P → P → ℝ := fun x i => s.F t i x * |f i - f x|
  let Q : P → P → ℝ := fun x i => s.F t i x * ∑ j, s.F t x j * |f i - f j|
  have hα : ∀ x i, 0 ≤ α x i := fun x i => by positivity
  have hβ : ∀ x i, 0 ≤ β x i := fun x i => mul_nonneg (hF i x) (abs_nonneg _)
  have hQ : ∀ x i, 0 ≤ Q x i := fun x i =>
    mul_nonneg (hF i x) (Finset.sum_nonneg fun j _ => mul_nonneg (hF x j) (abs_nonneg _))
  have hk1n : 0 ≤ k1 := by positivity
  have hk2n : 0 ≤ k2 := by positivity
  have hk3n : 0 ≤ k3 := by positivity
  have hpt : ∀ x ∈ S, ∀ i, |(laplacian (edgeG t s x (a x) (b x)) *ᵥ f) i| ≤
      k1 * α x i + k2 * β x i + k3 * Q x i := by
    intro x hx i
    have h := edge_output_bound t C G K s x (a x) (b x) f i hC hG hK hp0 hpC (ha x hx) (hb x hx)
    have h2 : 2 * C ^ 2 * G * ‖s.h t x x‖ * (s.F t i x * |f i - f x|) ≤ k2 * β x i := by
      have := hβ x i
      have : 2 * C ^ 2 * G * ‖s.h t x x‖ ≤ k2 := by
        rw [hk2]; gcongr; exact hdiag x
      exact mul_le_mul_of_nonneg_right this (hβ x i)
    simp only [α, Q, hk1, hk3] at h ⊢
    linarith
  have hE := energyF_nonneg (s.F t) hF f
  constructor
  · have step : (∑ x ∈ S, l2sq (laplacian (edgeG t s x (a x) (b x)) *ᵥ f)) ≤
        ∑ x, ∑ i, 3 * (k1 ^ 2 * α x i ^ 2 + k2 ^ 2 * β x i ^ 2 + k3 ^ 2 * Q x i ^ 2) := by
      refine le_trans ?_ (Finset.sum_le_univ_sum_of_nonneg (s := S) fun x => Finset.sum_nonneg
        fun i _ => by positivity)
      apply Finset.sum_le_sum; intro x hx
      unfold l2sq
      apply Finset.sum_le_sum; intro i _
      rw [Real.norm_eq_abs, ← sq_abs (|_|), abs_abs]
      have h := hpt x hx i
      calc |(laplacian (edgeG t s x (a x) (b x)) *ᵥ f) i| ^ 2
          ≤ (k1 * α x i + k2 * β x i + k3 * Q x i) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h 2
        _ ≤ 3 * ((k1 * α x i) ^ 2 + (k2 * β x i) ^ 2 + (k3 * Q x i) ^ 2) := sq_add3_le _ _ _
        _ = 3 * (k1 ^ 2 * α x i ^ 2 + k2 ^ 2 * β x i ^ 2 + k3 ^ 2 * Q x i ^ 2) := by ring
    have hexp : (∑ x, ∑ i, 3 * (k1 ^ 2 * α x i ^ 2 + k2 ^ 2 * β x i ^ 2 + k3 ^ 2 * Q x i ^ 2)) =
        3 * (k1 ^ 2 * (∑ x, ∑ i, α x i ^ 2) + k2 ^ 2 * (∑ x, ∑ i, β x i ^ 2) +
          k3 ^ 2 * (∑ x, ∑ i, Q x i ^ 2)) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    have h1 := linear_l2_stack t C Bop s f hp0 hpC hop
    have h2 := beta_l2_stack (s.F t) hF ε hmax f
    have h3 := Q_l2_stack (s.F t) hF hFsym A ε hA hε hrow hmax f
    refine step.trans (le_of_eq_of_le hexp ?_)
    have e : 3 * (k1 ^ 2 * (Bop * C ^ 2) + k2 ^ 2 * ε + k3 ^ 2 * (4 * A ^ 2 * ε)) *
        energyF (s.F t) f = 3 * (k1 ^ 2 * (Bop * C ^ 2 * energyF (s.F t) f) +
          k2 ^ 2 * (ε * energyF (s.F t) f) + k3 ^ 2 * (4 * A ^ 2 * ε * energyF (s.F t) f)) := by
      ring
    rw [e]
    gcongr
  · have step : (∑ x ∈ S, l1 (laplacian (edgeG t s x (a x) (b x)) *ᵥ f) ^ 2) ≤
        ∑ x, 3 * (k1 ^ 2 * (∑ i, α x i) ^ 2 + k2 ^ 2 * (∑ i, β x i) ^ 2 +
          k3 ^ 2 * (∑ i, Q x i) ^ 2) := by
      refine le_trans ?_ (Finset.sum_le_univ_sum_of_nonneg (s := S) fun x => by positivity)
      apply Finset.sum_le_sum; intro x hx
      have hl1 : l1 (laplacian (edgeG t s x (a x) (b x)) *ᵥ f) ≤
          k1 * (∑ i, α x i) + k2 * (∑ i, β x i) + k3 * (∑ i, Q x i) := by
        unfold l1
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum; intro i _
        rw [Real.norm_eq_abs]
        exact hpt x hx i
      have hl1n : 0 ≤ l1 (laplacian (edgeG t s x (a x) (b x)) *ᵥ f) :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      calc l1 (laplacian (edgeG t s x (a x) (b x)) *ᵥ f) ^ 2
          ≤ (k1 * (∑ i, α x i) + k2 * (∑ i, β x i) + k3 * (∑ i, Q x i)) ^ 2 :=
            pow_le_pow_left₀ hl1n hl1 2
        _ ≤ 3 * ((k1 * (∑ i, α x i)) ^ 2 + (k2 * (∑ i, β x i)) ^ 2 +
            (k3 * (∑ i, Q x i)) ^ 2) := sq_add3_le _ _ _
        _ = _ := by ring
    have hexp : (∑ x, 3 * (k1 ^ 2 * (∑ i, α x i) ^ 2 + k2 ^ 2 * (∑ i, β x i) ^ 2 +
          k3 ^ 2 * (∑ i, Q x i) ^ 2)) =
        3 * (k1 ^ 2 * (∑ x, (∑ i, α x i) ^ 2) + k2 ^ 2 * (∑ x, (∑ i, β x i) ^ 2) +
          k3 ^ 2 * (∑ x, (∑ i, Q x i) ^ 2)) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    have h1 := linear_l1_stack t C A Hn s f hp0 hpC hA hcol hh
    have h2 := beta_l1_stack (s.F t) hF A hcol f
    have h3 := Q_l1_stack (s.F t) hF hFsym A hA hrow f
    refine step.trans (le_of_eq_of_le hexp ?_)
    have e : 3 * (k1 ^ 2 * (A * Hn ^ 2 * C ^ 2) + k2 ^ 2 * A + k3 ^ 2 * (4 * A ^ 3)) *
        energyF (s.F t) f = 3 * (k1 ^ 2 * (A * Hn ^ 2 * C ^ 2 * energyF (s.F t) f) +
          k2 ^ 2 * (A * energyF (s.F t) f) + k3 ^ 2 * (4 * A ^ 3 * energyF (s.F t) f)) := by
      ring
    rw [e]
    gcongr

end DetStacks

section Mean

variable {P : Type*} [Fintype P] [DecidableEq P]

lemma laplacian_lin3 (c1 c2 c3 : RMat P) (r1 r2 r3 : ℝ) :
    laplacian (fun i j => r1 * c1 i j + r2 * c2 i j + r3 * c3 i j) =
      r1 • laplacian c1 + r2 • laplacian c2 + r3 • laplacian c3 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [laplacian, if_true, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    split_ifs <;> ring
  · simp only [laplacian, hij, if_false, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

lemma edgeG_decomp (t : ℝ) (s : State P) (x : P) (a : ℂ) (b : ℝ) :
    edgeG t s x a b = fun i j => a.re * edgeG t s x 1 0 i j +
      a.im * edgeG t s x Complex.I 0 i j + b * edgeG t s x 0 1 i j := by
  ext i j
  unfold edgeG
  split_ifs
  · have h1 : (a * star (s.h t i j) * s.h t i x * s.h t x j).re =
        a.re * (star (s.h t i j) * s.h t i x * s.h t x j).re -
          a.im * (star (s.h t i j) * s.h t i x * s.h t x j).im := by
      rw [show a * star (s.h t i j) * s.h t i x * s.h t x j =
        a * (star (s.h t i j) * s.h t i x * s.h t x j) by ring, Complex.mul_re]
    have h2 : (1 * star (s.h t i j) * s.h t i x * s.h t x j).re =
        (star (s.h t i j) * s.h t i x * s.h t x j).re := by ring_nf
    have h3 : (Complex.I * star (s.h t i j) * s.h t i x * s.h t x j).re =
        -(star (s.h t i j) * s.h t i x * s.h t x j).im := by
      rw [show Complex.I * star (s.h t i j) * s.h t i x * s.h t x j =
        Complex.I * (star (s.h t i j) * s.h t i x * s.h t x j) by ring, Complex.mul_re]
      simp
    have h4 : ((0 : ℂ) * star (s.h t i j) * s.h t i x * s.h t x j).re = 0 := by simp
    rw [h1, h2, h3, h4]
    ring
  · ring

lemma gamma_comp_measurable {Ω : Type*} [MeasurableSpace Ω] (t : ℝ) (s : State P) (x : P)
    (ξ : Ω → ℝ) (hξ : Measurable ξ) : Measurable (fun ω => gamma t s x (ξ ω)) := by
  change Measurable (fun ω =>
    ((ξ ω : ℂ) + t * s.r x) /
      ((Real.sqrt t : ℂ) * (1 + ((ξ ω : ℂ) + t * s.r x) * s.g x x)))
  have hξC : Measurable (fun ω => (ξ ω : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hξ
  have hnum : Measurable (fun ω => (ξ ω : ℂ) + t * s.r x) :=
    hξC.add measurable_const
  have hden : Measurable (fun ω =>
      (Real.sqrt t : ℂ) * (1 + ((ξ ω : ℂ) + t * s.r x) * s.g x x)) :=
    measurable_const.mul (measurable_const.add (hnum.mul measurable_const))
  exact hnum.div hden

/-- The expectation of a Laplacian increment is the increment with the mean
coefficients `μ_x = E γ_x` and `E ρ_x`. -/
lemma integral_Linc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : ℝ) (s : State P) (x : P) (ξ : Ω → ℝ) (hξ : Measurable ξ) (G : ℝ) (hG : 0 ≤ G)
    (hb : ∀ᵐ ω ∂μ, ‖gamma t s x (ξ ω)‖ ≤ G) :
    ∫ ω, Linc t s x (ξ ω) ∂μ = laplacian (edgeG t s x (∫ ω, gamma t s x (ξ ω) ∂μ)
      (∫ ω, (‖gamma t s x (ξ ω)‖ ^ 2 - cx t s x) ∂μ)) := by
  have hγm := gamma_comp_measurable t s x ξ hξ
  have hγi : Integrable (fun ω => gamma t s x (ξ ω)) μ :=
    Integrable.of_bound hγm.aestronglyMeasurable G hb
  have hρi : Integrable (fun ω => ‖gamma t s x (ξ ω)‖ ^ 2 - cx t s x) μ :=
    (integrable_sq_norm_of_ae_bound hG hγm hb).sub (integrable_const _)
  have hrei : Integrable (fun ω => (gamma t s x (ξ ω)).re) μ := hγi.re
  have himi : Integrable (fun ω => (gamma t s x (ξ ω)).im) μ := hγi.im
  let L1 := laplacian (edgeG t s x 1 0)
  let L2 := laplacian (edgeG t s x Complex.I 0)
  let L3 := laplacian (edgeG t s x 0 1)
  have hdec : ∀ (a : ℂ) (b : ℝ), laplacian (edgeG t s x a b) =
      a.re • L1 + a.im • L2 + b • L3 := by
    intro a b
    rw [edgeG_decomp t s x a b, laplacian_lin3]
  have hpt : (fun ω => Linc t s x (ξ ω)) = fun ω =>
      (gamma t s x (ξ ω)).re • L1 + (gamma t s x (ξ ω)).im • L2 +
        (‖gamma t s x (ξ ω)‖ ^ 2 - cx t s x) • L3 := by
    funext ω
    rw [Linc_eq_laplacian_edgeG, hdec]
  rw [hpt, hdec]
  rw [integral_add ?_ (hρi.smul_const L3), integral_add (hrei.smul_const L1)
    (himi.smul_const L2), integral_smul_const, integral_smul_const, integral_smul_const]
  · congr 3
    · exact integral_re hγi
    · exact integral_im hγi
  · exact (hrei.smul_const L1).add (himi.smul_const L2)


lemma qform_add' (A B : RMat P) (f : P → ℝ) : qform (A + B) f = qform A f + qform B f := by
  unfold qform
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.add_mulVec, Pi.add_apply, mul_add]

private lemma qform_finset_sum {ι : Type*} (S : Finset ι) (M : ι → RMat P) (f : P → ℝ) :
    qform (∑ x ∈ S, M x) f = ∑ x ∈ S, qform (M x) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [qform]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, qform_add', ih]

lemma edgeG_symm (t : ℝ) (s : State P) (x : P) (a : ℂ) (b : ℝ)
    (hhsym : ∀ i j, s.h t j i = s.h t i j) : (edgeG t s x a b).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold edgeG
  have hFji : ∀ u v, s.F t u v = s.F t v u := by
    intro u v; rw [F_eq_norm_sq, F_eq_norm_sq, hhsym]
  by_cases hm : i ≠ x ∧ j ≠ x
  · have hm' : j ≠ x ∧ i ≠ x := ⟨hm.2, hm.1⟩
    rw [if_pos hm, if_pos hm']
    have hc : a * star (s.h t i j) * s.h t i x * s.h t x j =
        a * star (s.h t j i) * s.h t j x * s.h t x i := by
      rw [hhsym i j, hhsym j x, hhsym x i]; ring
    rw [hc, hFji i x, hFji x j]
    ring
  · have hm' : ¬ (j ≠ x ∧ i ≠ x) := fun h => hm ⟨h.2, h.1⟩
    rw [if_neg hm, if_neg hm']

end Mean

section Commutator

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Cauchy–Schwarz for the bilinear pairing `Σ_j u_j y_j`. -/
lemma norm_sum_mul_le (u y : P → ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : l2sq u ≤ a ^ 2) (hy : l2sq y ≤ b ^ 2) : ‖∑ j, u j * y j‖ ≤ a * b := by
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖u j‖) (fun j => ‖y j‖)
  have hnn : 0 ≤ ∑ j, ‖u j‖ * ‖y j‖ := Finset.sum_nonneg fun j _ => by positivity
  have hl : (∑ j, ‖u j‖ * ‖y j‖) ^ 2 ≤ (a * b) ^ 2 := by
    refine hcs.trans ?_
    rw [mul_pow]
    exact mul_le_mul hu hy (Finset.sum_nonneg fun j _ => sq_nonneg _) (sq_nonneg _)
  exact (sq_le_sq₀ hnn (by positivity)).1 hl

/-- The p-weighted Hilbert–Schmidt commutator estimate for the signed linear
mean, with all intermediate indices included (04-sweep.tex, "The sum of the
means"). -/
lemma lin_main (t C m Hn : ℝ) (s : State P) (μS : P → ℂ) (f : P → ℝ)
    (hC : 0 ≤ C) (hm : 0 ≤ m) (hHn : 0 ≤ Hn)
    (hp0 : ∀ i, 0 ≤ s.p i) (hpC : ∀ i, s.p i ≤ C)
    (hhsym : ∀ i j, s.h t j i = s.h t i j) (hμ : ∀ x, ‖μS x‖ ≤ m)
    (hh : ‖s.h t‖ ≤ Hn) :
    ‖∑ x, ∑ i, ∑ j, ((s.p i * s.p j * (f i - f j) ^ 2 : ℝ) : ℂ) *
      (μS x * star (s.h t i j) * s.h t i x * s.h t x j)‖ ≤
      2 * C ^ 2 * Hn * m * energyF (s.F t) f := by
  classical
  let W : P → P → P → ℂ := fun x i j => μS x * star (s.h t i j) * s.h t i x * s.h t x j
  let v : P → P → ℂ := fun i x => ((f i - f x : ℝ) : ℂ) * μS x * s.h t i x
  let X1 : ℂ := ∑ x, ∑ i, ∑ j,
    ((s.p i * s.p j * (f i - f j) * (f i - f x) : ℝ) : ℂ) * W x i j
  let X2 : ℂ := ∑ x, ∑ i, ∑ j,
    ((s.p i * s.p j * (f i - f j) * (f x - f j) : ℝ) : ℂ) * W x i j
  have hsplit : (∑ x, ∑ i, ∑ j, ((s.p i * s.p j * (f i - f j) ^ 2 : ℝ) : ℂ) * W x i j) =
      X1 + X2 := by
    simp only [X1, X2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    push_cast; ring
  have hX2 : X2 = X1 := by
    simp only [X1, X2]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [W]
    rw [hhsym j i, hhsym i x, hhsym x j]
    push_cast; ring
  let Term1 : ℂ := ∑ i, (s.p i : ℂ) * ∑ j, ubar t s f i j * (s.h t *ᵥ v i) j
  have hX1 : X1 = Term1 := by
    simp only [X1, Term1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    simp only [W, v, ubar]
    rw [hhsym x j]
    push_cast; ring
  change ‖∑ x, ∑ i, ∑ j, ((s.p i * s.p j * (f i - f j) ^ 2 : ℝ) : ℂ) * W x i j‖ ≤ _
  rw [hsplit, hX2, hX1, ← two_mul]
  have hrow : ∀ i, ‖∑ j, ubar t s f i j * (s.h t *ᵥ v i) j‖ ≤
      C * (Hn * m) * ∑ j, s.F t i j * (f i - f j) ^ 2 := by
    intro i
    have he : 0 ≤ ∑ j, s.F t i j * (f i - f j) ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (F_nonneg t s i j) (sq_nonneg _)
    have hu : l2sq (ubar t s f i) ≤ (C * Real.sqrt (∑ j, s.F t i j * (f i - f j) ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt he]; exact ubar_l2sq_le t C s f i hp0 hpC
    have hv : l2sq (v i) ≤ m ^ 2 * ∑ j, s.F t i j * (f i - f j) ^ 2 := by
      unfold l2sq
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro x _
      simp only [v, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [F_eq_norm_sq, mul_pow, mul_pow, sq_abs]
      have h1 : ‖μS x‖ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hμ x) 2
      have h2 : 0 ≤ (f i - f x) ^ 2 * ‖s.h t i x‖ ^ 2 := by positivity
      nlinarith
    have hy : l2sq (s.h t *ᵥ v i) ≤ (Hn * m * Real.sqrt (∑ j, s.F t i j * (f i - f j) ^ 2)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt he]
      refine (l2sq_mulVec_le_opNorm_sq' _ _).trans ?_
      calc ‖s.h t‖ ^ 2 * l2sq (v i) ≤ Hn ^ 2 * (m ^ 2 * ∑ j, s.F t i j * (f i - f j) ^ 2) :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hh 2) hv
              (Finset.sum_nonneg fun x _ => sq_nonneg _) (sq_nonneg _)
        _ = _ := by ring
    have := norm_sum_mul_le (ubar t s f i) (s.h t *ᵥ v i) _ _ (by positivity) (by positivity) hu hy
    calc _ ≤ _ := this
      _ = C * (Hn * m) * (Real.sqrt (∑ j, s.F t i j * (f i - f j) ^ 2)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt he]
  have hT : ‖Term1‖ ≤ C ^ 2 * Hn * m * energyF (s.F t) f := by
    refine (norm_sum_le _ _).trans ?_
    unfold energyF
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 i)]
    calc s.p i * ‖∑ j, ubar t s f i j * (s.h t *ᵥ v i) j‖
        ≤ C * (C * (Hn * m) * ∑ j, s.F t i j * (f i - f j) ^ 2) :=
          mul_le_mul (hpC i) (hrow i) (norm_nonneg _) hC
      _ = _ := by ring
  rw [norm_mul]
  calc ‖(2 : ℂ)‖ * ‖Term1‖ ≤ 2 * (C ^ 2 * Hn * m * energyF (s.F t) f) := by
        rw [Complex.norm_two]; linarith
    _ = _ := by ring

end Commutator

section MeanBound

variable {P : Type*} [Fintype P] [DecidableEq P]

lemma h_symm_of_prestate (t C : ℝ) (Λplus Wstar : Form P) (s : State P)
    (hp : Prestate t C Λplus Wstar s) : ∀ i j, s.h t j i = s.h t i j := by
  have hh : (s.h t).IsSymm := by
    unfold State.h
    exact hp.symmetric.smul _
  intro i j; exact hh.apply i j

lemma qform_laplacian_edgeG (t : ℝ) (s : State P) (x : P) (a : ℂ) (b : ℝ) (f : P → ℝ)
    (hhsym : ∀ i j, s.h t j i = s.h t i j) :
    qform (laplacian (edgeG t s x a b)) f =
      (∑ i, ∑ j, if i ≠ x ∧ j ≠ x then
        -(s.p i * s.p j * (f i - f j) ^ 2 *
          (a * star (s.h t i j) * s.h t i x * s.h t x j).re) else 0) +
      (1 / 2) * ∑ i, ∑ j, if i ≠ x ∧ j ≠ x then
        s.p i * s.p j * s.F t i x * s.F t x j * b * (f i - f j) ^ 2 else 0 := by
  rw [qform_laplacian_eq_half_sum_diff _ (edgeG_symm t s x a b hhsym), Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  unfold edgeG
  split_ifs <;> ring

/-- Mean estimate (04-sweep.tex eq. sweep-laplacian-mean) for given mean
coefficients `μ_x` (linear) and `rb_x` (quadratic). -/
lemma mean_bound_det (t C A Hd Hn m Kq : ℝ) (Λplus Wstar : Form P) (s : State P)
    (S : Finset P) (μ : P → ℂ) (rb : P → ℝ) (f : P → ℝ)
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hm : 0 ≤ m) (hHn : 0 ≤ Hn) (hKq : 0 ≤ Kq)
    (hp : Prestate t C Λplus Wstar s) (hrow : ∀ i, (∑ j, s.F t i j) ≤ A)
    (hdiag : ∀ x, ‖s.h t x x‖ ≤ Hd) (hh : ‖s.h t‖ ≤ Hn)
    (hμ : ∀ x ∈ S, ‖μ x‖ ≤ m) (hρ : ∀ x ∈ S, |rb x| ≤ Kq) :
    |qform (∑ x ∈ S, laplacian (edgeG t s x (μ x) (rb x))) f| ≤
      (2 * C ^ 2 * Hn * m + 2 * C ^ 2 * m * Hd) * energyF (s.F t) f +
        4 * C ^ 4 * A * Kq * qform (s.D t) f := by
  classical
  have hC0 : 0 ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  have hp0 : ∀ i, 0 ≤ s.p i := fun i => le_trans (by positivity) (hp.broad i).2.1
  have hpC : ∀ i, s.p i ≤ C := fun i => (hp.broad i).2.2
  have hhsym := h_symm_of_prestate t C Λplus Wstar s hp
  have hF := F_nonneg t s
  have hE := energyF_nonneg (s.F t) hF f
  rw [qform_finset_sum]
  simp only [qform_laplacian_edgeG t s _ _ _ f hhsym]
  rw [Finset.sum_add_distrib]
  -- the quadratic part
  have hquad : |∑ x ∈ S, (1 / 2 : ℝ) * ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then
      s.p i * s.p j * s.F t i x * s.F t x j * rb x * (f i - f j) ^ 2 else 0)| ≤
      4 * C ^ 4 * A * Kq * qform (s.D t) f := by
    have hstack := quadratic_edge_stack_le_D t C A Λplus Wstar s S hC hA hrow hp f
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc (∑ x ∈ S, |(1 / 2 : ℝ) * ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then
          s.p i * s.p j * s.F t i x * s.F t x j * rb x * (f i - f j) ^ 2 else 0)|)
        ≤ ∑ x ∈ S, (1 / 2 : ℝ) * (Kq * ∑ i, ∑ j,
            s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2) := by
          apply Finset.sum_le_sum; intro x hx
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro i _
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro j _
          have hnn : 0 ≤ s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2 := by
            have := hp0 i; have := hp0 j; have := hF i x; have := hF x j; positivity
          split_ifs
          · rw [show s.p i * s.p j * s.F t i x * s.F t x j * rb x * (f i - f j) ^ 2 =
                rb x * (s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2) by ring,
              abs_mul, abs_of_nonneg hnn]
            exact mul_le_mul_of_nonneg_right (hρ x hx) hnn
          · simp only [abs_zero]; positivity
      _ = (1 / 2 : ℝ) * Kq * ∑ x ∈ S, ∑ i, ∑ j,
            s.p i * s.p j * s.F t i x * s.F t x j * (f i - f j) ^ 2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
      _ ≤ (1 / 2 : ℝ) * Kq * (8 * C ^ 4 * A * qform (s.D t) f) :=
          mul_le_mul_of_nonneg_left hstack (by positivity)
      _ = _ := by ring
  -- the linear part, moved to a sum over all pivots
  let μS : P → ℂ := fun x => if x ∈ S then μ x else 0
  have hμS : ∀ x, ‖μS x‖ ≤ m := by
    intro x; by_cases hx : x ∈ S
    · simp only [μS, hx, if_true]; exact hμ x hx
    · simp only [μS, hx, if_false, norm_zero]; exact hm
  let lin : P → P → P → ℝ := fun x i j => s.p i * s.p j * (f i - f j) ^ 2 *
    (μS x * star (s.h t i j) * s.h t i x * s.h t x j).re
  have hlinS : (∑ x ∈ S, ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then
      -(s.p i * s.p j * (f i - f j) ^ 2 *
        (μ x * star (s.h t i j) * s.h t i x * s.h t x j).re) else 0)) =
      -(∑ x, ∑ i, ∑ j, lin x i j) +
        ∑ x, ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then 0 else lin x i j) := by
    have hg : (∑ x ∈ S, ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then
        -(s.p i * s.p j * (f i - f j) ^ 2 *
          (μ x * star (s.h t i j) * s.h t i x * s.h t x j).re) else 0)) =
        ∑ x ∈ S, ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then -lin x i j else 0) := by
      apply Finset.sum_congr rfl; intro x hx
      simp only [lin, μS, hx, if_true]
    rw [hg, Finset.sum_subset (Finset.subset_univ S)]
    · rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> ring
    · intro x _ hx
      apply Finset.sum_eq_zero; intro i _
      apply Finset.sum_eq_zero; intro j _
      simp [lin, μS, hx]
  have hmain : |∑ x, ∑ i, ∑ j, lin x i j| ≤ 2 * C ^ 2 * Hn * m * energyF (s.F t) f := by
    have hre : (∑ x, ∑ i, ∑ j, lin x i j) =
        (∑ x, ∑ i, ∑ j, ((s.p i * s.p j * (f i - f j) ^ 2 : ℝ) : ℂ) *
          (μS x * star (s.h t i j) * s.h t i x * s.h t x j)).re := by
      simp only [Complex.re_sum, Complex.re_ofReal_mul, lin]
    rw [hre]
    exact (Complex.abs_re_le_norm _).trans
      (lin_main t C m Hn s μS f hC0 hm hHn hp0 hpC hhsym hμS hh)
  have hcorr : |∑ x, ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then 0 else lin x i j)| ≤
      2 * C ^ 2 * m * Hd * energyF (s.F t) f := by
    have hbnd : ∀ x i j, |lin x i j| ≤ C ^ 2 * m * (f i - f j) ^ 2 *
        (‖s.h t i j‖ * ‖s.h t i x‖ * ‖s.h t x j‖) := by
      intro x i j
      simp only [lin]
      rw [abs_mul, abs_of_nonneg (by have := hp0 i; have := hp0 j; positivity)]
      have h1 : |(μS x * star (s.h t i j) * s.h t i x * s.h t x j).re| ≤
          m * (‖s.h t i j‖ * ‖s.h t i x‖ * ‖s.h t x j‖) := by
        refine (Complex.abs_re_le_norm _).trans ?_
        simp only [norm_mul, norm_star]
        have := hμS x
        have : 0 ≤ ‖s.h t i j‖ * ‖s.h t i x‖ * ‖s.h t x j‖ := by positivity
        nlinarith
      have h2 : s.p i * s.p j * (f i - f j) ^ 2 ≤ C ^ 2 * (f i - f j) ^ 2 := by
        have : s.p i * s.p j ≤ C ^ 2 := by nlinarith [hp0 i, hp0 j, hpC i, hpC j]
        nlinarith [sq_nonneg (f i - f j)]
      calc s.p i * s.p j * (f i - f j) ^ 2 * |(μS x * star (s.h t i j) * s.h t i x *
            s.h t x j).re|
          ≤ C ^ 2 * (f i - f j) ^ 2 * (m * (‖s.h t i j‖ * ‖s.h t i x‖ * ‖s.h t x j‖)) :=
            mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hind : ∀ x i j, |(if i ≠ x ∧ j ≠ x then 0 else lin x i j)| ≤
        (if i = x then |lin x i j| else 0) + (if j = x then |lin x i j| else 0) := by
      intro x i j
      by_cases hi : i = x
      · subst hi; simp only [ne_eq, not_true_eq_false, false_and, if_false, if_true]
        have : 0 ≤ (if j = i then |lin i i j| else 0) := by split_ifs <;> positivity
        linarith
      · by_cases hj : j = x
        · subst hj; simp [hi]
        · simp [hi, hj]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsum1 : (∑ x, ∑ i, ∑ j, (if i = x then |lin x i j| else 0)) ≤
        C ^ 2 * m * Hd * energyF (s.F t) f := by
      unfold energyF
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro x _
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro j _
      refine (hbnd x x j).trans ?_
      rw [F_eq_norm_sq]
      have := hdiag x
      have : 0 ≤ (f x - f j) ^ 2 * ‖s.h t x j‖ ^ 2 := by positivity
      calc C ^ 2 * m * (f x - f j) ^ 2 * (‖s.h t x j‖ * ‖s.h t x x‖ * ‖s.h t x j‖)
          = C ^ 2 * m * ‖s.h t x x‖ * ((f x - f j) ^ 2 * ‖s.h t x j‖ ^ 2) := by ring
        _ ≤ C ^ 2 * m * Hd * ((f x - f j) ^ 2 * ‖s.h t x j‖ ^ 2) := by gcongr
        _ = _ := by ring
    have hsum2 : (∑ x, ∑ i, ∑ j, (if j = x then |lin x i j| else 0)) ≤
        C ^ 2 * m * Hd * energyF (s.F t) f := by
      have hsw := energyF_swap (s.F t) f
      rw [← hsw, Finset.mul_sum]
      apply Finset.sum_le_sum; intro x _
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      refine (hbnd x i x).trans ?_
      rw [F_eq_norm_sq]
      have := hdiag x
      have : 0 ≤ (f i - f x) ^ 2 * ‖s.h t i x‖ ^ 2 := by positivity
      calc C ^ 2 * m * (f i - f x) ^ 2 * (‖s.h t i x‖ * ‖s.h t i x‖ * ‖s.h t x x‖)
          = C ^ 2 * m * ‖s.h t x x‖ * ((f i - f x) ^ 2 * ‖s.h t i x‖ ^ 2) := by ring
        _ ≤ C ^ 2 * m * Hd * ((f i - f x) ^ 2 * ‖s.h t i x‖ ^ 2) := by gcongr
        _ = _ := by ring
    calc (∑ x, |∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then 0 else lin x i j)|)
        ≤ ∑ x, ∑ i, ∑ j, ((if i = x then |lin x i j| else 0) +
            (if j = x then |lin x i j| else 0)) := by
          apply Finset.sum_le_sum; intro x _
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          apply Finset.sum_le_sum; intro i _
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          apply Finset.sum_le_sum; intro j _
          exact hind x i j
      _ = (∑ x, ∑ i, ∑ j, (if i = x then |lin x i j| else 0)) +
            ∑ x, ∑ i, ∑ j, (if j = x then |lin x i j| else 0) := by
          simp only [Finset.sum_add_distrib]
      _ ≤ _ := by linarith
  rw [hlinS]
  have hq' : |∑ x ∈ S, (1 / 2 : ℝ) * ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then
      s.p i * s.p j * s.F t i x * s.F t x j * rb x * (f i - f j) ^ 2 else 0)| ≤
      4 * C ^ 4 * A * Kq * qform (s.D t) f := hquad
  calc _ ≤ |-(∑ x, ∑ i, ∑ j, lin x i j)| +
        |∑ x, ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then 0 else lin x i j)| +
        |∑ x ∈ S, (1 / 2 : ℝ) * ∑ i, ∑ j, (if i ≠ x ∧ j ≠ x then
          s.p i * s.p j * s.F t i x * s.F t x j * rb x * (f i - f j) ^ 2 else 0)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; nlinarith [hmain, hcorr, hq']

end MeanBound

section Dual

variable {P : Type*} [Fintype P] [DecidableEq P]

lemma amgm_23 (a b l : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 < l) :
    a ^ (2 / 3 : ℝ) * b ^ (1 / 3 : ℝ) ≤ 2 / 3 * l * a + 1 / 3 * (l ^ 2)⁻¹ * b := by
  have hgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 2 / 3) (w₂ := 1 / 3)
    (p₁ := l * a) (p₂ := (l ^ 2)⁻¹ * b) (by norm_num) (by norm_num) (by positivity)
    (by positivity) (by norm_num)
  have hl2 : ((l ^ 2)⁻¹) ^ (1 / 3 : ℝ) = (l ^ (2 / 3 : ℝ))⁻¹ := by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hl.le]
    norm_num
  have hlhs : (l * a) ^ (2 / 3 : ℝ) * ((l ^ 2)⁻¹ * b) ^ (1 / 3 : ℝ) =
      a ^ (2 / 3 : ℝ) * b ^ (1 / 3 : ℝ) := by
    rw [Real.mul_rpow hl.le ha, Real.mul_rpow (by positivity) hb, hl2]
    have : l ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hl _).ne'
    field_simp
  rw [hlhs] at hgm
  linarith

lemma l1_rpow_eq (a : ℝ) (ha : 0 ≤ a) : power a (4 / 3) = (a ^ 2) ^ (2 / 3 : ℝ) := by
  unfold power
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  norm_num

/-- The dual-norm stack from the `ℓ²`/`ℓ¹` stacks via the Fourier bound and
Hölder (here in its AM–GM form). -/
lemma wstar_stack (C t B1 B2 l : ℝ) (Wstar : Form P) (S : Finset P) (ys : P → P → ℝ)
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hl : 0 < l)
    (hdual : ∀ y, neutral y → Wstar y ≤
      l2sq y + C * t * power (l1 y) (4 / 3) * power (l2sq y) (1 / 3))
    (hneu : ∀ x ∈ S, neutral (ys x))
    (h2 : (∑ x ∈ S, l2sq (ys x)) ≤ B2) (h1 : (∑ x ∈ S, l1 (ys x) ^ 2) ≤ B1) :
    (∑ x ∈ S, Wstar (ys x)) ≤ B2 + C * t * (2 / 3 * l * B1 + 1 / 3 * (l ^ 2)⁻¹ * B2) := by
  have hpt : ∀ x ∈ S, Wstar (ys x) ≤ l2sq (ys x) + C * t *
      (2 / 3 * l * l1 (ys x) ^ 2 + 1 / 3 * (l ^ 2)⁻¹ * l2sq (ys x)) := by
    intro x hx
    have hd := hdual (ys x) (hneu x hx)
    have hl1 : 0 ≤ l1 (ys x) := Finset.sum_nonneg fun i _ => norm_nonneg _
    have hl2 : 0 ≤ l2sq (ys x) := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hg := amgm_23 (l1 (ys x) ^ 2) (l2sq (ys x)) l (sq_nonneg _) hl2 hl
    rw [l1_rpow_eq _ hl1] at hd
    have hCt : 0 ≤ C * t := mul_nonneg hC ht
    have : C * t * ((l1 (ys x) ^ 2) ^ (2 / 3 : ℝ) * power (l2sq (ys x)) (1 / 3)) ≤
        C * t * (2 / 3 * l * l1 (ys x) ^ 2 + 1 / 3 * (l ^ 2)⁻¹ * l2sq (ys x)) :=
      mul_le_mul_of_nonneg_left hg hCt
    calc Wstar (ys x) ≤ l2sq (ys x) + C * t * (l1 (ys x) ^ 2) ^ (2 / 3 : ℝ) *
          power (l2sq (ys x)) (1 / 3) := hd
      _ ≤ _ := by linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hCt : 0 ≤ C * t := mul_nonneg hC ht
  have hl2 : 0 ≤ (l ^ 2)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 / 3 * l)
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / 3 * (l ^ 2)⁻¹)
  nlinarith

end Dual

section Final

lemma F_le_power_half {P : Type*} [Fintype P] [DecidableEq P] (t : ℝ) (s : State P)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hrow : ∀ i, s.fourthRow t Finset.univ i ≤ rowCap t) :
    ∀ i j, s.F t i j ≤ power t (delta / 2) := by
  intro i j
  have h1 : ‖s.h t i j‖ ^ 4 ≤ rowCap t :=
    le_trans (Finset.single_le_sum (f := fun j => ‖s.h t i j‖ ^ 4)
      (fun j _ => by positivity) (Finset.mem_univ j)) (hrow i)
  have h2 : rowCap t ≤ (power t (delta / 2)) ^ 2 := by
    show t ^ (1 + delta) ≤ (t ^ (delta / 2)) ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    apply Real.rpow_le_rpow_of_exponent_ge ht ht1
    norm_num [delta]
  have h3 : (s.F t i j) ^ 2 ≤ (power t (delta / 2)) ^ 2 := by
    rw [F_eq_norm_sq, ← pow_mul]; linarith
  exact (sq_le_sq₀ (F_nonneg t s i j) (Real.rpow_nonneg ht.le _)).1 h3

set_option maxHeartbeats 2000000 in
theorem laplacian_bounds_proof : ∀ (C : ℝ), 1 ≤ C → ∃ C' > 0, ∃ t0 > 0,
    ∀ (P Ω : Type) [Fintype P] [DecidableEq P] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℝ) (s : State P)
    (Λplus Wstar : Form P) (S : Finset P) (ξ : P → Ω → ℝ),
    t < t0 → Prestate t C Λplus Wstar s → (∀ x ∈ S, MomentLaw μ t C (ξ x)) →
    formAbsLe (qform (∑ x ∈ S, ∫ ω, Linc t s x (ξ x ω) ∂μ))
      (qform (s.D t)) (C' * power t S45.beta) ∧
    (∀ z : P → ℝ, (∀ x ∈ S, |z x| ≤ C * Real.sqrt t) → ∀ f : P → ℝ,
      (∑ x ∈ S, l2sq (Linc t s x (z x) *ᵥ f)) ≤
        C' * power t (delta / 2) * qform (s.D t) f ∧
      (∑ x ∈ S, l1 (Linc t s x (z x) *ᵥ f)^2) ≤ C' / t * qform (s.D t) f ∧
      (∑ x ∈ S, Wstar (Linc t s x (z x) *ᵥ f)) ≤
        C' * power t (delta / 2) * qform (s.D t) f ∧
      (∀ x ∈ S, neutral (Linc t s x (z x) *ᵥ f))) := by
  intro C hC
  have hCpos : 0 < C := by linarith
  have hC0 : 0 ≤ C := hCpos.le
  obtain ⟨A, hA, tA, htA, hAn⟩ := analytic_any C hC
  obtain ⟨G, hG, tG, htG, hGb⟩ :=
    gamma_norm_bound_any_of_analyticPrestate analytic_prestate_proof C hC
  obtain ⟨G2, hG2, tG2, htG2, hmom⟩ := gamma_moments_prestate_of_small C hC
  let Ksm : ℝ := C + 2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2
  have hKsm : 0 < Ksm := by positivity
  obtain ⟨t1, ht1pos, hsm⟩ := exists_small_beta Ksm (1 / (4 * C)) hKsm (by positivity)
  let m0 : ℝ := G2 + 2 * (1 + C ^ 2)
  let q0 : ℝ := G2 + 2 * C * (2 * (1 + C ^ 2) + C * (C + 2 * (1 + C ^ 2)) ^ 2)
  let K : ℝ := G ^ 2 + 2 * C ^ 2
  let Cmean : ℝ := (2 * C ^ 3 * m0 + 2 * C ^ 2 * A * m0) * (2 * C ^ 2) + 4 * C ^ 4 * A * q0
  let c2 : ℝ := 3 * ((2 * C * G) ^ 2 * (A * C ^ 2) + (2 * C ^ 2 * G * A) ^ 2 +
    (C ^ 2 * K) ^ 2 * (4 * A ^ 2))
  let c1 : ℝ := 3 * ((2 * C * G) ^ 2 * (A * C ^ 2 * C ^ 2) + (2 * C ^ 2 * G * A) ^ 2 * A +
    (C ^ 2 * K) ^ 2 * (4 * A ^ 3))
  let C2D : ℝ := c2 * (2 * C ^ 2)
  let C1D : ℝ := c1 * (2 * C ^ 2)
  let CW : ℝ := C2D + C * (2 / 3) * C1D + C * (1 / 3) * C2D
  have hm0 : 0 < m0 := by positivity
  have hq0 : 0 < q0 := by positivity
  have hK : 0 < K := by positivity
  have hCmean : 0 ≤ Cmean := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc1 : 0 ≤ c1 := by positivity
  have hC2D : 0 ≤ C2D := by positivity
  have hC1D : 0 ≤ C1D := by positivity
  have hCW : 0 ≤ CW := by positivity
  refine ⟨Cmean + C2D + C1D + CW + 1, by positivity, min (min tA tG) (min tG2 t1),
    lt_min (lt_min htA htG) (lt_min htG2 ht1pos), ?_⟩
  intro P Ω _ _ _ μ _ t s Λplus Wstar S ξ htt hp hlaw
  have htA' : t < tA := lt_of_lt_of_le htt ((min_le_left _ _).trans (min_le_left _ _))
  have htG' : t < tG := lt_of_lt_of_le htt ((min_le_left _ _).trans (min_le_right _ _))
  have htG2' : t < tG2 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
  have ht1' : t < t1 := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))
  have ht : 0 < t := hp.scale.1
  have ht1 : t < 1 := hp.scale.2
  have hβ0 : 0 < power t S45.beta := Real.rpow_pos_of_pos ht _
  have hβ1 : power t S45.beta ≤ 1 :=
    Real.rpow_le_one ht.le ht1.le (by norm_num [S45.beta, delta])
  have hτ0 : 0 < power t (delta / 2) := Real.rpow_pos_of_pos ht _
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hKsmt := hsm t ht ht1'
  have htβ := t_le_power_beta ht ht1.le
  have hsmall : C * power t S45.beta ≤ 1 / 2 := by
    have h1 : C * power t S45.beta ≤ Ksm * power t S45.beta := by
      apply mul_le_mul_of_nonneg_right _ hβ0.le
      have k1 : 0 ≤ 2 * (1 + C ^ 2) := by positivity
      have k2 : 0 ≤ C * (C + 2 * (1 + C ^ 2)) ^ 2 := by positivity
      dsimp [Ksm]; linarith
    have h2 : 1 / (4 * C) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hsmallq : 2 * (1 + C ^ 2) * power t S45.beta ≤ 1 / (4 * C) := by
    have : 2 * (1 + C ^ 2) * power t S45.beta ≤ Ksm * power t S45.beta := by
      apply mul_le_mul_of_nonneg_right _ hβ0.le
      have k1 : 0 ≤ 2 * (1 + C ^ 2) := by positivity
      have k2 : 0 ≤ C * (C + 2 * (1 + C ^ 2)) ^ 2 := by positivity
      dsimp [Ksm]; linarith
    linarith
  have hsmallt : C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≤ 1 / (4 * C) := by
    have h1 : C * (C + 2 * (1 + C ^ 2)) ^ 2 * t ≤
        C * (C + 2 * (1 + C ^ 2)) ^ 2 * power t S45.beta :=
      mul_le_mul_of_nonneg_left htβ (by positivity)
    have h2 : C * (C + 2 * (1 + C ^ 2)) ^ 2 * power t S45.beta ≤ Ksm * power t S45.beta := by
      apply mul_le_mul_of_nonneg_right _ hβ0.le
      have k1 : 0 ≤ 2 * (1 + C ^ 2) := by positivity
      have k2 : 0 ≤ C * (C + 2 * (1 + C ^ 2)) ^ 2 := by positivity
      dsimp [Ksm]; linarith
    linarith
  obtain ⟨hAfacts, hopA⟩ := hAn P t s Λplus Wstar htA' hp
  have hrowA : ∀ i, (∑ j, s.F t i j) ≤ A := fun i => (hAfacts i).1
  have hdiagA : ∀ i, ‖s.h t i i‖ ≤ A * Real.sqrt t := fun i => (hAfacts i).2.1
  have hh : ‖s.h t‖ ≤ C / Real.sqrt t :=
    ward_h_operator_bound s t C ht hCpos hp.symmetric hp.ward (fun i => (hp.broad i).2.1)
  have hp0 : ∀ i, 0 ≤ s.p i := fun i => le_trans (by positivity) (hp.broad i).2.1
  have hpC : ∀ i, s.p i ≤ C := fun i => (hp.broad i).2.2
  have hhsym := h_symm_of_prestate t C Λplus Wstar s hp
  have hmax := F_le_power_half t s ht ht1.le hp.row_cap
  have hEle : ∀ f, energyF (s.F t) f ≤ 2 * C ^ 2 * qform (s.D t) f :=
    fun f => F_energy_le_D_of_prestate t C Λplus Wstar s hC hp f
  have hqD : ∀ f, 0 ≤ qform (s.D t) f := hp.kernel.2.1
  refine ⟨?_, ?_⟩
  · -- the mean
    intro f
    have hx : ∀ x ∈ S, (∀ᵐ ω ∂μ, ‖gamma t s x (ξ x ω)‖ ≤ G2) ∧
        ‖∫ ω, gamma t s x (ξ x ω) ∂μ‖ ≤ m0 * Real.sqrt t * power t S45.beta ∧
        |∫ ω, (‖gamma t s x (ξ x ω)‖ ^ 2 - cx t s x) ∂μ| ≤ q0 * power t S45.beta := by
      intro x hxS
      obtain ⟨hae, hmean, hsecond⟩ :=
        hmom P Ω μ t s Λplus Wstar x (ξ x) htG2' hsmall hp (hlaw x hxS)
      have hb : ∀ᵐ ω ∂μ, ‖gamma t s x (ξ x ω)‖ ≤ G2 := by
        filter_upwards [hae] with ω hω; exact hω.1
      refine ⟨hb, hmean, ?_⟩
      exact rho_expected_small_of_prestate μ t C G2 Λplus Wstar s x (ξ x) hC hsmall
        hsmallq hsmallt hp (hlaw x hxS) hG2.le hb hsecond
    have hsum : (∑ x ∈ S, ∫ ω, Linc t s x (ξ x ω) ∂μ) =
        ∑ x ∈ S, laplacian (edgeG t s x (∫ ω, gamma t s x (ξ x ω) ∂μ)
          (∫ ω, (‖gamma t s x (ξ x ω)‖ ^ 2 - cx t s x) ∂μ)) := by
      apply Finset.sum_congr rfl; intro x hxS
      exact integral_Linc μ t s x (ξ x) (hlaw x hxS).measurable G2 hG2.le (hx x hxS).1
    rw [hsum]
    have hmb := mean_bound_det t C A (A * Real.sqrt t) (C / Real.sqrt t)
      (m0 * Real.sqrt t * power t S45.beta) (q0 * power t S45.beta) Λplus Wstar s S
      (fun x => ∫ ω, gamma t s x (ξ x ω) ∂μ)
      (fun x => ∫ ω, (‖gamma t s x (ξ x ω)‖ ^ 2 - cx t s x) ∂μ) f hC hA.le
      (by positivity) (by positivity) (by positivity) hp hrowA hdiagA hh
      (fun x hxS => (hx x hxS).2.1) (fun x hxS => (hx x hxS).2.2)
    refine hmb.trans ?_
    have hE := hEle f
    have hE0 := energyF_nonneg (s.F t) (F_nonneg t s) f
    have hq := hqD f
    have hcoef : 2 * C ^ 2 * (C / Real.sqrt t) * (m0 * Real.sqrt t * power t S45.beta) +
        2 * C ^ 2 * (m0 * Real.sqrt t * power t S45.beta) * (A * Real.sqrt t) ≤
        (2 * C ^ 3 * m0 + 2 * C ^ 2 * A * m0) * power t S45.beta := by
      have e1 : 2 * C ^ 2 * (C / Real.sqrt t) * (m0 * Real.sqrt t * power t S45.beta) =
          2 * C ^ 3 * m0 * power t S45.beta := by
        field_simp
      have e2 : 2 * C ^ 2 * (m0 * Real.sqrt t * power t S45.beta) * (A * Real.sqrt t) =
          2 * C ^ 2 * A * m0 * power t S45.beta * t := by
        rw [show 2 * C ^ 2 * (m0 * Real.sqrt t * power t S45.beta) * (A * Real.sqrt t) =
          2 * C ^ 2 * A * m0 * power t S45.beta * Real.sqrt t ^ 2 by ring, hsq]
      rw [e1, e2]
      have : 0 ≤ 2 * C ^ 2 * A * m0 * power t S45.beta := by positivity
      nlinarith
    calc _ ≤ (2 * C ^ 3 * m0 + 2 * C ^ 2 * A * m0) * power t S45.beta *
          (2 * C ^ 2 * qform (s.D t) f) +
          4 * C ^ 4 * A * (q0 * power t S45.beta) * qform (s.D t) f := by
          gcongr
      _ = Cmean * power t S45.beta * qform (s.D t) f := by dsimp [Cmean]; ring
      _ ≤ (Cmean + C2D + C1D + CW + 1) * power t S45.beta * qform (s.D t) f := by
          gcongr; linarith
  · -- the deterministic stacks
    intro z hz f
    have hrw : ∀ x, Linc t s x (z x) = laplacian (edgeG t s x (gamma t s x (z x))
        (‖gamma t s x (z x)‖ ^ 2 - cx t s x)) := fun x => Linc_eq_laplacian_edgeG t s x (z x)
    have ha : ∀ x ∈ S, ‖gamma t s x (z x)‖ ≤ G := fun x hxS =>
      hGb P t s Λplus Wstar x (z x) htG' hp (hz x hxS)
    have hb : ∀ x ∈ S, |‖gamma t s x (z x)‖ ^ 2 - cx t s x| ≤ K := by
      intro x hxS
      obtain ⟨hc0, hc1⟩ := cx_bounds t C Λplus Wstar s hC hsmall hsmallq hsmallt hp x
      have hg := ha x hxS
      have hsq' : ‖gamma t s x (z x)‖ ^ 2 ≤ G ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hg 2
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖gamma t s x (z x)‖]
    obtain ⟨hl2, hl1⟩ := det_stacks t C G K A (A * Real.sqrt t) (C / Real.sqrt t)
      (A * power t (delta / 2)) (power t (delta / 2)) s S
      (fun x => gamma t s x (z x)) (fun x => ‖gamma t s x (z x)‖ ^ 2 - cx t s x) f
      hC0 hG.le hK.le hA.le hτ0.le (by positivity) hp0 hpC hhsym hrowA hdiagA hopA hh hmax
      ha hb
    simp only [← hrw] at hl2 hl1
    have hE := hEle f
    have hE0 := energyF_nonneg (s.F t) (F_nonneg t s) f
    have hq := hqD f
    -- l2 stack
    have hL2 : (∑ x ∈ S, l2sq (Linc t s x (z x) *ᵥ f)) ≤
        C2D * power t (delta / 2) * qform (s.D t) f := by
      refine hl2.trans ?_
      have hcoef : 3 * ((2 * C * G) ^ 2 * (A * power t (delta / 2) * C ^ 2) +
          (2 * C ^ 2 * G * (A * Real.sqrt t)) ^ 2 * power t (delta / 2) +
          (C ^ 2 * K) ^ 2 * (4 * A ^ 2 * power t (delta / 2))) ≤
          c2 * power t (delta / 2) := by
        have e : (2 * C ^ 2 * G * (A * Real.sqrt t)) ^ 2 = (2 * C ^ 2 * G * A) ^ 2 * t := by
          rw [show (2 * C ^ 2 * G * (A * Real.sqrt t)) ^ 2 =
            (2 * C ^ 2 * G * A) ^ 2 * Real.sqrt t ^ 2 by ring, hsq]
        rw [e]
        have : 0 ≤ (2 * C ^ 2 * G * A) ^ 2 * power t (delta / 2) := by positivity
        dsimp [c2]
        nlinarith
      calc _ ≤ c2 * power t (delta / 2) * energyF (s.F t) f :=
            mul_le_mul_of_nonneg_right hcoef hE0
        _ ≤ c2 * power t (delta / 2) * (2 * C ^ 2 * qform (s.D t) f) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by dsimp [C2D]; ring
    -- l1 stack
    have hL1 : (∑ x ∈ S, l1 (Linc t s x (z x) *ᵥ f) ^ 2) ≤ C1D / t * qform (s.D t) f := by
      refine hl1.trans ?_
      have hcoef : 3 * ((2 * C * G) ^ 2 * (A * (C / Real.sqrt t) ^ 2 * C ^ 2) +
          (2 * C ^ 2 * G * (A * Real.sqrt t)) ^ 2 * A + (C ^ 2 * K) ^ 2 * (4 * A ^ 3)) ≤
          c1 / t := by
        have e1 : (C / Real.sqrt t) ^ 2 = C ^ 2 / t := by rw [div_pow, hsq]
        have e2 : (2 * C ^ 2 * G * (A * Real.sqrt t)) ^ 2 = (2 * C ^ 2 * G * A) ^ 2 * t := by
          rw [show (2 * C ^ 2 * G * (A * Real.sqrt t)) ^ 2 =
            (2 * C ^ 2 * G * A) ^ 2 * Real.sqrt t ^ 2 by ring, hsq]
        rw [e1, e2]
        have hinv : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
        have htinv : t ≤ 1 / t := by rw [le_div_iff₀ ht]; nlinarith
        dsimp [c1]
        have ha1 : 0 ≤ (2 * C ^ 2 * G * A) ^ 2 * A := by positivity
        have ha2 : 0 ≤ (C ^ 2 * K) ^ 2 * (4 * A ^ 3) := by positivity
        have e3 : (2 * C * G) ^ 2 * (A * (C ^ 2 / t) * C ^ 2) =
            (2 * C * G) ^ 2 * (A * C ^ 2 * C ^ 2) * (1 / t) := by ring
        have e4 : c1 / t = 3 * ((2 * C * G) ^ 2 * (A * C ^ 2 * C ^ 2) * (1 / t) +
            (2 * C ^ 2 * G * A) ^ 2 * A * (1 / t) + (C ^ 2 * K) ^ 2 * (4 * A ^ 3) * (1 / t)) := by
          dsimp [c1]; ring
        rw [e3]
        rw [show 3 * ((2 * C * G) ^ 2 * (A * C ^ 2 * C ^ 2) + (2 * C ^ 2 * G * A) ^ 2 * A +
            (C ^ 2 * K) ^ 2 * (4 * A ^ 3)) / t = 3 * ((2 * C * G) ^ 2 * (A * C ^ 2 * C ^ 2) *
            (1 / t) + (2 * C ^ 2 * G * A) ^ 2 * A * (1 / t) + (C ^ 2 * K) ^ 2 * (4 * A ^ 3) *
            (1 / t)) by ring]
        have h1 : (2 * C ^ 2 * G * A) ^ 2 * t * A ≤ (2 * C ^ 2 * G * A) ^ 2 * A * (1 / t) := by
          rw [mul_right_comm]; exact mul_le_mul_of_nonneg_left htinv ha1
        have h2 : (C ^ 2 * K) ^ 2 * (4 * A ^ 3) ≤ (C ^ 2 * K) ^ 2 * (4 * A ^ 3) * (1 / t) := by
          nlinarith
        linarith
      calc _ ≤ c1 / t * energyF (s.F t) f := mul_le_mul_of_nonneg_right hcoef hE0
        _ ≤ c1 / t * (2 * C ^ 2 * qform (s.D t) f) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by dsimp [C1D]; ring
    -- dual stack
    have hneu : ∀ x ∈ S, neutral (Linc t s x (z x) *ᵥ f) :=
      fun x _ => Linc_neutral t s x (z x) hp.symmetric f
    have hW := wstar_stack C t (C1D / t * qform (s.D t) f)
      (C2D * power t (delta / 2) * qform (s.D t) f) (power t (delta / 2)) Wstar S
      (fun x => Linc t s x (z x) *ᵥ f) hC0 ht.le hτ0 hp.dual_fourier hneu hL2 hL1
    have hτsq : t * ((power t (delta / 2)) ^ 2)⁻¹ ≤ 1 := by
      have : t ≤ (power t (delta / 2)) ^ 2 := by
        show t ≤ (t ^ (delta / 2)) ^ 2
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
          _ ≤ t ^ (delta / 2 * ((2 : ℕ) : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_ge ht ht1.le; norm_num [delta]
      rw [mul_inv_le_iff₀ (by positivity)]; linarith
    have hLW : (∑ x ∈ S, Wstar (Linc t s x (z x) *ᵥ f)) ≤
        CW * power t (delta / 2) * qform (s.D t) f := by
      refine hW.trans ?_
      have e : C * t * (2 / 3 * power t (delta / 2) * (C1D / t * qform (s.D t) f) +
          1 / 3 * ((power t (delta / 2)) ^ 2)⁻¹ *
            (C2D * power t (delta / 2) * qform (s.D t) f)) =
          C * (2 / 3) * C1D * power t (delta / 2) * qform (s.D t) f +
          C * (1 / 3) * C2D * power t (delta / 2) * qform (s.D t) f *
            (t * ((power t (delta / 2)) ^ 2)⁻¹) := by
        field_simp
      rw [e]
      have : 0 ≤ C * (1 / 3) * C2D * power t (delta / 2) * qform (s.D t) f := by positivity
      have h3 : C * (1 / 3) * C2D * power t (delta / 2) * qform (s.D t) f *
          (t * ((power t (delta / 2)) ^ 2)⁻¹) ≤
          C * (1 / 3) * C2D * power t (delta / 2) * qform (s.D t) f := by
        have hr := mul_le_mul_of_nonneg_left hτsq this
        linarith
      have hCWe : CW * power t (delta / 2) * qform (s.D t) f =
          C2D * power t (delta / 2) * qform (s.D t) f +
          C * (2 / 3) * C1D * power t (delta / 2) * qform (s.D t) f +
          C * (1 / 3) * C2D * power t (delta / 2) * qform (s.D t) f := by
        dsimp [CW]; ring
      linarith
    have hC'1 : C2D ≤ Cmean + C2D + C1D + CW + 1 := by linarith
    have hC'2 : C1D ≤ Cmean + C2D + C1D + CW + 1 := by linarith
    have hC'3 : CW ≤ Cmean + C2D + C1D + CW + 1 := by linarith
    refine ⟨?_, ?_, ?_, hneu⟩
    · refine hL2.trans ?_
      gcongr
    · refine hL1.trans ?_
      gcongr
    · refine hLW.trans ?_
      gcongr

end Final

end AndersonAC.AgentS45
