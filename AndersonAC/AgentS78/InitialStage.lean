import AndersonAC.S3.Final
import AndersonAC.AgentS78.FormJoin
import AndersonAC.AgentS78.TorusGradient
import AndersonAC.AgentS78.EmptyTerminal

/-!
WP10 construction, initial stage (02-state.tex:300–360, 03-initialization.tex
Proposition 3.6): the §3 normalized initialization endpoint, transported to the
§§7–8 torus `Torus d m` (L = sideLength m) and real charge forms, gives the
initial damped endpoint, the stage invariant `StageBounds` at n = n₀, and the
`‖K‖ ≤ 1/4` hypothesis of `deterministic_induction`.

Upstream hypotheses (exact §3 statements, not yet proved on lane/agent-s3):
`S3.BottomResolventStatement` (luna-s3bottom) and
`S3.LargeSymbolDecayWStatement` (luna-s3symlarge).
-/

open scoped BigOperators
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

/-- The initial endpoint: all sites active, zero partial potentials,
`M = H₀ - E` with the negative-hopping free matrix, and the §3 scalar-damped inverse. -/
def initialEndpoint (d m : ℕ) (E t : ℝ) (ρ : ℂ) : AndersonAC.S78.Endpoint (AndersonAC.S78.Torus d m) where
  active := Finset.univ
  M := AndersonAC.S3.freeHopping (d := d) (L := OAI.Anderson.sideLength m) -
    (E : ℂ) • (1 : Matrix (AndersonAC.S78.Torus d m) (AndersonAC.S78.Torus d m) ℂ)
  g := AndersonAC.S3.initialG (d := d) (L := OAI.Anderson.sideLength m) E t ρ

section Energy

variable {A : Type} [Fintype A]

/-- The Ward weight matrix `F_ij = |H_ij|²` as a complex matrix. -/
def wardMatrix (H : Matrix A A ℂ) : Matrix A A ℂ := fun i j => ((‖H i j‖ ^ 2 : ℝ) : ℂ)

/-- Ward energy with constant damping equals the complex form of `p²(1 - F)` when
`F = |H|²` has unit row and column sums. -/
theorem wardEnergy_eq_form [DecidableEq A] (p : ℝ) (H : Matrix A A ℂ)
    (hrow : ∀ i, ∑ j, ‖H i j‖ ^ 2 = 1) (hcol : ∀ j, ∑ i, ‖H i j‖ ^ 2 = 1) (f : A → ℝ) :
    AndersonAC.S78.wardEnergy Finset.univ (fun _ => p) H f =
      AndersonAC.S3.form (((p : ℂ) ^ 2) • (1 - wardMatrix H)) (cx f) := by
  set w : A → A → ℝ := fun i j => ‖H i j‖ ^ 2 with hw
  have h1 : ∑ i, ∑ j, w i j * f i ^ 2 = ∑ i, f i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have h2 : ∑ i, ∑ j, w i j * f j ^ 2 = ∑ j, f j ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j, one_mul]
  have hL : AndersonAC.S78.wardEnergy Finset.univ (fun _ => p) H f =
      p ^ 2 * (∑ i, f i ^ 2) - p ^ 2 * ∑ i, ∑ j, w i j * (f i * f j) := by
    unfold AndersonAC.S78.wardEnergy
    have e : ∀ i j, p * p * ‖H i j‖ ^ 2 * (f i - f j) ^ 2 =
        p ^ 2 * (w i j * f i ^ 2) + p ^ 2 * (w i j * f j ^ 2) - 2 * p ^ 2 * (w i j * (f i * f j)) := by
      intro i j; simp only [hw]; ring
    simp_rw [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
    ring
  have hR : AndersonAC.S3.form (((p : ℂ) ^ 2) • (1 - wardMatrix H)) (cx f) =
      p ^ 2 * (∑ i, f i ^ 2) - p ^ 2 * ∑ i, ∑ j, w i j * (f i * f j) := by
    unfold AndersonAC.S3.form AndersonAC.S3.pairing cx
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum]
    have e : ∀ i j, (star ((f i : ℂ)) * ((((p : ℂ) ^ 2) • (1 - wardMatrix H)) i j *
        (f j : ℂ))).re = p ^ 2 * ((if i = j then 1 else 0) * (f i * f j)) - p ^ 2 * (w i j * (f i * f j)) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp [wardMatrix, Matrix.one_apply, Complex.mul_re, hw, pow_two]
        ring
      · simp [wardMatrix, Matrix.one_apply, hij, Complex.mul_re, hw, pow_two]
        ring
    simp_rw [e, Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    simp [pow_two]
  rw [hL, hR]

end Energy

section Transport

attribute [local instance] Classical.propDecidable

/-- The §3 normalized endpoint transported to `L = OAI.Anderson.sideLength m` (the
§§7–8 torus, definitionally `S3.sideLength m`) and to `t = stageScale u n₀ m`
(definitionally `startupT n₀ m u`). Same elaboration environment as §3. -/
theorem s3_endpoint (hB : AndersonAC.S3.BottomResolventStatement)
    (hLD : AndersonAC.S3.LargeSymbolDecayWStatement) {d : ℕ} (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    ∃ (nmin : ℕ) (a₀ B c C C₀ : ℝ), 1 ≤ nmin ∧
      0 < a₀ ∧ 0 < B ∧ 0 < c ∧ 0 < C ∧ 0 < C₀ ∧
      ∀ n₀ : ℕ, nmin ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m →
      ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
      ∃ r : ℝ → ℂ, ContinuousOn r (OAI.Anderson.energyWindow d e₂) ∧
      ∀ E ∈ OAI.Anderson.energyWindow d e₂,
        r E ∈ AndersonAC.S3.rectangle a₀ B ∧
        AndersonAC.Blueprint.twoSidedInverse
          (AndersonAC.S3.initialMatrix (d := d) (L := OAI.Anderson.sideLength m) E
            (AndersonAC.S78.stageScale u n₀ m) (r E))
          (AndersonAC.S3.initialG E (AndersonAC.S78.stageScale u n₀ m) (r E)) ∧
        (∀ i : AndersonAC.S3.Torus d (OAI.Anderson.sideLength m),
          AndersonAC.S3.initialG E (AndersonAC.S78.stageScale u n₀ m) (r E) i i = r E) ∧
        AndersonAC.Blueprint.opNorm (AndersonAC.S3.initialK (d := d) (L := OAI.Anderson.sideLength m) E
          (AndersonAC.S78.stageScale u n₀ m) (r E)) ≤ 1 / 10 ∧
        (∀ i : AndersonAC.S3.Torus d (OAI.Anderson.sideLength m),
          AndersonAC.S3.fourthRow E (AndersonAC.S78.stageScale u n₀ m) (r E) i ≤
            (1 / 10) * Real.rpow (AndersonAC.S78.stageScale u n₀ m) (1 + AndersonAC.S3.delta)) ∧
        AndersonAC.S3.connectedLaplacian (AndersonAC.S3.initialD (d := d) (L := OAI.Anderson.sideLength m) E
          (AndersonAC.S78.stageScale u n₀ m) (r E)) ∧
        (∀ y : AndersonAC.S3.Torus d (OAI.Anderson.sideLength m) → ℂ, AndersonAC.S3.neutral y →
          c * AndersonAC.S78.stageScale u n₀ m ^ 2 * AndersonAC.S3.form AndersonAC.S3.laplacianPlus y ≤
            AndersonAC.S3.form (AndersonAC.S3.initialX E (AndersonAC.S78.stageScale u n₀ m) (r E)) y ∧
          c * AndersonAC.S3.normSq y ≤
            AndersonAC.S3.form (AndersonAC.S3.initialX E (AndersonAC.S78.stageScale u n₀ m) (r E)) y ∧
          AndersonAC.S3.form (AndersonAC.S3.initialX E (AndersonAC.S78.stageScale u n₀ m) (r E)) y ≤
            C₀ * AndersonAC.S3.normSq y +
              C * AndersonAC.S78.stageScale u n₀ m ^ 2 * AndersonAC.S3.form AndersonAC.S3.laplacianPlus y ∧
          AndersonAC.S3.form (AndersonAC.S3.initialX E (AndersonAC.S78.stageScale u n₀ m) (r E)) y ≤
            (1 + Real.rpow (AndersonAC.S78.stageScale u n₀ m) AndersonAC.S3.kappa) * (r E).im ^ (-2 : ℤ) *
              AndersonAC.S3.normSq y +
              C * AndersonAC.S78.stageScale u n₀ m * AndersonAC.S3.form AndersonAC.S3.laplacianPlus y) := by
  obtain ⟨nmin, a₀, B, c, C, C₀, h1, ha, hB', hc, hC, hC0, hmain⟩ :=
    AndersonAC.S3.initialization_normalized_of_BR_decay hB hLD hd e₂ he₂
  refine ⟨nmin, a₀, B, c, C, C₀, h1, ha, hB', hc, hC, hC0, fun n₀ hn₀ m hm u hu => ?_⟩
  obtain ⟨r, hr, hE⟩ := hmain n₀ hn₀ m hm u hu
  refine ⟨r, hr, fun E hE' => ?_⟩
  obtain ⟨a1, -, -, a4, a5, a6, a7, a8, a9⟩ := hE E hE'
  exact ⟨a1, a4, a5, a6, a7, a8, a9⟩

end Transport

section Initial

variable {d : ℕ}

theorem freeHopping_im (L : ℕ) [NeZero L] (x y : AndersonAC.S3.Torus d L) :
    (AndersonAC.S3.freeHopping (d := d) (L := L) x y).im = 0 := by
  have h := AndersonAC.S3H.freeHopping_star (d := d) (L := L) x y
  exact Complex.conj_eq_iff_im.mp h

theorem laplacian_im (L : ℕ) [NeZero L] (x y : AndersonAC.S3.Torus d L) :
    (AndersonAC.S3.laplacian (d := d) (L := L) x y).im = 0 := by
  unfold AndersonAC.S3.laplacian
  rw [Matrix.add_apply, Complex.add_im, freeHopping_im]
  by_cases h : x = y <;> simp [Matrix.one_apply, h]

/-- The S78 graph energy on `Torus d m` is the §3 Laplacian form at L = sideLength m. -/
theorem gradientEnergy_eq_laplacian_form {m : ℕ} (hm : 0 < m) (f : AndersonAC.S78.Torus d m → ℝ) :
    AndersonAC.S78.gradientEnergy (AndersonAC.S78.nnGraph d m) f =
      AndersonAC.S3.form (AndersonAC.S3.laplacian (d := d) (L := OAI.Anderson.sideLength m)) (cx f) := by
  rw [gradientEnergy_eq_steps hm f, ← AndersonAC.S3H.gradientEnergy_eq_form]
  unfold AndersonAC.S3.gradientEnergy cx
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

theorem inverseOnConstants_inst {A : Type} [Fintype A] (i1 i2 : DecidableEq A) (D : Matrix A A ℂ) :
    @AndersonAC.S3.inverseOnConstants A _ i1 D = @AndersonAC.S3.inverseOnConstants A _ i2 D := by
  cases Subsingleton.elim i1 i2; rfl

theorem opNorm_inst {A : Type} [Fintype A] (i1 i2 : DecidableEq A) (D : Matrix A A ℂ) :
    @AndersonAC.Blueprint.opNorm A _ i1 D = @AndersonAC.Blueprint.opNorm A _ i2 D := by
  cases Subsingleton.elim i1 i2; rfl

theorem matrix_one_inst {A : Type} [Fintype A] (i1 i2 : DecidableEq A) :
    @OfNat.ofNat (Matrix A A ℂ) 1 (@One.toOfNat1 _ (@Matrix.one A ℂ i1 _ _)) =
    @OfNat.ofNat (Matrix A A ℂ) 1 (@One.toOfNat1 _ (@Matrix.one A ℂ i2 _ _)) := by
  cases Subsingleton.elim i1 i2; rfl

/-- **WP10 initial stage.** From the §3 normalized initialization endpoint
(conditional on the two named §3 helper statements), the initial endpoint at
`t = stageScale u n₀ m` is a damped real terminal-Schur endpoint satisfying the
full stage invariant `StageBounds` at `n = n₀` and the `‖K‖ ≤ 1/4` hypothesis of
`deterministic_induction`, with constants uniform in `n₀, m, u, E`. -/
theorem initial_stage (hB : AndersonAC.S3.BottomResolventStatement)
    (hLD : AndersonAC.S3.LargeSymbolDecayWStatement) (hd : 3 ≤ d) (e₂ : ℝ)
    (he₂ : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    ∃ (nmin : ℕ) (cP CP cL CL C₀ : ℝ), 1 ≤ nmin ∧ 0 < cP ∧ cP ≤ CP ∧ 0 < cL ∧ 0 < CL ∧ 0 < C₀ ∧
      ∀ n₀ : ℕ, nmin ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m → ∀ u ∈ Set.Ioc (1 / 4 : ℝ) 1,
      ∃ ρ : ℝ → ℂ, ContinuousOn ρ (OAI.Anderson.energyWindow d e₂) ∧
      ∀ E ∈ OAI.Anderson.energyWindow d e₂,
        AndersonAC.S78.IsDampedEndpoint
          (initialEndpoint d m E (AndersonAC.S78.stageScale u n₀ m) (ρ E)) (fun _ => ρ E)
          (AndersonAC.S78.stageScale u n₀ m) ∧
        AndersonAC.S78.StageBounds d m n₀ n₀ u cP CP cL CL C₀
          (initialEndpoint d m E (AndersonAC.S78.stageScale u n₀ m) (ρ E)) (fun _ => ρ E) ∧
        AndersonAC.S78.matrixNorm (AndersonAC.S78.squareKernel (AndersonAC.S78.normalizedInverse
          (initialEndpoint d m E (AndersonAC.S78.stageScale u n₀ m) (ρ E))
          (AndersonAC.S78.stageScale u n₀ m))) ≤ 1 / 4 := by
  obtain ⟨nmin, a₀, B, c, C, C₀, hnmin, ha₀, hB0, hc, hC, hC₀, hmain⟩ := s3_endpoint hB hLD hd e₂ he₂
  refine ⟨nmin, min a₀ B, 2 * B, c, C, C₀, hnmin, lt_min ha₀ hB0,
    (min_le_right _ _).trans (by linarith), hc, hC, hC₀, ?_⟩
  intro n₀ hn₀ m hm u hu
  obtain ⟨ρ, hcont, hE⟩ := hmain n₀ hn₀ m hm u hu
  refine ⟨ρ, hcont, fun E hEw => ?_⟩
  obtain ⟨hrect, hinv, hdiag, hK, hrow4, hconn, hcomp⟩ := hE E hEw
  have hm0 : 0 < m := by omega
  set t := AndersonAC.S78.stageScale u n₀ m with ht
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  have htpos : 0 < t := by
    simp only [ht, AndersonAC.S78.stageScale]; positivity
  set s := initialEndpoint d m E t (ρ E) with hs
  have hρim : 0 < (ρ E).im := lt_of_lt_of_le ha₀ hrect.2.1
  set G := AndersonAC.S3.initialG (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E) with hG
  set H := AndersonAC.S3.initialH (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E) with hH
  have hMeq : AndersonAC.S3.freeHopping (d := d) (L := OAI.Anderson.sideLength m) -
      ((E : ℂ) + (t : ℂ) * ρ E) • (1 : Matrix (AndersonAC.S78.Torus d m) (AndersonAC.S78.Torus d m) ℂ) =
      AndersonAC.S3.initialMatrix (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E) := by
    ext a b
    by_cases hab : a = b <;> simp [AndersonAC.S3.initialMatrix, Matrix.one_apply, hab]
  -- Ward row and column sums of `h = √t g`
  have hward : ∀ i, (G i i).im = ((E : ℂ) + (t : ℂ) * ρ E).im * ∑ j, ‖G i j‖ ^ 2 ∧
      (G i i).im = ((E : ℂ) + (t : ℂ) * ρ E).im * ∑ j, ‖G j i‖ ^ 2 := by
    intro i
    apply ward_scalar _ AndersonAC.S3H.freeHopping_hermitian
    · rw [hMeq, hinv.1]
    · rw [hMeq, hinv.2]
  have hnormH : ∀ i j, ‖H i j‖ ^ 2 = t * ‖G i j‖ ^ 2 := by
    intro i j
    simp only [hH, hG, AndersonAC.S3.initialH, Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t), mul_pow, Real.sq_sqrt htpos.le]
  have hzim : ((E : ℂ) + (t : ℂ) * ρ E).im = t * (ρ E).im := by simp
  have hrow : ∀ i, ∑ j, ‖H i j‖ ^ 2 = 1 := by
    intro i
    have h1 := (hward i).1
    rw [hdiag i, hzim] at h1
    simp_rw [hnormH]
    rw [← Finset.mul_sum]
    have : (ρ E).im * (1 - t * ∑ j, ‖G i j‖ ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hcol : ∀ j, ∑ i, ‖H i j‖ ^ 2 = 1 := by
    intro i
    have h1 := (hward i).2
    rw [hdiag i, hzim] at h1
    simp_rw [hnormH]
    rw [← Finset.mul_sum]
    have : (ρ E).im * (1 - t * ∑ j, ‖G j i‖ ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  -- the endpoint energy is the §3 form of `initialD`
  have hDeq : AndersonAC.S3.initialD (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E) =
      (((ρ E).im : ℂ) ^ 2) • (1 - wardMatrix H) := by
    unfold AndersonAC.S3.initialD AndersonAC.S3.initialF wardMatrix
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hH]
  have hQ : ∀ f, AndersonAC.S78.endpointEnergy s (fun _ => ρ E) t f =
      AndersonAC.S3.form (AndersonAC.S3.initialD (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E)) (cx f) := by
    intro f
    rw [hDeq]
    exact wardEnergy_eq_form (ρ E).im H hrow hcol f
  have hDim : ∀ i j, (AndersonAC.S3.initialD (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E) i j).im = 0 := by
    intro i j
    rw [hDeq]
    by_cases hij : i = j <;> simp [wardMatrix, Matrix.one_apply, hij, pow_two]
  have hX : ∀ y : AndersonAC.S78.Torus d m → ℝ, ∑ i, y i = 0 →
      AndersonAC.S78.inverseEnergy s.active (AndersonAC.S78.endpointEnergy s (fun _ => ρ E) t) y =
        AndersonAC.S3.form (AndersonAC.S3.initialX (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E)) (cx y) := by
    intro y hy
    rw [show s.active = Finset.univ from rfl, inverseEnergy_eq_form _ _ hDim hconn hQ y hy]
    unfold AndersonAC.S3.initialX
    exact congrArg (fun X => AndersonAC.S3.form X (cx y)) (inverseOnConstants_inst _ _ _)
  have hL : ∀ y : AndersonAC.S78.Torus d m → ℝ, ∑ i, y i = 0 →
      AndersonAC.S78.inverseEnergy Finset.univ
        (AndersonAC.S78.gradientEnergy (AndersonAC.S78.nnGraph d m)) y =
        AndersonAC.S3.form (AndersonAC.S3.laplacianPlus (d := d) (L := OAI.Anderson.sideLength m)) (cx y) := by
    intro y hy
    rw [inverseEnergy_eq_form _ _ (laplacian_im _) AndersonAC.S3H.laplacian_connected
      (gradientEnergy_eq_laplacian_form hm0) y hy]
    unfold AndersonAC.S3.laplacianPlus
    exact congrArg (fun X => AndersonAC.S3.form X (cx y)) (inverseOnConstants_inst _ _ _)
  have hKnorm : AndersonAC.S78.matrixNorm (AndersonAC.S78.squareKernel
      (AndersonAC.S78.normalizedInverse s t)) ≤ 1 / 10 := by
    rw [matrixNorm_eq_opNorm, opNorm_inst _ _ ]
    exact hK
  have hbij : Function.Bijective (fun i : s.active => i.val) :=
    ⟨Subtype.val_injective, fun x => ⟨⟨x, Finset.mem_univ x⟩, rfl⟩⟩
  refine ⟨⟨fun i j => ⟨?_, ?_⟩, fun i j h => by rcases h with h | h <;> exact absurd (Finset.mem_univ _) h,
    ?_⟩, ?_, hKnorm.trans (by norm_num)⟩
  · -- symmetry of M = H₀ - E
    simp only [hs, initialEndpoint, Matrix.sub_apply, Matrix.smul_apply]
    rw [AndersonAC.S3H.freeHopping_symm]
    by_cases hij : i = j
    · rw [hij]
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  · simp only [hs, initialEndpoint, Matrix.sub_apply, Matrix.smul_apply, Complex.sub_im, freeHopping_im]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · -- the active block of `M - t diag r` is the §3 initial matrix, inverted by `g`
    dsimp only
    have hBeq : s.M.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val) -
        (t : ℂ) • Matrix.diagonal (fun _ : s.active => ρ E) =
        (AndersonAC.S3.initialMatrix (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E)).submatrix
          (fun i : s.active => i.val) (fun i : s.active => i.val) := by
      rw [← hMeq]
      ext ⟨i, hi⟩ ⟨j, hj⟩
      by_cases hij : i = j
      · subst hij
        simp [hs, initialEndpoint, Matrix.one_apply, Matrix.diagonal_apply, Matrix.submatrix_apply]
        ring
      · have hne : (⟨i, hi⟩ : s.active) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
        simp [hs, initialEndpoint, Matrix.one_apply, Matrix.diagonal_apply, Matrix.submatrix_apply,
          hij, hne]
    have hone : ∀ (X : Matrix (AndersonAC.S78.Torus d m) (AndersonAC.S78.Torus d m) ℂ),
        X = 1 → X.submatrix (fun i : s.active => i.val) (fun i : s.active => i.val) = 1 := by
      intro X hX
      subst hX
      ext a b
      by_cases hab : a = b
      · subst hab; simp [Matrix.one_apply]
      · have : a.val ≠ b.val := fun h => hab (Subtype.ext h)
        simp [Matrix.one_apply, hab, this]
    rw [hBeq]
    constructor
    · rw [← Matrix.submatrix_mul _ _ _ _ _ hbij]
      exact hone _ (hinv.1.trans (matrix_one_inst _ _))
    · rw [← Matrix.submatrix_mul _ _ _ _ _ hbij]
      exact hone _ (hinv.2.trans (matrix_one_inst _ _))
  · -- the stage invariant at n = n₀
    unfold AndersonAC.S78.StageBounds
    dsimp only
    refine ⟨fun i _ => ⟨hdiag i, (min_le_left _ _).trans hrect.2.1, by linarith [hrect.2.2], ?_⟩,
      fun i => ?_, hKnorm.trans (by norm_num), constantKernel_of_form _ _ hconn hQ, ?_, ?_, ?_⟩
    · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [abs_of_pos hρim]
      linarith [hrect.1, hrect.2.2]
    · calc AndersonAC.S78.rowFour (AndersonAC.S78.normalizedInverse s t) i
          = AndersonAC.S3.fourthRow (d := d) (L := OAI.Anderson.sideLength m) E t (ρ E) i := rfl
        _ ≤ 1 / 10 * Real.rpow t (1 + AndersonAC.S3.delta) := hrow4 i
        _ ≤ t ^ (1 + AndersonAC.S78.delta) := by
          have e : Real.rpow t (1 + AndersonAC.S3.delta) = t ^ (1 + AndersonAC.S78.delta) := by
            simp only [AndersonAC.S3.delta, AndersonAC.S78.delta, Real.rpow_eq_pow]
          rw [e]
          have := Real.rpow_nonneg htpos.le (1 + AndersonAC.S78.delta)
          linarith
    · show Fintype.card _ ≤ 2 * (Finset.univ : Finset (AndersonAC.S78.Torus d m)).card
      rw [Finset.card_univ]; omega
    · intro x y
      rw [show Finset.univ \ s.active = ∅ from Finset.sdiff_self _]
      have h1 := dist_le_terminalDistance_empty (AndersonAC.S78.nnGraph d m)
        AndersonAC.SolS78.nnGraph_connected_proof x y
      have h2 : (0 : ℝ) ≤ t ^ (-1.03 : ℝ) := Real.rpow_nonneg htpos.le _
      have h3 : (0 : ℝ) ≤ ((AndersonAC.S78.nnGraph d m).dist x y : ℝ) := Nat.cast_nonneg _
      unfold AndersonAC.S78.physicalDistance
      linarith
    · intro y hy
      have hy0 : ∑ i, y i = 0 := hy.2
      rw [hX y hy0, hL y hy0]
      obtain ⟨c1, -, c3, c4⟩ := hcomp (cx y) (neutral_cx y hy0)
      have hN : AndersonAC.S3.normSq (cx y) = ∑ i ∈ s.active, y i ^ 2 := by
        unfold AndersonAC.S3.normSq cx
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hk : Real.rpow t AndersonAC.S3.kappa = t ^ (0.005 * AndersonAC.S78.delta) := by
        rw [Real.rpow_eq_pow]
        congr 1
        norm_num [AndersonAC.S3.kappa, AndersonAC.S3.delta, AndersonAC.S78.delta]
      have hρ : (ρ E).im ^ (-2 : ℤ) * AndersonAC.S3.normSq (cx y) =
          ∑ i ∈ s.active, y i ^ 2 / (ρ E).im ^ 2 := by
        rw [hN, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [_root_.zpow_neg, zpow_two]
        field_simp
      refine ⟨?_, ?_, ?_⟩
      · convert c1 using 2
        ring
      · rw [hN] at c3
        convert c3 using 3
        ring
      · rw [mul_assoc, hρ, hk] at c4
        exact c4

end Initial

end AndersonAC.AgentS78
