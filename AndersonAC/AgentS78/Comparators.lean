import AndersonAC.AgentS78.InitialComparison
import AndersonAC.AgentS78.ResetJoin

/-!
certificate construction: the `W*` comparison `c W* ≤ X ≤ C W*` required by `initial_comparison`, from the
stage comparators `X ≥ cL b Λ⁺`, `X ≤ C₀ |y|² + CL b Λ⁺` and the bound `D ≤ 2K |f|²`
(02-state.tex:346–350: bounded weighted row sums give `X ≥ c Id`).
-/

open scoped BigOperators
open Matrix

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Ward energy is at most twice the weighted row sums times `|f|²`. -/
theorem wardEnergy_le_rows {ι : Type} (A : Finset ι) (p : ι → ℝ) (h : Matrix ι ι ℂ)
    (hp : ∀ i ∈ A, 0 ≤ p i) (hsymm : ∀ i j, ‖h i j‖ = ‖h j i‖) (K : ℝ)
    (hrow : ∀ i ∈ A, p i * ∑ j ∈ A, p j * ‖h i j‖ ^ 2 ≤ K) (f : ι → ℝ) :
    wardEnergy A p h f ≤ 2 * K * ∑ i ∈ A, f i ^ 2 := by
  unfold wardEnergy
  have hw : ∀ i ∈ A, ∀ j ∈ A, 0 ≤ p i * p j * ‖h i j‖ ^ 2 := fun i hi j hj =>
    mul_nonneg (mul_nonneg (hp i hi) (hp j hj)) (sq_nonneg _)
  have step1 : (1 / 2) * ∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * (f i - f j) ^ 2 ≤
      (∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * f i ^ 2) +
      (∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * f j ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have := hw i hi j hj
    nlinarith [sq_nonneg (f i + f j)]
  have hsw : (∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * f j ^ 2) =
      ∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * f i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i]; ring
  have hrow' : (∑ i ∈ A, ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * f i ^ 2) ≤ K * ∑ i ∈ A, f i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have e : ∑ j ∈ A, p i * p j * ‖h i j‖ ^ 2 * f i ^ 2 = (p i * ∑ j ∈ A, p j * ‖h i j‖ ^ 2) * f i ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)
  rw [hsw] at step1
  linarith

/-- `X ≥ |y|² / (2K)` from `D ≤ K |f|²`-type bounds, when the dual is bounded. -/
theorem inverseEnergy_ge_l2 {ι : Type} (A : Finset ι) (Q : (ι → ℝ) → ℝ) (K : ℝ) (hK : 0 < K)
    (hQ : ∀ f, Q f ≤ 2 * K * ∑ i ∈ A, f i ^ 2) (y : ι → ℝ)
    (hb : BddAbove (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - Q f)) :
    (∑ i ∈ A, y i ^ 2) / (2 * K) ≤ inverseEnergy A Q y := by
  unfold inverseEnergy
  refine le_csSup_of_le hb ⟨fun i => y i / (2 * K), rfl⟩ ?_
  have h1 := hQ (fun i => y i / (2 * K))
  have e1 : ∑ i ∈ A, y i * (y i / (2 * K)) = (∑ i ∈ A, y i ^ 2) / (2 * K) := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ A, (y i / (2 * K)) ^ 2 = (∑ i ∈ A, y i ^ 2) / (2 * K) ^ 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  simp only at h1 ⊢
  rw [e1]
  rw [e2] at h1
  have hS : 0 ≤ ∑ i ∈ A, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have : 2 * K * ((∑ i ∈ A, y i ^ 2) / (2 * K) ^ 2) = (∑ i ∈ A, y i ^ 2) / (2 * K) := by
    field_simp
  linarith

/-- The `W*` comparison from the three stage-type comparators. -/
theorem wstar_comparison {ι : Type} (A : Finset ι) (X Λ : (ι → ℝ) → ℝ) (y : ι → ℝ)
    (b cL C₀ CL κ : ℝ) (hb : 0 ≤ b) (hΛ : 0 ≤ Λ y) (hcL : 0 < cL) (hκ : 0 < κ)
    (hlow : cL * b * Λ y ≤ X y) (hup : X y ≤ C₀ * (∑ i ∈ A, y i ^ 2) + CL * b * Λ y)
    (hl2 : κ * (∑ i ∈ A, y i ^ 2) ≤ X y) (hC₀ : 0 ≤ C₀) (hCL : 0 ≤ CL) :
    (min cL κ / 2) * ((∑ i ∈ A, y i ^ 2) + b * Λ y) ≤ X y ∧
      X y ≤ max C₀ CL * ((∑ i ∈ A, y i ^ 2) + b * Λ y) := by
  have hS : 0 ≤ ∑ i ∈ A, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hbΛ : 0 ≤ b * Λ y := mul_nonneg hb hΛ
  have m1 := min_le_left cL κ
  have m2 := min_le_right cL κ
  have M1 := le_max_left C₀ CL
  have M2 := le_max_right C₀ CL
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right m2 hS, mul_le_mul_of_nonneg_right m1 hbΛ]
  · nlinarith [mul_le_mul_of_nonneg_right M1 hS, mul_le_mul_of_nonneg_right M2 hbΛ]

/-- **Assembly initial comparison at a stage boundary.** A damped endpoint satisfying the
stage invariant has `c W ≤ D ≤ C W` (the `AssemblyInput.initialComparison` form) with
`b = stageScale u n₀ m · t` and constants depending only on `cP, CP, cL, CL, C₀`. -/
theorem initial_comparison_of_stageBounds {d m n₀ n : ℕ} {u cP CP cL CL C₀ : ℝ} (hm : 0 < m)
    (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (s : Endpoint (Torus d m)) (r : Torus d m → ℂ)
    (hD : IsDampedEndpoint s r (stageScale u n m)) (hne : s.active.Nonempty)
    (hcP : 0 < cP) (hcL : 0 < cL) (hCL : 0 ≤ CL) (hC₀ : 0 < C₀)
    (hSB : StageBounds d m n₀ n u cP CP cL CL C₀ s r) :
    ∀ f, (max C₀ CL)⁻¹ * spatialEnergy (nnGraph d m) s.active (stageScale u n₀ m * stageScale u n m) f ≤
        endpointEnergy s r (stageScale u n m) f ∧
      endpointEnergy s r (stageScale u n m) f ≤
        (min cL (1 / (2 * (CP * CP))) / 2)⁻¹ *
          spatialEnergy (nnGraph d m) s.active (stageScale u n₀ m * stageScale u n m) f := by
  classical
  set t := stageScale u n m with ht
  have htpos : 0 < t := stageScale_pos' hu n m
  have hbpos : 0 < stageScale u n₀ m * t := mul_pos (stageScale_pos' hu n₀ m) htpos
  unfold StageBounds at hSB
  dsimp only at hSB
  obtain ⟨hdiag, -, -, hker, -, -, hcomp⟩ := hSB
  have hp : ∀ i ∈ s.active, 0 ≤ (r i).im := fun i hi => hcP.le.trans (hdiag i hi).2.1
  have hCP : 0 < CP := hcP.trans_le ((hdiag _ hne.choose_spec).2.1.trans (hdiag _ hne.choose_spec).2.2.1)
  -- row bound K = CP²
  set e : s.active ≃ s.active := Equiv.refl _ with he
  obtain ⟨hsym, hward⟩ := ward_of_damped s r t htpos.le hD e
  have hzero := hD.2.1
  have hsymm : ∀ i j, ‖normalizedInverse s t i j‖ = ‖normalizedInverse s t j i‖ := by
    intro i j
    by_cases hi : i ∈ s.active
    · by_cases hj : j ∈ s.active
      · have hgs : s.g j i = s.g i j := congrFun (congrFun hsym ⟨i, hi⟩) ⟨j, hj⟩
        simp only [normalizedInverse, Matrix.smul_apply, smul_eq_mul, norm_mul]
        rw [hgs]
      · simp [normalizedInverse, hzero i j (Or.inr hj), hzero j i (Or.inl hj)]
    · simp [normalizedInverse, hzero i j (Or.inl hi), hzero j i (Or.inr hi)]
  have hrow : ∀ i ∈ s.active, (r i).im * ∑ j ∈ s.active, (r j).im * ‖normalizedInverse s t i j‖ ^ 2 ≤
      CP * CP := by
    intro i hi
    have hw := S45_ward_row (toS45 s r e) t hward ⟨i, hi⟩
    have hsum : ∑ j ∈ s.active, (r j).im * ‖normalizedInverse s t i j‖ ^ 2 = (r i).im := by
      rw [← Finset.sum_coe_sort s.active]
      refine Eq.trans ?_ (hw.symm.trans ?_)
      · rfl
      · simp only [AndersonAC.S45.State.q, toS45, he, Equiv.refl_apply]
        rw [(hdiag i hi).1]
    rw [hsum]
    have := (hdiag i hi).2.2.1
    nlinarith [hp i hi]
  have hK : 0 < CP * CP := mul_pos hCP hCP
  have hEle : ∀ f, endpointEnergy s r t f ≤ 2 * (CP * CP) * ∑ i ∈ s.active, f i ^ 2 := fun f =>
    wardEnergy_le_rows _ _ _ hp hsymm _ hrow f
  have hnn : ∀ f, 0 ≤ endpointEnergy s r t f := fun f => wardEnergy_nonneg _ _ hp _ f
  have hfr : AndersonAC.SolS78.FiniteRealForm s.active (endpointEnergy s r t) :=
    wardEnergy_finiteRealForm _ _ _
  have hΛ0 : ∀ y, 0 ≤ inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y := fun y =>
    inverseEnergy_nonneg_zero _ _ (by simp [gradientEnergy]) y
  have hW : ∀ y, neutral s.active y →
      (min cL (1 / (2 * (CP * CP))) / 2) * ((∑ i ∈ s.active, y i ^ 2) + (stageScale u n₀ m * t) *
          inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y) ≤
        inverseEnergy s.active (endpointEnergy s r t) y ∧
      inverseEnergy s.active (endpointEnergy s r t) y ≤
        max C₀ CL * ((∑ i ∈ s.active, y i ^ 2) + (stageScale u n₀ m * t) *
          inverseEnergy Finset.univ (gradientEnergy (nnGraph d m)) y) := by
    intro y hy
    obtain ⟨c1, c2, -⟩ := hcomp y hy
    have hb := (AndersonAC.SolS78.finiteFormInput_proof _ s.active _ hfr hnn hker).1 y hy
    have hl2 := inverseEnergy_ge_l2 s.active _ (CP * CP) hK hEle y hb
    have hl2' : (1 / (2 * (CP * CP))) * (∑ i ∈ s.active, y i ^ 2) ≤
        inverseEnergy s.active (endpointEnergy s r t) y := by
      rw [one_div_mul_eq_div]; exact hl2
    exact wstar_comparison s.active _ _ y _ cL C₀ CL _ hbpos.le (hΛ0 y) hcL (by positivity)
      (by linarith [c1]) (by linarith [c2]) hl2' hC₀.le hCL
  have hmin : 0 < min cL (1 / (2 * (CP * CP))) / 2 := by
    have : 0 < min cL (1 / (2 * (CP * CP))) := lt_min hcL (by positivity)
    linarith
  have hmax : 0 < max C₀ CL := lt_of_lt_of_le hC₀ (le_max_left _ _)
  intro f
  obtain ⟨o1, o2⟩ := initial_comparison hm s r t htpos hD hne hp hker _ _ _ hbpos hmin hmax hW f
  exact ⟨o1, o2⟩

end AndersonAC.AgentS78
