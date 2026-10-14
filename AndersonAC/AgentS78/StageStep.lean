import AndersonAC.S78.Definitions

/-!
WP10: `PathwiseStageInputs` from per-stage section endpoints (07-assembly.tex:939–1082,
proof of Proposition 7.5). One stage `n → n+1` is the ordinary sweep at the old scale
`t` (S45 `ordinary_sweep_endpoint`, transported by `AgentS78/S45Join.lean`), the
committed clearing assembly at `t'` (S78 `committed_assembly`, compared with its
initial state = the sweep output) and the diagonal reset at `t'` (S78 `diagonal_reset`).
`StageStep` records exactly the conclusions of these three results in S78 form; the
theorem `pathwise_of_steps` assembles the `PathwiseStageInputs` step fields from them
(the boundary fields are passed through). Constructing the actual random history that
supplies the `StageStep`s is the remaining WP10 construction.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace AndersonAC.AgentS78

open AndersonAC.S78

/-- Variational inverse form of an endpoint. -/
def Xof {d m : ℕ} (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (t : ℝ) :
    (Torus d m → ℝ) → ℝ :=
  inverseEnergy s.active (endpointEnergy s r t)

/-- Operator norm of `K = (√t g)^{∘2}`. -/
def Kn {d m : ℕ} (s : Endpoint (Torus d m)) (t : ℝ) : ℝ :=
  matrixNorm (squareKernel (normalizedInverse s t))

/-- The affine comparison target of a stage. -/
def stageTarget {d m : ℕ} (old : Endpoint (Torus d m)) (rOld : Torus d m → ℂ) (t t' : ℝ)
    (A : Finset (Torus d m)) (y : Torus d m → ℝ) : ℝ :=
  t' / t * Xof old rOld t y + (1 - t' / t) * ∑ i ∈ A, y i ^ 2 / (rOld i).im ^ 2

/-- Conclusions of the three section results along one stage, in S78 form. -/
structure StageStep (d m : ℕ) (C t t' : ℝ) (old new : Endpoint (Torus d m))
    (rOld rNew : Torus d m → ℂ) where
  /-- post-sweep endpoint at the new scale (frozen `rOld`) -/
  sw : Endpoint (Torus d m)
  /-- committed endpoint after the stage's clearings (frozen `rOld`) -/
  fin : Endpoint (Torus d m)
  sw_active : sw.active = old.active
  sw_affine : ∀ y, neutral old.active y →
    (1 - C * t ^ (0.10 * delta)) * stageTarget old rOld t t' old.active y ≤ Xof sw rOld t' y ∧
    Xof sw rOld t' y ≤ (1 + C * t ^ (0.10 * delta)) * stageTarget old rOld t t' old.active y
  sw_K : Kn sw t' ≤ Kn old t + C * t ^ (0.10 * delta)
  fin_nested : fin.active ⊆ sw.active
  fin_K : Kn fin t' ≤ Kn sw t' + t' ^ (0.10 * delta)
  fin_inv : ∀ y, neutral fin.active y →
    (1 + t' ^ (0.10 * delta))⁻¹ * Xof sw rOld t' y ≤ Xof fin rOld t' y ∧
    Xof fin rOld t' y ≤ (1 - t' ^ (0.10 * delta))⁻¹ * Xof sw rOld t' y
  new_active : new.active = fin.active
  r_close : ‖rNew - rOld‖ ≤ t' ^ (0.35 * delta)
  new_K : Kn new t' ≤ Kn fin t' + C * t' ^ (0.35 * delta)
  new_inv : ∀ y, neutral new.active y →
    (1 + C * t' ^ (0.35 * delta))⁻¹ * Xof fin rOld t' y ≤ Xof new rNew t' y ∧
    Xof new rNew t' y ≤ (1 - C * t' ^ (0.35 * delta))⁻¹ * Xof fin rOld t' y

theorem inverseEnergy_nonneg_zero {ι : Type} (A : Finset ι) (Q : (ι → ℝ) → ℝ) (hQ : Q 0 = 0)
    (y : ι → ℝ) : 0 ≤ inverseEnergy A Q y := by
  unfold inverseEnergy
  by_cases hb : BddAbove (Set.range fun f : ι → ℝ => 2 * (∑ i ∈ A, y i * f i) - Q f)
  · exact le_csSup_of_le hb ⟨0, rfl⟩ (by simp [hQ])
  · rw [Real.sSup_of_not_bddAbove hb]

theorem endpointEnergy_zero {ι : Type} (s : Endpoint ι) (r : ι → ℂ) (t : ℝ) :
    endpointEnergy s r t 0 = 0 := by
  simp [endpointEnergy, wardEnergy]

theorem Xof_nonneg {d m : ℕ} (s : Endpoint (Torus d m)) (r : Torus d m → ℂ) (t : ℝ)
    (y : Torus d m → ℝ) : 0 ≤ Xof s r t y :=
  inverseEnergy_nonneg_zero _ _ (endpointEnergy_zero s r t) y

theorem chain_lower (a b c T X1 X2 X3 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hT : 0 ≤ T)
    (h1 : (1 - a) * T ≤ X1) (h2 : (1 + b)⁻¹ * X1 ≤ X2) (h3 : (1 + c)⁻¹ * X2 ≤ X3) :
    (1 - (a + b + c)) * T ≤ X3 := by
  have hb1 : 0 < 1 + b := by linarith
  have hc1 : 0 < 1 + c := by linarith
  have e2 : (1 + b)⁻¹ * ((1 - a) * T) ≤ X2 :=
    (mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hb1.le)).trans h2
  have e3 : (1 + c)⁻¹ * ((1 + b)⁻¹ * ((1 - a) * T)) ≤ X3 :=
    (mul_le_mul_of_nonneg_left e2 (inv_nonneg.mpr hc1.le)).trans h3
  refine le_trans ?_ e3
  rw [show (1 + c)⁻¹ * ((1 + b)⁻¹ * ((1 - a) * T)) = (1 - a) * T / ((1 + b) * (1 + c)) by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  have hkey : (1 - (a + b + c)) * ((1 + b) * (1 + c)) ≤ 1 - a := by
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc, mul_nonneg (mul_nonneg ha hb) hc,
      mul_nonneg (mul_nonneg hb hb) hc, mul_nonneg (mul_nonneg hb hc) hc, sq_nonneg b, sq_nonneg c]
  nlinarith [mul_le_mul_of_nonneg_right hkey hT]

theorem chain_upper (a b c T X1 X2 X3 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha4 : a ≤ 1 / 4) (hb4 : b ≤ 1 / 4) (hc4 : c ≤ 1 / 4) (hT : 0 ≤ T)
    (h1 : X1 ≤ (1 + a) * T) (h2 : X2 ≤ (1 - b)⁻¹ * X1) (h3 : X3 ≤ (1 - c)⁻¹ * X2) :
    X3 ≤ (1 + 4 * (a + b + c)) * T := by
  have hb1 : 0 < 1 - b := by linarith
  have hc1 : 0 < 1 - c := by linarith
  have e2 : X2 ≤ (1 - b)⁻¹ * ((1 + a) * T) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hb1.le))
  have e3 : X3 ≤ (1 - c)⁻¹ * ((1 - b)⁻¹ * ((1 + a) * T)) :=
    h3.trans (mul_le_mul_of_nonneg_left e2 (inv_nonneg.mpr hc1.le))
  refine e3.trans ?_
  rw [show (1 - c)⁻¹ * ((1 - b)⁻¹ * ((1 + a) * T)) = (1 + a) * T / ((1 - b) * (1 - c)) by
    field_simp]
  rw [div_le_iff₀ (by positivity)]
  have hkey : 1 + a ≤ (1 + 4 * (a + b + c)) * ((1 - b) * (1 - c)) := by
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc, mul_nonneg (mul_nonneg ha hb) hc,
      mul_nonneg (mul_nonneg hb hb) hc, mul_nonneg (mul_nonneg hb hc) hc, sq_nonneg b, sq_nonneg c,
      mul_nonneg (mul_nonneg hb hc) hb]
  nlinarith [mul_le_mul_of_nonneg_right hkey hT]

theorem neutral_mono {ι : Type} [Fintype ι] {A B : Finset ι} (hAB : A ⊆ B) {y : ι → ℝ}
    (hy : neutral A y) : neutral B y := by
  refine ⟨fun i hi => hy.1 i (fun h => hi (hAB h)), ?_⟩
  rw [← Finset.sum_subset hAB (fun i _ hi => hy.1 i hi)]
  exact hy.2

theorem sum_target_mono {ι : Type} [Fintype ι] {A B : Finset ι} (hAB : A ⊆ B) {y : ι → ℝ}
    (hy : ∀ i ∉ A, y i = 0) (w : ι → ℝ) :
    ∑ i ∈ B, y i ^ 2 / w i = ∑ i ∈ A, y i ^ 2 / w i := by
  rw [← Finset.sum_subset hAB (fun i _ hi => by simp [hy i hi])]

theorem rpow_le_of_scale {t t' e e' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (ht1 : t ≤ 1)
    (he : 0 ≤ e) (hee : e ≤ e') : t' ^ e' ≤ t ^ e :=
  (Real.rpow_le_rpow_of_exponent_ge ht' (htt.trans ht1) hee).trans
    (Real.rpow_le_rpow ht'.le htt he)

/-- **One stage of Proposition 7.5's step fields** from the three section conclusions. -/
theorem stage_step_fields {d m : ℕ} {C t t' : ℝ} {old new : Endpoint (Torus d m)}
    {rOld rNew : Torus d m → ℂ} (S : StageStep d m C t t' old new rOld rNew)
    (hC : 1 ≤ C) (ht' : 0 < t') (htt : t' ≤ t) (ht1 : t ≤ 1)
    (hsmall : C * t ^ (0.10 * delta) ≤ 1 / 4) :
    new.active ⊆ old.active ∧
    Kn new t' ≤ Kn old t + (2 * C + 1) * t ^ (0.10 * delta) ∧
    ‖rNew - rOld‖ ≤ t ^ (0.35 * delta) ∧
    ∀ y, neutral new.active y →
      (1 - (8 * C + 4) * t ^ (0.10 * delta)) *
          stageTarget old rOld t t' new.active y ≤ Xof new rNew t' y ∧
      Xof new rNew t' y ≤ (1 + (8 * C + 4) * t ^ (0.10 * delta)) *
          stageTarget old rOld t t' new.active y := by
  have hd0 : (0 : ℝ) ≤ delta := by norm_num [delta]
  have hτ : t' ^ (0.10 * delta) ≤ t ^ (0.10 * delta) :=
    rpow_le_of_scale ht' htt ht1 (by positivity) le_rfl
  have hσ : t' ^ (0.35 * delta) ≤ t ^ (0.10 * delta) :=
    rpow_le_of_scale ht' htt ht1 (by positivity) (by nlinarith)
  have hσσ : t' ^ (0.35 * delta) ≤ t ^ (0.35 * delta) :=
    rpow_le_of_scale ht' htt ht1 (by positivity) le_rfl
  have htpos : 0 < t := ht'.trans_le htt
  have hτ0 : 0 ≤ t ^ (0.10 * delta) := Real.rpow_nonneg htpos.le _
  have hτ'0 : 0 ≤ t' ^ (0.10 * delta) := Real.rpow_nonneg ht'.le _
  have hσ'0 : 0 ≤ t' ^ (0.35 * delta) := Real.rpow_nonneg ht'.le _
  have hnested : new.active ⊆ old.active := by
    rw [S.new_active, ← S.sw_active]; exact S.fin_nested
  refine ⟨hnested, ?_, S.r_close.trans hσσ, ?_⟩
  · have := S.new_K; have := S.fin_K; have := S.sw_K
    nlinarith
  · intro y hy
    have hyfin : neutral S.fin.active y := S.new_active ▸ hy
    have hyold : neutral old.active y := neutral_mono hnested hy
    have hT : stageTarget old rOld t t' old.active y = stageTarget old rOld t t' new.active y := by
      unfold stageTarget
      rw [sum_target_mono hnested hy.1]
    have hθ0 : 0 ≤ t' / t := div_nonneg ht'.le htpos.le
    have hθ1 : t' / t ≤ 1 := (div_le_one htpos).mpr htt
    have hT0 : 0 ≤ stageTarget old rOld t t' new.active y := by
      unfold stageTarget
      have := Xof_nonneg old rOld t y
      have : 0 ≤ ∑ i ∈ new.active, y i ^ 2 / (rOld i).im ^ 2 :=
        Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
      have : 0 ≤ 1 - t' / t := by linarith
      positivity
    obtain ⟨s1, s2⟩ := S.sw_affine y hyold
    obtain ⟨f1, f2⟩ := S.fin_inv y hyfin
    obtain ⟨n1, n2⟩ := S.new_inv y hy
    rw [hT] at s1 s2
    have ha : 0 ≤ C * t ^ (0.10 * delta) := by positivity
    have hc : 0 ≤ C * t' ^ (0.35 * delta) := by positivity
    have hcle : C * t' ^ (0.35 * delta) ≤ C * t ^ (0.10 * delta) :=
      mul_le_mul_of_nonneg_left hσ (by linarith)
    have hble : t' ^ (0.10 * delta) ≤ C * t ^ (0.10 * delta) := by nlinarith
    have hsum : C * t ^ (0.10 * delta) + t' ^ (0.10 * delta) + C * t' ^ (0.35 * delta) ≤
        (2 * C + 1) * t ^ (0.10 * delta) := by nlinarith
    constructor
    · have h := chain_lower _ _ _ _ _ _ _ ha hτ'0 hc hT0 s1 f1 n1
      refine le_trans ?_ h
      apply mul_le_mul_of_nonneg_right _ hT0
      nlinarith
    · have h := chain_upper _ _ _ _ _ _ _ ha hτ'0 hc hsmall (hble.trans hsmall)
        (hcle.trans hsmall) hT0 s2 f2 n2
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_right _ hT0
      nlinarith

theorem stageScale_pos' {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (n m : ℕ) : 0 < stageScale u n m := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  unfold stageScale; positivity

theorem stageScale_anti {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {n n' : ℕ} (m : ℕ) (h : n ≤ n') :
    stageScale u n' m ≤ stageScale u n m := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  unfold stageScale
  have : u / (4 : ℝ) ^ n' ≤ u / (4 : ℝ) ^ n :=
    div_le_div_of_nonneg_left hu0.le (by positivity) (pow_le_pow_right₀ (by norm_num) h)
  linarith

theorem stageScale_le_one {u : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) : stageScale u n m ≤ 1 := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu.1
  unfold stageScale
  have h1 : ∀ k : ℕ, 1 ≤ k → u / (4 : ℝ) ^ k ≤ 1 / 2 := by
    intro k hk
    rw [div_le_iff₀ (by positivity)]
    have : (4 : ℝ) ≤ 4 ^ k := by
      calc (4 : ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hk
    nlinarith [hu.2]
  linarith [h1 n hn, h1 m hm]

/-- **`PathwiseStageInputs` from the per-stage section conclusions.** Given the stage
endpoints, one `StageStep` per stage and the boundary facts at each stage start, the
history is a `PathwiseStageInputs` with constant `8C+4`. -/
def pathwise_of_steps {d m n₀ : ℕ} {u C : ℝ} (hu : u ∈ Set.Ioc (1 / 4 : ℝ) 1) (hC : 1 ≤ C)
    (hn₀ : 1 ≤ n₀) (state : ℕ → Endpoint (Torus d m)) (r : ℕ → Torus d m → ℂ)
    (hsmall : C * stageScale u n₀ m ^ (0.10 * delta) ≤ 1 / 4)
    (step : ∀ n, n₀ ≤ n → n < m → StageStep d m C (stageScale u n m) (stageScale u (n + 1) m)
      (state n) (state (n + 1)) (r n) (r (n + 1)))
    (physical : ∀ n, n₀ ≤ n → n ≤ m → IsDampedEndpoint (state n) (r n) (stageScale u n m))
    (reset : ∀ n, n₀ ≤ n → n ≤ m → ∀ i ∈ (state n).active, (state n).g i i = r n i)
    (rows : ∀ n, n₀ ≤ n → n ≤ m → ∀ i,
      rowFour (normalizedInverse (state n) (stageScale u n m)) i ≤ stageScale u n m ^ (1 + delta))
    (kernels : ∀ n, n₀ ≤ n → n ≤ m →
      constantKernel (state n).active (endpointEnergy (state n) (r n) (stageScale u n m)))
    (counts : ∀ n, n₀ ≤ n → n ≤ m → Fintype.card (Torus d m) ≤ 2 * (state n).active.card)
    (metrics : ∀ n, n₀ ≤ n → n ≤ m → ∀ x y,
      physicalDistance d m x y / 2 - stageScale u n m ^ (-1.03 : ℝ) ≤
        terminalDistance (nnGraph d m) (Finset.univ \ (state n).active) x y) :
    PathwiseStageInputs d m n₀ u (8 * C + 4) where
  state := state
  r := r
  physical := physical
  nested := fun n h1 h2 =>
    (stage_step_fields (step n h1 h2) hC (stageScale_pos' hu _ _) (stageScale_anti hu m (Nat.le_succ n))
      (stageScale_le_one hu (hn₀.trans h1) (by omega))
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (stageScale_pos' hu _ _).le
        (stageScale_anti hu m h1) (by norm_num [delta])) (by linarith)).trans hsmall)).1
  reset := reset
  rows := rows
  normStep := fun n h1 h2 => by
    have F := stage_step_fields (step n h1 h2) hC (stageScale_pos' hu _ _)
      (stageScale_anti hu m (Nat.le_succ n)) (stageScale_le_one hu (hn₀.trans h1) (by omega))
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (stageScale_pos' hu _ _).le
        (stageScale_anti hu m h1) (by norm_num [delta])) (by linarith)).trans hsmall)
    have h0 : 0 ≤ stageScale u n m ^ (0.10 * delta) := Real.rpow_nonneg (stageScale_pos' hu _ _).le _
    have := F.2.1
    unfold Kn at this
    nlinarith
  rStep := fun n h1 h2 => by
    have F := stage_step_fields (step n h1 h2) hC (stageScale_pos' hu _ _)
      (stageScale_anti hu m (Nat.le_succ n)) (stageScale_le_one hu (hn₀.trans h1) (by omega))
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (stageScale_pos' hu _ _).le
        (stageScale_anti hu m h1) (by norm_num [delta])) (by linarith)).trans hsmall)
    have h0 : 0 ≤ stageScale u n m ^ (0.35 * delta) := Real.rpow_nonneg (stageScale_pos' hu _ _).le _
    have := F.2.2.1
    nlinarith
  kernels := kernels
  counts := counts
  metrics := metrics
  affineStep := fun n h1 h2 y hy => by
    have F := stage_step_fields (step n h1 h2) hC (stageScale_pos' hu _ _)
      (stageScale_anti hu m (Nat.le_succ n)) (stageScale_le_one hu (hn₀.trans h1) (by omega))
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (stageScale_pos' hu _ _).le
        (stageScale_anti hu m h1) (by norm_num [delta])) (by linarith)).trans hsmall)
    exact F.2.2.2 y hy

end AndersonAC.AgentS78
