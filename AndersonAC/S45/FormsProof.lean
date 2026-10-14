import AndersonAC.S45.Definitions

noncomputable section

open Matrix
open scoped BigOperators Pointwise

namespace AndersonAC.AgentS45

theorem port_decay_proof {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I]
    (s : AndersonAC.S45.State I) (v : AndersonAC.S45.PortMap P I)
    (dist : I → I → ℝ) (t C c : ℝ)
    (hC : 0 ≤ C) (hk : ∀ x, 0 ≤ v.weight x ∧ v.weight x ≤ 1)
    (hdecay : ∀ i j, ‖s.h t i j‖ ≤ C * Real.exp (-c * dist i j)) :
    ∀ x y, ‖(v.liftState s).h t x y‖ ≤
      C * Real.exp (-c * dist (v.site x) (v.site y)) := by
  intro x y
  have hweights : 0 ≤ v.weight x * v.weight y ∧ v.weight x * v.weight y ≤ 1 := by
    constructor
    · exact mul_nonneg (hk x).1 (hk y).1
    · nlinarith [mul_le_mul_of_nonneg_left (hk y).2 (hk x).1,
        mul_le_mul_of_nonneg_right (hk x).2 (hk y).1]
  have hfactor :
      ‖(v.liftState s).h t x y‖ =
        ‖(Real.sqrt t : ℂ)‖ *
          (‖s.g (v.site x) (v.site y)‖ * (v.weight x * v.weight y)) := by
    simp only [AndersonAC.S45.State.h]
    rw [Matrix.smul_apply]
    simp [AndersonAC.S45.PortMap.liftState, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hk x).1, abs_of_nonneg (hk y).1,
      mul_assoc, mul_left_comm, mul_comm]
  have holdnorm : ‖s.h t (v.site x) (v.site y)‖ =
      ‖(Real.sqrt t : ℂ)‖ * ‖s.g (v.site x) (v.site y)‖ := by
    simp [AndersonAC.S45.State.h, Matrix.smul_apply, norm_mul]
  rw [hfactor]
  calc
    ‖(Real.sqrt t : ℂ)‖ *
        (‖s.g (v.site x) (v.site y)‖ * (v.weight x * v.weight y))
        = (v.weight x * v.weight y) *
          (‖(Real.sqrt t : ℂ)‖ * ‖s.g (v.site x) (v.site y)‖) := by ring
    _ ≤ ‖s.h t (v.site x) (v.site y)‖ := by
      rw [holdnorm]
      calc
        (v.weight x * v.weight y) *
            (‖(Real.sqrt t : ℂ)‖ * ‖s.g (v.site x) (v.site y)‖)
            ≤ 1 * (‖(Real.sqrt t : ℂ)‖ * ‖s.g (v.site x) (v.site y)‖) :=
              mul_le_mul_of_nonneg_right hweights.2
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖(Real.sqrt t : ℂ)‖ * ‖s.g (v.site x) (v.site y)‖ := by ring
    _ ≤ C * Real.exp (-c * dist (v.site x) (v.site y)) := hdecay _ _

private theorem sum_inv_sq_le {I : Type*} [Fintype I]
    (p y : I → ℝ) (C : ℝ) (hC : 0 < C)
    (hp : ∀ i, 1 / C ≤ p i ∧ p i ≤ C) :
    (∑ i, y i ^ 2 / p i ^ 2) ≤ C ^ 2 * AndersonAC.S45.l2sq y := by
  have hp_pos : ∀ i, 0 < p i := by
    intro i
    have h := (hp i).1
    have : 0 < 1 / C := by positivity
    exact lt_of_lt_of_le this h
  have hterm : ∀ i, y i ^ 2 / p i ^ 2 ≤ C ^ 2 * y i ^ 2 := by
    intro i
    have hmul : 1 ≤ C * p i := by
      have := (hp i).1
      have hmul' := (div_le_iff₀ hC).mp this
      nlinarith [hmul']
    have hsq : 1 ≤ C ^ 2 * p i ^ 2 := by nlinarith [sq_nonneg (C * p i - 1)]
    have hinv : 1 / p i ^ 2 ≤ C ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (hp_pos i))).2
      nlinarith
    calc
      y i ^ 2 / p i ^ 2 = y i ^ 2 * (1 / p i ^ 2) := by ring
      _ ≤ y i ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_left hinv (sq_nonneg (y i))
      _ = C ^ 2 * y i ^ 2 := by ring
  have hl2 : AndersonAC.S45.l2sq y = ∑ i, y i ^ 2 := by
    simp [AndersonAC.S45.l2sq, Real.norm_eq_abs, sq_abs]
  rw [hl2]
  calc
    (∑ i, y i ^ 2 / p i ^ 2) ≤ ∑ i, C ^ 2 * y i ^ 2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = C ^ 2 * ∑ i, y i ^ 2 := by rw [Finset.mul_sum]

theorem comparator_transport_proof {I : Type*} [Fintype I]
    (Xold Xnew Λplus : AndersonAC.S45.Form I) (p : I → ℝ)
    (t b θ ε cLow cHigh C0 C : ℝ)
    (hθ : 0 < θ ∧ θ < 1) (hε : 0 ≤ ε ∧ ε < 1)
    (hC : 0 < C) (hp : ∀ i, 1 / C ≤ p i ∧ p i ≤ C)
    (hc : 0 ≤ cLow ∧ 0 ≤ cHigh) (htb : 0 ≤ t ∧ 0 ≤ b)
    (hΛ : ∀ y, AndersonAC.S45.neutral y → 0 ≤ Λplus y)
    (hlower : ∀ y, AndersonAC.S45.neutral y → cLow * b * Λplus y ≤ Xold y)
    (hrough : ∀ y, AndersonAC.S45.neutral y →
      Xold y ≤ C0 * AndersonAC.S45.l2sq y + cHigh * b * Λplus y)
    (hsharp : ∀ y, AndersonAC.S45.neutral y →
      Xold y ≤ (1 + AndersonAC.S45.power t AndersonAC.S45.kappa) *
        (∑ i, y i ^ 2 / p i ^ 2) + cHigh * t * Λplus y)
    (hmix : ∀ y, AndersonAC.S45.neutral y →
      (1 - ε) * (θ * Xold y + (1 - θ) * (∑ i, y i ^ 2 / p i ^ 2)) ≤ Xnew y ∧
      Xnew y ≤ (1 + ε) * (θ * Xold y + (1 - θ) * (∑ i, y i ^ 2 / p i ^ 2))) :
    ∀ y, AndersonAC.S45.neutral y →
      (1 - ε) * cLow * (θ * b) * Λplus y ≤ Xnew y ∧
      Xnew y ≤ (1 + ε) * ((θ * C0 + C ^ 2) * AndersonAC.S45.l2sq y +
        cHigh * (θ * b) * Λplus y) ∧
      Xnew y ≤ (1 + ε) * ((1 + θ * AndersonAC.S45.power t AndersonAC.S45.kappa) *
        (∑ i, y i ^ 2 / p i ^ 2) + cHigh * (θ * t) * Λplus y) := by
  intro y hy
  have hdiag := sum_inv_sq_le p y C hC hp
  have hdiag_nonneg : 0 ≤ ∑ i, y i ^ 2 / p i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    positivity
  have hl2_nonneg : 0 ≤ AndersonAC.S45.l2sq y := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖y i‖)
  have htheta0 : 0 ≤ θ := hθ.1.le
  have htheta1 : 0 ≤ 1 - θ := by linarith [hθ.2]
  have heps0 : 0 ≤ 1 - ε := by linarith [hε.2]
  have heps1 : 0 ≤ 1 + ε := by linarith [hε.1]
  have hm := hmix y hy
  have hlow := hlower y hy
  have hrough' := hrough y hy
  have hsharp' := hsharp y hy
  constructor
  · have hbase : θ * (cLow * b * Λplus y) ≤
        θ * Xold y + (1 - θ) * (∑ i, y i ^ 2 / p i ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hlow htheta0
      nlinarith [mul_nonneg htheta1 hdiag_nonneg]
    have hscaled := mul_le_mul_of_nonneg_left hbase heps0
    calc
      (1 - ε) * cLow * (θ * b) * Λplus y =
          (1 - ε) * (θ * (cLow * b * Λplus y)) := by ring
      _ ≤ (1 - ε) * (θ * Xold y + (1 - θ) * (∑ i, y i ^ 2 / p i ^ 2)) := hscaled
      _ ≤ Xnew y := hm.1
  constructor
  · have hrough_mix :
        θ * Xold y + (1 - θ) * (∑ i, y i ^ 2 / p i ^ 2) ≤
          (θ * C0 + C ^ 2) * AndersonAC.S45.l2sq y +
            cHigh * (θ * b) * Λplus y := by
      nlinarith [mul_le_mul_of_nonneg_left hrough' htheta0,
        mul_le_mul_of_nonneg_left hdiag htheta1,
        mul_nonneg htheta0 (mul_nonneg (sq_nonneg C) hl2_nonneg)]
    nlinarith [mul_le_mul_of_nonneg_left hrough_mix heps1, hm.2]
  · have htκ : 0 ≤ AndersonAC.S45.power t AndersonAC.S45.kappa := by
      unfold AndersonAC.S45.power
      exact Real.rpow_nonneg htb.1 _
    have hsharp_mix :
        θ * Xold y + (1 - θ) * (∑ i, y i ^ 2 / p i ^ 2) ≤
          (1 + θ * AndersonAC.S45.power t AndersonAC.S45.kappa) *
              (∑ i, y i ^ 2 / p i ^ 2) + cHigh * (θ * t) * Λplus y := by
      nlinarith [mul_le_mul_of_nonneg_left hsharp' htheta0,
        mul_nonneg htheta1 hdiag_nonneg,
        mul_nonneg htheta0 (mul_nonneg htκ hdiag_nonneg)]
    nlinarith [mul_le_mul_of_nonneg_left hsharp_mix heps1, hm.2]

private theorem rpow_quarter_fourth (a : ℝ) (ha : 0 ≤ a) :
    AndersonAC.S45.power a (1 / 4) ^ 4 = a := by
  change (Real.rpow a (1 / 4 : ℝ)) ^ 4 = a
  calc
    (Real.rpow a (1 / 4 : ℝ)) ^ 4 =
        Real.rpow a ((1 / 4 : ℝ) * 4) :=
          (Real.rpow_mul_natCast ha (1 / 4 : ℝ) 4).symm
    _ = a := by norm_num [Real.rpow_one]

private theorem rpow_quarter_sq (a : ℝ) (ha : 0 ≤ a) :
    AndersonAC.S45.power a (1 / 4) ^ 2 = Real.sqrt a := by
  change (Real.rpow a (1 / 4 : ℝ)) ^ 2 = Real.sqrt a
  calc
    (Real.rpow a (1 / 4 : ℝ)) ^ 2 = Real.rpow a ((1 / 4 : ℝ) * 2) :=
      (Real.rpow_mul_natCast ha (1 / 4 : ℝ) 2).symm
    _ = Real.sqrt a := by rw [Real.sqrt_eq_rpow]; congr 1 <;> norm_num

private theorem qform_matrix_smul {I : Type*} [Fintype I]
    (D : AndersonAC.S45.RMat I) (a : ℝ) (f : I → ℝ) :
    AndersonAC.S45.qform (a • D) f = a * AndersonAC.S45.qform D f := by
  simp only [AndersonAC.S45.qform, Matrix.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  have hrow (i : I) :
      (∑ j, a * D i j * f j) = a * (∑ j, D i j * f j) := by
    calc
      (∑ j, a * D i j * f j) = ∑ j, a * (D i j * f j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = a * (∑ j, D i j * f j) := by rw [← Finset.mul_sum]
  calc
    (∑ i, f i * (∑ j, a * D i j * f j)) =
        ∑ i, a * (f i * (∑ j, D i j * f j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrow i]
      ring
    _ = a * (∑ i, f i * (∑ j, D i j * f j)) := by
      exact (Finset.univ.mul_sum (fun i => f i * (∑ j, D i j * f j)) a).symm

private theorem qform_vector_smul {I : Type*} [Fintype I]
    (D : AndersonAC.S45.RMat I) (a : ℝ) (f : I → ℝ) :
    AndersonAC.S45.qform D (a • f) = a ^ 2 * AndersonAC.S45.qform D f := by
  simp only [AndersonAC.S45.qform, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  have hrow (i : I) :
      (∑ j, D i j * (a * f j)) = a * (∑ j, D i j * f j) := by
    calc
      (∑ j, D i j * (a * f j)) = ∑ j, a * (D i j * f j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = a * (∑ j, D i j * f j) := by rw [← Finset.mul_sum]
  calc
    (∑ i, a * f i * (∑ j, D i j * (a * f j))) =
        ∑ i, a ^ 2 * (f i * (∑ j, D i j * f j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrow i]
      ring
    _ = a ^ 2 * (∑ i, f i * (∑ j, D i j * f j)) := by
      exact (Finset.univ.mul_sum (fun i => f i * (∑ j, D i j * f j)) (a ^ 2)).symm

private theorem charge_sum_smul {I : Type*} [Fintype I]
    (y f : I → ℝ) (a : ℝ) :
    (∑ i, y i * (a * f i)) = a * (∑ i, y i * f i) := by
  calc
    (∑ i, y i * (a * f i)) = ∑ i, a * (y i * f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * (∑ i, y i * f i) := by rw [← Finset.mul_sum]

private theorem dualForm_qform_matrix_smul {I : Type*} [Fintype I]
    (D : AndersonAC.S45.RMat I) (a : ℝ) (ha : 0 < a) (y : I → ℝ) :
    AndersonAC.S45.dualForm (AndersonAC.S45.qform (a • D)) y =
      (1 / a) * AndersonAC.S45.dualForm (AndersonAC.S45.qform D) y := by
  let S : Set ℝ := {z | ∃ f : I → ℝ,
    z = 2 * (∑ i, y i * f i) - AndersonAC.S45.qform D f}
  let T : Set ℝ := {z | ∃ f : I → ℝ,
    z = 2 * (∑ i, y i * f i) - AndersonAC.S45.qform (a • D) f}
  have hsets : T = (1 / a) • S := by
    ext z
    constructor
    · rintro ⟨f, rfl⟩
      rw [Set.mem_smul_set]
      refine ⟨2 * (∑ i, y i * (a • f) i) - AndersonAC.S45.qform D (a • f), ?_, ?_⟩
      · exact ⟨a • f, rfl⟩
      · simp only [smul_eq_mul, Pi.smul_apply]
        rw [qform_vector_smul, qform_matrix_smul]
        simp [charge_sum_smul]
        field_simp [ne_of_gt ha]
    · rw [Set.mem_smul_set]
      rintro ⟨u, ⟨f, rfl⟩, hz⟩
      refine ⟨(1 / a) • f, ?_⟩
      simp only [smul_eq_mul, Pi.smul_apply]
      rw [qform_matrix_smul, qform_vector_smul]
      have hcandidate :
          2 * (∑ i, y i * ((1 / a) * f i)) -
              a * ((1 / a) ^ 2 * AndersonAC.S45.qform D f) =
            (1 / a) * (2 * (∑ i, y i * f i) - AndersonAC.S45.qform D f) := by
        rw [charge_sum_smul]
        field_simp [ne_of_gt ha]
      calc
        z = (1 / a) * (2 * (∑ i, y i * f i) - AndersonAC.S45.qform D f) := hz.symm
        _ = 2 * (∑ i, y i * ((1 / a) * f i)) -
              a * ((1 / a) ^ 2 * AndersonAC.S45.qform D f) := hcandidate.symm
  change sSup T = (1 / a) * sSup S
  rw [hsets, Real.sSup_smul_of_nonneg (by positivity) S]
  rfl

theorem reserve_scaling_proof {I : Type*} [Fintype I] [DecidableEq I]
    (s : AndersonAC.S45.State I) (t θ : ℝ) (hθ : 0 < θ) :
    let v : AndersonAC.S45.PortMap I I := ⟨id, fun _ => AndersonAC.S45.power θ (1 / 4)⟩
    (v.liftState s).h t = s.h (θ * t) ∧
    (v.liftState s).D t = θ • s.D (θ * t) ∧
    (∀ y, θ * (v.liftState s).X t y = s.X (θ * t) y) := by
  dsimp
  let w : ℝ := AndersonAC.S45.power θ (1 / 4)
  have hw2 : w ^ 2 = Real.sqrt θ := by
    exact rpow_quarter_sq θ hθ.le
  have hroot : Real.sqrt t * w ^ 2 = Real.sqrt (θ * t) := by
    rw [hw2]
    rw [mul_comm (Real.sqrt t) (Real.sqrt θ), ← Real.sqrt_mul hθ.le]
  have hrootC : (Real.sqrt t : ℂ) * (w : ℂ) ^ 2 = (Real.sqrt (θ * t) : ℂ) := by
    exact_mod_cast hroot
  have hww : w * w = Real.sqrt θ := by nlinarith [hw2]
  let v : AndersonAC.S45.PortMap I I := ⟨id, fun _ => w⟩
  have hh : (v.liftState s).h t = s.h (θ * t) := by
    ext i j
    simp only [AndersonAC.S45.State.h]
    rw [Matrix.smul_apply, Matrix.smul_apply]
    simp only [smul_eq_mul, v, AndersonAC.S45.PortMap.liftState, id_eq]
    change (Real.sqrt t : ℂ) * ((w : ℂ) * (w : ℂ) * s.g (id i) (id j)) =
      (Real.sqrt (θ * t) : ℂ) * s.g (id i) (id j)
    calc
      (Real.sqrt t : ℂ) * ((w : ℂ) * (w : ℂ) * s.g (id i) (id j)) =
          ((Real.sqrt t : ℂ) * (w : ℂ) ^ 2) * s.g (id i) (id j) := by ring
      _ = (Real.sqrt (θ * t) : ℂ) * s.g (id i) (id j) := by rw [hrootC]
  have hp : ∀ i, (v.liftState s).p i = Real.sqrt θ * s.p i := by
    intro i
    simp only [AndersonAC.S45.State.p, v, AndersonAC.S45.PortMap.liftState]
    change (((w : ℂ) ^ 2 * s.r (id i)).im) = Real.sqrt θ * (s.r i).im
    have hwcast : (w : ℂ) ^ 2 = ((w ^ 2 : ℝ) : ℂ) := by norm_cast
    rw [hwcast, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    simp [hw2, Function.id_def]
  have hq : ∀ i, (v.liftState s).q i = Real.sqrt θ * s.q i := by
    intro i
    simp only [AndersonAC.S45.State.q, v, AndersonAC.S45.PortMap.liftState]
    change (((w : ℂ) * (w : ℂ) * s.g (id i) (id i)).im) =
      Real.sqrt θ * (s.g i i).im
    have hwcast : (w : ℂ) * (w : ℂ) = ((w * w : ℝ) : ℂ) := by norm_cast
    rw [hwcast, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    simp [hww, Function.id_def]
  have hF : ∀ i j, (v.liftState s).F t i j = s.F (θ * t) i j := by
    intro i j
    simp [AndersonAC.S45.State.F, AndersonAC.S45.entryAbsSquare, hh]
  have hD : (v.liftState s).D t = θ • s.D (θ * t) := by
    ext i j
    simp [AndersonAC.S45.State.D, hp, hq, hF,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp
      ring_nf
      rw [Real.sq_sqrt hθ.le]
      ring
    · simp [hij]
      ring_nf
      rw [Real.sq_sqrt hθ.le]
      ring
  have hX : ∀ y, (v.liftState s).X t y =
      (1 / θ) * s.X (θ * t) y := by
    intro y
    rw [AndersonAC.S45.State.X, AndersonAC.S45.State.X, hD]
    exact dualForm_qform_matrix_smul (s.D (θ * t)) θ hθ y
  refine ⟨hh, hD, ?_⟩
  intro y
  rw [hX y]
  field_simp [ne_of_gt hθ]

end AndersonAC.AgentS45
