import AndersonAC.S3H.Quadrature
import AndersonAC.S3.Comparators

/-!
Lemma 3.2 of §3 (`lem:fourier-charge`): the low-frequency sum
`N⁻¹ Σ_{0<|θ|≤a} ℓ(θ)⁻¹ ≤ C a` (dimension `d ≥ 3`, `a ≤ 1`) by sup-norm level sets,
and the charge estimate `⟨y_Σ, Λ⁺ y_Σ⟩ ≤ C ‖y‖₁^{4/3} ‖y‖₂^{2/3}`.
-/

noncomputable section
open scoped BigOperators
open AndersonAC.S3H

namespace AndersonAC.S3

variable {d : ℕ}

theorem hsq_ge (x : ℝ) (hx : |x| ≤ Real.pi) : 4 / Real.pi ^ 2 * x ^ 2 ≤ hsq x := by
  have hpi := Real.pi_pos
  have hs : |x| / 2 ≤ Real.pi / 2 := by linarith
  have hsin := Real.mul_le_sin (x := |x| / 2) (by positivity) hs
  have e : hsq x = 4 * Real.sin (|x| / 2) ^ 2 := by
    unfold hsq
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_div, Real.sin_neg, neg_sq]
  rw [e]
  have h2 : 2 / Real.pi * (|x| / 2) = |x| / Real.pi := by field_simp
  rw [h2] at hsin
  have h3 : (|x| / Real.pi) ^ 2 ≤ Real.sin (|x| / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin 2
  have h4 : 4 / Real.pi ^ 2 * x ^ 2 = 4 * (|x| / Real.pi) ^ 2 := by
    rw [div_pow, sq_abs]; field_simp
  linarith

theorem laplacianSymbol_ge_radius {L : ℕ} [NeZero L] (ζ : Torus d L) :
    4 / Real.pi ^ 2 * radius (gridAngle ζ) ^ 2 ≤ laplacianSymbol (gridAngle ζ) := by
  rw [laplacianSymbol_eq_sum, radius_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => hsq_ge _ ?_
  have hb := angle1_bounds (ζ j)
  rw [← gridAngle_apply] at hb
  exact abs_le.mpr ⟨hb.1, hb.2.le⟩

theorem maxAbs_le_floor {L : ℕ} [NeZero L] (ζ : Torus d L) {a : ℝ} (ha : 0 ≤ a)
    (hr : radius (gridAngle ζ) ≤ a) :
    maxAbs d L ζ ≤ ⌊a * L / (2 * Real.pi)⌋₊ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  unfold maxAbs
  apply Finset.sup_le
  intro j _
  apply Nat.le_floor
  have hθ : |gridAngle ζ j| ≤ a := by
    refine le_trans ?_ hr
    have h1 : gridAngle ζ j ^ 2 ≤ radius (gridAngle ζ) ^ 2 := by
      rw [radius_sq_eq]
      exact Finset.single_le_sum (f := fun i => gridAngle ζ i ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : 0 ≤ radius (gridAngle ζ) := Real.sqrt_nonneg _
    nlinarith [sq_abs (gridAngle ζ j), abs_nonneg (gridAngle ζ j)]
  rw [gridAngle_eq, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    abs_of_pos hL] at hθ
  rw [le_div_iff₀ (by positivity)]
  rw [div_le_iff₀ hL] at hθ
  have : (((centered L (ζ j)).natAbs : ℕ) : ℝ) = |((centered L (ζ j) : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [this]
  linarith

/-- **Low-frequency sum** (§3, eq. `initial-frequency-sum`). -/
theorem ball_frequency_sum (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L → ∀ a : ℝ, 0 < a → a ≤ 1 →
      gridAvgReal (fun ζ : Torus d L =>
        if 0 < radius (gridAngle ζ) ∧ radius (gridAngle ζ) ≤ a
          then (laplacianSymbol (gridAngle ζ))⁻¹ else 0) ≤ C * a := by
  have hpi := Real.pi_pos
  set K : ℝ := 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) with hK
  refine ⟨Real.pi ^ 2 / 4 * (1 / (2 * Real.pi)) ^ 2 * K * (1 / (2 * Real.pi)) ^ (d - 2),
    by positivity, fun L _ hL a ha ha1 => ?_⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  set J : ℕ := ⌊a * L / (2 * Real.pi)⌋₊ with hJ
  set g : Torus d L → ℝ := fun ζ =>
    if maxAbs d L ζ ≤ J then (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ else 0 with hg
  -- termwise comparison
  have hterm : ∀ ζ : Torus d L,
      (if 0 < radius (gridAngle ζ) ∧ radius (gridAngle ζ) ≤ a
        then (laplacianSymbol (gridAngle ζ))⁻¹ else 0) ≤
        Real.pi ^ 2 / 4 * ((L : ℝ) / (2 * Real.pi)) ^ 2 * g ζ := by
    intro ζ
    split_ifs with h
    · have hne : ζ ≠ 0 := by
        intro h0; rw [h0] at h
        have : radius (gridAngle (0 : Torus d L)) = 0 := by
          rw [gridAngle_zero]; simp [radius]
        linarith [h.1]
      have hJζ := maxAbs_le_floor ζ ha.le h.2
      have hgζ : g ζ = (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ := by
        simp only [hg]; rw [if_pos (hJζ : maxAbs d L ζ ≤ J)]
      rw [hgζ]
      have hr2 : 0 < radius (gridAngle ζ) ^ 2 := pow_pos h.1 2
      have h1 : (laplacianSymbol (gridAngle ζ))⁻¹ ≤ Real.pi ^ 2 / 4 *
          (radius (gridAngle ζ) ^ 2)⁻¹ := by
        rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) (laplacianSymbol_ge_radius ζ))
          (by positivity)]
        rw [mul_inv, inv_inv, inv_div]
        have := laplacianSymbol_ge_radius ζ
        linarith
      have h2 := term_le_of_ne_zero hne
      calc (laplacianSymbol (gridAngle ζ))⁻¹ ≤ Real.pi ^ 2 / 4 * (radius (gridAngle ζ) ^ 2)⁻¹ :=
            h1
        _ ≤ Real.pi ^ 2 / 4 * (((L : ℝ) / (2 * Real.pi)) ^ 2 *
              (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    · have : 0 ≤ g ζ := by simp only [hg]; split_ifs <;> positivity
      positivity
  -- the sum of `g`
  have hgsum : ∑ ζ : Torus d L, g ζ ≤ K * (J : ℝ) ^ (d - 2) := by
    have hfilt : ∑ ζ : Torus d L, g ζ = ∑ ζ ∈ Finset.univ.filter
        (fun ζ : Torus d L => maxAbs d L ζ ≤ J), (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_filter]
    have hmaps : ∀ ζ ∈ Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J),
        maxAbs d L ζ ∈ Finset.Icc 0 J := by
      intro ζ hζ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      simp [hζ]
    rw [hfilt, ← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfib : ∀ j ∈ Finset.Icc 0 J,
        ∑ ζ ∈ (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
          (fun ζ => maxAbs d L ζ = j), (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ ≤
        if j = 0 then 0 else K * (J : ℝ) ^ (d - 3) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      have heq : ∀ ζ ∈ (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
          (fun ζ => maxAbs d L ζ = j), (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ = (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
        intro ζ hζ
        simp only [Finset.mem_filter] at hζ
        rw [hζ.2]
      rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
      split_ifs with hj0
      · subst hj0; simp
      · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
        have hsub : (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
            (fun ζ => maxAbs d L ζ = j) ⊆ Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j) := by
          intro ζ hζ; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢; exact hζ.2
        have hcard := (Finset.card_le_card hsub).trans (card_level_le d L j hj1)
        have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
        have hcardR : (((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
            (fun ζ => maxAbs d L ζ = j)).card : ℝ) ≤ 2 * d * (3 * (j : ℝ)) ^ (d - 1) := by
          have h1 : (((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
              (fun ζ => maxAbs d L ζ = j)).card : ℝ) ≤ ((2 * d * (2 * j + 1) ^ (d - 1) : ℕ) : ℝ) := by
            exact_mod_cast hcard
          refine h1.trans ?_
          push_cast
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
          linarith
        have hd3 : d - 1 = (d - 3) + 2 := by omega
        have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj.2
        calc (((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
              (fun ζ => maxAbs d L ζ = j)).card : ℝ) * (((j : ℕ) : ℝ) ^ 2)⁻¹
            ≤ 2 * d * (3 * (j : ℝ)) ^ (d - 1) * (((j : ℕ) : ℝ) ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hcardR (by positivity)
          _ = K * (j : ℝ) ^ (d - 3) := by
              rw [hK, mul_pow, hd3, pow_add, pow_add]
              field_simp
          _ ≤ K * (J : ℝ) ^ (d - 3) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hjJ _) (by positivity)
    calc ∑ j ∈ Finset.Icc 0 J, ∑ ζ ∈ (Finset.univ.filter
            (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter (fun ζ => maxAbs d L ζ = j),
            (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹
        ≤ ∑ j ∈ Finset.Icc 0 J, (if j = 0 then 0 else K * (J : ℝ) ^ (d - 3)) :=
          Finset.sum_le_sum hfib
      _ ≤ ∑ j ∈ Finset.Icc 1 J, K * (J : ℝ) ^ (d - 3) := by
          rw [← Finset.sum_subset (s₁ := Finset.Icc 1 J) (s₂ := Finset.Icc 0 J)
            (f := fun j => if j = 0 then 0 else K * (J : ℝ) ^ (d - 3))
            (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
            (fun j hj hj' => by
              simp only [Finset.mem_Icc] at hj hj'
              have : j = 0 := by omega
              simp [this])]
          apply le_of_eq
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_Icc] at hj
          rw [if_neg (by omega)]
      _ = K * (J : ℝ) ^ (d - 2) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          have hd2 : d - 2 = (d - 3) + 1 := by omega
          rw [hd2, pow_succ]
          push_cast
          ring
  -- assemble
  have hJle : (J : ℝ) ≤ a * L / (2 * Real.pi) := Nat.floor_le (by positivity)
  have hJpow : (J : ℝ) ^ (d - 2) ≤ (a * L / (2 * Real.pi)) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) hJle _
  have ha_pow : a ^ (d - 2) ≤ a := by
    calc a ^ (d - 2) ≤ a ^ 1 := pow_le_pow_of_le_one ha.le ha1 (by omega)
      _ = a := pow_one a
  have hN : (Fintype.card (Torus d L) : ℝ) = (L : ℝ) ^ d := by
    exact AndersonAC.S3.card_torus
  unfold gridAvgReal
  rw [hN]
  calc ((L : ℝ) ^ d)⁻¹ * ∑ ζ : Torus d L,
        (if 0 < radius (gridAngle ζ) ∧ radius (gridAngle ζ) ≤ a
          then (laplacianSymbol (gridAngle ζ))⁻¹ else 0)
      ≤ ((L : ℝ) ^ d)⁻¹ * ∑ ζ : Torus d L,
          Real.pi ^ 2 / 4 * ((L : ℝ) / (2 * Real.pi)) ^ 2 * g ζ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ζ _ => hterm ζ) (by positivity)
    _ = ((L : ℝ) ^ d)⁻¹ * (Real.pi ^ 2 / 4 * ((L : ℝ) / (2 * Real.pi)) ^ 2) *
          ∑ ζ : Torus d L, g ζ := by rw [← Finset.mul_sum]; ring
    _ ≤ ((L : ℝ) ^ d)⁻¹ * (Real.pi ^ 2 / 4 * ((L : ℝ) / (2 * Real.pi)) ^ 2) *
          (K * (a * L / (2 * Real.pi)) ^ (d - 2)) := by
        apply mul_le_mul_of_nonneg_left (hgsum.trans
          (mul_le_mul_of_nonneg_left hJpow (by positivity))) (by positivity)
    _ = Real.pi ^ 2 / 4 * (1 / (2 * Real.pi)) ^ 2 * K * (1 / (2 * Real.pi)) ^ (d - 2) *
          a ^ (d - 2) := by
        have e1 : (a * L / (2 * Real.pi)) ^ (d - 2) =
            a ^ (d - 2) * (L : ℝ) ^ (d - 2) * (1 / (2 * Real.pi)) ^ (d - 2) := by
          rw [show a * L / (2 * Real.pi) = a * L * (1 / (2 * Real.pi)) by ring, mul_pow, mul_pow]
        have e2 : (L : ℝ) ^ d = (L : ℝ) ^ (d - 2) * (L : ℝ) ^ 2 := by
          rw [← pow_add]; congr 1; omega
        rw [e1, e2]
        field_simp
    _ ≤ Real.pi ^ 2 / 4 * (1 / (2 * Real.pi)) ^ 2 * K * (1 / (2 * Real.pi)) ^ (d - 2) * a :=
        mul_le_mul_of_nonneg_left ha_pow (by positivity)

/-- Low-frequency sum with the sharp power `a^{d-2}`. -/
theorem ball_frequency_sum_pow (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L → ∀ a : ℝ, 0 < a → a ≤ 1 →
      gridAvgReal (fun ζ : Torus d L =>
        if 0 < radius (gridAngle ζ) ∧ radius (gridAngle ζ) ≤ a
          then (laplacianSymbol (gridAngle ζ))⁻¹ else 0) ≤ C * a ^ (d - 2) := by
  have hpi := Real.pi_pos
  set K : ℝ := 2 * (d : ℝ) * (3 : ℝ) ^ (d - 1) with hK
  refine ⟨Real.pi ^ 2 / 4 * (1 / (2 * Real.pi)) ^ 2 * K * (1 / (2 * Real.pi)) ^ (d - 2),
    by positivity, fun L _ hL a ha ha1 => ?_⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  set J : ℕ := ⌊a * L / (2 * Real.pi)⌋₊ with hJ
  set g : Torus d L → ℝ := fun ζ =>
    if maxAbs d L ζ ≤ J then (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ else 0 with hg
  -- termwise comparison
  have hterm : ∀ ζ : Torus d L,
      (if 0 < radius (gridAngle ζ) ∧ radius (gridAngle ζ) ≤ a
        then (laplacianSymbol (gridAngle ζ))⁻¹ else 0) ≤
        Real.pi ^ 2 / 4 * ((L : ℝ) / (2 * Real.pi)) ^ 2 * g ζ := by
    intro ζ
    split_ifs with h
    · have hne : ζ ≠ 0 := by
        intro h0; rw [h0] at h
        have : radius (gridAngle (0 : Torus d L)) = 0 := by
          rw [gridAngle_zero]; simp [radius]
        linarith [h.1]
      have hJζ := maxAbs_le_floor ζ ha.le h.2
      have hgζ : g ζ = (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ := by
        simp only [hg]; rw [if_pos (hJζ : maxAbs d L ζ ≤ J)]
      rw [hgζ]
      have hr2 : 0 < radius (gridAngle ζ) ^ 2 := pow_pos h.1 2
      have h1 : (laplacianSymbol (gridAngle ζ))⁻¹ ≤ Real.pi ^ 2 / 4 *
          (radius (gridAngle ζ) ^ 2)⁻¹ := by
        rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) (laplacianSymbol_ge_radius ζ))
          (by positivity)]
        rw [mul_inv, inv_inv, inv_div]
        have := laplacianSymbol_ge_radius ζ
        linarith
      have h2 := term_le_of_ne_zero hne
      calc (laplacianSymbol (gridAngle ζ))⁻¹ ≤ Real.pi ^ 2 / 4 * (radius (gridAngle ζ) ^ 2)⁻¹ :=
            h1
        _ ≤ Real.pi ^ 2 / 4 * (((L : ℝ) / (2 * Real.pi)) ^ 2 *
              (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    · have : 0 ≤ g ζ := by simp only [hg]; split_ifs <;> positivity
      positivity
  -- the sum of `g`
  have hgsum : ∑ ζ : Torus d L, g ζ ≤ K * (J : ℝ) ^ (d - 2) := by
    have hfilt : ∑ ζ : Torus d L, g ζ = ∑ ζ ∈ Finset.univ.filter
        (fun ζ : Torus d L => maxAbs d L ζ ≤ J), (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_filter]
    have hmaps : ∀ ζ ∈ Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J),
        maxAbs d L ζ ∈ Finset.Icc 0 J := by
      intro ζ hζ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ
      simp [hζ]
    rw [hfilt, ← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfib : ∀ j ∈ Finset.Icc 0 J,
        ∑ ζ ∈ (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
          (fun ζ => maxAbs d L ζ = j), (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ ≤
        if j = 0 then 0 else K * (J : ℝ) ^ (d - 3) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      have heq : ∀ ζ ∈ (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
          (fun ζ => maxAbs d L ζ = j), (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹ = (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
        intro ζ hζ
        simp only [Finset.mem_filter] at hζ
        rw [hζ.2]
      rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
      split_ifs with hj0
      · subst hj0; simp
      · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
        have hsub : (Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
            (fun ζ => maxAbs d L ζ = j) ⊆ Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ = j) := by
          intro ζ hζ; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢; exact hζ.2
        have hcard := (Finset.card_le_card hsub).trans (card_level_le d L j hj1)
        have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
        have hcardR : (((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
            (fun ζ => maxAbs d L ζ = j)).card : ℝ) ≤ 2 * d * (3 * (j : ℝ)) ^ (d - 1) := by
          have h1 : (((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
              (fun ζ => maxAbs d L ζ = j)).card : ℝ) ≤ ((2 * d * (2 * j + 1) ^ (d - 1) : ℕ) : ℝ) := by
            exact_mod_cast hcard
          refine h1.trans ?_
          push_cast
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
          linarith
        have hd3 : d - 1 = (d - 3) + 2 := by omega
        have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj.2
        calc (((Finset.univ.filter (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter
              (fun ζ => maxAbs d L ζ = j)).card : ℝ) * (((j : ℕ) : ℝ) ^ 2)⁻¹
            ≤ 2 * d * (3 * (j : ℝ)) ^ (d - 1) * (((j : ℕ) : ℝ) ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hcardR (by positivity)
          _ = K * (j : ℝ) ^ (d - 3) := by
              rw [hK, mul_pow, hd3, pow_add, pow_add]
              field_simp
          _ ≤ K * (J : ℝ) ^ (d - 3) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hjJ _) (by positivity)
    calc ∑ j ∈ Finset.Icc 0 J, ∑ ζ ∈ (Finset.univ.filter
            (fun ζ : Torus d L => maxAbs d L ζ ≤ J)).filter (fun ζ => maxAbs d L ζ = j),
            (((maxAbs d L ζ : ℕ) : ℝ) ^ 2)⁻¹
        ≤ ∑ j ∈ Finset.Icc 0 J, (if j = 0 then 0 else K * (J : ℝ) ^ (d - 3)) :=
          Finset.sum_le_sum hfib
      _ ≤ ∑ j ∈ Finset.Icc 1 J, K * (J : ℝ) ^ (d - 3) := by
          rw [← Finset.sum_subset (s₁ := Finset.Icc 1 J) (s₂ := Finset.Icc 0 J)
            (f := fun j => if j = 0 then 0 else K * (J : ℝ) ^ (d - 3))
            (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
            (fun j hj hj' => by
              simp only [Finset.mem_Icc] at hj hj'
              have : j = 0 := by omega
              simp [this])]
          apply le_of_eq
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_Icc] at hj
          rw [if_neg (by omega)]
      _ = K * (J : ℝ) ^ (d - 2) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          have hd2 : d - 2 = (d - 3) + 1 := by omega
          rw [hd2, pow_succ]
          push_cast
          ring
  -- assemble
  have hJle : (J : ℝ) ≤ a * L / (2 * Real.pi) := Nat.floor_le (by positivity)
  have hJpow : (J : ℝ) ^ (d - 2) ≤ (a * L / (2 * Real.pi)) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) hJle _
  have ha_pow : a ^ (d - 2) ≤ a := by
    calc a ^ (d - 2) ≤ a ^ 1 := pow_le_pow_of_le_one ha.le ha1 (by omega)
      _ = a := pow_one a
  have hN : (Fintype.card (Torus d L) : ℝ) = (L : ℝ) ^ d := by
    exact AndersonAC.S3.card_torus
  unfold gridAvgReal
  rw [hN]
  calc ((L : ℝ) ^ d)⁻¹ * ∑ ζ : Torus d L,
        (if 0 < radius (gridAngle ζ) ∧ radius (gridAngle ζ) ≤ a
          then (laplacianSymbol (gridAngle ζ))⁻¹ else 0)
      ≤ ((L : ℝ) ^ d)⁻¹ * ∑ ζ : Torus d L,
          Real.pi ^ 2 / 4 * ((L : ℝ) / (2 * Real.pi)) ^ 2 * g ζ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ζ _ => hterm ζ) (by positivity)
    _ = ((L : ℝ) ^ d)⁻¹ * (Real.pi ^ 2 / 4 * ((L : ℝ) / (2 * Real.pi)) ^ 2) *
          ∑ ζ : Torus d L, g ζ := by rw [← Finset.mul_sum]; ring
    _ ≤ ((L : ℝ) ^ d)⁻¹ * (Real.pi ^ 2 / 4 * ((L : ℝ) / (2 * Real.pi)) ^ 2) *
          (K * (a * L / (2 * Real.pi)) ^ (d - 2)) := by
        apply mul_le_mul_of_nonneg_left (hgsum.trans
          (mul_le_mul_of_nonneg_left hJpow (by positivity))) (by positivity)
    _ = Real.pi ^ 2 / 4 * (1 / (2 * Real.pi)) ^ 2 * K * (1 / (2 * Real.pi)) ^ (d - 2) *
          a ^ (d - 2) := by
        have e1 : (a * L / (2 * Real.pi)) ^ (d - 2) =
            a ^ (d - 2) * (L : ℝ) ^ (d - 2) * (1 / (2 * Real.pi)) ^ (d - 2) := by
          rw [show a * L / (2 * Real.pi) = a * L * (1 / (2 * Real.pi)) by ring, mul_pow, mul_pow]
        have e2 : (L : ℝ) ^ d = (L : ℝ) ^ (d - 2) * (L : ℝ) ^ 2 := by
          rw [← pow_add]; congr 1; omega
        rw [e1, e2]
        field_simp

theorem norm_character {L : ℕ} [NeZero L] (k x : Torus d L) : ‖character k x‖ = 1 := by
  unfold character
  rw [Complex.norm_exp]
  simp

theorem radius_pos_of_ne {L : ℕ} [NeZero L] {k : Torus d L} (hk : k ≠ 0) :
    0 < radius (gridAngle k) := by
  obtain ⟨j, hj⟩ := exists_gridAngle_ne hk
  unfold radius
  apply Real.sqrt_pos.mpr
  have : 0 < gridAngle k j ^ 2 := by positivity
  exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => gridAngle k i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j))

/-- The Fourier form of `Λ⁺`. -/
theorem form_laplacianPlus (hC : CirculantCalculusStatement) {L : ℕ} [NeZero L] (hL : 4 ≤ L)
    (v : Torus d L → ℂ) :
    form (laplacianPlus (d := d) (L := L)) v = gridAvgReal (fun k =>
      (if k = 0 then 0 else (laplacianSymbol (gridAngle k))⁻¹) * ‖fourier v k‖ ^ 2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨mΛ, hΛ, hΛsym⟩, -⟩ := hC d L hL
  have hℓ0 : laplacianSymbol (gridAngle (0 : Torus d L)) = 0 := by
    rw [gridAngle_zero]; simp [laplacianSymbol]
  have hℓpos : ∀ k : Torus d L, k ≠ 0 → 0 < laplacianSymbol (gridAngle k) := fun k hk =>
    lt_of_lt_of_le (by have := radius_pos_of_ne hk; positivity) (laplacianSymbol_ge_radius k)
  obtain ⟨mΛX, hΛX, hΛXsym⟩ := inverseOnConstants_circulant hC hL mΛ
    (by rw [hΛsym, hℓ0]; simp)
    (fun ζ hζ => by rw [hΛsym]; exact_mod_cast (hℓpos ζ hζ).ne')
  have hΛPeq : laplacianPlus (d := d) (L := L) = circulant mΛX := by
    unfold laplacianPlus; rw [hΛ]; convert hΛX using 2
  rw [hΛPeq]
  refine form_circulant_real hC hL mΛX _ (fun ζ => ?_) v
  rw [hΛXsym, hΛsym]
  by_cases h : ζ = 0 <;> simp [h]

theorem siteSum_fourier_le {L : ℕ} [NeZero L] {A : Type*} [Fintype A] (π : A → Torus d L)
    (y : A → ℂ) (k : Torus d L) : ‖fourier (siteSum π y) k‖ ≤ normOne y := by
  unfold fourier siteSum normOne
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ x : Torus d L, ‖(∑ a ∈ Finset.univ.filter (fun a => π a = x), y a) *
      star (character k x)‖ ≤ ∑ a ∈ Finset.univ.filter (fun a => π a = x), ‖y a‖ := by
    intro x
    rw [norm_mul, norm_star, norm_character, mul_one]
    exact norm_sum_le _ _
  refine (Finset.sum_le_sum fun x _ => h1 x).trans (le_of_eq ?_)
  exact Finset.sum_fiberwise Finset.univ π (fun a => ‖y a‖)

theorem siteSum_normSq_le {L : ℕ} [NeZero L] {A : Type*} [Fintype A] (π : A → Torus d L)
    (hπ : atMostTwo π) (y : A → ℂ) : normSq (siteSum π y) ≤ 2 * normSq y := by
  unfold normSq siteSum
  have h1 : ∀ x : Torus d L, ‖∑ a ∈ Finset.univ.filter (fun a => π a = x), y a‖ ^ 2 ≤
      2 * ∑ a ∈ Finset.univ.filter (fun a => π a = x), ‖y a‖ ^ 2 := by
    intro x
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ.filter (fun a => π a = x))
      (f := fun a => ‖y a‖)
    have hn : ‖∑ a ∈ Finset.univ.filter (fun a => π a = x), y a‖ ≤
        ∑ a ∈ Finset.univ.filter (fun a => π a = x), ‖y a‖ := norm_sum_le _ _
    have hc : ((Finset.univ.filter (fun a => π a = x)).card : ℝ) ≤ 2 := by
      exact_mod_cast hπ x
    have h0 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a => π a = x), ‖y a‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc ‖∑ a ∈ Finset.univ.filter (fun a => π a = x), y a‖ ^ 2
        ≤ (∑ a ∈ Finset.univ.filter (fun a => π a = x), ‖y a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ _ := hcs
      _ ≤ 2 * ∑ a ∈ Finset.univ.filter (fun a => π a = x), ‖y a‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hc h0
  refine (Finset.sum_le_sum fun x _ => h1 x).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_fiberwise Finset.univ π (fun a => ‖y a‖ ^ 2)

theorem normSq_le_normOne_sq {A : Type*} [Fintype A] (y : A → ℂ) :
    normSq y ≤ normOne y ^ 2 := by
  unfold normSq normOne
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun b => ‖y a‖ * ‖y b‖)
    (fun b _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ a)

/-- **Lemma 3.2 (Fourier charge estimate)**, conditional on the circulant calculus. -/
theorem fourier_charge_of (hC : CirculantCalculusStatement) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L →
      ∀ (A : Type*) [Fintype A] (π : A → Torus d L), atMostTwo π → ∀ y : A → ℂ,
        form laplacianPlus (siteSum π y) ≤
          C * Real.rpow (normOne y) (4 / 3) * Real.rpow (Real.sqrt (normSq y)) (2 / 3) := by
  obtain ⟨C₁, hC₁, hball⟩ := ball_frequency_sum (d := d) hd
  have hpi := Real.pi_pos
  refine ⟨C₁ + Real.pi ^ 2 / 2, by positivity, fun L _ hL A _ π hπ y => ?_⟩
  set v := siteSum π y with hv
  set M1 := normOne y with hM1
  set S2 := normSq y with hS2
  have hM10 : 0 ≤ M1 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hRHS0 : 0 ≤ (C₁ + Real.pi ^ 2 / 2) * Real.rpow M1 (4 / 3) *
      Real.rpow (Real.sqrt S2) (2 / 3) := by
    have := Real.rpow_nonneg hM10 (4 / 3)
    have := Real.rpow_nonneg (Real.sqrt_nonneg S2) (2 / 3)
    positivity
  rw [form_laplacianPlus hC hL v]
  -- degenerate case
  by_cases hS : S2 = 0
  · have hy : ∀ a, y a = 0 := by
      intro a
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖y b‖)).mp hS a
        (Finset.mem_univ a)
      exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
    have hv0 : ∀ k, fourier v k = 0 := by
      intro k
      unfold fourier; rw [hv]; unfold siteSum
      simp [hy]
    refine le_trans (le_of_eq ?_) hRHS0
    unfold gridAvgReal
    simp [hv0]
  have hS2pos : 0 < S2 := lt_of_le_of_ne hS20 (Ne.symm hS)
  have hM1S : Real.sqrt S2 ≤ M1 := by
    rw [Real.sqrt_le_left hM10]; exact normSq_le_normOne_sq y
  have hsq0 : 0 < Real.sqrt S2 := Real.sqrt_pos.mpr hS2pos
  have hM1pos : 0 < M1 := lt_of_lt_of_le hsq0 hM1S
  set ρ := Real.sqrt S2 / M1 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hM1pos]; exact hM1S
  set a := Real.rpow ρ (2 / 3) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hρ0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by norm_num)
  -- pointwise split
  have hpt : ∀ k : Torus d L,
      (if k = 0 then 0 else (laplacianSymbol (gridAngle k))⁻¹) * ‖fourier v k‖ ^ 2 ≤
        M1 ^ 2 * (if 0 < radius (gridAngle k) ∧ radius (gridAngle k) ≤ a
          then (laplacianSymbol (gridAngle k))⁻¹ else 0) +
        Real.pi ^ 2 / (4 * a ^ 2) * ‖fourier v k‖ ^ 2 := by
    intro k
    have hF := siteSum_fourier_le π y k
    have hF2 : ‖fourier v k‖ ^ 2 ≤ M1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hF 2
    have hsec : 0 ≤ Real.pi ^ 2 / (4 * a ^ 2) * ‖fourier v k‖ ^ 2 := by positivity
    by_cases hk : k = 0
    · simp only [if_pos hk, zero_mul]
      have : 0 ≤ M1 ^ 2 * (if 0 < radius (gridAngle k) ∧ radius (gridAngle k) ≤ a
          then (laplacianSymbol (gridAngle k))⁻¹ else 0) := by
        apply mul_nonneg (sq_nonneg _)
        split_ifs
        · exact inv_nonneg.mpr (le_trans (by positivity) (laplacianSymbol_ge_radius k))
        · exact le_rfl
      linarith
    · rw [if_neg hk]
      have hr := radius_pos_of_ne hk
      have hℓ := laplacianSymbol_ge_radius k
      have hℓpos : 0 < laplacianSymbol (gridAngle k) := lt_of_lt_of_le (by positivity) hℓ
      by_cases hra : radius (gridAngle k) ≤ a
      · rw [if_pos ⟨hr, hra⟩]
        have : (laplacianSymbol (gridAngle k))⁻¹ * ‖fourier v k‖ ^ 2 ≤
            M1 ^ 2 * (laplacianSymbol (gridAngle k))⁻¹ := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right hF2 (by positivity)
        linarith
      · rw [if_neg (fun h => hra h.2)]
        push Not at hra
        have h1 : (laplacianSymbol (gridAngle k))⁻¹ ≤ Real.pi ^ 2 / (4 * a ^ 2) := by
          rw [inv_le_comm₀ hℓpos (by positivity), inv_div]
          have : 4 / Real.pi ^ 2 * a ^ 2 ≤ laplacianSymbol (gridAngle k) := by
            refine le_trans ?_ hℓ
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0.le hra.le 2) (by positivity)
          calc 4 * a ^ 2 / Real.pi ^ 2 = 4 / Real.pi ^ 2 * a ^ 2 := by ring
            _ ≤ _ := this
        have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖fourier v k‖)
        simp only [mul_zero, zero_add]
        exact this
  -- average
  have hP : gridAvgReal (fun k : Torus d L => ‖fourier v k‖ ^ 2) ≤ 2 * S2 := by
    obtain ⟨-, h2, -⟩ := hC d L hL
    rw [← h2 v]; exact siteSum_normSq_le π hπ y
  calc gridAvgReal (fun k => (if k = 0 then 0 else (laplacianSymbol (gridAngle k))⁻¹) *
        ‖fourier v k‖ ^ 2)
      ≤ gridAvgReal (fun k => M1 ^ 2 * (if 0 < radius (gridAngle k) ∧ radius (gridAngle k) ≤ a
          then (laplacianSymbol (gridAngle k))⁻¹ else 0) +
          Real.pi ^ 2 / (4 * a ^ 2) * ‖fourier v k‖ ^ 2) := gridAvgReal_mono hpt
    _ = M1 ^ 2 * gridAvgReal (fun k : Torus d L =>
          if 0 < radius (gridAngle k) ∧ radius (gridAngle k) ≤ a
            then (laplacianSymbol (gridAngle k))⁻¹ else 0) +
        Real.pi ^ 2 / (4 * a ^ 2) * gridAvgReal (fun k : Torus d L => ‖fourier v k‖ ^ 2) := by
        rw [gridAvgReal_add, gridAvgReal_mul_left, gridAvgReal_mul_left]
    _ ≤ M1 ^ 2 * (C₁ * a) + Real.pi ^ 2 / (4 * a ^ 2) * (2 * S2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hball L hL a ha0 ha1) (sq_nonneg _)
        · exact mul_le_mul_of_nonneg_left hP (by positivity)
    _ = (C₁ + Real.pi ^ 2 / 2) * (M1 ^ 2 * a) := by
        -- `S2 / a² = M1² a` since `a³ = ρ²` and `S2 = M1² ρ²`
        have ha3 : a ^ 3 = ρ ^ 2 := by
          rw [ha, Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]; norm_num
        have hS2eq : S2 = M1 ^ 2 * ρ ^ 2 := by
          rw [hρ, div_pow, Real.sq_sqrt hS20]; field_simp
        have : S2 / a ^ 2 = M1 ^ 2 * a := by
          rw [div_eq_iff (by positivity), hS2eq, ← ha3]; ring
        have e : Real.pi ^ 2 / (4 * a ^ 2) * (2 * S2) = Real.pi ^ 2 / 2 * (S2 / a ^ 2) := by
          field_simp; ring
        rw [e, this]; ring
    _ = (C₁ + Real.pi ^ 2 / 2) * Real.rpow M1 (4 / 3) * Real.rpow (Real.sqrt S2) (2 / 3) := by
        have hsqrt : Real.sqrt S2 = M1 * ρ := by rw [hρ]; field_simp
        rw [hsqrt, Real.rpow_eq_pow, Real.rpow_eq_pow, Real.mul_rpow hM10 hρ0.le]
        have e1 : M1 ^ 2 = M1 ^ (4 / 3 : ℝ) * M1 ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_add hM1pos]; norm_num
        rw [e1, ha, Real.rpow_eq_pow]; ring

/-- The planned `site_sum_bounds` (§3, proof of Lemma 3.2). -/
theorem site_sum_bounds_proof {L : ℕ} [NeZero L] {A : Type*} [Fintype A] (π : A → Torus d L)
    (hπ : atMostTwo π) (y : A → ℂ) :
    normSq (siteSum π y) ≤ 2 * normSq y ∧
    (∀ k : Torus d L, ‖fourier (siteSum π y) k‖ ≤ normOne y) ∧
    (neutral y → neutral (siteSum π y)) := by
  refine ⟨siteSum_normSq_le π hπ y, siteSum_fourier_le π y, fun hy => ?_⟩
  unfold neutral siteSum at *
  rw [Finset.sum_fiberwise Finset.univ π y]
  exact hy

/-- The planned `laplacian_symbol_comparison`: `ℓ ≍ |θ|²` on the grid. -/
theorem laplacian_symbol_comparison_proof {L : ℕ} [NeZero L] (_hL : 4 ≤ L) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k : Torus d L,
      c * radius (gridAngle k) ^ 2 ≤ laplacianSymbol (gridAngle k) ∧
      laplacianSymbol (gridAngle k) ≤ C * radius (gridAngle k) ^ 2 := by
  refine ⟨4 / Real.pi ^ 2, 1, by have := Real.pi_pos; positivity, one_pos, fun k =>
    ⟨laplacianSymbol_ge_radius k, ?_⟩⟩
  rw [laplacianSymbol_eq_sum, radius_sq_eq, one_mul]
  exact Finset.sum_le_sum fun j _ => hsq_le_sq _

/-- The planned `frequency_sum_bound`. -/
theorem frequency_sum_bound_proof (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 4 ≤ L → ∀ a : ℝ,
      0 < a → a ≤ 1 →
      gridAvgReal (fun k : Torus d L =>
        if 0 < radius (gridAngle k) ∧ radius (gridAngle k) ≤ a
          then (laplacianSymbol (gridAngle k))⁻¹ else 0) ≤ C * a ^ (d - 2) ∧
      C * a ^ (d - 2) ≤ C * a := by
  obtain ⟨C, hC, h⟩ := ball_frequency_sum_pow (d := d) hd
  refine ⟨C, hC, fun L _ hL a ha ha1 => ⟨h L hL a ha ha1, ?_⟩⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  calc a ^ (d - 2) ≤ a ^ 1 := pow_le_pow_of_le_one ha.le ha1 (by omega)
    _ = a := pow_one a

end AndersonAC.S3
